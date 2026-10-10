#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

typedef struct
{
    char *data;
    size_t length;
    size_t capacity;
} TextBuffer;

typedef struct
{
    pid_t pid;
    int input_fd;
    int output_fd;
    unsigned long command_id;

    char marker[96];
    size_t marker_length;
    char marker_pending[96];
    size_t marker_pending_length;

    int command_running;
    int alive;
} ShellProcess;

static int text_buffer_init(TextBuffer *buffer)
{
    buffer->capacity = 128;
    buffer->length = 0;
    buffer->data = malloc(buffer->capacity);

    if (buffer->data == NULL)
    {
        buffer->capacity = 0;
        return 0;
    }

    buffer->data[0] = '\0';
    return 1;
}

static int text_buffer_append_n(
    TextBuffer *buffer,
    const char *text,
    size_t text_length
)
{
    if (text_length > SIZE_MAX - buffer->length - 1)
    {
        return 0;
    }

    size_t required = buffer->length + text_length + 1;

    if (required > buffer->capacity)
    {
        size_t new_capacity = buffer->capacity;

        while (new_capacity < required)
        {
            if (new_capacity > SIZE_MAX / 2)
            {
                new_capacity = required;
                break;
            }
            new_capacity *= 2;
        }

        char *new_data = realloc(buffer->data, new_capacity);
        if (new_data == NULL)
        {
            return 0;
        }

        buffer->data = new_data;
        buffer->capacity = new_capacity;
    }

    if (text_length > 0)
    {
        memcpy(buffer->data + buffer->length, text, text_length);
    }

    buffer->length += text_length;
    buffer->data[buffer->length] = '\0';
    return 1;
}

static int text_buffer_append(TextBuffer *buffer, const char *text)
{
    return text_buffer_append_n(buffer, text, strlen(text));
}

static void close_if_open(int *fd)
{
    if (*fd >= 0)
    {
        (void)close(*fd);
        *fd = -1;
    }
}

static int shell_start(ShellProcess *shell)
{
    int to_shell[2] = {-1, -1};
    int from_shell[2] = {-1, -1};

    shell->pid = -1;
    shell->input_fd = -1;
    shell->output_fd = -1;
    shell->command_id = 1;
    shell->marker_length = 0;
    shell->marker_pending_length = 0;
    shell->command_running = 0;
    shell->alive = 0;

    if (pipe(to_shell) == -1)
    {
        perror("pipe to Bash");
        return 0;
    }

    if (pipe(from_shell) == -1)
    {
        perror("pipe from Bash");
        close_if_open(&to_shell[0]);
        close_if_open(&to_shell[1]);
        return 0;
    }

    pid_t child = fork();

    if (child == -1)
    {
        perror("fork");
        close_if_open(&to_shell[0]);
        close_if_open(&to_shell[1]);
        close_if_open(&from_shell[0]);
        close_if_open(&from_shell[1]);
        return 0;
    }

    if (child == 0)
    {
        // Give Bash and its commands a process group we can clean up.
        (void)setpgid(0, 0);
        (void)signal(SIGPIPE, SIG_DFL);

        close_if_open(&to_shell[1]);
        close_if_open(&from_shell[0]);

        if (dup2(to_shell[0], STDIN_FILENO) == -1 ||
            dup2(from_shell[1], STDOUT_FILENO) == -1 ||
            dup2(from_shell[1], STDERR_FILENO) == -1)
        {
            _exit(126);
        }

        close_if_open(&to_shell[0]);
        close_if_open(&from_shell[1]);

        execl(
            "/bin/bash",
            "bash",
            "--noprofile",
            "--norc",
            (char *)NULL
        );

        _exit(127);
    }

    // Also set the process group from the parent to avoid a race.
    (void)setpgid(child, child);

    close_if_open(&to_shell[0]);
    close_if_open(&from_shell[1]);

    shell->pid = child;
    shell->input_fd = to_shell[1];
    shell->output_fd = from_shell[0];
    shell->alive = 1;

    return 1;
}

static int shell_submit_command(ShellProcess *shell, const char *command)
{
    if (!shell->alive || shell->input_fd < 0 || shell->command_running)
    {
        return 0;
    }

    char request[512];
    unsigned long id = shell->command_id++;

    int marker_size = snprintf(
        shell->marker,
        sizeof(shell->marker),
        "__TERMINATOR_DONE_%ld_%lu__",
        (long)shell->pid,
        id
    );

    if (marker_size < 0 || (size_t)marker_size >= sizeof(shell->marker))
    {
        return 0;
    }

    int request_size = snprintf(
        request,
        sizeof(request),
        "%s\nprintf '%%s' '%s'\n",
        command,
        shell->marker
    );

    if (request_size < 0 || (size_t)request_size >= sizeof(request))
    {
        return 0;
    }

    size_t request_length = (size_t)request_size;
    size_t sent = 0;

    while (sent < request_length)
    {
        ssize_t n = write(
            shell->input_fd,
            request + sent,
            request_length - sent
        );

        if (n > 0)
        {
            sent += (size_t)n;
        }
        else if (n == -1 && errno == EINTR)
        {
            continue;
        }
        else
        {
            return 0;
        }
    }

    shell->marker_length = strlen(shell->marker);
    shell->marker_pending_length = 0;
    shell->command_running = 1;
    return 1;
}

static int finish_command_line(TextBuffer *buffer)
{
    if (buffer->length == 0 || buffer->data[buffer->length - 1] != '\n')
    {
        return text_buffer_append_n(buffer, "\n", 1);
    }
    return 1;
}

static int shell_handle_output(ShellProcess *shell, TextBuffer *buffer)
{
    if (shell->output_fd < 0)
    {
        return 1;
    }

    char incoming[4096];
    ssize_t count = read(shell->output_fd, incoming, sizeof(incoming));

    if (count == -1)
    {
        if (errno == EINTR)
        {
            return 1;
        }
        return 0;
    }

    if (count == 0)
    {
        // If Bash ends halfway through a possible marker, preserve those bytes.
        if (shell->marker_pending_length > 0)
        {
            if (!text_buffer_append_n(
                    buffer,
                    shell->marker_pending,
                    shell->marker_pending_length))
            {
                return 0;
            }
        }

        shell->marker_pending_length = 0;
        shell->marker_length = 0;
        shell->command_running = 0;
        shell->alive = 0;
        close_if_open(&shell->output_fd);
        (void)finish_command_line(buffer);
        return 1;
    }

    char visible[sizeof(incoming) + sizeof(shell->marker_pending) + 1];
    size_t visible_length = 0;
    int command_completed = 0;

    for (size_t i = 0; i < (size_t)count; i++)
    {
        char ch = incoming[i];

        if (!shell->command_running || shell->marker_length == 0)
        {
            visible[visible_length++] = ch;
            continue;
        }

        shell->marker_pending[shell->marker_pending_length++] = ch;

        // Preserve a possible marker prefix. Release bytes that cannot match.
        while (shell->marker_pending_length > 0)
        {
            size_t pending_length = shell->marker_pending_length;
            int is_prefix =
                pending_length <= shell->marker_length &&
                memcmp(
                    shell->marker_pending,
                    shell->marker,
                    pending_length
                ) == 0;

            if (is_prefix)
            {
                if (pending_length == shell->marker_length)
                {
                    // The marker marks the end of this command; don't display it.
                    shell->marker_pending_length = 0;
                    shell->marker_length = 0;
                    shell->command_running = 0;
                    command_completed = 1;
                }
                break;
            }

            visible[visible_length++] = shell->marker_pending[0];
            memmove(
                shell->marker_pending,
                shell->marker_pending + 1,
                pending_length - 1
            );
            shell->marker_pending_length--;
        }
    }

    if (visible_length > 0 &&
        !text_buffer_append_n(buffer, visible, visible_length))
    {
        return 0;
    }

    if (command_completed && !finish_command_line(buffer))
    {
        return 0;
    }

    return 1;
}

static void shell_close(ShellProcess *shell)
{
    // Terminate Bash and any command still running in its process group.
    if (shell->pid > 0)
    {
        (void)kill(-shell->pid, SIGTERM);
    }

    close_if_open(&shell->input_fd);
    close_if_open(&shell->output_fd);

    if (shell->pid > 0)
    {
        int status = 0;
        pid_t result = -1;

        // Give the process a short chance to handle SIGTERM.
        for (int attempt = 0; attempt < 10; attempt++)
        {
            result = waitpid(shell->pid, &status, WNOHANG);
            if (result == shell->pid || (result == -1 && errno == ECHILD))
            {
                shell->pid = -1;
                break;
            }
            if (result == -1 && errno != EINTR)
            {
                shell->pid = -1;
                break;
            }

            struct timespec delay = {0, 20 * 1000 * 1000};
            (void)nanosleep(&delay, NULL);
        }

        if (shell->pid > 0)
        {
            (void)kill(-shell->pid, SIGKILL);
            do
            {
                result = waitpid(shell->pid, &status, 0);
            }
            while (result == -1 && errno == EINTR);
            shell->pid = -1;
        }
    }

    shell->alive = 0;
    shell->command_running = 0;
}

static void request_redraw(Display *display, Window window)
{
    XClearArea(display, window, 0, 0, 0, 0, True);
    XFlush(display);
}

static void draw_terminal(
    Display *display,
    Window window,
    GC gc,
    XFontStruct *font,
    const TextBuffer *buffer,
    const char *input,
    size_t input_length,
    const ShellProcess *shell
)
{
    const char *title = "Terminator - Task 1";
    const char *prompt = "user@terminator> ";
    const int x = 30;
    int y = 80;
    size_t start = 0;

    XClearWindow(display, window);

    XDrawString(
        display, window, gc,
        x, 40,
        title, (int)strlen(title)
    );

    // Draw each complete history line.
    for (size_t i = 0; i < buffer->length; i++)
    {
        if (buffer->data[i] == '\n')
        {
            XDrawString(
                display, window, gc,
                x, y,
                buffer->data + start,
                (int)(i - start)
            );
            y += 22;
            start = i + 1;
        }
    }

    // Draw any final line that does not end in a newline.
    if (start < buffer->length)
    {
        XDrawString(
            display, window, gc,
            x, y,
            buffer->data + start,
            (int)(buffer->length - start)
        );
        y += 22;
    }

    if (shell->command_running)
    {
        const char *status = "[Command running...]";
        XDrawString(display, window, gc, x, y, status, (int)strlen(status));
    }
    else if (!shell->alive)
    {
        const char *status = "[Bash session ended]";
        XDrawString(display, window, gc, x, y, status, (int)strlen(status));
    }
    else
    {
        XDrawString(display, window, gc, x, y, prompt, (int)strlen(prompt));

        int prompt_width = XTextWidth(font, prompt, (int)strlen(prompt));
        XDrawString(
            display, window, gc,
            x + prompt_width, y,
            input, (int)input_length
        );
    }

    XFlush(display);
}

int main(void)
{
    Display *display = XOpenDisplay(NULL);
    if (display == NULL)
    {
        fprintf(stderr, "Could not connect to X11\n");
        return 1;
    }

    // The parent should receive EPIPE instead of being killed if Bash exits.
    (void)signal(SIGPIPE, SIG_IGN);

    TextBuffer buffer;
    if (!text_buffer_init(&buffer))
    {
        fprintf(stderr, "Could not allocate terminal buffer\n");
        XCloseDisplay(display);
        return 1;
    }

    ShellProcess shell;
    if (!shell_start(&shell))
    {
        fprintf(stderr, "Could not start Bash\n");
        free(buffer.data);
        XCloseDisplay(display);
        return 1;
    }

    char input[256] = "";
    size_t input_length = 0;
    int running = 1;

    int screen = DefaultScreen(display);
    Window window = XCreateSimpleWindow(
        display,
        RootWindow(display, screen),
        100, 100,
        800, 500,
        1,
        BlackPixel(display, screen),
        WhitePixel(display, screen)
    );

    XStoreName(display, window, "Terminator - Task 1");

    Atom wm_delete_window = XInternAtom(display, "WM_DELETE_WINDOW", False);
    (void)XSetWMProtocols(display, window, &wm_delete_window, 1);

    XSelectInput(display, window, ExposureMask | KeyPressMask);
    XMapWindow(display, window);

    GC gc = XCreateGC(display, window, 0, NULL);
    XFontStruct *font = XLoadQueryFont(display, "fixed");

    if (font == NULL)
    {
        fprintf(stderr, "Could not load X11 font\n");
        XFreeGC(display, gc);
        XDestroyWindow(display, window);
        shell_close(&shell);
        free(buffer.data);
        XCloseDisplay(display);
        return 1;
    }

    XSetFont(display, gc, font->fid);

    while (running)
    {
        // Process all X11 events already queued in Xlib.
        while (XPending(display) > 0 && running)
        {
            XEvent event;
            XNextEvent(display, &event);

            if (event.type == Expose)
            {
                draw_terminal(
                    display, window, gc, font,
                    &buffer, input, input_length, &shell
                );
            }
            else if (event.type == KeyPress)
            {
                char key_buffer[10];
                KeySym key;
                int n = XLookupString(
                    &event.xkey,
                    key_buffer,
                    sizeof(key_buffer),
                    &key,
                    NULL
                );

                int changed = 0;

                if (key == XK_Escape)
                {
                    running = 0;
                }
                else if (shell.command_running || !shell.alive)
                {
                    // While a command runs, or after Bash exits,
                    // ignore input other than Escape.
                }
                else if (key == XK_Return || key == XK_KP_Enter)
                {
                    char submitted_line[sizeof(input) + 32];
                    int written = snprintf(
                        submitted_line,
                        sizeof(submitted_line),
                        "user@terminator> %s\n",
                        input
                    );

                    if (written >= 0 &&
                        (size_t)written < sizeof(submitted_line) &&
                        text_buffer_append(&buffer, submitted_line))
                    {
                        if (input_length > 0 &&
                            !shell_submit_command(&shell, input))
                        {
                            (void)text_buffer_append(
                                &buffer,
                                "[Terminator: could not submit command]\n"
                            );
                        }

                        input_length = 0;
                        input[0] = '\0';
                        changed = 1;
                    }
                    else
                    {
                        (void)text_buffer_append(
                            &buffer,
                            "[Terminator: could not store command]\n"
                        );
                        changed = 1;
                    }
                }
                else if (key == XK_BackSpace)
                {
                    if (input_length > 0)
                    {
                        input_length--;
                        input[input_length] = '\0';
                        changed = 1;
                    }
                }
                else
                {
                    for (int i = 0;
                         i < n && input_length < sizeof(input) - 1;
                         i++)
                    {
                        unsigned char ch = (unsigned char)key_buffer[i];
                        if (ch >= 32 && ch != 127)
                        {
                            input[input_length++] = (char)ch;
                            changed = 1;
                        }
                    }
                    input[input_length] = '\0';
                }

                if (changed)
                {
                    request_redraw(display, window);
                }
            }
            else if (event.type == ClientMessage &&
                     (Atom)event.xclient.data.l[0] == wm_delete_window)
            {
                running = 0;
            }
        }

        if (!running)
        {
            break;
        }

        // Sleep until X11 has an event or Bash has output ready.
        struct pollfd fds[2];
        fds[0].fd = ConnectionNumber(display);
        fds[0].events = POLLIN;
        fds[0].revents = 0;

        fds[1].fd = shell.output_fd;
        fds[1].events = POLLIN | POLLHUP | POLLERR;
        fds[1].revents = 0;

        int result = poll(fds, 2, -1);
        if (result == -1)
        {
            if (errno == EINTR)
            {
                continue;
            }

            (void)text_buffer_append(&buffer, "[Terminator: poll failed]\n");
            request_redraw(display, window);
            break;
        }

        if (fds[0].revents & (POLLERR | POLLHUP | POLLNVAL))
        {
            break;
        }

        if (fds[1].fd >= 0 &&
            (fds[1].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)))
        {
            if (!shell_handle_output(&shell, &buffer))
            {
                (void)text_buffer_append(
                    &buffer,
                    "[Terminator: failed to read Bash output]\n"
                );
                shell.alive = 0;
                shell.command_running = 0;
                close_if_open(&shell.output_fd);
                close_if_open(&shell.input_fd);
            }

            request_redraw(display, window);
        }
    }

    // Release X11 objects and stop/reap Bash on exit.
    XFreeFont(display, font);
    XFreeGC(display, gc);
    XDestroyWindow(display, window);
    shell_close(&shell);
    free(buffer.data);
    XCloseDisplay(display);

    return 0;
}
