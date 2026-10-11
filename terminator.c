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

#define MAX_TABS 8
#define INPUT_CAPACITY 256
#define TAB_BAR_Y 7
#define TAB_BAR_HEIGHT 28
#define TAB_BAR_LEFT 10
#define TAB_BAR_TOP 5
#define TERMINAL_TOP 58
#define LINE_HEIGHT 22
#define TAB_WIDTH_MAX 160
#define TAB_WIDTH_MIN 28
#define PLUS_WIDTH 28

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

typedef struct
{
    TextBuffer history;
    ShellProcess shell;
    char input[INPUT_CAPACITY];
    size_t input_length;
    size_t scroll_offset;
    int is_open;
} Tab;

static void close_if_open(int *fd)
{
    if (fd != NULL && *fd >= 0)
    {
        (void)close(*fd);
        *fd = -1;
    }
}

static int text_buffer_init(TextBuffer *buffer)
{
    buffer->data = malloc(128);
    if (buffer->data == NULL)
    {
        buffer->length = 0;
        buffer->capacity = 0;
        return 0;
    }

    buffer->length = 0;
    buffer->capacity = 128;
    buffer->data[0] = '\0';
    return 1;
}

static int text_buffer_append_n(
    TextBuffer *buffer,
    const char *text,
    size_t text_length
)
{
    if (buffer->length == SIZE_MAX ||
        text_length > SIZE_MAX - buffer->length - 1)
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

static int finish_command_line(TextBuffer *buffer)
{
    if (buffer->length == 0 || buffer->data[buffer->length - 1] != '\n')
    {
        return text_buffer_append_n(buffer, "\n", 1);
    }
    return 1;
}

static int set_close_on_exec(int fd)
{
    int flags = fcntl(fd, F_GETFD);
    if (flags == -1)
    {
        return 0;
    }
    return fcntl(fd, F_SETFD, flags | FD_CLOEXEC) != -1;
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

    int all_fds[] = {to_shell[0], to_shell[1], from_shell[0], from_shell[1]};
    for (size_t i = 0; i < sizeof(all_fds) / sizeof(all_fds[0]); i++)
    {
        if (!set_close_on_exec(all_fds[i]))
        {
            perror("fcntl FD_CLOEXEC");
            close_if_open(&to_shell[0]);
            close_if_open(&to_shell[1]);
            close_if_open(&from_shell[0]);
            close_if_open(&from_shell[1]);
            return 0;
        }
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

        execl("/bin/bash", "bash", "--noprofile", "--norc", (char *)NULL);
        _exit(127);
    }

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

    char request[INPUT_CAPACITY + 160];
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
        ssize_t n = write(shell->input_fd, request + sent, request_length - sent);
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
            perror("write to Bash");
            return 0;
        }
    }

    shell->marker_length = strlen(shell->marker);
    shell->marker_pending_length = 0;
    shell->command_running = 1;
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
        if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)
        {
            return 1;
        }
        perror("read from Bash");
        return 0;
    }

    if (count == 0)
    {
        if (shell->marker_pending_length > 0 &&
            !text_buffer_append_n(
                buffer,
                shell->marker_pending,
                shell->marker_pending_length))
        {
            return 0;
        }

        shell->marker_pending_length = 0;
        shell->marker_length = 0;
        shell->command_running = 0;
        shell->alive = 0;
        close_if_open(&shell->output_fd);
        return finish_command_line(buffer);
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

        while (shell->marker_pending_length > 0)
        {
            size_t pending_length = shell->marker_pending_length;
            int is_prefix =
                pending_length <= shell->marker_length &&
                memcmp(shell->marker_pending, shell->marker, pending_length) == 0;

            if (is_prefix)
            {
                if (pending_length == shell->marker_length)
                {
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
    pid_t pid = shell->pid;
    int reaped = 0;

    if (pid > 0)
    {
        // Stop Bash and commands in its process group.
        (void)kill(-pid, SIGTERM);
    }

    close_if_open(&shell->input_fd);
    close_if_open(&shell->output_fd);

    if (pid > 0)
    {
        int status = 0;
        for (int attempt = 0; attempt < 10; attempt++)
        {
            pid_t result = waitpid(pid, &status, WNOHANG);
            if (result == pid || (result == -1 && errno == ECHILD))
            {
                reaped = 1;
                break;
            }
            if (result == -1 && errno != EINTR)
            {
                reaped = 1;
                break;
            }

            struct timespec delay = {0, 20 * 1000 * 1000};
            (void)nanosleep(&delay, NULL);
        }

        // The shell may have exited while a command is still alive in
        // the same process group, so force-stop the group after the grace period.
        (void)kill(-pid, SIGKILL);

        if (!reaped)
        {
            pid_t result;
            do
            {
                result = waitpid(pid, &status, 0);
            }
            while (result == -1 && errno == EINTR);
        }

        shell->pid = -1;
    }

    shell->alive = 0;
    shell->command_running = 0;
}

static int tab_init(Tab *tab)
{
    memset(tab, 0, sizeof(*tab));
    tab->shell.pid = -1;
    tab->shell.input_fd = -1;
    tab->shell.output_fd = -1;

    if (!text_buffer_init(&tab->history))
    {
        return 0;
    }

    if (!shell_start(&tab->shell))
    {
        free(tab->history.data);
        tab->history.data = NULL;
        tab->history.length = 0;
        tab->history.capacity = 0;
        return 0;
    }

    tab->is_open = 1;
    return 1;
}

static void tab_destroy(Tab *tab)
{
    if (!tab->is_open)
    {
        return;
    }

    shell_close(&tab->shell);
    free(tab->history.data);
    memset(tab, 0, sizeof(*tab));
    tab->shell.pid = -1;
    tab->shell.input_fd = -1;
    tab->shell.output_fd = -1;
}

static int tab_width_for(int window_width, size_t tab_count)
{
    if (tab_count == 0)
    {
        return TAB_WIDTH_MIN;
    }

    int width = (window_width - 50) / (int)tab_count;
    if (width > TAB_WIDTH_MAX)
    {
        width = TAB_WIDTH_MAX;
    }
    if (width < TAB_WIDTH_MIN)
    {
        width = TAB_WIDTH_MIN;
    }
    return width;
}

static int plus_x_for(int tab_width, size_t tab_count)
{
    return TAB_BAR_LEFT + tab_width * (int)tab_count + 6;
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
    Tab *tab,
    size_t tab_index,
    size_t tab_count
)
{
    XWindowAttributes attributes;
    int window_width = 800;
    int window_height = 500;
    if (XGetWindowAttributes(display, window, &attributes))
    {
        window_width = attributes.width;
        window_height = attributes.height;
    }

    XClearWindow(display, window);

    // Draw the tab bar. The selected tab is black with white text.
    int tab_width = tab_width_for(window_width, tab_count);
    for (size_t i = 0; i < tab_count; i++)
    {
        int x = TAB_BAR_LEFT + tab_width * (int)i;
        if (i == tab_index)
        {
            XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
            XFillRectangle(display, window, gc, x, TAB_BAR_Y, (unsigned int)tab_width, TAB_BAR_HEIGHT);
            XSetForeground(display, gc, WhitePixel(display, DefaultScreen(display)));
        }
        else
        {
            XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
            XDrawRectangle(display, window, gc, x, TAB_BAR_Y, (unsigned int)tab_width, TAB_BAR_HEIGHT);
        }

        char label[32];
        (void)snprintf(label, sizeof(label), "Tab %zu", i + 1);
        XDrawString(display, window, gc, x + 8, TAB_BAR_Y + 19, label, (int)strlen(label));
        if (tab_width >= 48)
        {
            XDrawString(display, window, gc, x + tab_width - 17, TAB_BAR_Y + 19, "x", 1);
        }
    }

    XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
    int plus_x = plus_x_for(tab_width, tab_count);
    XDrawRectangle(display, window, gc, plus_x, TAB_BAR_Y, PLUS_WIDTH, TAB_BAR_HEIGHT);
    XDrawString(display, window, gc, plus_x + 10, TAB_BAR_Y + 19, "+", 1);

    const char *prompt = "user@terminator> ";
    int x = 15;
    int y = TERMINAL_TOP;

    size_t history_lines = 0;
    for (size_t i = 0; i < tab->history.length; i++)
    {
        if (tab->history.data[i] == '\n')
        {
            history_lines++;
        }
    }
    if (tab->history.length > 0 &&
        tab->history.data[tab->history.length - 1] != '\n')
    {
        history_lines++;
    }

    int available_height = window_height - TERMINAL_TOP - 10;
    int visible_rows_int = available_height / LINE_HEIGHT;
    if (visible_rows_int < 1)
    {
        visible_rows_int = 1;
    }
    size_t rows = (size_t)visible_rows_int;
    size_t total_rows = history_lines + 1; // History plus prompt/status row.
    size_t max_scroll = total_rows > rows ? total_rows - rows : 0;
    if (tab->scroll_offset > max_scroll)
    {
        tab->scroll_offset = max_scroll;
    }

    size_t first_line = max_scroll - tab->scroll_offset;
    size_t end_line = first_line + rows;
    size_t line_number = 0;
    size_t start = 0;

    for (size_t i = 0; i < tab->history.length; i++)
    {
        if (tab->history.data[i] == '\n')
        {
            if (line_number >= first_line && line_number < end_line)
            {
                XDrawString(
                    display, window, gc, x, y,
                    tab->history.data + start,
                    (int)(i - start)
                );
                y += LINE_HEIGHT;
            }
            line_number++;
            start = i + 1;
        }
    }

    if (start < tab->history.length)
    {
        if (line_number >= first_line && line_number < end_line)
        {
            XDrawString(
                display, window, gc, x, y,
                tab->history.data + start,
                (int)(tab->history.length - start)
            );
            y += LINE_HEIGHT;
        }
        line_number++;
    }

    // Draw the prompt/status only if that row is currently visible.
    if (history_lines >= first_line && history_lines < end_line)
    {
        if (tab->shell.command_running)
        {
            const char *status = "[Command running...]";
            XDrawString(display, window, gc, x, y, status, (int)strlen(status));
        }
        else if (!tab->shell.alive)
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
                tab->input, (int)tab->input_length
            );
        }
    }

    XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
    XFlush(display);
}

static int add_tab(Tab tabs[MAX_TABS], size_t *tab_count, size_t *active_tab)
{
    if (*tab_count >= MAX_TABS)
    {
        (void)text_buffer_append(&tabs[*active_tab].history, "[Terminator: maximum of 8 tabs reached]\n");
        tabs[*active_tab].scroll_offset = 0;
        return 0;
    }

    if (!tab_init(&tabs[*tab_count]))
    {
        // During initial startup there may not yet be an active tab
        // to which an error could be written.
        if (*tab_count > 0 && tabs[*active_tab].is_open)
        {
            (void)text_buffer_append(
                &tabs[*active_tab].history,
                "[Terminator: could not open new tab]\n"
            );
            tabs[*active_tab].scroll_offset = 0;
        }
        return 0;
    }

    *active_tab = *tab_count;
    (*tab_count)++;
    return 1;
}

static void close_tab_at(
    Tab tabs[MAX_TABS],
    size_t *tab_count,
    size_t *active_tab,
    size_t index
)
{
    if (index >= *tab_count)
    {
        return;
    }

    size_t old_active = *active_tab;
    tab_destroy(&tabs[index]);

    // Move remaining structs left. Ownership of their allocated history
    // and process descriptors moves with each struct assignment.
    for (size_t i = index; i + 1 < *tab_count; i++)
    {
        tabs[i] = tabs[i + 1];
    }

    (*tab_count)--;
    memset(&tabs[*tab_count], 0, sizeof(tabs[*tab_count]));
    tabs[*tab_count].shell.pid = -1;
    tabs[*tab_count].shell.input_fd = -1;
    tabs[*tab_count].shell.output_fd = -1;

    if (*tab_count == 0)
    {
        *active_tab = 0;
    }
    else if (old_active > index)
    {
        *active_tab = old_active - 1;
    }
    else if (old_active == index)
    {
        *active_tab = index < *tab_count ? index : *tab_count - 1;
    }
    else
    {
        *active_tab = old_active;
    }
}

static int handle_tab_shortcut(
    KeySym key,
    unsigned int state,
    Tab tabs[MAX_TABS],
    size_t *tab_count,
    size_t *active_tab,
    int *running
)
{
    int control = (state & ControlMask) != 0;
    int shift = (state & ShiftMask) != 0;

    if (control && shift && (key == XK_t || key == XK_T))
    {
        (void)add_tab(tabs, tab_count, active_tab);
        if (*tab_count == 0)
        {
            *running = 0;
        }
        return 1;
    }

    if (control && shift && (key == XK_w || key == XK_W))
    {
        close_tab_at(tabs, tab_count, active_tab, *active_tab);
        if (*tab_count == 0)
        {
            *running = 0;
        }
        return 1;
    }

    if (control && key == XK_Tab)
    {
        if (*tab_count > 1)
        {
            if (shift)
            {
                *active_tab = (*active_tab + *tab_count - 1) % *tab_count;
            }
            else
            {
                *active_tab = (*active_tab + 1) % *tab_count;
            }
        }
        return 1;
    }

    return 0;
}

int main(void)
{
    Display *display = XOpenDisplay(NULL);
    if (display == NULL)
    {
        fprintf(stderr, "Could not connect to X11\n");
        return 1;
    }

    (void)signal(SIGPIPE, SIG_IGN);

    // Child shells started later must not keep the X11 connection open.
    int x11_fd = ConnectionNumber(display);
    int x11_fd_flags = fcntl(x11_fd, F_GETFD);
    if (x11_fd_flags != -1)
    {
        (void)fcntl(x11_fd, F_SETFD, x11_fd_flags | FD_CLOEXEC);
    }

    Tab tabs[MAX_TABS];
    memset(tabs, 0, sizeof(tabs));
    for (size_t i = 0; i < MAX_TABS; i++)
    {
        tabs[i].shell.pid = -1;
        tabs[i].shell.input_fd = -1;
        tabs[i].shell.output_fd = -1;
    }

    size_t tab_count = 0;
    size_t active_tab = 0;
    if (!add_tab(tabs, &tab_count, &active_tab))
    {
        XCloseDisplay(display);
        return 1;
    }

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
    XSelectInput(display, window, ExposureMask | KeyPressMask | ButtonPressMask);
    XMapWindow(display, window);

    GC gc = XCreateGC(display, window, 0, NULL);
    XFontStruct *font = XLoadQueryFont(display, "fixed");
    if (font == NULL)
    {
        fprintf(stderr, "Could not load X11 font\n");
        XFreeGC(display, gc);
        XDestroyWindow(display, window);
        for (size_t i = 0; i < tab_count; i++)
        {
            tab_destroy(&tabs[i]);
        }
        XCloseDisplay(display);
        return 1;
    }
    XSetFont(display, gc, font->fid);

    int running = 1;
    while (running)
    {
        // Process X11 events already queued by Xlib.
        while (XPending(display) > 0 && running)
        {
            XEvent event;
            XNextEvent(display, &event);

            if (event.type == Expose)
            {
                draw_terminal(
                    display, window, gc, font,
                    &tabs[active_tab], active_tab, tab_count
                );
            }
            else if (event.type == KeyPress)
            {
                char key_buffer[32];
                KeySym key;
                int n = XLookupString(
                    &event.xkey,
                    key_buffer,
                    (int)sizeof(key_buffer),
                    &key,
                    NULL
                );

                if (key == XK_Escape)
                {
                    running = 0;
                    continue;
                }

                if (handle_tab_shortcut(
                        key, event.xkey.state,
                        tabs, &tab_count, &active_tab, &running))
                {
                    request_redraw(display, window);
                    continue;
                }

                Tab *tab = &tabs[active_tab];
                int changed = 0;

                if (key == XK_Page_Up)
                {
                    tab->scroll_offset += 10;
                    changed = 1;
                }
                else if (key == XK_Page_Down)
                {
                    tab->scroll_offset = tab->scroll_offset > 10
                        ? tab->scroll_offset - 10 : 0;
                    changed = 1;
                }
                else if (key == XK_End)
                {
                    tab->scroll_offset = 0;
                    changed = 1;
                }
                else if (tab->shell.command_running || !tab->shell.alive)
                {
                    // Keep tab switching and scrolling available, but don't
                    // edit or submit input while this tab's command is running.
                }
                else if (key == XK_Return || key == XK_KP_Enter)
                {
                    char submitted_line[INPUT_CAPACITY + 32];
                    int written = snprintf(
                        submitted_line,
                        sizeof(submitted_line),
                        "user@terminator> %s\n",
                        tab->input
                    );

                    if (written >= 0 &&
                        (size_t)written < sizeof(submitted_line) &&
                        text_buffer_append(&tab->history, submitted_line))
                    {
                        if (tab->input_length > 0 &&
                            !shell_submit_command(&tab->shell, tab->input))
                        {
                            (void)text_buffer_append(
                                &tab->history,
                                "[Terminator: could not submit command]\n"
                            );
                        }
                        tab->input_length = 0;
                        tab->input[0] = '\0';
                        tab->scroll_offset = 0;
                        changed = 1;
                    }
                    else
                    {
                        (void)text_buffer_append(
                            &tab->history,
                            "[Terminator: could not store command]\n"
                        );
                        tab->scroll_offset = 0;
                        changed = 1;
                    }
                }
                else if (key == XK_BackSpace)
                {
                    if (tab->input_length > 0)
                    {
                        tab->input_length--;
                        tab->input[tab->input_length] = '\0';
                        changed = 1;
                    }
                }
                else
                {
                    for (int i = 0;
                         i < n && tab->input_length < sizeof(tab->input) - 1;
                         i++)
                    {
                        unsigned char ch = (unsigned char)key_buffer[i];
                        if (ch >= 32 && ch != 127)
                        {
                            tab->input[tab->input_length++] = (char)ch;
                            changed = 1;
                        }
                    }
                    tab->input[tab->input_length] = '\0';
                }

                if (changed)
                {
                    request_redraw(display, window);
                }
            }
            else if (event.type == ButtonPress)
            {
                if (event.xbutton.button == Button4 ||
                    event.xbutton.button == Button5)
                {
                    if (event.xbutton.y >= TERMINAL_TOP - 10)
                    {
                        Tab *tab = &tabs[active_tab];
                        if (event.xbutton.button == Button4)
                        {
                            tab->scroll_offset += 3;
                        }
                        else
                        {
                            tab->scroll_offset = tab->scroll_offset > 3
                                ? tab->scroll_offset - 3 : 0;
                        }
                        request_redraw(display, window);
                    }
                }
                else if (event.xbutton.button == Button1 &&
                         event.xbutton.y >= TAB_BAR_TOP &&
                         event.xbutton.y <= TAB_BAR_Y + TAB_BAR_HEIGHT)
                {
                    XWindowAttributes attributes;
                    int ww = 800;
                    if (XGetWindowAttributes(display, window, &attributes))
                    {
                        ww = attributes.width;
                    }
                    int tab_width = tab_width_for(ww, tab_count);
                    int plus_x = plus_x_for(tab_width, tab_count);
                    int px = event.xbutton.x;

                    if (px >= plus_x && px < plus_x + PLUS_WIDTH)
                    {
                        (void)add_tab(tabs, &tab_count, &active_tab);
                    }
                    else if (px >= TAB_BAR_LEFT &&
                             px < TAB_BAR_LEFT + tab_width * (int)tab_count)
                    {
                        size_t clicked = (size_t)((px - TAB_BAR_LEFT) / tab_width);
                        if (clicked < tab_count)
                        {
                            int close_x = TAB_BAR_LEFT + tab_width * (int)clicked + tab_width - 22;
                            if (px >= close_x)
                            {
                                close_tab_at(tabs, &tab_count, &active_tab, clicked);
                                if (tab_count == 0)
                                {
                                    running = 0;
                                }
                            }
                            else
                            {
                                active_tab = clicked;
                            }
                        }
                    }
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

        // Wait for X11 activity and output from every open tab's shell.
        struct pollfd fds[MAX_TABS + 1];
        int fd_to_tab[MAX_TABS + 1];
        nfds_t fd_count = 1;

        fds[0].fd = ConnectionNumber(display);
        fds[0].events = POLLIN;
        fds[0].revents = 0;
        fd_to_tab[0] = -1;

        for (size_t i = 0; i < tab_count; i++)
        {
            if (tabs[i].is_open && tabs[i].shell.output_fd >= 0)
            {
                fds[fd_count].fd = tabs[i].shell.output_fd;
                fds[fd_count].events = POLLIN | POLLHUP | POLLERR;
                fds[fd_count].revents = 0;
                fd_to_tab[fd_count] = (int)i;
                fd_count++;
            }
        }

        int result = poll(fds, fd_count, -1);
        if (result == -1)
        {
            if (errno == EINTR)
            {
                continue;
            }
            perror("poll");
            break;
        }

        if (fds[0].revents & (POLLERR | POLLHUP | POLLNVAL))
        {
            fprintf(stderr, "X11 connection failed\n");
            break;
        }

        for (nfds_t i = 1; i < fd_count; i++)
        {
            if (fds[i].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL))
            {
                int tab_index = fd_to_tab[i];
                if (tab_index < 0 || (size_t)tab_index >= tab_count)
                {
                    continue;
                }

                Tab *tab = &tabs[tab_index];
                if (!shell_handle_output(&tab->shell, &tab->history))
                {
                    (void)text_buffer_append(
                        &tab->history,
                        "[Terminator: failed to read Bash output]\n"
                    );
                    shell_close(&tab->shell);
                }

                if ((size_t)tab_index == active_tab)
                {
                    request_redraw(display, window);
                }
            }
        }
    }

    XFreeFont(display, font);
    XFreeGC(display, gc);
    XDestroyWindow(display, window);

    for (size_t i = 0; i < tab_count; i++)
    {
        tab_destroy(&tabs[i]);
    }

    XCloseDisplay(display);
    return 0;
}
