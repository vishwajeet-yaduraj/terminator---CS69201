#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>

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
} ShellProcess;


// Initialize an empty text buffer
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


// Append text to the buffer, growing it if necessary
static int text_buffer_append(TextBuffer *buffer, const char *text)
{
    size_t text_length = strlen(text);
    size_t required = buffer->length + text_length + 1;

    if (required > buffer->capacity)
    {
        size_t new_capacity = buffer->capacity;

        while (new_capacity < required)
        {
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

    memcpy(
        buffer->data + buffer->length,
        text,
        text_length + 1
    );

    buffer->length += text_length;

    return 1;
}

static int shell_start(ShellProcess *shell)
{
    int to_shell[2];
    int from_shell[2];

    if (pipe(to_shell) == -1)
    {
        perror("pipe to shell");
        return 0;
    }

    if (pipe(from_shell) == -1)
    {
        perror("pipe from shell");
        close(to_shell[0]);
        close(to_shell[1]);
        return 0;
    }

    pid_t child = fork();

    if (child == -1)
    {
        perror("fork");
        close(to_shell[0]);
        close(to_shell[1]);
        close(from_shell[0]);
        close(from_shell[1]);
        return 0;
    }

    if (child == 0)
    {
        // Child process: connect the pipes to Bash
        close(to_shell[1]);
        close(from_shell[0]);

        if (dup2(to_shell[0], STDIN_FILENO) == -1 ||
            dup2(from_shell[1], STDOUT_FILENO) == -1 ||
            dup2(from_shell[1], STDERR_FILENO) == -1)
        {
            _exit(126);
        }

        close(to_shell[0]);
        close(from_shell[1]);

        execl(
            "/bin/bash",
            "bash",
            "--noprofile",
            "--norc",
            (char *)NULL
        );

        _exit(127);
    }

    // Parent process: retain only the required pipe ends
    close(to_shell[0]);
    close(from_shell[1]);

    shell->pid = child;
    shell->input_fd = to_shell[1];
    shell->output_fd = from_shell[0];
    shell->command_id = 1;

    return 1;
}


static int flush_output_chunk(
    TextBuffer *buffer,
    char *chunk,
    size_t *length
)
{
    if (*length == 0)
    {
        return 1;
    }

    chunk[*length] = '\0';

    int success = text_buffer_append(buffer, chunk);

    *length = 0;

    return success;
}


static int shell_run_command(
    ShellProcess *shell,
    TextBuffer *buffer,
    const char *command
)
{
    char marker[96];
    char request[512];

    int marker_size = snprintf(
        marker,
        sizeof(marker),
        "__TERMINATOR_DONE_%ld_%lu__",
        (long)shell->pid,
        shell->command_id++
    );

    if (marker_size < 0 ||
        (size_t)marker_size >= sizeof(marker))
    {
        return 0;
    }

    // Send the command, followed by a unique completion marker
    int request_size = snprintf(
        request,
        sizeof(request),
        "%s\nprintf '%%s' '%s'\n",
        command,
        marker
    );

    if (request_size < 0 ||
        (size_t)request_size >= sizeof(request))
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
            perror("write to Bash");
            return 0;
        }
    }

    // Read output until we encounter this command's marker
    size_t marker_length = strlen(marker);
    char pending[96];
    size_t pending_length = 0;

    char output_chunk[1025];
    size_t output_length = 0;

    int found_marker = 0;
    int success = 1;

    while (!found_marker)
    {
        char ch;

        ssize_t n = read(
            shell->output_fd,
            &ch,
            1
        );

        if (n == 0)
        {
            break;
        }

        if (n == -1)
        {
            if (errno == EINTR)
            {
                continue;
            }

            perror("read from Bash");
            success = 0;
            break;
        }

        pending[pending_length++] = ch;

        if (pending_length == marker_length)
        {
            if (memcmp(pending, marker, marker_length) == 0)
            {
                found_marker = 1;
                break;
            }

            // The first pending byte cannot be part of
            // a marker beginning at this position.
            output_chunk[output_length++] = pending[0];

            memmove(
                pending,
                pending + 1,
                --pending_length
            );

            if (output_length == sizeof(output_chunk) - 1)
            {
                if (!flush_output_chunk(
                        buffer,
                        output_chunk,
                        &output_length))
                {
                    success = 0;
                }
            }
        }
    }

    // Preserve any unread output if Bash stopped unexpectedly
    if (!found_marker)
    {
        for (size_t i = 0; i < pending_length; i++)
        {
            output_chunk[output_length++] = pending[i];

            if (output_length == sizeof(output_chunk) - 1)
            {
                if (!flush_output_chunk(
                        buffer,
                        output_chunk,
                        &output_length))
                {
                    success = 0;
                }
            }
        }
    }

    if (!flush_output_chunk(
            buffer,
            output_chunk,
            &output_length))
    {
        success = 0;
    }

    return found_marker && success;
}


static void shell_close(ShellProcess *shell)
{
    // Closing the input pipe tells Bash that no more
    // commands will be sent.
    close(shell->input_fd);
    close(shell->output_fd);

    int status;
    pid_t result;

    do
    {
        result = waitpid(shell->pid, &status, 0);
    }
    while (result == -1 && errno == EINTR);
}


int main(void)
{
    // Connect to X11
    Display *display = XOpenDisplay(NULL);

    if (display == NULL)
    {
        fprintf(stderr, "Could not connect to X11\n");
        return 1;
    }
    signal(SIGPIPE, SIG_IGN);

    // Initialize terminal history
    TextBuffer buffer;

    if (!text_buffer_init(&buffer))
    {
        fprintf(stderr, "Could not allocate text buffer\n");
        XCloseDisplay(display);
        return 1;
    }

    // Start the persistent Bash session
ShellProcess shell;

if (!shell_start(&shell))
{
    fprintf(stderr, "Could not start Bash\n");
    free(buffer.data);
    XCloseDisplay(display);
    return 1;
}



    // Current command being typed
    char input[256] = "";
    size_t input_length = 0;

    int screen = DefaultScreen(display);

    // Create the window
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

    // Allow the window manager's close button to work
    Atom wm_delete_window =
        XInternAtom(display, "WM_DELETE_WINDOW", False);

    XSetWMProtocols(
        display,
        window,
        &wm_delete_window,
        1
    );

    // Select events and show the window
    XSelectInput(
        display,
        window,
        ExposureMask | KeyPressMask
    );

    XMapWindow(display, window);

    // Set up drawing
    GC gc = XCreateGC(display, window, 0, NULL);

    XFontStruct *font = XLoadQueryFont(display, "fixed");

if (font == NULL)
{
    fprintf(stderr, "Could not load font\n");

    XFreeGC(display, gc);
    XDestroyWindow(display, window);

    shell_close(&shell);  // ADD THIS LINE

    free(buffer.data);
    XCloseDisplay(display);

    return 1;
}
    XSetFont(display, gc, font->fid);

    // Main event loop
    int running = 1;

    while (running)
    {
        XEvent event;

        // Wait for the next X11 event
        XNextEvent(display, &event);

        if (event.type == Expose)
        {
            const char *title = "Terminator - Task 1";
            const char *prompt = "user@terminator> ";

            XClearWindow(display, window);

            // Draw the title
            XDrawString(
                display,
                window,
                gc,
                30, 40,
                title,
                (int)strlen(title)
            );

            // Draw terminal history, one line at a time
            int x = 30;
            int y = 80;
            size_t start = 0;

            for (size_t i = 0; i < buffer.length; i++)
            {
                if (buffer.data[i] == '\n')
                {
                    XDrawString(
                        display,
                        window,
                        gc,
                        x, y,
                        buffer.data + start,
                        (int)(i - start)
                    );

                    y += 22;
                    start = i + 1;
                }
            }

            // Draw any remaining text
            if (start < buffer.length)
            {
                XDrawString(
                    display,
                    window,
                    gc,
                    x, y,
                    buffer.data + start,
                    (int)(buffer.length - start)
                );

                y += 22;
            }

            // Draw the prompt
            XDrawString(
                display,
                window,
                gc,
                x, y,
                prompt,
                (int)strlen(prompt)
            );

            // Calculate the prompt width
            int prompt_width = XTextWidth(
                font,
                prompt,
                (int)strlen(prompt)
            );

            // Draw the current command input
            XDrawString(
                display,
                window,
                gc,
                x + prompt_width, y,
                input,
                (int)input_length
            );

            // Send drawing requests to the display
            XFlush(display);
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

    // Escape exits the application
    if (key == XK_Escape)
    {
        running = 0;
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
        // Execute the submitted command if it isn't empty
        if (input_length > 0)
        {
           if (!shell_run_command(&shell, &buffer, input))
{
    text_buffer_append(
        &buffer,
        "[Terminator: Bash communication failed]\n"
    );
}
        }

        // Clear the command input
        input_length = 0;
        input[0] = '\0';

        // Request a redraw
        changed = 1;
    }
}


    // Backspace deletes the last typed character
    else if (key == XK_BackSpace)
    {
        if (input_length > 0)
        {
            input_length--;
            input[input_length] = '\0';
            changed = 1;
        }
    }
    // Add ordinary printable characters
    else
    {
        for (int i = 0;
             i < n && input_length < sizeof(input) - 1;
             i++)
        {
            unsigned char ch = (unsigned char)key_buffer[i];

            if (ch >= 32 && ch != 127)
            {
                input[input_length] = (char)ch;
                input_length++;
                changed = 1;
            }
        }

        input[input_length] = '\0';
    }

    // Request a redraw when the input changes
    if (changed)
    {
        XClearArea(display, window, 0, 0, 0, 0, True);
        XFlush(display);
    }
}
   
        else if (
            event.type == ClientMessage &&
            (Atom)event.xclient.data.l[0] == wm_delete_window
        )
        {
            // Handle the window manager's close button
            running = 0;
        }
    }

    // Release resources after the event loop ends
    XFreeFont(display, font);
    XFreeGC(display, gc);
    XDestroyWindow(display, window);

    shell_close(&shell);  // ADD THIS LINE

    free(buffer.data);
    XCloseDisplay(display);

    return 0;
}
