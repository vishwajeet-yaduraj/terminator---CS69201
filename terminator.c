
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct
{
    char *data;
    size_t length;
    size_t capacity;
} TextBuffer;


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


int main(void)
{
    // Connect to X11
    Display *display = XOpenDisplay(NULL);

    if (display == NULL)
    {
        fprintf(stderr, "Could not connect to X11\n");
        return 1;
    }

    // Initialize terminal history
    TextBuffer buffer;

    if (!text_buffer_init(&buffer))
    {
        fprintf(stderr, "Could not allocate text buffer\n");
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
        input_length = 0;
        input[0] = '\0';
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
    free(buffer.data);
    XCloseDisplay(display);

    return 0;
}
