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
    // Create a text buffer
TextBuffer buffer;

if (!text_buffer_init(&buffer))
{
    fprintf(stderr, "Could not allocate text buffer\n");
    XCloseDisplay(display);
    return 1;
}

// Temporary sample text for testing
const char *sample_text =
    "user@terminator> pwd\n"
    "/home/vishwajeet/terminator\n"
    "user@terminator> ls\n"
    "terminator.c  x11_input.c\n"
    "Buffer growth test: line 1\n"
    "Buffer growth test: line 2\n"
    "Buffer growth test: line 3\n"
    "Buffer growth test: line 4\n"
    "Buffer growth test: line 5\n"
    "Buffer growth test: line 6\n"
    "Buffer growth test: line 7\n"
    "Buffer growth test: line 8\n"
    "Buffer growth test: line 9\n"
    "Buffer growth test: line 10\n";

if (!text_buffer_append(&buffer, sample_text))
{
    fprintf(stderr, "Could not append sample text\n");
    free(buffer.data);
    XCloseDisplay(display);
    return 1;
}



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

    // Select events and display the window
    XSelectInput(display, window, ExposureMask | KeyPressMask);
    XMapWindow(display, window);

    // Set up drawing
    GC gc = XCreateGC(display, window, 0, NULL);
    XFontStruct *font = XLoadQueryFont(display, "fixed");

    if (font != NULL)
    {
        XSetFont(display, gc, font->fid);
    }

    // Main event loop
    while (1)
    {
        XEvent event;
        XNextEvent(display, &event);

        if (event.type == Expose)
        {
            const char *title = "Terminator - Task 1";
            

            XClearWindow(display, window);

            XDrawString(
                display, window, gc,
                30, 40, title, strlen(title)
            );

            // Draw text stored in the buffer
int x = 30;
int y = 80;
size_t start = 0;

for (size_t i = 0; i <= buffer.length; i++)
{
    if (buffer.data[i] == '\n' || buffer.data[i] == '\0')
    {
        XDrawString(
            display,
            window,
            gc,
            x,
            y,
            buffer.data + start,
            (int)(i - start)
        );

        y += 22;
        start = i + 1;
    }
}

            
        }
        else if (event.type == KeyPress)
        {
            char buffer[10];
            KeySym key;

            XLookupString(
                &event.xkey,
                buffer,
                sizeof(buffer),
                &key,
                NULL
            );

            if (key == XK_Escape)
            {
                break;
            }
        }
    }

    // Release resources
    if (font != NULL)
    {
        XFreeFont(display, font);
    }

    XFreeGC(display, gc);
    XDestroyWindow(display, window);
    free(buffer.data);
    XCloseDisplay(display);

    return 0;
}

