#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <stdio.h>
#include <string.h>

int main(void)
{
    // Connect to X11
    Display *display = XOpenDisplay(NULL);

    if (display == NULL)
    {
        fprintf(stderr, "Could not connect to X11\n");
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
            const char *prompt = "user@terminator> ";

            XClearWindow(display, window);

            XDrawString(
                display, window, gc,
                30, 40, title, strlen(title)
            );

            XDrawString(
                display, window, gc,
                30, 80, prompt, strlen(prompt)
            );
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
    XCloseDisplay(display);

    return 0;
}

