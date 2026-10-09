#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <stdio.h>

int main()
{
    // Connect to X11
    Display *display = XOpenDisplay(NULL);

    if (display == NULL)
    {
        printf("Could not connect to X11\n");
        return 1;
    }

    // Create the window
    Window window = XCreateSimpleWindow(
        display,
        RootWindow(display, 0),
        100, 100,
        800, 400,
        1,
        BlackPixel(display, 0),
        WhitePixel(display, 0)
    );

    // Tell X11 which events we want
    XSelectInput(display, window, ExposureMask | KeyPressMask);

    // Show the window
    XMapWindow(display, window);

    // Create drawing settings
    GC gc = XCreateGC(display, window, 0, NULL);

    // Load font
    XFontStruct *font = XLoadQueryFont(display, "fixed");
    XSetFont(display, gc, font->fid);

    // Store everything the user types
    char text[256] = "";
    int length = 0;

    // Position of cursor inside text
    int cursor_pos = 0;

    while (1)
    {
        XEvent event;

        // Wait for the next event
        XNextEvent(display, &event);

        // Window needs to be drawn
        if (event.type == Expose)
        {
            XClearWindow(display, window);

            // Draw prompt
            XDrawString(
                display,
                window,
                gc,
                50, 50,
                "Type something:",
                15
            );

            // Draw typed text
            int x = 50;
            int y = 75;
            int start = 0;

            for (int i = 0; i <= length; i++)
            {
                if (text[i] == '\n' || text[i] == '\0')
                {
                    XDrawString(
                        display,
                        window,
                        gc,
                        x,
                        y,
                        text + start,
                        i - start
                    );

                    y += 25;
                    start = i + 1;
                }
            }

            // Find beginning of current line
            int line_start = 0;

            for (int i = cursor_pos - 1; i >= 0; i--)
            {
                if (text[i] == '\n')
                {
                    line_start = i + 1;
                    break;
                }
            }

            // Number of characters before cursor on current line
            int current_line_length = cursor_pos - line_start;

            // Find cursor X position
            int cursor_x = 50 + XTextWidth(
                font,
                text + line_start,
                current_line_length
            );

            // Find cursor Y position
            int cursor_y = 75;

            for (int i = 0; i < cursor_pos; i++)
            {
                if (text[i] == '\n')
                {
                    cursor_y += 25;
                }
            }

            // Draw cursor
            XFillRectangle(
                display,
                window,
                gc,
                cursor_x,
                cursor_y - 18,
                2,
                20
            );

            XFlush(display);
        }

        // Keyboard key pressed
        else if (event.type == KeyPress)
        {
            char buffer[10];
            KeySym key;

            int n = XLookupString(
                &event.xkey,
                buffer,
                sizeof(buffer),
                &key,
                NULL
            );

            // Escape = exit
            if (key == XK_Escape)
            {
                break;
            }

            // Move cursor left
            else if (key == XK_Left)
            {
                if (cursor_pos > 0)
                {
                    cursor_pos--;
                }
            }

            // Move cursor right
            else if (key == XK_Right)
            {
                if (cursor_pos < length)
                {
                    cursor_pos++;
                }
            }

            // Move cursor up
            else if (key == XK_Up)
            {
                // Find beginning of current line
                int current_line_start = 0;

                for (int i = cursor_pos - 1; i >= 0; i--)
                {
                    if (text[i] == '\n')
                    {
                        current_line_start = i + 1;
                        break;
                    }
                }

                // Current horizontal position
                int current_column = cursor_pos - current_line_start;

                // Is there a previous line?
                if (current_line_start > 0)
                {
                    // The newline belongs to the end of previous line
                    int previous_line_end = current_line_start - 1;

                    // Find beginning of previous line
                    int previous_line_start = 0;

                    for (int i = previous_line_end - 1; i >= 0; i--)
                    {
                        if (text[i] == '\n')
                        {
                            previous_line_start = i + 1;
                            break;
                        }
                    }

                    // Length of previous line
                    int previous_line_length =
                        previous_line_end - previous_line_start;

                    // If previous line is shorter, move to its end
                    if (current_column > previous_line_length)
                    {
                        current_column = previous_line_length;
                    }

                    cursor_pos =
                        previous_line_start + current_column;
                }
            }

            // Move cursor down
            else if (key == XK_Down)
            {
                // Find beginning of current line
                int current_line_start = 0;

                for (int i = cursor_pos - 1; i >= 0; i--)
                {
                    if (text[i] == '\n')
                    {
                        current_line_start = i + 1;
                        break;
                    }
                }

                // Current horizontal position
                int current_column = cursor_pos - current_line_start;

                // Find end of current line
                int current_line_end = length;

                for (int i = cursor_pos; i < length; i++)
                {
                    if (text[i] == '\n')
                    {
                        current_line_end = i;
                        break;
                    }
                }

                // Is there a next line?
                if (current_line_end < length)
                {
                    int next_line_start = current_line_end + 1;

                    // Find end of next line
                    int next_line_end = length;

                    for (int i = next_line_start; i < length; i++)
                    {
                        if (text[i] == '\n')
                        {
                            next_line_end = i;
                            break;
                        }
                    }

                    // Length of next line
                    int next_line_length =
                        next_line_end - next_line_start;

                    // If next line is shorter, move to its end
                    if (current_column > next_line_length)
                    {
                        current_column = next_line_length;
                    }

                    cursor_pos =
                        next_line_start + current_column;
                }
            }

            // Backspace
            else if (key == XK_BackSpace)
            {
                if (cursor_pos > 0)
                {
                    // Move everything after cursor one position left
                    for (int i = cursor_pos - 1; i < length - 1; i++)
                    {
                        text[i] = text[i + 1];
                    }

                    length--;
                    cursor_pos--;

                    text[length] = '\0';
                }
            }

            // Enter
            else if (key == XK_Return || key == XK_KP_Enter)
            {
                if (length < 255)
                {
                    // Move existing text to the right
                    for (int i = length; i > cursor_pos; i--)
                    {
                        text[i] = text[i - 1];
                    }

                    text[cursor_pos] = '\n';

                    length++;
                    cursor_pos++;

                    text[length] = '\0';
                }
            }

            // Normal character
            else if (n > 0 && length < 255)
            {
                // Move existing text to the right
                for (int i = length; i > cursor_pos; i--)
                {
                    text[i] = text[i - 1];
                }

                // Insert character
                text[cursor_pos] = buffer[0];

                length++;
                cursor_pos++;

                text[length] = '\0';
            }

            // Clear everything before redrawing
            XClearWindow(display, window);

            // Draw prompt
            XDrawString(
                display,
                window,
                gc,
                50, 50,
                "Type something:",
                15
            );

            // Draw typed text
            int x = 50;
            int y = 75;
            int start = 0;

            for (int i = 0; i <= length; i++)
            {
                if (text[i] == '\n' || text[i] == '\0')
                {
                    XDrawString(
                        display,
                        window,
                        gc,
                        x,
                        y,
                        text + start,
                        i - start
                    );

                    y += 25;
                    start = i + 1;
                }
            }

            // Find beginning of current line
            int line_start = 0;

            for (int i = cursor_pos - 1; i >= 0; i--)
            {
                if (text[i] == '\n')
                {
                    line_start = i + 1;
                    break;
                }
            }

            // Number of characters before cursor on current line
            int current_line_length = cursor_pos - line_start;

            // Find cursor X position
            int cursor_x = 50 + XTextWidth(
                font,
                text + line_start,
                current_line_length
            );

            // Find cursor Y position
            int cursor_y = 75;

            for (int i = 0; i < cursor_pos; i++)
            {
                if (text[i] == '\n')
                {
                    cursor_y += 25;
                }
            }

            // Draw cursor
            XFillRectangle(
                display,
                window,
                gc,
                cursor_x,
                cursor_y - 18,
                2,
                20
            );

            // Make drawing appear immediately
            XFlush(display);
        }
    }

    // Clean up
    XFreeFont(display, font);
    XFreeGC(display, gc);
    XDestroyWindow(display, window);
    XCloseDisplay(display);

    return 0;
}