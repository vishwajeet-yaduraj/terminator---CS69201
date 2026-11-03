# Terminator Design Document

## X11 GUI and event loop

The main thread owns the X11 display and window. It handles keyboard and mouse events, updates the selected tab, checks shell input/output, and redraws the window. Shell workers do not call Xlib.

Each tab stores its input line, cursor position, displayed text, scroll position, working directory, and shell communication state. The GUI redraws each tab from its stored text, wrapping long lines to the window width. A command can continue running in one tab while another tab is selected.

## Thread mode and process mode

Thread mode is the default. The GUI and tab shell workers run in one process. Each tab tracks its own working directory so a `cd` in one tab does not change another tab's directory.

Process mode is started with:

    ./terminator useProcess=True

The GUI stays in the parent process. Each tab's shell worker runs in a child process, and pipes carry data between the GUI and that worker.

Command history is shared between tabs. It is stored in shared memory and protected by a process-shared semaphore so concurrent tabs do not update it at the same time.

## Process and job management

Built-in commands run in the shell worker. External commands run in child processes created with `fork` and started with `execvp`. The shell waits for foreground commands and tracks background jobs for `jobs`, `fg`, and `bg`.

Pipelines connect command processes with pipes. Unused pipe ends are closed after setup so commands can receive end-of-file and pipelines can finish. The pipeline status comes from its last command.

## IPC, pipes, and redirection

Pipes connect the GUI to each shell worker and connect stages in a pipeline. `dup2` connects a command's standard input and output to the appropriate pipe or redirected file.

The shell supports input redirection, output redirection, append redirection, and standard-error redirection. Redirection file descriptors are restored after a command so later commands continue using the tab's normal input and output.

## History and filename completion

Command history is kept in a bounded shared-memory list and persisted to a history file. A semaphore protects shared history operations. History search returns exact or partial matches.

Filename completion reads entries from the active tab's current directory, filters them by the typed prefix, and inserts a unique match or the common prefix. The input buffer keeps text after the cursor when completion replaces a word.

## Signals and key settings

Ctrl+C and Ctrl+Z are sent to the active tab's foreground command or process group. The shell handles interrupted or stopped jobs and returns the tab to a usable prompt.

Editing key defaults and user key settings are loaded from `~/.terminatorrc`. X11 selections are used for copy and paste.

## Other design decisions and limitations

The implementation supports the assignment's required shell features, including quoting, variable expansion, command substitution, scripts, and `multiWatch`. It is not a full Bash implementation.

The program uses fixed limits for tabs, command input, command arguments, and completion candidates. Scripts should use the shell syntax supported by the project.
