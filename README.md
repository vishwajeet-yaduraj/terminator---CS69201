# Terminator: A Custom Terminal

Terminator is a C terminal emulator for Linux. It uses X11 to display a window with tabs and runs shell commands from those tabs.

## Requirements

- Linux or WSL with a working X server
- GCC and Make
- X11 development files (`libx11-dev` on Debian or Ubuntu)
- POSIX threads

Install the dependencies on Debian or Ubuntu:

```bash
sudo apt update
sudo apt install build-essential make libx11-dev
```

## Build

From the project directory, run:

```bash
make
```

This builds the `terminator` executable from `terminator.c`.

To remove the executable:

```bash
make clean
```

## Run

Start in the default thread mode:

```bash
./terminator
```

Start in process mode:

```bash
./terminator useProcess=True
```

A working X11 display is required. In WSL, make sure your X server is running and `DISPLAY` is configured.

## Features

- X11 window with tabs, command input, output, and scrolling
- Per-tab working directories
- Built-in and external commands
- Quoting, variable and tilde expansion, and command substitution
- Pipelines and input/output redirection
- Background jobs and job-control commands
- `multiWatch`
- Basic shell scripts and conditional statements
- Shared command history, history search, and filename completion
- Configurable editing keys and X11 selection copy/paste
- Thread mode and process mode
- Wrapped long input and output

## Design

See [DESIGN.md](DESIGN.md) for the GUI event loop, execution modes, synchronization, process management, and implementation decisions.

## Testing

See [TESTING.md](TESTING.md) for the manual test checklist for Tasks 1–11 and additional edge cases.

## Limitations

Terminator implements the shell features required for this project; it is not a complete Bash replacement. It has fixed limits on tabs, input length, command arguments, and displayed filename-completion candidates. Scripts should use the syntax supported by the project.
