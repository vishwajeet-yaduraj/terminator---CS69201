# Manual Test Checklist

Run the checks in both modes where noted:

- Thread mode: `./terminator`
- Process mode: `./terminator useProcess=True`

Mark a check only after you have run it.

## Task 1 — X11 GUI and tabs

- [ ] Run `echo task1-check`; confirm output appears in the Terminator window.
- [ ] Run `seq 1 80`; confirm output is scrollable.
- [ ] Run `sleep 8`, open another tab with Ctrl+T, and run `pwd` there.
- [ ] Switch back and confirm the first tab remains usable.

## Task 2 — Built-in and external commands

- [ ] Run `pwd`, `cd /tmp`, `pwd`, `cd -`, and `pwd`.
- [ ] Run `date` and `echo still-working`.
- [ ] Run a nonexistent command; confirm an error appears and the shell remains usable.

## Task 3 — Quoting and command substitution

- [ ] Enter `echo "hello`, press Enter, then enter `world"`; confirm the continuation prompt and two-line output.
- [ ] Compare `echo 'literal: $HOME' "expanded: $HOME"`.
- [ ] Run `echo "base: $(basename $(pwd))"`.
- [ ] Test a backtick substitution.

## Task 4 — Redirection

- [ ] Test `<`, `>`, `>>`, and `2>` using temporary files.
- [ ] Test `> output.txt 2>&1`.
- [ ] Try a missing input file and malformed redirection; confirm errors do not break the shell.

## Task 5 — Pipelines

- [ ] Run `printf 'pear\napple\n' | sort`.
- [ ] Try a three-stage pipeline and a pipeline with redirection.
- [ ] Run `yes | head -3`; confirm it finishes.
- [ ] Try malformed syntax such as `echo x | | cat`.

## Task 6 — multiWatch

- [ ] Run `multiWatch ["date", "pwd"]`; confirm labeled output repeats.
- [ ] Press Ctrl+C; confirm the prompt returns and the tab remains usable.

## Task 7 — Editing keys and key settings

- [ ] Try line movement, Home/End, history arrows, Ctrl+U, Ctrl+K, Ctrl+W, and Ctrl+L.
- [ ] Try Ctrl+Shift+C and Ctrl+Shift+V.
- [ ] Change a supported binding in `~/.terminatorrc`, restart, and check that it persists.

## Task 8 — Jobs and signals

- [ ] Run `sleep 30`, press Ctrl+Z, then run `jobs`.
- [ ] Resume it with `bg %1`, then bring it back with `fg %1`.
- [ ] Press Ctrl+C and confirm the prompt returns.

## Task 9 — History search and persistence

- [ ] Search for an exact recent command and a partial command.
- [ ] Try a query with no match.
- [ ] Restart Terminator and check that history remains available.

## Task 10 — Filename completion

- [ ] Try completing a unique filename prefix and a prefix with multiple matches.
- [ ] Try completion in a path containing `/`.
- [ ] Try completing in the middle of a command line and confirm text after the cursor remains.

## Task 11 — Scripts

- [ ] Run a script with `bash script.sh` and with `source script.sh`.
- [ ] Check comments, arguments, variable expansion, command substitution, and a supported conditional.
- [ ] Try a script with a missing `fi`; confirm it reports an error.

## Additional edge cases

- [ ] Resize the window during long output; check wrapping and scrolling.
- [ ] Test an empty quoted argument and paths containing spaces.
- [ ] Interrupt a long pipeline; check that its child commands stop.
- [ ] Close a tab while a command runs; confirm other tabs still work.
- [ ] Repeat redirection and job checks in both modes.

This file is a test plan. Mark checks only after you have run them.
