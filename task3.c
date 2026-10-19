#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

#include <errno.h>
#include <fcntl.h>
#include <ctype.h>
#include <poll.h>
#include <semaphore.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define MAX_TABS 8
#define INPUT_CAPACITY 4096
#define TAB_BAR_Y 7
#define TAB_BAR_HEIGHT 28
#define TAB_BAR_LEFT 10
#define TAB_BAR_TOP 5
#define TERMINAL_TOP 58
#define LINE_HEIGHT 22
#define TAB_WIDTH_MAX 160
#define TAB_WIDTH_MIN 28
#define PLUS_WIDTH 28

#define SHELL_HISTORY_LIMIT 10000
#define SHELL_JOB_LIMIT 64

typedef struct
{
    pid_t pid;
    char command[256];
    int active;
} ShellJob;

typedef struct
{
    sem_t lock;
    size_t count;
    char entries[SHELL_HISTORY_LIMIT][INPUT_CAPACITY];
} SharedCommandHistory;

static SharedCommandHistory *shared_command_history;
static ShellJob shell_jobs[SHELL_JOB_LIMIT];
static int shell_last_status;
static int shell_should_exit;

static void shell_add_history(const char *line)
{
    if (line == NULL || line[0] == '\0') return;
    if (shared_command_history == NULL) return;
    while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
    if (shared_command_history->count == SHELL_HISTORY_LIMIT)
    {
        memmove(shared_command_history->entries,
                shared_command_history->entries + 1,
                (SHELL_HISTORY_LIMIT - 1) * INPUT_CAPACITY);
        shared_command_history->count--;
    }
    snprintf(shared_command_history->entries[shared_command_history->count],
             INPUT_CAPACITY, "%s", line);
    shared_command_history->count++;
    (void)sem_post(&shared_command_history->lock);
}

/* A small Task 2 tokenizer. Full multiline Bash quoting is added in Task 3. */
static int shell_tokenize(const char *line, char **argv, int capacity)
{
    int argc = 0;
    const char *p = line;
    while (*p != '\0')
    {
        while (isspace((unsigned char)*p)) p++;
        if (*p == '\0') break;
        if (argc >= capacity - 1) break;
        char token[INPUT_CAPACITY];
        size_t n = 0;
        char quote = 0;
        while (*p != '\0' && (quote != 0 || !isspace((unsigned char)*p)))
        {
            if (quote == 0 && (*p == '\'' || *p == '"'))
            {
                quote = *p++;
                continue;
            }
            if (quote != 0 && *p == quote)
            {
                quote = 0;
                p++;
                continue;
            }
            if (*p == '\\' && p[1] == '\n' && quote != '\'') { p += 2; continue; }
            if (*p == '\\' && p[1] != '\0' && quote != '\'') p++;
            if (n + 1 < sizeof(token)) token[n++] = *p;
            p++;
        }
        token[n] = '\0';
        argv[argc] = strdup(token);
        if (argv[argc] == NULL) break;
        argc++;
    }
    argv[argc] = NULL;
    return argc;
}

static void shell_free_argv(char **argv, int argc)
{
    for (int i = 0; i < argc; i++) free(argv[i]);
}

static void shell_reap_jobs(void)
{
    for (int i = 0; i < SHELL_JOB_LIMIT; i++)
    {
        if (!shell_jobs[i].active) continue;
        int status;
        pid_t result = waitpid(shell_jobs[i].pid, &status, WNOHANG);
        if (result == shell_jobs[i].pid)
        {
            dprintf(STDOUT_FILENO, "[%d] Done %s\n", i + 1, shell_jobs[i].command);
            shell_jobs[i].active = 0;
        }
    }
}

static int shell_run_line(const char *line, int record_history, int depth);

static int command_is_incomplete(const char *s)
{
    int single = 0, dbl = 0, backtick = 0, substitutions = 0;
    for (size_t i = 0; s[i] != '\0'; i++)
    {
        char c = s[i];
        if (c == '\\' && !single)
        {
            if (s[i + 1] == '\0') return 1;
            if (s[i + 1] == '\n') { i++; continue; }
            i++;
            continue;
        }
        if (single)
        {
            if (c == '\'') single = 0;
            continue;
        }
        if (c == '`' && !single) { backtick = !backtick; continue; }
        if (!dbl && !backtick && c == '\'') { single = 1; continue; }
        if (!single && !backtick && c == '"') { dbl = !dbl; continue; }
        if (c == '$' && s[i + 1] == '(' && !single)
        {
            substitutions++;
            i++;
            continue;
        }
        if (substitutions > 0)
        {
            if (c == '(') substitutions++;
            else if (c == ')') substitutions--;
        }
    }
    return single || dbl || backtick || substitutions > 0;
}

static int append_text(char **out, size_t *length, size_t *capacity,
                       const char *value, size_t count)
{
    if (count > SIZE_MAX - *length - 1) return 0;
    size_t need = *length + count + 1;
    if (need > *capacity)
    {
        size_t cap = *capacity ? *capacity : 128;
        while (cap < need)
        {
            if (cap > SIZE_MAX / 2) { cap = need; break; }
            cap *= 2;
        }
        char *next = realloc(*out, cap);
        if (next == NULL) return 0;
        *out = next; *capacity = cap;
    }
    memcpy(*out + *length, value, count);
    *length += count;
    (*out)[*length] = '\0';
    return 1;
}

static char *capture_substitution(const char *command, int depth)
{
    int pipe_fd[2];
    if (pipe(pipe_fd) == -1) return strdup("");
    pid_t child = fork();
    if (child == -1)
    {
        close(pipe_fd[0]); close(pipe_fd[1]);
        return strdup("");
    }
    if (child == 0)
    {
        close(pipe_fd[0]);
        if (dup2(pipe_fd[1], STDOUT_FILENO) == -1) _exit(126);
        close(pipe_fd[1]);
        int status = shell_run_line(command, 0, depth + 1);
        _exit(status & 255);
    }
    close(pipe_fd[1]);
    char *result = NULL; size_t used = 0, capacity = 0;
    char chunk[1024];
    for (;;)
    {
        ssize_t n = read(pipe_fd[0], chunk, sizeof(chunk));
        if (n > 0)
        {
            if (!append_text(&result, &used, &capacity, chunk, (size_t)n)) break;
        }
        else if (n == 0) break;
        else if (errno != EINTR) break;
    }
    close(pipe_fd[0]);
    while (used > 0 && result[used - 1] == '\n') result[--used] = '\0';
    int status;
    while (waitpid(child, &status, 0) < 0 && errno == EINTR) {}
    if (result == NULL) result = strdup("");
    return result;
}

static char *expand_shell_text(const char *line, int depth)
{
    if (depth > 16) return strdup(line);
    char *out = NULL; size_t used = 0, capacity = 0;
    int single = 0, dbl = 0;
    for (size_t i = 0; line[i] != '\0'; )
    {
        char c = line[i];
        if (c == '\\' && !single && line[i + 1] != '\0')
        {
            if (!append_text(&out, &used, &capacity, line + i, 2)) goto fail;
            i += 2; continue;
        }
        if (c == '\'' && !dbl) single = !single;
        else if (c == '"' && !single) dbl = !dbl;
        if (!single && c == '$' && line[i + 1] == '(')
        {
            size_t start = i + 2, j = start; int nesting = 1;
            int in_single = 0, in_double = 0;
            for (; line[j] != '\0'; j++)
            {
                if (line[j] == '\\' && line[j + 1] != '\0') { j++; continue; }
                if (line[j] == '\'' && !in_double) in_single = !in_single;
                else if (line[j] == '"' && !in_single) in_double = !in_double;
                else if (!in_single && line[j] == '(') nesting++;
                else if (!in_single && line[j] == ')' && --nesting == 0) break;
            }
            if (line[j] == ')')
            {
                char *subcommand = strndup(line + start, j - start);
                char *value = capture_substitution(subcommand ? subcommand : "", depth);
                free(subcommand);
                if (value != NULL)
                {
                    if (dbl)
                    {
                        for (size_t k = 0; value[k] != '\0'; k++)
                        {
                            if ((value[k] == '"' || value[k] == '\\') &&
                                !append_text(&out, &used, &capacity, "\\", 1)) { free(value); goto fail; }
                            if (!append_text(&out, &used, &capacity, value + k, 1)) { free(value); goto fail; }
                        }
                    }
                    else if (!append_text(&out, &used, &capacity, value, strlen(value))) { free(value); goto fail; }
                    free(value);
                }
                i = j + 1; continue;
            }
        }
        if (!single && c == '`')
        {
            size_t j = i + 1;
            int nested_backtick = 0;
            while (line[j] != '\0')
            {
                if (line[j] == '\\' && line[j + 1] == '`')
                {
                    nested_backtick = !nested_backtick;
                    j += 2;
                    continue;
                }
                if (line[j] == '`' && !nested_backtick) break;
                j++;
            }
            if (line[j] == '`')
            {
                char *subcommand = NULL; size_t sub_length = 0, sub_capacity = 0;
                for (size_t k = i + 1; k < j; k++)
                {
                    if (line[k] == '\\' && line[k + 1] == '`') k++;
                    if (!append_text(&subcommand, &sub_length, &sub_capacity, line + k, 1))
                    { free(subcommand); subcommand = NULL; break; }
                }
                char *value = capture_substitution(subcommand ? subcommand : "", depth);
                free(subcommand);
                if (value != NULL)
                {
                    for (size_t k = 0; value[k] != '\0'; k++)
                    {
                        if (dbl && (value[k] == '"' || value[k] == '\\') &&
                            !append_text(&out, &used, &capacity, "\\", 1)) { free(value); goto fail; }
                        if (!append_text(&out, &used, &capacity, value + k, 1)) { free(value); goto fail; }
                    }
                    free(value);
                }
                i = j + 1; continue;
            }
        }
        if (!single && c == '$' && (isalpha((unsigned char)line[i + 1]) || line[i + 1] == '_' || line[i + 1] == '?'))
        {
            size_t j = i + 1; char name[256]; size_t n = 0;
            if (line[j] == '?') { name[n++] = line[j++]; }
            else while ((isalnum((unsigned char)line[j]) || line[j] == '_') && n + 1 < sizeof(name)) name[n++] = line[j++];
            name[n] = '\0';
            char status_text[32];
            const char *value;
            if (strcmp(name, "?") == 0) { snprintf(status_text, sizeof(status_text), "%d", shell_last_status); value = status_text; }
            else { value = getenv(name); if (value == NULL) value = ""; }
            if (dbl)
            {
                for (size_t k = 0; value[k] != '\0'; k++)
                {
                    if ((value[k] == '"' || value[k] == '\\') && !append_text(&out, &used, &capacity, "\\", 1)) goto fail;
                    if (!append_text(&out, &used, &capacity, value + k, 1)) goto fail;
                }
            }
            else if (!append_text(&out, &used, &capacity, value, strlen(value))) goto fail;
            i = j; continue;
        }
        if (!append_text(&out, &used, &capacity, line + i, 1)) goto fail;
        i++;
    }
    if (out == NULL) out = strdup("");
    return out;
fail:
    free(out); return strdup("");
}

static int shell_run_external(char **argv, int argc, const char *line, int background)
{
    if (argc == 0) return 0;
    pid_t pid = fork();
    if (pid < 0)
    {
        perror("fork");
        return 1;
    }
    if (pid == 0)
    {
        execvp(argv[0], argv);
        dprintf(STDERR_FILENO, "terminator: %s: command not found\n", argv[0]);
        _exit(errno == ENOENT ? 127 : 126);
    }
    if (background)
    {
        for (int i = 0; i < SHELL_JOB_LIMIT; i++)
        {
            if (!shell_jobs[i].active)
            {
                shell_jobs[i].pid = pid;
                shell_jobs[i].active = 1;
                snprintf(shell_jobs[i].command, sizeof(shell_jobs[i].command), "%s", line);
                dprintf(STDOUT_FILENO, "[%d] %ld\n", i + 1, (long)pid);
                return 0;
            }
        }
        dprintf(STDOUT_FILENO, "terminator: job table is full\n");
        (void)waitpid(pid, NULL, 0);
        return 1;
    }
    int status = 0;
    while (waitpid(pid, &status, 0) < 0)
    {
        if (errno == EINTR) continue;
        perror("waitpid");
        return 1;
    }
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    if (WIFSIGNALED(status)) return 128 + WTERMSIG(status);
    return 1;
}

/* Pipeline execution is included here because Task 3's substitution examples
   use pipelines inside $(...). The general pipeline task will extend this. */
static int shell_run_pipeline_line(const char *line, int *handled)
{
    *handled = 0;
    char *parts[32]; int count = 1;
    size_t length = strlen(line), start = 0;
    int single = 0, dbl = 0;
    for (size_t i = 0; i < length; i++)
    {
        char c = line[i];
        if (c == '\\' && !single && i + 1 < length) { i++; continue; }
        if (c == '\'' && !dbl) single = !single;
        else if (c == '"' && !single) dbl = !dbl;
        else if (c == '|' && !single && !dbl)
        {
            if (count >= 32) return 2;
            size_t end = i;
            while (start < end && isspace((unsigned char)line[start])) start++;
            while (end > start && isspace((unsigned char)line[end - 1])) end--;
            parts[count - 1] = strndup(line + start, end - start);
            if (parts[count - 1] == NULL) return 1;
            count++; start = i + 1;
        }
    }
    if (count == 1) return 0;
    *handled = 1;
    size_t end = length;
    while (start < end && isspace((unsigned char)line[start])) start++;
    while (end > start && isspace((unsigned char)line[end - 1])) end--;
    parts[count - 1] = strndup(line + start, end - start);
    if (parts[count - 1] == NULL) return 1;
    int pipes[31][2]; pid_t pids[32]; int made = 0, launched = 0, result = 0;
    for (int i = 0; i < count - 1; i++)
    {
        if (pipe(pipes[i]) == -1) { perror("pipe"); result = 1; goto done; }
        made++;
    }
    for (int i = 0; i < count; i++)
    {
        pid_t child = fork();
        if (child == -1) { perror("fork"); result = 1; break; }
        if (child == 0)
        {
            if (i > 0) (void)dup2(pipes[i - 1][0], STDIN_FILENO);
            if (i < count - 1) (void)dup2(pipes[i][1], STDOUT_FILENO);
            for (int k = 0; k < made; k++) { close(pipes[k][0]); close(pipes[k][1]); }
            char *argv[64]; int argc = shell_tokenize(parts[i], argv, 64);
            if (argc == 0) _exit(0);
            execvp(argv[0], argv);
            dprintf(2, "terminator: %s: command not found\n", argv[0]);
            _exit(127);
        }
        pids[launched++] = child;
    }
    for (int i = 0; i < made; i++) { close(pipes[i][0]); close(pipes[i][1]); }
    for (int i = 0; i < launched; i++)
    {
        int status = 0;
        while (waitpid(pids[i], &status, 0) < 0 && errno == EINTR) {}
        if (i == launched - 1 && WIFEXITED(status)) result = WEXITSTATUS(status);
    }
done:
    for (int i = 0; i < count; i++) free(parts[i]);
    return result;
}

/* Task 2 baseline: run the listed commands concurrently once. Task 6 adds
   periodic reruns and event-loop Ctrl+C cancellation. */
static int shell_multiwatch(const char *line)
{
    const char *p = strchr(line, '[');
    if (p == NULL) { dprintf(1, "usage: multiWatch [\"cmd1\", \"cmd2\"]\n"); return 2; }
    p++;
    pid_t pids[32];
    int count = 0;
    while (*p != '\0' && *p != ']' && count < 32)
    {
        while (*p == ' ' || *p == ',' || *p == '\t') p++;
        if (*p == '\0' || *p == ']') break;
        char quote = (*p == '\'' || *p == '"') ? *p++ : 0;
        char cmd[INPUT_CAPACITY]; size_t n = 0;
        while (*p != '\0' && (quote ? *p != quote : *p != ',' && *p != ']'))
        {
            if (n + 1 < sizeof(cmd)) cmd[n++] = *p;
            p++;
        }
        if (quote && *p == quote) p++;
        cmd[n] = '\0';
        char *argv[64]; int argc = shell_tokenize(cmd, argv, 64);
        if (argc == 0) { shell_free_argv(argv, argc); continue; }
        pid_t child = fork();
        if (child == 0)
        {
            execvp(argv[0], argv);
            dprintf(2, "terminator: %s: command not found\n", argv[0]);
            _exit(127);
        }
        if (child > 0) pids[count++] = child;
        else perror("fork");
        shell_free_argv(argv, argc);
    }
    int result = 0;
    for (int i = 0; i < count; i++)
    {
        int status = 0;
        while (waitpid(pids[i], &status, 0) < 0 && errno == EINTR) {}
        if (WIFEXITED(status) && WEXITSTATUS(status) != 0) result = WEXITSTATUS(status);
    }
    return result;
}

static int shell_run_line(const char *line, int record_history, int depth)
{
    if (depth > 8) { dprintf(2, "terminator: source nesting limit reached\n"); return 1; }
    if (record_history) shell_add_history(line);
    char *expanded = expand_shell_text(line, depth);
    int pipeline_handled = 0;
    int pipeline_status = shell_run_pipeline_line(expanded, &pipeline_handled);
    if (pipeline_handled)
    {
        shell_last_status = pipeline_status;
        free(expanded);
        return pipeline_status;
    }
    char *argv[64];
    int argc = shell_tokenize(expanded, argv, 64);
    if (argc == 0) { shell_free_argv(argv, argc); free(expanded); return 0; }
    int background = strcmp(argv[argc - 1], "&") == 0;
    if (background) { free(argv[--argc]); argv[argc] = NULL; }
    int status = 0;
    if (strcmp(argv[0], "cd") == 0)
    {
        const char *dest = argc > 1 ? argv[1] : getenv("HOME");
        if (dest == NULL || chdir(dest) != 0) { perror("cd"); status = 1; }
    }
    else if (strcmp(argv[0], "exit") == 0)
    {
        shell_should_exit = 1;
        if (argc > 1) shell_last_status = atoi(argv[1]);
    }
    else if (strcmp(argv[0], "history") == 0)
    {
        if (shared_command_history != NULL)
        {
            while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
            size_t first = shared_command_history->count > 1000 ? shared_command_history->count - 1000 : 0;
            for (size_t i = first; i < shared_command_history->count; i++)
                dprintf(1, "%zu  %s\n", i + 1, shared_command_history->entries[i]);
            (void)sem_post(&shared_command_history->lock);
        }
    }
    else if (strcmp(argv[0], "jobs") == 0)
    {
        shell_reap_jobs();
        for (int i = 0; i < SHELL_JOB_LIMIT; i++)
            if (shell_jobs[i].active)
                dprintf(1, "[%d] Running %s\n", i + 1, shell_jobs[i].command);
    }
    else if (strcmp(argv[0], "fg") == 0 || strcmp(argv[0], "bg") == 0)
    {
        int job = argc > 1 ? atoi(argv[1][0] == '%' ? argv[1] + 1 : argv[1]) : 1;
        if (job < 1 || job > SHELL_JOB_LIMIT || !shell_jobs[job - 1].active)
        { dprintf(2, "terminator: no such job\n"); status = 1; }
        else if (strcmp(argv[0], "bg") == 0)
        {
            (void)kill(shell_jobs[job - 1].pid, SIGCONT);
            dprintf(1, "[%d]+ %s &\n", job, shell_jobs[job - 1].command);
        }
        else
        {
            int child_status = 0;
            while (waitpid(shell_jobs[job - 1].pid, &child_status, 0) < 0 && errno == EINTR) {}
            shell_jobs[job - 1].active = 0;
            if (WIFEXITED(child_status)) status = WEXITSTATUS(child_status);
        }
    }
    else if (strcmp(argv[0], "source") == 0)
    {
        if (argc < 2) { dprintf(2, "usage: source file\n"); status = 2; }
        else
        {
            FILE *script = fopen(argv[1], "r");
            if (script == NULL) { perror("source"); status = 1; }
            else
            {
                char *script_line = NULL; size_t cap = 0; ssize_t len;
                while (!shell_should_exit && (len = getline(&script_line, &cap, script)) >= 0)
                {
                    while (len > 0 && (script_line[len - 1] == '\n' || script_line[len - 1] == '\r')) script_line[--len] = '\0';
                    if (script_line[0] == '#' || script_line[0] == '\0') continue;
                    status = shell_run_line(script_line, 1, depth + 1);
                }
                free(script_line); fclose(script);
            }
        }
    }
    else if (strcmp(argv[0], "multiWatch") == 0)
    {
        status = shell_multiwatch(expanded);
    }
    else
    {
        /* $? is substituted as a simple standalone argument in this version. */
        char status_text[24]; snprintf(status_text, sizeof(status_text), "%d", shell_last_status);
        for (int i = 0; i < argc; i++)
            if (strcmp(argv[i], "$?") == 0) { free(argv[i]); argv[i] = strdup(status_text); }
        status = shell_run_external(argv, argc, line, background);
    }
    shell_last_status = status;
    shell_free_argv(argv, argc);
    free(expanded);
    return status;
}

static void shell_worker(void)
{
    char *command = NULL, *marker = NULL;
    size_t command_capacity = 0, marker_capacity = 0;
    while (!shell_should_exit)
    {
        ssize_t command_length = getline(&command, &command_capacity, stdin);
        if (command_length < 0) break;
        ssize_t marker_length = getline(&marker, &marker_capacity, stdin);
        if (marker_length < 0) break;
        while (command_length > 0 && (command[command_length - 1] == '\n' || command[command_length - 1] == '\r')) command[--command_length] = '\0';
        while (marker_length > 0 && (marker[marker_length - 1] == '\n' || marker[marker_length - 1] == '\r')) marker[--marker_length] = '\0';
        for (ssize_t i = 0; i < command_length; i++)
            if (command[i] == '\x1e') command[i] = '\n';
        (void)shell_run_line(command, 1, 0);
        dprintf(STDOUT_FILENO, "%s", marker);
    }
    free(command); free(marker);
    _exit(shell_last_status);
}

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

static int append_input_with_prompts(TextBuffer *buffer, const char *input, size_t length)
{
    const char *prompt = "user@terminator> ";
    size_t start = 0;
    int continuation = 0;
    for (size_t i = 0; i <= length; i++)
    {
        if (i == length || input[i] == '\n')
        {
            const char *prefix = continuation ? "> " : prompt;
            if (!text_buffer_append(buffer, prefix) ||
                !text_buffer_append_n(buffer, input + start, i - start) ||
                !text_buffer_append_n(buffer, "\n", 1)) return 0;
            start = i + 1;
            continuation = 1;
        }
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

        /* The GUI remains the only X11 client. Close every inherited fd
           except the worker's command/output streams before entering it. */
        long max_fd = sysconf(_SC_OPEN_MAX);
        if (max_fd < 0 || max_fd > 65536) max_fd = 65536;
        for (int fd = 3; fd < max_fd; fd++) (void)close(fd);
        shell_worker();
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
    char encoded_command[INPUT_CAPACITY];
    (void)snprintf(encoded_command, sizeof(encoded_command), "%s", command);
    for (size_t i = 0; encoded_command[i] != '\0'; i++)
        if (encoded_command[i] == '\n') encoded_command[i] = '\x1e';
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
        "%s\n%s\n",
        encoded_command,
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
    size_t input_lines = 1;
    for (size_t i = 0; i < tab->input_length; i++)
        if (tab->input[i] == '\n') input_lines++;
    size_t total_rows = history_lines + input_lines;
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

    // Draw the prompt and any continuation lines currently visible.
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
            size_t input_start = 0;
            size_t input_row = 0;
            for (size_t i = 0; i <= tab->input_length; i++)
            {
                if (i == tab->input_length || tab->input[i] == '\n')
                {
                    const char *prefix = input_row == 0 ? prompt : "> ";
                    int prefix_width = XTextWidth(font, prefix, (int)strlen(prefix));
                    XDrawString(display, window, gc, x, y, prefix, (int)strlen(prefix));
                    if (i > input_start)
                    {
                        XDrawString(display, window, gc, x + prefix_width, y,
                                    tab->input + input_start, (int)(i - input_start));
                    }
                    y += LINE_HEIGHT;
                    input_row++;
                    input_start = i + 1;
                }
            }
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

    shared_command_history = mmap(NULL, sizeof(*shared_command_history),
                                  PROT_READ | PROT_WRITE,
                                  MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shared_command_history == MAP_FAILED)
    {
        perror("mmap shared history");
        XCloseDisplay(display);
        return 1;
    }
    memset(shared_command_history, 0, sizeof(*shared_command_history));
    if (sem_init(&shared_command_history->lock, 1, 1) == -1)
    {
        perror("sem_init shared history");
        munmap(shared_command_history, sizeof(*shared_command_history));
        XCloseDisplay(display);
        return 1;
    }

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
    XStoreName(display, window, "Terminator - Task 3");

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
                    if (command_is_incomplete(tab->input))
                    {
                        if (tab->input_length < sizeof(tab->input) - 1)
                        {
                            tab->input[tab->input_length++] = '\n';
                            tab->input[tab->input_length] = '\0';
                        }
                        changed = 1;
                    }
                    else
                    {
                        if (append_input_with_prompts(&tab->history, tab->input, tab->input_length))
                        {
                            if (tab->input_length > 0 &&
                                !shell_submit_command(&tab->shell, tab->input))
                            {
                                (void)text_buffer_append(&tab->history,
                                    "[Terminator: could not submit command]\n");
                            }
                            tab->input_length = 0;
                            tab->input[0] = '\0';
                            tab->scroll_offset = 0;
                            changed = 1;
                        }
                        else
                        {
                            (void)text_buffer_append(&tab->history,
                                "[Terminator: could not store command]\n");
                            tab->scroll_offset = 0;
                            changed = 1;
                        }
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
    (void)sem_destroy(&shared_command_history->lock);
    (void)munmap(shared_command_history, sizeof(*shared_command_history));
    return 0;
}
