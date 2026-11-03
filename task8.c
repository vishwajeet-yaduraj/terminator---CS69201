#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

#include <errno.h>
#include <fcntl.h>
#include <ctype.h>
#include <glob.h>
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
    int stopped;
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
static volatile sig_atomic_t shell_interrupted;
static volatile sig_atomic_t shell_foreground_pgid;
static char selection_clipboard[INPUT_CAPACITY];
static size_t selection_clipboard_length;
static size_t pending_paste_tab = SIZE_MAX;

static void shell_sigint_handler(int signal_number)
{
    (void)signal_number;
    shell_interrupted = 1;
    if (shell_foreground_pgid > 0)
        (void)kill(-(pid_t)shell_foreground_pgid, SIGINT);
}

static void shell_sigtstp_handler(int signal_number)
{
    (void)signal_number;
    if (shell_foreground_pgid > 0)
        (void)kill(-(pid_t)shell_foreground_pgid, SIGTSTP);
}

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
        int was_quoted = 0;
        while (*p != '\0' && (quote != 0 || !isspace((unsigned char)*p)))
        {
            if (quote == 0 && (*p == '\'' || *p == '"'))
            {
                was_quoted = 1;
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
            if (*p == '\\' && p[1] != '\0' && quote != '\'') { was_quoted = 1; p++; }
            if (n + 1 < sizeof(token)) token[n++] = *p;
            p++;
        }
        token[n] = '\0';
        if (!was_quoted && strpbrk(token, "*?[" ) != NULL)
        {
            glob_t matches;
            memset(&matches, 0, sizeof(matches));
            if (glob(token, 0, NULL, &matches) == 0 && matches.gl_pathc > 0)
            {
                for (size_t i = 0; i < matches.gl_pathc && argc < capacity - 1; i++)
                {
                    argv[argc] = strdup(matches.gl_pathv[i]);
                    if (argv[argc] == NULL) break;
                    argc++;
                }
                globfree(&matches);
                continue;
            }
            globfree(&matches);
        }
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

static int shell_extract_redirections(char **argv, int *argc,
                                      char **input_path, char **output_path)
{
    int kept = 0;
    *input_path = NULL;
    *output_path = NULL;
    for (int i = 0; i < *argc; i++)
    {
        if (strcmp(argv[i], "<") == 0 || strcmp(argv[i], ">") == 0)
        {
            int is_input = strcmp(argv[i], "<") == 0;
            if (i + 1 >= *argc)
            {
                dprintf(STDERR_FILENO, "terminator: missing file after %s\n", argv[i]);
                return 0;
            }
            char **slot = is_input ? input_path : output_path;
            free(*slot);
            char *operator_token = argv[i];
            char *target_token = argv[i + 1];
            *slot = strdup(target_token);
            free(operator_token);
            free(target_token);
            argv[i] = NULL;
            argv[i + 1] = NULL;
            i++;
            if (*slot == NULL) return 0;
        }
        else
        {
            argv[kept++] = argv[i];
        }
    }
    *argc = kept;
    argv[kept] = NULL;
    return 1;
}

static int shell_apply_redirections(const char *input_path, const char *output_path,
                                    int *saved_stdin, int *saved_stdout)
{
    *saved_stdin = -1;
    *saved_stdout = -1;
    if (input_path != NULL)
    {
        int fd = open(input_path, O_RDONLY);
        if (fd == -1) { perror(input_path); return 0; }
        *saved_stdin = dup(STDIN_FILENO);
        if (*saved_stdin == -1 || dup2(fd, STDIN_FILENO) == -1)
        {
            perror("dup2 input"); close(fd); return 0;
        }
        close(fd);
    }
    if (output_path != NULL)
    {
        int fd = open(output_path, O_WRONLY | O_CREAT | O_TRUNC, 0666);
        if (fd == -1) { perror(output_path); return 0; }
        *saved_stdout = dup(STDOUT_FILENO);
        if (*saved_stdout == -1 || dup2(fd, STDOUT_FILENO) == -1)
        {
            perror("dup2 output"); close(fd); return 0;
        }
        close(fd);
    }
    return 1;
}

static void shell_restore_redirections(int saved_stdin, int saved_stdout)
{
    if (saved_stdin >= 0) { (void)dup2(saved_stdin, STDIN_FILENO); close(saved_stdin); }
    if (saved_stdout >= 0) { (void)dup2(saved_stdout, STDOUT_FILENO); close(saved_stdout); }
}

static int shell_register_job(pid_t pid, const char *command, int stopped)
{
    for (int i = 0; i < SHELL_JOB_LIMIT; i++)
    {
        if (!shell_jobs[i].active)
        {
            shell_jobs[i].pid = pid;
            shell_jobs[i].active = 1;
            shell_jobs[i].stopped = stopped;
            snprintf(shell_jobs[i].command, sizeof(shell_jobs[i].command), "%s", command);
            return i;
        }
    }
    return -1;
}

static void shell_reap_jobs(void)
{
    for (int i = 0; i < SHELL_JOB_LIMIT; i++)
    {
        if (!shell_jobs[i].active) continue;
        int status;
        pid_t result = waitpid(shell_jobs[i].pid, &status, WNOHANG | WUNTRACED | WCONTINUED);
        if (result == shell_jobs[i].pid)
        {
            if (WIFSTOPPED(status))
            {
                shell_jobs[i].stopped = 1;
                dprintf(STDOUT_FILENO, "[%d] Stopped %s\n", i + 1, shell_jobs[i].command);
            }
            else if (WIFCONTINUED(status)) shell_jobs[i].stopped = 0;
            else
            {
                dprintf(STDOUT_FILENO, "[%d] Done %s\n", i + 1, shell_jobs[i].command);
                shell_jobs[i].active = 0;
            }
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

static int shell_run_external(char **argv, int argc, const char *line, int background,
                              const char *input_path, const char *output_path)
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
        (void)setpgid(0, 0);
        (void)signal(SIGINT, SIG_DFL);
        (void)signal(SIGTERM, SIG_DFL);
        (void)signal(SIGTSTP, SIG_DFL);
        if (input_path != NULL)
        {
            int fd = open(input_path, O_RDONLY);
            if (fd == -1) { perror(input_path); _exit(1); }
            if (dup2(fd, STDIN_FILENO) == -1) { perror("dup2 input"); _exit(1); }
            close(fd);
        }
        if (output_path != NULL)
        {
            int fd = open(output_path, O_WRONLY | O_CREAT | O_TRUNC, 0666);
            if (fd == -1) { perror(output_path); _exit(1); }
            if (dup2(fd, STDOUT_FILENO) == -1) { perror("dup2 output"); _exit(1); }
            close(fd);
        }
        execvp(argv[0], argv);
        dprintf(STDERR_FILENO, "terminator: %s: command not found\n", argv[0]);
        _exit(errno == ENOENT ? 127 : 126);
    }
    (void)setpgid(pid, pid);
    if (background)
    {
        int job = shell_register_job(pid, line, 0);
        if (job >= 0)
        {
            dprintf(STDOUT_FILENO, "[%d] %ld\n", job + 1, (long)pid);
            return 0;
        }
        dprintf(STDERR_FILENO, "terminator: job table is full\n");
        (void)waitpid(pid, NULL, 0);
        return 1;
    }
    int status = 0;
    shell_foreground_pgid = pid;
    while (waitpid(pid, &status, WUNTRACED) < 0)
    {
        if (errno == EINTR) continue;
        shell_foreground_pgid = 0;
        perror("waitpid");
        return 1;
    }
    shell_foreground_pgid = 0;
    if (WIFSTOPPED(status))
    {
        int job = shell_register_job(pid, line, 1);
        if (job >= 0)
            dprintf(STDOUT_FILENO, "[%d] Stopped %s\n", job + 1, line);
        else
        {
            dprintf(STDERR_FILENO, "terminator: job table is full; terminating stopped job\n");
            (void)kill(-pid, SIGTERM);
            (void)waitpid(pid, NULL, 0);
        }
        return 128 + SIGTSTP;
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
    size_t length = strlen(line), count = 1, start = 0;
    int single = 0, dbl = 0;
    for (size_t i = 0; i < length; i++)
    {
        char c = line[i];
        if (c == '\\' && !single && i + 1 < length) { i++; continue; }
        if (c == '\'' && !dbl) single = !single;
        else if (c == '"' && !single) dbl = !dbl;
        else if (c == '|' && !single && !dbl) count++;
    }
    if (count == 1) return 0;
    *handled = 1;
    char **parts = calloc(count, sizeof(*parts));
    int (*pipes)[2] = calloc(count - 1, sizeof(*pipes));
    pid_t *pids = calloc(count, sizeof(*pids));
    if (parts == NULL || pipes == NULL || pids == NULL)
    {
        free(parts); free(pipes); free(pids); return 1;
    }
    size_t part = 0;
    single = 0; dbl = 0;
    for (size_t i = 0; i <= length; i++)
    {
        char c = line[i];
        if (i < length && c == '\\' && !single && i + 1 < length) { i++; continue; }
        if (i < length && c == '\'' && !dbl) single = !single;
        else if (i < length && c == '"' && !single) dbl = !dbl;
        if (i == length || (c == '|' && !single && !dbl))
        {
            size_t end = i;
            while (start < end && isspace((unsigned char)line[start])) start++;
            while (end > start && isspace((unsigned char)line[end - 1])) end--;
            parts[part++] = strndup(line + start, end - start);
            start = i + 1;
        }
    }
    for (size_t i = 0; i < count; i++)
        if (parts[i] == NULL) { for (size_t j = 0; j < count; j++) free(parts[j]); free(parts); free(pipes); free(pids); return 1; }
    int result = 0, made = 0, launched = 0;
    for (size_t i = 0; i + 1 < count; i++)
    {
        if (pipe(pipes[i]) == -1) { perror("pipe"); result = 1; goto cleanup; }
        made++;
    }
    for (size_t i = 0; i < count; i++)
    {
        pid_t child = fork();
        if (child == -1) { perror("fork"); result = 1; break; }
        if (child == 0)
        {
            (void)signal(SIGINT, SIG_DFL);
            (void)signal(SIGTERM, SIG_DFL);
            if (i > 0 && dup2(pipes[i - 1][0], STDIN_FILENO) == -1) _exit(126);
            if (i + 1 < count && dup2(pipes[i][1], STDOUT_FILENO) == -1) _exit(126);
            for (int k = 0; k < made; k++) { close(pipes[k][0]); close(pipes[k][1]); }
            char *argv[64]; int argc = shell_tokenize(parts[i], argv, 64);
            if (argc == 0) _exit(0);
            char *input_path = NULL, *output_path = NULL;
            if (!shell_extract_redirections(argv, &argc, &input_path, &output_path)) _exit(2);
            int saved_in = -1, saved_out = -1;
            if (!shell_apply_redirections(input_path, output_path, &saved_in, &saved_out)) _exit(1);
            if (saved_in >= 0) close(saved_in);
            if (saved_out >= 0) close(saved_out);
            free(input_path); free(output_path);
            if (argc == 0) _exit(0);
            execvp(argv[0], argv);
            dprintf(2, "terminator: %s: command not found\n", argv[0]);
            _exit(127);
        }
        pids[launched++] = child;
    }
    for (int i = 0; i < made; i++)
    {
        close(pipes[i][0]); close(pipes[i][1]);
        pipes[i][0] = pipes[i][1] = -1;
    }
    for (int i = 0; i < launched; i++)
    {
        int status = 0;
        while (waitpid(pids[i], &status, 0) < 0 && errno == EINTR) {}
        if (i == launched - 1 && WIFEXITED(status)) result = WEXITSTATUS(status);
    }
cleanup:
    for (int i = 0; i < made; i++)
    {
        if (pipes[i][0] >= 0) close(pipes[i][0]);
        if (pipes[i][1] >= 0) close(pipes[i][1]);
    }
    for (size_t i = 0; i < count; i++) free(parts[i]);
    free(parts); free(pipes); free(pids);
    return result;
}

typedef struct
{
    char *command;
    pid_t pid;
    int fd;
    int active;
    int output_started;
    int last_was_newline;
} MultiWatchProcess;

static int shell_parse_multiwatch(const char *line, char ***out_commands,
                                  size_t *out_count)
{
    const char *p = strchr(line, '[');
    if (p == NULL) return 0;
    p++;
    char **commands = NULL;
    size_t count = 0;
    while (*p != '\0' && *p != ']')
    {
        while (*p == ' ' || *p == '\t' || *p == ',') p++;
        if (*p == '\0' || *p == ']') break;
        char quote = (*p == '\'' || *p == '"') ? *p++ : 0;
        char *command = NULL; size_t length = 0, capacity = 0;
        while (*p != '\0' && (quote ? *p != quote : *p != ',' && *p != ']'))
        {
            if (*p == '\\' && p[1] != '\0' && quote != '\'') p++;
            if (!append_text(&command, &length, &capacity, p, 1))
            { free(command); goto fail; }
            p++;
        }
        if (quote && *p == quote) p++;
        if (command == NULL) command = strdup("");
        if (command == NULL) goto fail;
        char **next = realloc(commands, (count + 1) * sizeof(*commands));
        if (next == NULL) { free(command); goto fail; }
        commands = next;
        commands[count++] = command;
    }
    if (count == 0) goto fail;
    *out_commands = commands;
    *out_count = count;
    return 1;
fail:
    for (size_t i = 0; i < count; i++) free(commands[i]);
    free(commands);
    return 0;
}

static void multiwatch_close_process(MultiWatchProcess *process, time_t timestamp)
{
    static const char separator[] = "----------------------------------------------------\n";
    if (!process->output_started)
    {
        dprintf(STDOUT_FILENO, "\"%s\", %ld:\n%s", process->command,
                (long)timestamp, separator);
        process->output_started = 1;
    }
    if (!process->last_was_newline) dprintf(STDOUT_FILENO, "\n");
    dprintf(STDOUT_FILENO, "%s", separator);
}

static int shell_multiwatch(const char *line, int depth)
{
    char **commands = NULL; size_t count = 0;
    if (!shell_parse_multiwatch(line, &commands, &count))
    {
        dprintf(STDERR_FILENO, "usage: multiWatch [\"cmd1\", \"cmd2\"]\n");
        return 2;
    }
    shell_interrupted = 0;
    int result = 0;
    const int interval_ms = 2000;
    while (!shell_interrupted)
    {
        struct timespec cycle_start;
        (void)clock_gettime(CLOCK_MONOTONIC, &cycle_start);
        time_t timestamp = time(NULL);
        MultiWatchProcess *processes = calloc(count, sizeof(*processes));
        struct pollfd *fds = calloc(count, sizeof(*fds));
        if (processes == NULL || fds == NULL)
        {
            free(processes); free(fds); result = 1; break;
        }
        for (size_t i = 0; i < count; i++) fds[i].fd = -1;
        size_t active = 0;
        for (size_t i = 0; i < count && !shell_interrupted; i++)
        {
            int pipe_fd[2];
            if (pipe(pipe_fd) == -1) { perror("multiWatch pipe"); result = 1; break; }
            pid_t child = fork();
            if (child == -1)
            {
                perror("multiWatch fork"); close(pipe_fd[0]); close(pipe_fd[1]);
                result = 1; break;
            }
            if (child == 0)
            {
                (void)signal(SIGINT, SIG_DFL);
                (void)signal(SIGTERM, SIG_DFL);
                close(pipe_fd[0]);
                if (dup2(pipe_fd[1], STDOUT_FILENO) == -1 ||
                    dup2(pipe_fd[1], STDERR_FILENO) == -1) _exit(126);
                close(pipe_fd[1]);
                int status = shell_run_line(commands[i], 0, depth + 1);
                _exit(status & 255);
            }
            close(pipe_fd[1]);
            processes[i].command = commands[i];
            processes[i].pid = child;
            processes[i].fd = pipe_fd[0];
            processes[i].active = 1;
            processes[i].last_was_newline = 1;
            fds[i].fd = pipe_fd[0];
            fds[i].events = POLLIN | POLLHUP | POLLERR;
            active++;
        }
        while (active > 0 && !shell_interrupted)
        {
            int ready = poll(fds, count, -1);
            if (ready == -1)
            {
                if (errno == EINTR) continue;
                perror("multiWatch poll"); result = 1; break;
            }
            for (size_t i = 0; i < count; i++)
            {
                if (!processes[i].active || fds[i].revents == 0) continue;
                char output[2048];
                ssize_t n = read(processes[i].fd, output, sizeof(output));
                if (n > 0)
                {
                    if (!processes[i].output_started)
                    {
                        static const char separator[] = "----------------------------------------------------\n";
                        dprintf(STDOUT_FILENO, "\"%s\", %ld:\n%s",
                                processes[i].command, (long)timestamp, separator);
                        processes[i].output_started = 1;
                    }
                    size_t sent = 0;
                    while (sent < (size_t)n)
                    {
                        ssize_t wrote = write(STDOUT_FILENO, output + sent, (size_t)n - sent);
                        if (wrote > 0) sent += (size_t)wrote;
                        else if (wrote == -1 && errno == EINTR) continue;
                        else break;
                    }
                    processes[i].last_was_newline = output[n - 1] == '\n';
                }
                else if (n == 0 || (n == -1 && errno != EINTR && errno != EAGAIN))
                {
                    multiwatch_close_process(&processes[i], timestamp);
                    close(processes[i].fd);
                    processes[i].fd = -1;
                    processes[i].active = 0;
                    fds[i].fd = -1;
                    int child_status = 0;
                    while (waitpid(processes[i].pid, &child_status, 0) < 0 && errno == EINTR) {}
                    if (WIFEXITED(child_status) && WEXITSTATUS(child_status) != 0)
                        result = WEXITSTATUS(child_status);
                    active--;
                }
                fds[i].revents = 0;
            }
        }
        if (shell_interrupted)
        {
            for (size_t i = 0; i < count; i++)
                if (processes[i].active) (void)kill(processes[i].pid, SIGTERM);
            for (size_t i = 0; i < count; i++)
            {
                if (!processes[i].active) continue;
                struct timespec grace = {0, 200 * 1000 * 1000};
                (void)nanosleep(&grace, NULL);
                if (waitpid(processes[i].pid, NULL, WNOHANG) == 0)
                {
                    (void)kill(processes[i].pid, SIGTERM);
                    (void)nanosleep(&grace, NULL);
                    if (waitpid(processes[i].pid, NULL, WNOHANG) == 0)
                        (void)kill(processes[i].pid, SIGKILL);
                }
                while (waitpid(processes[i].pid, NULL, 0) < 0 && errno == EINTR) {}
                close(processes[i].fd);
                processes[i].active = 0;
            }
        }
        free(processes); free(fds);
        if (shell_interrupted || result != 0) break;
        struct timespec now;
        (void)clock_gettime(CLOCK_MONOTONIC, &now);
        long elapsed = (now.tv_sec - cycle_start.tv_sec) * 1000L +
                       (now.tv_nsec - cycle_start.tv_nsec) / 1000000L;
        while (!shell_interrupted && elapsed < interval_ms)
        {
            int remaining = interval_ms - (int)elapsed;
            (void)poll(NULL, 0, remaining);
            (void)clock_gettime(CLOCK_MONOTONIC, &now);
            elapsed = (now.tv_sec - cycle_start.tv_sec) * 1000L +
                      (now.tv_nsec - cycle_start.tv_nsec) / 1000000L;
        }
    }
    if (shell_interrupted) dprintf(STDOUT_FILENO, "^C\n");
    shell_interrupted = 0;
    for (size_t i = 0; i < count; i++) free(commands[i]);
    free(commands);
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
    char *input_path = NULL, *output_path = NULL;
    int redirections_ok = shell_extract_redirections(argv, &argc, &input_path, &output_path);
    int saved_stdin = -1, saved_stdout = -1;
    if (!redirections_ok)
        status = 2;
    else if (!background &&
             !shell_apply_redirections(input_path, output_path, &saved_stdin, &saved_stdout))
        status = 1;
    else if (argc == 0)
        status = 0;
    else if (strcmp(argv[0], "cd") == 0)
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
                dprintf(1, "[%d] %s %s\n", i + 1,
                        shell_jobs[i].stopped ? "Stopped" : "Running",
                        shell_jobs[i].command);
    }
    else if (strcmp(argv[0], "fg") == 0 || strcmp(argv[0], "bg") == 0)
    {
        int job = argc > 1 ? atoi(argv[1][0] == '%' ? argv[1] + 1 : argv[1]) : 1;
        if (job < 1 || job > SHELL_JOB_LIMIT || !shell_jobs[job - 1].active)
        { dprintf(2, "terminator: no such job\n"); status = 1; }
        else if (strcmp(argv[0], "bg") == 0)
        {
            if (kill(-shell_jobs[job - 1].pid, SIGCONT) == -1)
            { perror("bg"); status = 1; }
            else
            {
                shell_jobs[job - 1].stopped = 0;
                dprintf(1, "[%d]+ %s &\n", job, shell_jobs[job - 1].command);
            }
        }
        else
        {
            int child_status = 0;
            pid_t job_pid = shell_jobs[job - 1].pid;
            (void)kill(-job_pid, SIGCONT);
            shell_jobs[job - 1].stopped = 0;
            shell_foreground_pgid = job_pid;
            pid_t waited;
            do { waited = waitpid(job_pid, &child_status, WUNTRACED); }
            while (waited < 0 && errno == EINTR);
            shell_foreground_pgid = 0;
            if (waited < 0)
            { perror("fg"); status = 1; }
            else if (WIFSTOPPED(child_status))
            {
                shell_jobs[job - 1].stopped = 1;
                dprintf(1, "[%d] Stopped %s\n", job, shell_jobs[job - 1].command);
            }
            else
            {
                shell_jobs[job - 1].active = 0;
                if (WIFEXITED(child_status)) status = WEXITSTATUS(child_status);
                else if (WIFSIGNALED(child_status)) status = 128 + WTERMSIG(child_status);
            }
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
        status = shell_multiwatch(expanded, depth);
    }
    else
    {
        /* $? is substituted as a simple standalone argument in this version. */
        char status_text[24]; snprintf(status_text, sizeof(status_text), "%d", shell_last_status);
        for (int i = 0; i < argc; i++)
            if (strcmp(argv[i], "$?") == 0) { free(argv[i]); argv[i] = strdup(status_text); }
        status = shell_run_external(argv, argc, line, background,
                                    input_path, output_path);
    }
    shell_restore_redirections(saved_stdin, saved_stdout);
    free(input_path); free(output_path);
    shell_last_status = status;
    shell_free_argv(argv, argc);
    free(expanded);
    return status;
}

static void shell_worker(void)
{
    (void)signal(SIGINT, shell_sigint_handler);
    (void)signal(SIGTSTP, shell_sigtstp_handler);
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
    size_t cursor_position;
    size_t selection_anchor;
    int selection_active;
    size_t history_position;
    char history_draft[INPUT_CAPACITY];
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
    tab->history_position = SIZE_MAX;

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
                    if (tab->selection_active)
                    {
                        size_t selection_start = tab->selection_anchor < tab->cursor_position
                            ? tab->selection_anchor : tab->cursor_position;
                        size_t selection_end = tab->selection_anchor > tab->cursor_position
                            ? tab->selection_anchor : tab->cursor_position;
                        size_t from = selection_start > input_start ? selection_start : input_start;
                        size_t to = selection_end < i ? selection_end : i;
                        if (to > from)
                        {
                            int before_width = XTextWidth(font, tab->input + input_start,
                                                          (int)(from - input_start));
                            int selected_width = XTextWidth(font, tab->input + from,
                                                            (int)(to - from));
                            int selected_x = x + prefix_width + before_width;
                            XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
                            XFillRectangle(display, window, gc, selected_x,
                                           y - font->ascent, (unsigned int)selected_width,
                                           (unsigned int)(font->ascent + font->descent + 2));
                            XSetForeground(display, gc, WhitePixel(display, DefaultScreen(display)));
                            XDrawString(display, window, gc, selected_x, y,
                                        tab->input + from, (int)(to - from));
                            XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
                        }
                    }
                    if (tab->cursor_position >= input_start &&
                        tab->cursor_position <= i)
                    {
                        size_t before = tab->cursor_position - input_start;
                        int cursor_x = x + prefix_width +
                            XTextWidth(font, tab->input + input_start, (int)before);
                        XDrawLine(display, window, gc, cursor_x, y - font->ascent,
                                  cursor_x, y + 2);
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

static void tab_replace_input(Tab *tab, const char *text)
{
    size_t length = text != NULL ? strlen(text) : 0;
    if (length >= sizeof(tab->input)) length = sizeof(tab->input) - 1;
    if (length > 0) memcpy(tab->input, text, length);
    tab->input[length] = '\0';
    tab->input_length = length;
    tab->cursor_position = length;
}

static int tab_history_move(Tab *tab, int direction)
{
    if (shared_command_history == NULL) return 0;
    while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
    size_t count = shared_command_history->count;
    if (direction < 0)
    {
        if (count == 0 || (tab->history_position != SIZE_MAX && tab->history_position == 0))
        {
            (void)sem_post(&shared_command_history->lock);
            return 0;
        }
        if (tab->history_position == SIZE_MAX)
        {
            memcpy(tab->history_draft, tab->input, tab->input_length + 1);
            tab->history_position = count - 1;
        }
        else
        {
            tab->history_position--;
        }
    }
    else
    {
        if (tab->history_position == SIZE_MAX)
        {
            (void)sem_post(&shared_command_history->lock);
            return 0;
        }
        if (tab->history_position + 1 >= count)
        {
            tab->history_position = SIZE_MAX;
            tab_replace_input(tab, tab->history_draft);
            (void)sem_post(&shared_command_history->lock);
            return 1;
        }
        tab->history_position++;
    }
    tab_replace_input(tab, shared_command_history->entries[tab->history_position]);
    (void)sem_post(&shared_command_history->lock);
    return 1;
}

static int tab_insert_text(Tab *tab, const char *text, size_t length)
{
    size_t start = tab->cursor_position;
    size_t end = tab->cursor_position;
    if (tab->selection_active)
    {
        start = tab->selection_anchor < tab->cursor_position
            ? tab->selection_anchor : tab->cursor_position;
        end = tab->selection_anchor > tab->cursor_position
            ? tab->selection_anchor : tab->cursor_position;
    }
    size_t removed = end - start;
    if (length == 0 || length > sizeof(tab->input) - 1 - (tab->input_length - removed)) return 0;
    if (removed > 0)
    {
        memmove(tab->input + start, tab->input + end,
                tab->input_length - end + 1);
        tab->input_length -= removed;
        tab->cursor_position = start;
    }
    memmove(tab->input + tab->cursor_position + length,
            tab->input + tab->cursor_position,
            tab->input_length - tab->cursor_position + 1);
    memcpy(tab->input + tab->cursor_position, text, length);
    tab->input_length += length;
    tab->cursor_position += length;
    tab->selection_active = 0;
    tab->history_position = SIZE_MAX;
    return 1;
}

static void tab_copy_selection(Tab *tab)
{
    size_t start = tab->selection_active && tab->selection_anchor < tab->cursor_position
        ? tab->selection_anchor : (tab->selection_active ? tab->cursor_position : 0);
    size_t end = tab->selection_active && tab->selection_anchor > tab->cursor_position
        ? tab->selection_anchor : (tab->selection_active ? tab->cursor_position : tab->input_length);
    selection_clipboard_length = end - start;
    if (selection_clipboard_length >= sizeof(selection_clipboard))
        selection_clipboard_length = sizeof(selection_clipboard) - 1;
    if (selection_clipboard_length > 0)
        memcpy(selection_clipboard, tab->input + start, selection_clipboard_length);
    selection_clipboard[selection_clipboard_length] = '\0';
    tab->selection_active = 0;
}

static int tab_delete_selection(Tab *tab)
{
    if (!tab->selection_active) return 0;
    size_t start = tab->selection_anchor < tab->cursor_position
        ? tab->selection_anchor : tab->cursor_position;
    size_t end = tab->selection_anchor > tab->cursor_position
        ? tab->selection_anchor : tab->cursor_position;
    if (end > start)
    {
        memmove(tab->input + start, tab->input + end,
                tab->input_length - end + 1);
        tab->input_length -= end - start;
        tab->cursor_position = start;
    }
    tab->selection_active = 0;
    tab->history_position = SIZE_MAX;
    return end > start;
}

static void x11_selection_request(Display *display, XSelectionRequestEvent *request,
                                  Atom clipboard, Atom targets, Atom utf8)
{
    XEvent reply;
    memset(&reply, 0, sizeof(reply));
    reply.xselection.type = SelectionNotify;
    reply.xselection.display = request->display;
    reply.xselection.requestor = request->requestor;
    reply.xselection.selection = request->selection;
    reply.xselection.target = request->target;
    reply.xselection.time = request->time;
    reply.xselection.property = None;
    Atom property = request->property == None ? request->target : request->property;
    if (request->selection == clipboard && request->target == targets)
    {
        Atom supported[] = {targets, utf8, XA_STRING};
        XChangeProperty(display, request->requestor, property, XA_ATOM, 32,
                        PropModeReplace, (unsigned char *)supported, 3);
        reply.xselection.property = property;
    }
    else if (request->selection == clipboard &&
             (request->target == utf8 || request->target == XA_STRING))
    {
        XChangeProperty(display, request->requestor, property, request->target, 8,
                        PropModeReplace, (unsigned char *)selection_clipboard,
                        (int)selection_clipboard_length);
        reply.xselection.property = property;
    }
    XSendEvent(display, request->requestor, False, 0, &reply);
    XFlush(display);
}

typedef struct
{
    KeySym left, right, home, end, history_up, history_down, backspace, delete_key;
} KeySettings;

static void key_settings_defaults(KeySettings *settings)
{
    settings->left = XK_Left; settings->right = XK_Right;
    settings->home = XK_Home; settings->end = XK_End;
    settings->history_up = XK_Up; settings->history_down = XK_Down;
    settings->backspace = XK_BackSpace; settings->delete_key = XK_Delete;
}

static int key_settings_load(KeySettings *settings)
{
    key_settings_defaults(settings);
    const char *home_dir = getenv("HOME");
    if (home_dir == NULL || home_dir[0] == '\0') return 1;
    char path[1024];
    if (snprintf(path, sizeof(path), "%s/.terminatorrc", home_dir) >= (int)sizeof(path)) return 0;
    FILE *file = fopen(path, "r");
    if (file == NULL)
    {
        if (errno != ENOENT) return 0;
        file = fopen(path, "w");
        if (file == NULL) return 0;
        fputs("# Terminator Task 7 key settings (edit a value, then restart)\n"
              "left=Left\nright=Right\nhome=Home\nend=End\n"
              "history_up=Up\nhistory_down=Down\nbackspace=BackSpace\ndelete=Delete\n", file);
        fclose(file);
        return 1;
    }

    KeySettings loaded;
    key_settings_defaults(&loaded);
    char line[160];
    int bad = 0;
    while (fgets(line, sizeof(line), file) != NULL)
    {
        char *p = line;
        while (isspace((unsigned char)*p)) p++;
        if (*p == '#' || *p == '\0') continue;
        char *equals = strchr(p, '=');
        if (equals == NULL) { bad = 1; continue; }
        *equals++ = '\0';
        char *end = equals + strlen(equals);
        while (end > equals && isspace((unsigned char)end[-1])) *--end = '\0';
        while (*p != '\0' && isspace((unsigned char)p[strlen(p) - 1])) p[strlen(p) - 1] = '\0';
        KeySym value = XStringToKeysym(equals);
        if (value == NoSymbol) { bad = 1; continue; }
        if (strcmp(p, "left") == 0) loaded.left = value;
        else if (strcmp(p, "right") == 0) loaded.right = value;
        else if (strcmp(p, "home") == 0) loaded.home = value;
        else if (strcmp(p, "end") == 0) loaded.end = value;
        else if (strcmp(p, "history_up") == 0) loaded.history_up = value;
        else if (strcmp(p, "history_down") == 0) loaded.history_down = value;
        else if (strcmp(p, "backspace") == 0) loaded.backspace = value;
        else if (strcmp(p, "delete") == 0) loaded.delete_key = value;
        else bad = 1;
    }
    fclose(file);

    KeySym values[] = {loaded.left, loaded.right, loaded.home, loaded.end,
                       loaded.history_up, loaded.history_down,
                       loaded.backspace, loaded.delete_key};
    for (size_t i = 0; i < sizeof(values) / sizeof(values[0]); i++)
        for (size_t j = i + 1; j < sizeof(values) / sizeof(values[0]); j++)
            if (values[i] == values[j]) bad = 1;
    if (!bad) *settings = loaded;
    else fprintf(stderr, "Invalid or conflicting ~/.terminatorrc keys; using defaults.\n");
    return 1;
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

    KeySettings key_settings;
    (void)key_settings_load(&key_settings);

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
    XStoreName(display, window, "Terminator - Task 8");

    Atom wm_delete_window = XInternAtom(display, "WM_DELETE_WINDOW", False);
    Atom clipboard_atom = XInternAtom(display, "CLIPBOARD", False);
    Atom utf8_atom = XInternAtom(display, "UTF8_STRING", False);
    Atom targets_atom = XInternAtom(display, "TARGETS", False);
    Atom selection_property = XInternAtom(display, "TERMINATOR_CLIPBOARD", False);
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

            if (event.type == SelectionRequest)
            {
                x11_selection_request(display, &event.xselectionrequest,
                                      clipboard_atom, targets_atom, utf8_atom);
            }
            else if (event.type == SelectionNotify)
            {
                if (pending_paste_tab < tab_count && tabs[pending_paste_tab].is_open &&
                    event.xselection.property != None)
                {
                    Atom actual_type = None;
                    int actual_format = 0;
                    unsigned long item_count = 0, bytes_after = 0;
                    unsigned char *data = NULL;
                    if (XGetWindowProperty(display, window, selection_property, 0,
                                           INPUT_CAPACITY, True, AnyPropertyType,
                                           &actual_type, &actual_format, &item_count,
                                           &bytes_after, &data) == Success &&
                        data != NULL && actual_format == 8)
                    {
                        Tab *paste_tab = &tabs[pending_paste_tab];
                        if (!paste_tab->shell.command_running && paste_tab->shell.alive &&
                            item_count > 0)
                            (void)tab_insert_text(paste_tab, (const char *)data,
                                                  (size_t)item_count);
                        XFree(data);
                        request_redraw(display, window);
                    }
                }
                pending_paste_tab = SIZE_MAX;
            }
            else if (event.type == Expose)
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

                if ((event.xkey.state & (ControlMask | ShiftMask)) == (ControlMask | ShiftMask) &&
                    (key == XK_c || key == XK_C))
                {
                    tab_copy_selection(tab);
                    XSetSelectionOwner(display, clipboard_atom, window, CurrentTime);
                    request_redraw(display, window);
                }
                else if ((event.xkey.state & (ControlMask | ShiftMask)) == (ControlMask | ShiftMask) &&
                         (key == XK_v || key == XK_V) && !tab->shell.command_running)
                {
                    pending_paste_tab = active_tab;
                    XConvertSelection(display, clipboard_atom, utf8_atom,
                                      selection_property, window, CurrentTime);
                }
                else if (tab->shell.command_running &&
                    (event.xkey.state & ControlMask) && (key == XK_c || key == XK_C))
                {
                    if (tab->shell.pid > 0) (void)kill(-tab->shell.pid, SIGINT);
                    changed = 1;
                }
                else if (tab->shell.command_running &&
                    (event.xkey.state & ControlMask) && (key == XK_z || key == XK_Z))
                {
                    if (tab->shell.pid > 0) (void)kill(-tab->shell.pid, SIGTSTP);
                    changed = 1;
                }
                else if (key == XK_Page_Up)
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
                else if (key == key_settings.end)
                {
                    if (tab->shell.command_running || !tab->shell.alive)
                        tab->scroll_offset = 0;
                    else
                    {
                        if (event.xkey.state & ShiftMask)
                        {
                            if (!tab->selection_active) { tab->selection_anchor = tab->cursor_position; tab->selection_active = 1; }
                        }
                        else tab->selection_active = 0;
                        tab->cursor_position = tab->input_length;
                    }
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
                            tab->cursor_position = tab->input_length;
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
                            tab->cursor_position = 0;
                            tab->history_position = SIZE_MAX;
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
                else if (key == key_settings.left)
                {
                    if (event.xkey.state & ShiftMask)
                    {
                        if (!tab->selection_active) { tab->selection_anchor = tab->cursor_position; tab->selection_active = 1; }
                    }
                    else tab->selection_active = 0;
                    if (tab->cursor_position > 0) { tab->cursor_position--; changed = 1; }
                    else changed = 1;
                }
                else if (key == key_settings.right)
                {
                    if (event.xkey.state & ShiftMask)
                    {
                        if (!tab->selection_active) { tab->selection_anchor = tab->cursor_position; tab->selection_active = 1; }
                    }
                    else tab->selection_active = 0;
                    if (tab->cursor_position < tab->input_length) { tab->cursor_position++; changed = 1; }
                    else changed = 1;
                }
                else if (key == key_settings.home || ((event.xkey.state & ControlMask) && (key == XK_a || key == XK_A)))
                {
                    if (event.xkey.state & ShiftMask)
                    {
                        if (!tab->selection_active) { tab->selection_anchor = tab->cursor_position; tab->selection_active = 1; }
                    }
                    else tab->selection_active = 0;
                    tab->cursor_position = 0; changed = 1;
                }
                else if ((event.xkey.state & ControlMask) && (key == XK_e || key == XK_E))
                {
                    if (event.xkey.state & ShiftMask)
                    {
                        if (!tab->selection_active) { tab->selection_anchor = tab->cursor_position; tab->selection_active = 1; }
                    }
                    else tab->selection_active = 0;
                    tab->cursor_position = tab->input_length; changed = 1;
                }
                else if (key == key_settings.history_up)
                {
                    changed = tab_history_move(tab, -1);
                }
                else if (key == key_settings.history_down)
                {
                    changed = tab_history_move(tab, 1);
                }
                else if (key == key_settings.backspace)
                {
                    if (tab_delete_selection(tab))
                    {
                        changed = 1;
                    }
                    else if (tab->cursor_position > 0)
                    {
                        memmove(tab->input + tab->cursor_position - 1,
                                tab->input + tab->cursor_position,
                                tab->input_length - tab->cursor_position + 1);
                        tab->cursor_position--; tab->input_length--;
                        tab->history_position = SIZE_MAX; changed = 1;
                    }
                }
                else if (key == key_settings.delete_key || ((event.xkey.state & ControlMask) && (key == XK_d || key == XK_D)))
                {
                    if (tab_delete_selection(tab))
                    {
                        changed = 1;
                    }
                    else if (tab->cursor_position < tab->input_length)
                    {
                        memmove(tab->input + tab->cursor_position,
                                tab->input + tab->cursor_position + 1,
                                tab->input_length - tab->cursor_position);
                        tab->input_length--; tab->history_position = SIZE_MAX; changed = 1;
                    }
                    else if (tab->input_length == 0 && (event.xkey.state & ControlMask))
                    {
                        close_tab_at(tabs, &tab_count, &active_tab, active_tab);
                        if (tab_count == 0) running = 0;
                        changed = 1;
                    }
                }
                else if ((event.xkey.state & ControlMask) && (key == XK_u || key == XK_U))
                {
                    memmove(tab->input, tab->input + tab->cursor_position,
                            tab->input_length - tab->cursor_position + 1);
                    tab->input_length -= tab->cursor_position; tab->cursor_position = 0;
                    tab->selection_active = 0; tab->history_position = SIZE_MAX; changed = 1;
                }
                else if ((event.xkey.state & ControlMask) && (key == XK_k || key == XK_K))
                {
                    tab->input_length = tab->cursor_position;
                    tab->input[tab->input_length] = '\0';
                    tab->selection_active = 0; tab->history_position = SIZE_MAX; changed = 1;
                }
                else if ((event.xkey.state & ControlMask) && (key == XK_w || key == XK_W))
                {
                    size_t start = tab->cursor_position;
                    while (start > 0 && isspace((unsigned char)tab->input[start - 1])) start--;
                    while (start > 0 && !isspace((unsigned char)tab->input[start - 1])) start--;
                    memmove(tab->input + start, tab->input + tab->cursor_position,
                            tab->input_length - tab->cursor_position + 1);
                    tab->input_length -= tab->cursor_position - start;
                    tab->cursor_position = start; tab->selection_active = 0;
                    tab->history_position = SIZE_MAX; changed = 1;
                }
                else if ((event.xkey.state & ControlMask) && (key == XK_l || key == XK_L))
                {
                    tab->history.length = 0;
                    if (tab->history.data != NULL) tab->history.data[0] = '\0';
                    tab->scroll_offset = 0; changed = 1;
                }
                else
                {
                    for (int i = 0; i < n; i++)
                        if ((unsigned char)key_buffer[i] >= 32 && key_buffer[i] != 127)
                            changed |= tab_insert_text(tab, key_buffer + i, 1);
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
