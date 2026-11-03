#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <dirent.h>

#include <errno.h>
#include <fcntl.h>
#include <ctype.h>
#include <limits.h>
#include <glob.h>
#include <poll.h>
#include <pwd.h>
#include <pthread.h>
#include <semaphore.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
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
static char history_file_path[1024];
static _Thread_local ShellJob shell_jobs[SHELL_JOB_LIMIT];
static _Thread_local int shell_last_status;
static _Thread_local volatile sig_atomic_t shell_should_exit;
static _Thread_local volatile sig_atomic_t shell_interrupted;
static _Thread_local volatile sig_atomic_t shell_foreground_pgid;
static _Thread_local _Atomic pid_t *shell_foreground_slot;
static _Thread_local int shell_io_active;
static _Thread_local int shell_input_fd = STDIN_FILENO;
static _Thread_local int shell_output_fd = STDOUT_FILENO;
static _Thread_local int shell_error_fd = STDERR_FILENO;
static _Thread_local int shell_cwd_fd = -1;
static _Thread_local char shell_previous_dir[PATH_MAX];
typedef struct { char name[128]; char value[INPUT_CAPACITY]; int exported; } ShellVariable;
static _Thread_local ShellVariable shell_variables[128];
static _Thread_local size_t shell_variable_count;
static _Thread_local int shell_script_argc;
static _Thread_local char *shell_script_argv[32];
static int use_process_mode;

static void shell_set_foreground_pgid(pid_t pgid)
{
    shell_foreground_pgid = (sig_atomic_t)pgid;
    if (shell_foreground_slot != NULL)
        atomic_store_explicit(shell_foreground_slot, pgid, memory_order_relaxed);
}

static int shell_map_fd(int fd)
{
    if (!shell_io_active) return fd;
    if (fd == STDIN_FILENO) return shell_input_fd;
    if (fd == STDOUT_FILENO) return shell_output_fd;
    if (fd == STDERR_FILENO) return shell_error_fd;
    return fd;
}

static int shell_dprintf(int fd, const char *format, ...)
{
    va_list args;
    va_start(args, format);
    int result = vdprintf(shell_map_fd(fd), format, args);
    va_end(args);
    return result;
}

static void shell_perror(const char *message)
{
    int saved_errno = errno;
    shell_dprintf(STDERR_FILENO, "%s: %s\n",
                  message != NULL ? message : "error", strerror(saved_errno));
    errno = saved_errno;
}

static ssize_t shell_write(int fd, const void *buffer, size_t length)
{
    return write(shell_map_fd(fd), buffer, length);
}

#define dprintf shell_dprintf
#define perror shell_perror
#define write shell_write

static int shell_enter_cwd(void)
{
    if (shell_cwd_fd < 0 || fchdir(shell_cwd_fd) == 0) return 1;
    shell_dprintf(STDERR_FILENO, "terminator: cannot restore tab directory: %s\n",
                  strerror(errno));
    return 0;
}

static int shell_fd_path(int fd, char *buffer, size_t capacity)
{
    if (fd < 0 || buffer == NULL || capacity < 2) return 0;
    char link[64];
    int n = snprintf(link, sizeof(link), "/proc/self/fd/%d", fd);
    if (n < 0 || (size_t)n >= sizeof(link)) return 0;
    ssize_t length = readlink(link, buffer, capacity - 1);
    if (length < 0 || (size_t)length >= capacity - 1) return 0;
    buffer[length] = '\0';
    return 1;
}

static void *shell_glob_opendir(const char *name)
{
    int fd = shell_cwd_fd >= 0
        ? openat(shell_cwd_fd, name, O_RDONLY | O_DIRECTORY)
        : open(name, O_RDONLY | O_DIRECTORY);
    if (fd < 0) return NULL;
    DIR *directory = fdopendir(fd);
    if (directory == NULL) close(fd);
    return directory;
}

static void *shell_glob_readdir(void *directory)
{
    return readdir((DIR *)directory);
}

static void shell_glob_closedir(void *directory)
{
    (void)closedir((DIR *)directory);
}

static int shell_glob_stat(const char *path, void *status)
{
    return shell_cwd_fd >= 0
        ? fstatat(shell_cwd_fd, path, (struct stat *)status, 0)
        : stat(path, (struct stat *)status);
}

static int shell_glob_lstat(const char *path, void *status)
{
    return shell_cwd_fd >= 0
        ? fstatat(shell_cwd_fd, path, (struct stat *)status, AT_SYMLINK_NOFOLLOW)
        : lstat(path, (struct stat *)status);
}
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

static void shell_sigterm_handler(int signal_number)
{
    (void)signal_number;
    shell_should_exit = 1;
}

static void history_write_entry(FILE *file, const char *line)
{
    for (size_t i = 0; line[i] != '\0'; i++)
        fputc(line[i] == '\n' ? '\x1f' : line[i], file);
    fputc('\n', file);
}

static void history_append_memory_locked(const char *line)
{
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
}

static void history_persist_locked(const char *new_line, int rewrite)
{
    if (history_file_path[0] == '\0') return;
    int flags = O_WRONLY | O_CREAT | (rewrite ? O_TRUNC : O_APPEND);
    int fd = open(history_file_path, flags, 0600);
    if (fd >= 0) (void)fchmod(fd, 0600);
    FILE *file = fd >= 0 ? fdopen(fd, rewrite ? "w" : "a") : NULL;
    if (file == NULL && fd >= 0) close(fd);
    if (file == NULL) return;
    if (rewrite)
    {
        for (size_t i = 0; i < shared_command_history->count; i++)
            history_write_entry(file, shared_command_history->entries[i]);
    }
    else if (new_line != NULL)
    {
        history_write_entry(file, new_line);
    }
    (void)fclose(file);
}

static void history_load_file(void)
{
    const char *home_dir = getenv("HOME");
    const char *override = getenv("TERMINATOR_HISTFILE");
    int path_length;
    if (override != NULL && override[0] != '\0')
        path_length = snprintf(history_file_path, sizeof(history_file_path), "%s", override);
    else if (home_dir != NULL && home_dir[0] != '\0')
        path_length = snprintf(history_file_path, sizeof(history_file_path), "%s/.terminator_history", home_dir);
    else
        path_length = -1;
    if (path_length < 0 || path_length >= (int)sizeof(history_file_path))
    {
        history_file_path[0] = '\0';
        return;
    }
    FILE *file = fopen(history_file_path, "r");
    if (file == NULL) return;
    char *line = NULL;
    size_t capacity = 0;
    size_t loaded_entries = 0;
    ssize_t length;
    while ((length = getline(&line, &capacity, file)) >= 0)
    {
        loaded_entries++;
        while (length > 0 && (line[length - 1] == '\n' || line[length - 1] == '\r'))
            line[--length] = '\0';
        for (ssize_t i = 0; i < length; i++)
            if (line[i] == '\x1f') line[i] = '\n';
        history_append_memory_locked(line);
    }
    free(line);
    fclose(file);
    if (loaded_entries > SHELL_HISTORY_LIMIT)
        history_persist_locked(NULL, 1);
}

static void shell_add_history(const char *line)
{
    if (line == NULL || line[0] == '\0') return;
    if (shared_command_history == NULL) return;
    while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
    int rewrite = shared_command_history->count == SHELL_HISTORY_LIMIT;
    history_append_memory_locked(line);
    history_persist_locked(line, rewrite);
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
            matches.gl_opendir = shell_glob_opendir;
            matches.gl_readdir = shell_glob_readdir;
            matches.gl_closedir = shell_glob_closedir;
            matches.gl_stat = shell_glob_stat;
            matches.gl_lstat = shell_glob_lstat;
            if (glob(token, GLOB_ALTDIRFUNC, NULL, &matches) == 0 && matches.gl_pathc > 0)
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

typedef struct
{
    char *input_path;
    char *output_path;
    char *error_path;
    int append_output;
    int append_error;
    int merge_error;
} ShellRedirections;

static int shell_extract_redirections(char **argv, int *argc, ShellRedirections *redirs)
{
    int kept = 0;
    memset(redirs, 0, sizeof(*redirs));
    for (int i = 0; i < *argc; i++)
    {
        const char *op = argv[i];
        int is_input = strcmp(op, "<") == 0;
        int is_out = strcmp(op, ">") == 0 || strcmp(op, ">>") == 0;
        int is_err = strcmp(op, "2>") == 0 || strcmp(op, "2>>") == 0;
        int append_out = strcmp(op, ">>") == 0;
        int append_err = strcmp(op, "2>>") == 0;
        if (strcmp(op, "2>&1") == 0)
        {
            redirs->merge_error = 1;
            free(argv[i]); argv[i] = NULL;
            continue;
        }
        if (is_input || is_out || is_err)
        {
            if (i + 1 >= *argc)
            {
                dprintf(STDERR_FILENO, "terminator: syntax error near unexpected token 'newline'\n");
                return 0;
            }
            if (strcmp(argv[i + 1], ">") == 0 || strcmp(argv[i + 1], ">>") == 0 ||
                strcmp(argv[i + 1], "<") == 0 || strcmp(argv[i + 1], "|") == 0)
            {
                dprintf(STDERR_FILENO, "terminator: syntax error near unexpected token '%s'\n", argv[i + 1]);
                return 0;
            }
            char **slot = is_input ? &redirs->input_path
                : (is_err ? &redirs->error_path : &redirs->output_path);
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
            if (is_out) redirs->append_output = append_out;
            if (is_err) redirs->append_error = append_err;
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

static int shell_apply_redirections(const ShellRedirections *redirs,
                                    int saved[3])
{
    for (int i = 0; i < 3; i++) saved[i] = -1;
    if (redirs->input_path != NULL)
    {
        int fd = shell_cwd_fd >= 0
            ? openat(shell_cwd_fd, redirs->input_path, O_RDONLY)
            : open(redirs->input_path, O_RDONLY);
        if (fd == -1) { perror(redirs->input_path); return 0; }
        if (shell_io_active)
        {
            saved[0] = shell_input_fd;
            shell_input_fd = fd;
        }
        else
        {
            saved[0] = dup(STDIN_FILENO);
            if (saved[0] == -1 || dup2(fd, STDIN_FILENO) == -1)
            { perror("dup2 input"); close(fd); return 0; }
            close(fd);
        }
    }
    if (redirs->output_path != NULL)
    {
        int flags = O_WRONLY | O_CREAT | (redirs->append_output ? O_APPEND : O_TRUNC);
        int fd = shell_cwd_fd >= 0
            ? openat(shell_cwd_fd, redirs->output_path, flags, 0666)
            : open(redirs->output_path, flags, 0666);
        if (fd == -1) { perror(redirs->output_path); return 0; }
        if (shell_io_active)
        {
            saved[1] = shell_output_fd;
            shell_output_fd = fd;
        }
        else
        {
            saved[1] = dup(STDOUT_FILENO);
            if (saved[1] == -1 || dup2(fd, STDOUT_FILENO) == -1)
            { perror("dup2 output"); close(fd); return 0; }
            close(fd);
        }
    }
    if (redirs->error_path != NULL)
    {
        int flags = O_WRONLY | O_CREAT | (redirs->append_error ? O_APPEND : O_TRUNC);
        int fd = shell_cwd_fd >= 0
            ? openat(shell_cwd_fd, redirs->error_path, flags, 0666)
            : open(redirs->error_path, flags, 0666);
        if (fd == -1) { perror(redirs->error_path); return 0; }
        if (shell_io_active) { saved[2] = shell_error_fd; shell_error_fd = fd; }
        else
        {
            saved[2] = dup(STDERR_FILENO);
            if (saved[2] == -1 || dup2(fd, STDERR_FILENO) == -1)
            { perror("dup2 stderr"); close(fd); return 0; }
            close(fd);
        }
    }
    if (redirs->merge_error)
    {
        if (shell_io_active) { saved[2] = shell_error_fd; shell_error_fd = shell_output_fd; }
        else
        {
            saved[2] = dup(STDERR_FILENO);
            if (saved[2] == -1 || dup2(STDOUT_FILENO, STDERR_FILENO) == -1)
            { perror("dup2 stderr"); return 0; }
        }
    }
    return 1;
}

static void shell_restore_redirections(int saved[3])
{
    if (shell_io_active)
    {
        if (saved[0] >= 0) { if (shell_input_fd != saved[0]) close(shell_input_fd); shell_input_fd = saved[0]; }
        if (saved[1] >= 0) { if (shell_output_fd != saved[1]) close(shell_output_fd); shell_output_fd = saved[1]; }
        if (saved[2] >= 0) { if (shell_error_fd != saved[2]) close(shell_error_fd); shell_error_fd = saved[2]; }
    }
    else
    {
        for (int i = 0; i < 3; i++)
            if (saved[i] >= 0) { (void)dup2(saved[i], i); close(saved[i]); }
    }
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
static int shell_run_script(const char *path, int argc, char **argv, int depth);

static const char *shell_get_variable(const char *name)
{
    for (size_t i = 0; i < shell_variable_count; i++)
        if (strcmp(shell_variables[i].name, name) == 0) return shell_variables[i].value;
    return getenv(name) != NULL ? getenv(name) : "";
}

static int shell_set_variable(const char *name, const char *value)
{
    if (name == NULL || !((isalpha((unsigned char)name[0])) || name[0] == '_')) return 0;
    for (size_t i = 1; name[i]; i++)
        if (!(isalnum((unsigned char)name[i]) || name[i] == '_')) return 0;
    size_t i;
    for (i = 0; i < shell_variable_count; i++)
        if (strcmp(shell_variables[i].name, name) == 0) break;
    if (i == shell_variable_count)
    {
        if (i >= sizeof(shell_variables) / sizeof(shell_variables[0])) return 0;
        snprintf(shell_variables[i].name, sizeof(shell_variables[i].name), "%s", name);
        shell_variable_count++;
    }
    snprintf(shell_variables[i].value, sizeof(shell_variables[i].value), "%s", value);
    return 1;
}

static int shell_mark_exported(const char *name, const char *value)
{
    if (value != NULL && !shell_set_variable(name, value)) return 0;
    for (size_t i = 0; i < shell_variable_count; i++)
        if (strcmp(shell_variables[i].name, name) == 0)
        { shell_variables[i].exported = 1; return 1; }
    if (!shell_set_variable(name, value != NULL ? value : shell_get_variable(name))) return 0;
    shell_variables[shell_variable_count - 1].exported = 1;
    return 1;
}

static void shell_export_environment(void)
{
    for (size_t i = 0; i < shell_variable_count; i++)
        if (shell_variables[i].exported)
            (void)setenv(shell_variables[i].name, shell_variables[i].value, 1);
}

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
        if (shell_io_active)
        {
            if (dup2(shell_input_fd, STDIN_FILENO) == -1 ||
                dup2(shell_error_fd, STDERR_FILENO) == -1) _exit(126);
        }
        close(pipe_fd[0]);
        if (dup2(pipe_fd[1], STDOUT_FILENO) == -1) _exit(126);
        close(pipe_fd[1]);
        shell_io_active = 0;
        if (!shell_enter_cwd()) _exit(126);
        (void)signal(SIGPIPE, SIG_DFL);
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
        if (!single && !dbl && c == '~' &&
            (i == 0 || isspace((unsigned char)line[i - 1]) || line[i - 1] == '='))
        {
            size_t j = i + 1;
            while (line[j] != '\0' && line[j] != '/' && !isspace((unsigned char)line[j])) j++;
            const char *directory = NULL;
            char *user = NULL;
            if (j == i + 1) directory = shell_get_variable("HOME");
            else
            {
                user = strndup(line + i + 1, j - i - 1);
                struct passwd *entry = user != NULL ? getpwnam(user) : NULL;
                if (entry != NULL) directory = entry->pw_dir;
            }
            if (directory != NULL)
            {
                if (!append_text(&out, &used, &capacity, directory, strlen(directory))) { free(user); goto fail; }
                i = j;
            }
            else
            {
                if (!append_text(&out, &used, &capacity, line + i, j - i)) { free(user); goto fail; }
                i = j;
            }
            free(user);
            continue;
        }
        if (!single && c == '$' && (isalpha((unsigned char)line[i + 1]) || line[i + 1] == '_' || line[i + 1] == '?' || line[i + 1] == '#' || line[i + 1] == '$' || isdigit((unsigned char)line[i + 1]) || line[i + 1] == '{'))
        {
            size_t j = i + 1; char name[256]; size_t n = 0;
            int braced = line[j] == '{';
            if (braced) j++;
            if (line[j] == '?' || line[j] == '#' || line[j] == '$') { name[n++] = line[j++]; }
            else if (isdigit((unsigned char)line[j])) { while (isdigit((unsigned char)line[j]) && n + 1 < sizeof(name)) name[n++] = line[j++]; }
            else while ((isalnum((unsigned char)line[j]) || line[j] == '_') && n + 1 < sizeof(name)) name[n++] = line[j++];
            if (braced && line[j] == '}') j++;
            name[n] = '\0';
            char status_text[32]; const char *value = "";
            if (strcmp(name, "?") == 0) { snprintf(status_text, sizeof(status_text), "%d", shell_last_status); value = status_text; }
            else if (strcmp(name, "#") == 0) { snprintf(status_text, sizeof(status_text), "%d", shell_script_argc); value = status_text; }
            else if (strcmp(name, "$") == 0) { snprintf(status_text, sizeof(status_text), "%ld", (long)getpid()); value = status_text; }
            else if (strcmp(name, "0") == 0)
                value = shell_script_argv[0] != NULL ? shell_script_argv[0] : "terminator";
            else if (isdigit((unsigned char)name[0])) { int arg = atoi(name); if (arg > 0 && arg <= shell_script_argc && arg < 32) value = shell_script_argv[arg]; }
            else value = shell_get_variable(name);
            if (dbl)
            {
                for (size_t k = 0; value[k] != '\0'; k++)
                {
                    if ((value[k] == '"' || value[k] == '\\') && !append_text(&out, &used, &capacity, "\\", 1)) goto fail;
                    if (!append_text(&out, &used, &capacity, value + k, 1)) goto fail;
                }
            }
            else if (!append_text(&out, &used, &capacity, value, strlen(value))) goto fail;
            if (j == i + 1) { if (!append_text(&out, &used, &capacity, "$", 1)) goto fail; i++; }
            else i = j;
            continue;
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
                              const ShellRedirections *redirs)
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
        if (shell_io_active &&
            (dup2(shell_input_fd, STDIN_FILENO) == -1 ||
             dup2(shell_output_fd, STDOUT_FILENO) == -1 ||
             dup2(shell_error_fd, STDERR_FILENO) == -1)) _exit(126);
        shell_io_active = 0;
        if (!shell_enter_cwd()) _exit(126);
        (void)setpgid(0, 0);
        (void)signal(SIGINT, SIG_DFL);
        (void)signal(SIGTERM, SIG_DFL);
        (void)signal(SIGTSTP, SIG_DFL);
        (void)signal(SIGPIPE, SIG_DFL);
        shell_export_environment();
        if (background && redirs->input_path != NULL)
        {
            int fd = open(redirs->input_path, O_RDONLY);
            if (fd == -1) { perror(redirs->input_path); _exit(1); }
            if (dup2(fd, STDIN_FILENO) == -1) { perror("dup2 input"); _exit(1); }
            close(fd);
        }
        if (background && redirs->output_path != NULL)
        {
            int flags = O_WRONLY | O_CREAT | (redirs->append_output ? O_APPEND : O_TRUNC);
            int fd = open(redirs->output_path, flags, 0666);
            if (fd == -1) { perror(redirs->output_path); _exit(1); }
            if (dup2(fd, STDOUT_FILENO) == -1) { perror("dup2 output"); _exit(1); }
            close(fd);
        }
        if (background && redirs->error_path != NULL)
        {
            int flags = O_WRONLY | O_CREAT | (redirs->append_error ? O_APPEND : O_TRUNC);
            int fd = open(redirs->error_path, flags, 0666);
            if (fd == -1) { perror(redirs->error_path); _exit(1); }
            if (dup2(fd, STDERR_FILENO) == -1) { perror("dup2 stderr"); _exit(1); }
            close(fd);
        }
        if (background && redirs->merge_error && dup2(STDOUT_FILENO, STDERR_FILENO) == -1)
        { perror("dup2 stderr"); _exit(1); }
        execvp(argv[0], argv);
        int exec_error = errno;
        if (exec_error == ENOENT || exec_error == ENOTDIR)
            dprintf(STDERR_FILENO, "terminator: %s: command not found\n", argv[0]);
        else
            dprintf(STDERR_FILENO, "terminator: %s: %s\n", argv[0], strerror(exec_error));
        _exit(exec_error == ENOENT || exec_error == ENOTDIR ? 127 : 126);
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
    shell_set_foreground_pgid(pid);
    while (waitpid(pid, &status, WUNTRACED) < 0)
    {
        if (errno == EINTR) continue;
        shell_set_foreground_pgid(0);
        perror("waitpid");
        return 1;
    }
    shell_set_foreground_pgid(0);
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
    /* Reject empty stages before creating children (e.g. `a | | b`, `| b`). */
    size_t first = 0, last = length;
    while (first < last && isspace((unsigned char)line[first])) first++;
    while (last > first && isspace((unsigned char)line[last - 1])) last--;
    int previous_pipe = 0, syntax_error = first == last || line[first] == '|' || line[last - 1] == '|';
    single = 0; dbl = 0;
    for (size_t i = first; i < last && !syntax_error; i++)
    {
        char c = line[i];
        if (c == '\\' && !single && i + 1 < last) { i++; previous_pipe = 0; continue; }
        if (c == '\'' && !dbl) single = !single;
        else if (c == '"' && !single) dbl = !dbl;
        else if (c == '|' && !single && !dbl)
        {
            size_t j = i + 1;
            while (j < last && isspace((unsigned char)line[j])) j++;
            if (previous_pipe || j == last || line[j] == '|') syntax_error = 1;
            previous_pipe = 1;
        }
        else if (!isspace((unsigned char)c)) previous_pipe = 0;
    }
    if (syntax_error)
    {
        dprintf(STDERR_FILENO, "terminator: syntax error near unexpected token '|'\n");
        return 2;
    }
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
            if (shell_io_active &&
                (dup2(shell_input_fd, STDIN_FILENO) == -1 ||
                 dup2(shell_output_fd, STDOUT_FILENO) == -1 ||
                 dup2(shell_error_fd, STDERR_FILENO) == -1)) _exit(126);
            shell_io_active = 0;
            if (!shell_enter_cwd()) _exit(126);
            (void)signal(SIGINT, SIG_DFL);
            (void)signal(SIGTERM, SIG_DFL);
            (void)signal(SIGPIPE, SIG_DFL);
            if (i > 0 && dup2(pipes[i - 1][0], STDIN_FILENO) == -1) _exit(126);
            if (i + 1 < count && dup2(pipes[i][1], STDOUT_FILENO) == -1) _exit(126);
            for (int k = 0; k < made; k++) { close(pipes[k][0]); close(pipes[k][1]); }
            int stage_status = shell_run_line(parts[i], 0, 1);
            _exit(stage_status & 255);
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
                if (shell_io_active &&
                    (dup2(shell_input_fd, STDIN_FILENO) == -1 ||
                     dup2(shell_output_fd, STDOUT_FILENO) == -1 ||
                     dup2(shell_error_fd, STDERR_FILENO) == -1)) _exit(126);
                shell_io_active = 0;
                if (!shell_enter_cwd()) _exit(126);
                (void)signal(SIGINT, SIG_DFL);
                (void)signal(SIGTERM, SIG_DFL);
                (void)signal(SIGPIPE, SIG_DFL);
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

static int script_test(const char *condition)
{
    char *expanded = expand_shell_text(condition, 0);
    char *args[8]; int argc = shell_tokenize(expanded, args, 8); int ok = 0;
    if (argc == 4 && strcmp(args[0], "[") == 0 && strcmp(args[3], "]") == 0 &&
        (strcmp(args[1], "-f") == 0 || strcmp(args[1], "-d") == 0))
    {
        struct stat st;
        int rc = shell_cwd_fd >= 0 ? fstatat(shell_cwd_fd, args[2], &st, 0) : stat(args[2], &st);
        if (strcmp(args[1], "-f") == 0) ok = rc == 0 && S_ISREG(st.st_mode);
        else ok = rc == 0 && S_ISDIR(st.st_mode);
    }
    else if (argc >= 5 && strcmp(args[0], "[") == 0 && strcmp(args[argc - 1], "]") == 0)
    {
        const char *a = args[1], *op = args[2], *b = args[3];
        if (strcmp(op, "-eq") == 0 || strcmp(op, "-gt") == 0)
        {
            char *ea, *eb; long x = strtol(a, &ea, 10), y = strtol(b, &eb, 10);
            ok = *a && *b && *ea == '\0' && *eb == '\0' &&
                 (strcmp(op, "-eq") == 0 ? x == y : x > y);
        }
        else if (strcmp(op, "=") == 0 || strcmp(op, "==") == 0) ok = strcmp(a, b) == 0;
    }
    shell_free_argv(args, argc); free(expanded); return ok;
}

static int shell_run_script(const char *path, int argc, char **argv, int depth)
{
    if (depth > 8) { dprintf(2, "terminator: script nesting limit reached\n"); return 2; }
    int fd = shell_cwd_fd >= 0 ? openat(shell_cwd_fd, path, O_RDONLY) : open(path, O_RDONLY);
    FILE *file = fd >= 0 ? fdopen(fd, "r") : NULL;
    if (file == NULL) { perror(path); return 1; }
    char **lines = NULL; size_t nlines = 0, caplines = 0; char *line = NULL; size_t cap = 0; ssize_t len;
    int syntax = 0, nesting = 0, saw_else[64] = {0};
    while ((len = getline(&line, &cap, file)) >= 0)
    {
        while (len && (line[len-1] == '\n' || line[len-1] == '\r')) line[--len] = '\0';
        if (nlines == caplines) { size_t nc = caplines ? caplines * 2 : 32; char **nl = realloc(lines, nc * sizeof(*nl)); if (!nl) { syntax = 1; break; } lines = nl; caplines = nc; }
        lines[nlines++] = strdup(line);
        char *p = line; while (isspace((unsigned char)*p)) p++;
        if (!strncmp(p, "if ", 3))
        {
            if (nesting >= 64) syntax = 1;
            else { saw_else[nesting] = 0; nesting++; }
        }
        else if (!strncmp(p, "elif ", 5))
        { if (!nesting || saw_else[nesting - 1]) syntax = 1; }
        else if (!strcmp(p, "else") || !strncmp(p, "else ", 5) || !strncmp(p, "else;", 5))
        {
            if (!nesting || saw_else[nesting - 1]) syntax = 1;
            else saw_else[nesting - 1] = 1;
        }
        else if (!strcmp(p, "fi")) { if (!nesting) syntax = 1; else nesting--; }
    }
    free(line); fclose(file);
    if (nesting != 0) syntax = 1;
    if (syntax) { dprintf(2, "terminator: script syntax error (unmatched if/fi)\n"); for (size_t i=0;i<nlines;i++) free(lines[i]); free(lines); return 2; }

    int saved_argc = shell_script_argc; char *saved_args[32];
    memcpy(saved_args, shell_script_argv, sizeof(saved_args));
    shell_script_argc = argc < 31 ? argc : 31; shell_script_argv[0] = (char *)path;
    for (int i=0;i<shell_script_argc;i++) shell_script_argv[i+1] = argv[i];
    int active[64], taken[64]; int level = 0, status = 0;
    for (size_t i=0; i<nlines && !shell_should_exit; i++)
    {
        char *p=lines[i]; while (isspace((unsigned char)*p)) p++;
        if (*p == '\0' || *p == '#') continue;
        if (!strncmp(p,"if ",3))
        {
            char *cond=p+3; size_t l=strlen(cond); if (l>=6 && strcmp(cond+l-6,"; then")==0) cond[l-6]='\0';
            int parent = level ? active[level-1] : 1;
            int pass = parent && script_test(cond);
            active[level]=pass; taken[level]=pass; level++; continue;
        }
        if (!strncmp(p,"elif ",5) && level)
        {
            char *cond=p+5; size_t l=strlen(cond); if (l>=6 && strcmp(cond+l-6,"; then")==0) cond[l-6]='\0';
            int parent = level > 1 ? active[level-2] : 1;
            int pass = parent && !taken[level-1] && script_test(cond);
            active[level-1]=pass; if(pass) taken[level-1]=1; continue;
        }
        if ((!strcmp(p,"else") || !strncmp(p,"else;",5)) && level)
        { int parent=level>1?active[level-2]:1; active[level-1]=parent&&!taken[level-1]; taken[level-1]=1; continue; }
        if (!strcmp(p,"fi") && level) { level--; continue; }
        if (level && !active[level-1]) continue;
        if (!strncmp(p,"then",4) && (p[4]=='\0' || isspace((unsigned char)p[4]) || p[4]==';')) continue;
        if (!strcmp(p,"#!/bin/bash")) continue;
        status=shell_run_line(p,1,depth+1);
    }
    shell_script_argc=saved_argc; memcpy(shell_script_argv,saved_args,sizeof(saved_args));
    for (size_t i = 0; i < nlines; i++)
        free(lines[i]);
    free(lines);
    return status;
}

static int shell_run_line(const char *line, int record_history, int depth)
{
    if (depth > 8) { dprintf(2, "terminator: source nesting limit reached\n"); return 1; }
    if (record_history) shell_add_history(line);
    /* Execute simple top-level `;` command lists. Quoted and nested command
       substitutions keep their semicolons as data/input. */
    {
        size_t length = strlen(line), start = 0;
        int single = 0, dbl = 0, backtick = 0, nesting = 0, has_separator = 0;
        for (size_t i = 0; i <= length; i++)
        {
            char c = line[i];
            if (i < length && c == '\\' && !single && i + 1 < length) { i++; continue; }
            if (i < length && c == '\'' && !dbl && !backtick) single = !single;
            else if (i < length && c == '"' && !single && !backtick) dbl = !dbl;
            else if (i < length && c == '`' && !single) backtick = !backtick;
            else if (i < length && c == '(' && !single) nesting++;
            else if (i < length && c == ')' && !single && nesting > 0) nesting--;
            if (i == length || (c == ';' && !single && !dbl && !backtick && nesting == 0))
            {
                if (i < length) has_separator = 1;
                if (has_separator || i < length)
                {
                    char *part = strndup(line + start, i - start);
                    if (part == NULL) return 1;
                    int part_status = 0;
                    if (part[0] != '\0') part_status = shell_run_line(part, 0, depth + 1);
                    free(part);
                    start = i + 1;
                    if (i == length) { shell_last_status = part_status; return part_status; }
                    shell_last_status = part_status;
                }
            }
        }
    }
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
    int status = 0;
    if (argc == 1 && strchr(argv[0], '=') != NULL)
    {
        char *equals = strchr(argv[0], '='); *equals++ = '\0';
        status = shell_set_variable(argv[0], equals) ? 0 : 2;
        if (status != 0) dprintf(2, "terminator: invalid assignment\n");
        shell_last_status = status; shell_free_argv(argv, argc); free(expanded); return status;
    }
    int background = strcmp(argv[argc - 1], "&") == 0;
    if (background) { free(argv[--argc]); argv[argc] = NULL; }
    ShellRedirections redirs;
    memset(&redirs, 0, sizeof(redirs));
    int empty_expanded_redirect = argc > 0 &&
        (strcmp(argv[argc - 1], "<") == 0 || strcmp(argv[argc - 1], ">") == 0 ||
         strcmp(argv[argc - 1], ">>") == 0 || strcmp(argv[argc - 1], "2>") == 0 ||
         strcmp(argv[argc - 1], "2>>") == 0) && strchr(line, '$') != NULL;
    int redirections_ok;
    if (empty_expanded_redirect)
    {
        dprintf(STDERR_FILENO, "terminator: ambiguous redirect\n");
        redirections_ok = 0;
    }
    else redirections_ok = shell_extract_redirections(argv, &argc, &redirs);
    int saved_fds[3] = {-1, -1, -1};
    if (!redirections_ok)
        status = empty_expanded_redirect ? 1 : 2;
    else if (!background &&
             !shell_apply_redirections(&redirs, saved_fds))
        status = 1;
    else if (argc == 0)
        status = 0;
    else if (strcmp(argv[0], "export") == 0)
    {
        if (argc == 1)
        {
            for (size_t i = 0; i < shell_variable_count; i++)
                if (shell_variables[i].exported)
                    dprintf(1, "declare -x %s=\"%s\"\n", shell_variables[i].name,
                            shell_variables[i].value);
        }
        else for (int i = 1; i < argc; i++)
        {
            char *eq = strchr(argv[i], '=');
            if (eq != NULL) { *eq = '\0'; if (!shell_mark_exported(argv[i], eq + 1)) status = 1; }
            else if (!shell_mark_exported(argv[i], NULL)) status = 1;
        }
    }
    else if (strcmp(argv[0], "cd") == 0)
    {
        int change_to_previous = argc > 1 && strcmp(argv[1], "-") == 0;
        const char *dest = change_to_previous ? shell_previous_dir
            : (argc > 1 ? argv[1] : shell_get_variable("HOME"));
        char old_path[PATH_MAX] = "";
        (void)shell_fd_path(shell_cwd_fd, old_path, sizeof(old_path));
        int next_cwd = dest != NULL && shell_cwd_fd >= 0
            ? openat(shell_cwd_fd, dest, O_RDONLY | O_DIRECTORY)
            : (dest != NULL ? open(dest, O_RDONLY | O_DIRECTORY) : -1);
        if (next_cwd < 0) { perror("cd"); status = 1; }
        else
        {
            if (old_path[0] != '\0') snprintf(shell_previous_dir, sizeof(shell_previous_dir), "%s", old_path);
            if (change_to_previous) dprintf(1, "%s\n", dest);
            if (shell_cwd_fd >= 0) close(shell_cwd_fd);
            shell_cwd_fd = next_cwd;
        }
    }
    else if (strcmp(argv[0], "exit") == 0)
    {
        shell_should_exit = 1;
        if (argc > 1) status = atoi(argv[1]) & 255;
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
            shell_set_foreground_pgid(job_pid);
            pid_t waited;
            do { waited = waitpid(job_pid, &child_status, WUNTRACED); }
            while (waited < 0 && errno == EINTR);
            shell_set_foreground_pgid(0);
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
        if (argc < 2)
        {
            dprintf(2, "terminator: source: not implemented yet\nusage: source file\n");
            status = 2;
        }
        else
        {
            status = shell_run_script(argv[1], argc - 1, argv + 1, depth + 1);
        }
    }
    else if (strcmp(argv[0], "bash") == 0 && argc >= 2)
        status = shell_run_script(argv[1], argc - 2, argv + 2, depth + 1);
    else if (argv[0][0] == '.' && argv[0][1] == '/' && strstr(argv[0], ".sh") != NULL)
        status = shell_run_script(argv[0], argc - 1, argv + 1, depth + 1);
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
        status = shell_run_external(argv, argc, line, background, &redirs);
    }
    shell_restore_redirections(saved_fds);
    free(redirs.input_path); free(redirs.output_path); free(redirs.error_path);
    shell_last_status = status;
    shell_free_argv(argv, argc);
    free(expanded);
    return status;
}

static int shell_worker(int input_fd, int output_fd, int in_thread)
{
    shell_io_active = 1;
    shell_input_fd = input_fd;
    shell_output_fd = output_fd;
    shell_error_fd = output_fd;
    shell_cwd_fd = open(".", O_RDONLY | O_DIRECTORY);
    (void)signal(SIGINT, shell_sigint_handler);
    (void)signal(SIGTSTP, shell_sigtstp_handler);
    (void)signal(SIGTERM, shell_sigterm_handler);
    FILE *input_stream = fdopen(input_fd, "r");
    if (input_stream == NULL)
    {
        perror("fdopen shell input");
        if (shell_cwd_fd >= 0) close(shell_cwd_fd);
        if (in_thread && output_fd >= 0) close(output_fd);
        if (in_thread) return 1;
        _exit(1);
    }
    char *command = NULL, *marker = NULL;
    size_t command_capacity = 0, marker_capacity = 0;
    while (!shell_should_exit)
    {
        ssize_t command_length = getline(&command, &command_capacity, input_stream);
        if (command_length < 0) break;
        ssize_t marker_length = getline(&marker, &marker_capacity, input_stream);
        if (marker_length < 0) break;
        while (command_length > 0 && (command[command_length - 1] == '\n' || command[command_length - 1] == '\r')) command[--command_length] = '\0';
        while (marker_length > 0 && (marker[marker_length - 1] == '\n' || marker[marker_length - 1] == '\r')) marker[--marker_length] = '\0';
        for (ssize_t i = 0; i < command_length; i++)
            if (command[i] == '\x1e') command[i] = '\n';
        (void)shell_run_line(command, 1, 0);
        dprintf(STDOUT_FILENO, "%s", marker);
    }
    free(command); free(marker);
    for (int i = 0; i < SHELL_JOB_LIMIT; i++)
    {
        if (!shell_jobs[i].active) continue;
        (void)kill(-shell_jobs[i].pid, SIGTERM);
        (void)kill(-shell_jobs[i].pid, SIGCONT);
        while (waitpid(shell_jobs[i].pid, NULL, 0) < 0 && errno == EINTR) {}
    }
    if (shell_cwd_fd >= 0) close(shell_cwd_fd);
    if (in_thread)
    {
        fclose(input_stream);
        if (output_fd >= 0) close(output_fd);
        return shell_last_status;
    }
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
    int input_fd;
    int output_fd;
    pthread_t thread;
    int started;
    _Atomic pid_t foreground_pgid;
} ThreadControl;

typedef struct ShellProcess
{
    pid_t pid;
    int input_fd;
    int output_fd;
    int is_thread;
    int thread_control_shared;
    ThreadControl *thread_control;
    unsigned long command_id;

    char marker[96];
    size_t marker_length;
    char marker_pending[96];
    size_t marker_pending_length;

    int command_running;
    int alive;
} ShellProcess;

static void *shell_thread_main(void *argument)
{
    ThreadControl *control = argument;
    shell_foreground_slot = &control->foreground_pgid;
    (void)shell_worker(control->input_fd, control->output_fd, 1);
    return NULL;
}

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
    int search_active;
    size_t search_length;
    char search_query[INPUT_CAPACITY];
    char search_match[INPUT_CAPACITY];
    size_t search_match_index;
    int search_match_found;
    char cwd_path[PATH_MAX];
    char previous_cwd_path[PATH_MAX];
    char completion_candidates[128][NAME_MAX + 1];
    size_t completion_count;
    size_t completion_word_start;
    size_t completion_word_end;
    char completion_prefix[NAME_MAX + 1];
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
    shell->thread_control = NULL;
    shell->is_thread = !use_process_mode;
    shell->thread_control_shared = 0;
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

    if (!use_process_mode)
    {
        shell->thread_control = calloc(1, sizeof(*shell->thread_control));
        if (shell->thread_control == NULL)
        {
            close_if_open(&to_shell[0]); close_if_open(&to_shell[1]);
            close_if_open(&from_shell[0]); close_if_open(&from_shell[1]);
            return 0;
        }
        shell->thread_control->input_fd = to_shell[0];
        shell->thread_control->output_fd = from_shell[1];
        atomic_init(&shell->thread_control->foreground_pgid, 0);
        shell->input_fd = to_shell[1];
        shell->output_fd = from_shell[0];
        shell->alive = 1;
        int error = pthread_create(&shell->thread_control->thread, NULL, shell_thread_main,
                                   shell->thread_control);
        if (error != 0)
        {
            errno = error;
            perror("pthread_create shell thread");
            close_if_open(&to_shell[0]); close_if_open(&to_shell[1]);
            close_if_open(&from_shell[0]); close_if_open(&from_shell[1]);
            shell->input_fd = shell->output_fd = -1;
            shell->alive = 0;
            free(shell->thread_control);
            shell->thread_control = NULL;
            return 0;
        }
        shell->thread_control->started = 1;
        /* File descriptors are process-wide in thread mode, so the worker
           owns the read/write ends and closes them when it exits. */
        return 1;
    }

    shell->thread_control = mmap(NULL, sizeof(*shell->thread_control),
                                 PROT_READ | PROT_WRITE,
                                 MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shell->thread_control == MAP_FAILED)
    {
        shell->thread_control = NULL;
        close_if_open(&to_shell[0]); close_if_open(&to_shell[1]);
        close_if_open(&from_shell[0]); close_if_open(&from_shell[1]);
        return 0;
    }
    memset(shell->thread_control, 0, sizeof(*shell->thread_control));
    atomic_init(&shell->thread_control->foreground_pgid, 0);
    shell->thread_control_shared = 1;

    pid_t child = fork();
    if (child == -1)
    {
        perror("fork");
        close_if_open(&to_shell[0]);
        close_if_open(&to_shell[1]);
        close_if_open(&from_shell[0]);
        close_if_open(&from_shell[1]);
        munmap(shell->thread_control, sizeof(*shell->thread_control));
        shell->thread_control = NULL;
        return 0;
    }

    if (child == 0)
    {
        shell_foreground_slot = &shell->thread_control->foreground_pgid;
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
        (void)shell_worker(STDIN_FILENO, STDOUT_FILENO, 0);
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

    if (shell->is_thread && shell->thread_control != NULL &&
        shell->thread_control->started)
    {
        pid_t foreground = shell->thread_control != NULL
            ? atomic_load_explicit(&shell->thread_control->foreground_pgid, memory_order_relaxed) : 0;
        if (foreground > 0) (void)kill(-foreground, SIGTERM);
        close_if_open(&shell->input_fd);
        close_if_open(&shell->output_fd);
        (void)pthread_join(shell->thread_control->thread, NULL);
        shell->thread_control->started = 0;
        free(shell->thread_control);
        shell->thread_control = NULL;
        shell->alive = 0;
        shell->command_running = 0;
        return;
    }
    if (shell->is_thread)
    {
        close_if_open(&shell->input_fd);
        close_if_open(&shell->output_fd);
        shell->alive = 0;
        shell->command_running = 0;
        return;
    }

    if (pid > 0)
    {
        // Stop Bash and commands in its process group.
        (void)kill(-pid, SIGTERM);
        pid_t foreground = shell->thread_control != NULL
            ? atomic_load_explicit(&shell->thread_control->foreground_pgid, memory_order_relaxed) : 0;
        if (foreground > 0) (void)kill(-foreground, SIGTERM);
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

    if (shell->thread_control_shared && shell->thread_control != NULL)
    {
        munmap(shell->thread_control, sizeof(*shell->thread_control));
        shell->thread_control = NULL;
        shell->thread_control_shared = 0;
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
    if (getcwd(tab->cwd_path, sizeof(tab->cwd_path)) == NULL)
        snprintf(tab->cwd_path, sizeof(tab->cwd_path), "/");

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

static void tab_track_cd(Tab *tab, const char *command)
{
    char copy[INPUT_CAPACITY]; snprintf(copy,sizeof(copy),"%s",command);
    char *args[8]; int argc=shell_tokenize(copy,args,8);
    if (argc > 0 && strcmp(args[0],"cd")==0)
    {
        int to_previous = argc > 1 && strcmp(args[1], "-") == 0;
        const char *target = to_previous ? tab->previous_cwd_path
            : (argc > 1 ? args[1] : getenv("HOME"));
        if (target != NULL)
        {
            char candidate[PATH_MAX], resolved[PATH_MAX];
            size_t target_len = strlen(target);
            if (target[0] == '/')
            {
                if (target_len >= sizeof(candidate)) { shell_free_argv(args,argc); return; }
                memcpy(candidate, target, target_len + 1);
            }
            else
            {
                size_t cwd_len = strlen(tab->cwd_path);
                if (cwd_len + 1 + target_len >= sizeof(candidate))
                { shell_free_argv(args,argc); return; }
                memcpy(candidate, tab->cwd_path, cwd_len);
                candidate[cwd_len] = '/';
                memcpy(candidate + cwd_len + 1, target, target_len + 1);
            }
            struct stat st;
            if (realpath(candidate,resolved)!=NULL && stat(resolved,&st)==0 && S_ISDIR(st.st_mode))
            {
                snprintf(tab->previous_cwd_path,sizeof(tab->previous_cwd_path),"%s",tab->cwd_path);
                snprintf(tab->cwd_path,sizeof(tab->cwd_path),"%s",resolved);
            }
        }
    }
    shell_free_argv(args,argc);
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

static void draw_input_segment(Display *display, Window window, GC gc,
                               XFontStruct *font, Tab *tab, int x, int *y,
                               int window_width, size_t start, size_t end,
                               size_t *logical_row, const char *prompt)
{
    size_t length = end - start, offset = 0;
    do
    {
        const char *prefix = *logical_row == 0 ? prompt : (offset == 0 ? "> " : "  ");
        int prefix_width = XTextWidth(font, prefix, (int)strlen(prefix));
        int room = window_width - x - prefix_width - 12;
        int char_width = font->max_bounds.width > 0 ? font->max_bounds.width : 8;
        size_t cols = room > char_width ? (size_t)(room / char_width) : 1;
        size_t chunk = length - offset;
        if (chunk > cols) chunk = cols;
        size_t chunk_start = start + offset, chunk_end = chunk_start + chunk;
        XDrawString(display, window, gc, x, *y, prefix, (int)strlen(prefix));
        if (chunk > 0)
            XDrawString(display, window, gc, x + prefix_width, *y,
                        tab->input + chunk_start, (int)chunk);

        if (tab->selection_active)
        {
            size_t sel_start = tab->selection_anchor < tab->cursor_position
                ? tab->selection_anchor : tab->cursor_position;
            size_t sel_end = tab->selection_anchor > tab->cursor_position
                ? tab->selection_anchor : tab->cursor_position;
            size_t from = sel_start > chunk_start ? sel_start : chunk_start;
            size_t to = sel_end < chunk_end ? sel_end : chunk_end;
            if (to > from)
            {
                int before = XTextWidth(font, tab->input + chunk_start, (int)(from - chunk_start));
                int selected = XTextWidth(font, tab->input + from, (int)(to - from));
                int sx = x + prefix_width + before;
                XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
                XFillRectangle(display, window, gc, sx, *y - font->ascent,
                               (unsigned int)selected,
                               (unsigned int)(font->ascent + font->descent + 2));
                XSetForeground(display, gc, WhitePixel(display, DefaultScreen(display)));
                XDrawString(display, window, gc, sx, *y, tab->input + from, (int)(to - from));
                XSetForeground(display, gc, BlackPixel(display, DefaultScreen(display)));
            }
        }
        int final_chunk = offset + chunk >= length;
        if (tab->cursor_position >= chunk_start &&
            (tab->cursor_position < chunk_end ||
             (final_chunk && tab->cursor_position == chunk_end)))
        {
            size_t before = tab->cursor_position - chunk_start;
            int cx = x + prefix_width + XTextWidth(font, tab->input + chunk_start, (int)before);
            XDrawLine(display, window, gc, cx, *y - font->ascent, cx, *y + 2);
        }
        *y += LINE_HEIGHT;
        (*logical_row)++;
        offset += chunk;
    } while (offset < length);
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

    int char_width = font->max_bounds.width > 0 ? font->max_bounds.width : 8;
    int text_area_width = window_width - x - 12;
    size_t wrap_cols = text_area_width > char_width
        ? (size_t)(text_area_width / char_width) : 1;
    size_t history_lines = 0;
    size_t logical_start = 0;
    for (size_t i = 0; i <= tab->history.length; i++)
        if (i == tab->history.length || tab->history.data[i] == '\n')
        {
            size_t length = i - logical_start;
            history_lines += length ? (length + wrap_cols - 1) / wrap_cols : 1;
            logical_start = i + 1;
        }

    int available_height = window_height - TERMINAL_TOP - 10;
    int visible_rows_int = available_height / LINE_HEIGHT;
    if (visible_rows_int < 1)
    {
        visible_rows_int = 1;
    }
    size_t rows = (size_t)visible_rows_int;
    size_t input_lines = 0, input_start_for_count = 0;
    for (size_t i = 0; i <= tab->input_length; i++)
        if (i == tab->input_length || tab->input[i] == '\n')
        {
            const char *prefix = input_lines == 0 ? prompt : "> ";
            int room = window_width - x - XTextWidth(font, prefix, (int)strlen(prefix)) - 12;
            size_t cols = room > char_width ? (size_t)(room / char_width) : 1;
            size_t len = i - input_start_for_count;
            input_lines += len ? (len + cols - 1) / cols : 1;
            input_start_for_count = i + 1;
        }
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

    for (size_t i = 0; i <= tab->history.length; i++)
        if (i == tab->history.length || tab->history.data[i] == '\n')
        {
            size_t length = i - start;
            size_t offset = 0;
            do {
                size_t chunk = length - offset;
                if (chunk > wrap_cols) chunk = wrap_cols;
                if (line_number >= first_line && line_number < end_line && y < window_height - 2)
                {
                    if (chunk) XDrawString(display, window, gc, x, y,
                        tab->history.data + start + offset, (int)chunk);
                    y += LINE_HEIGHT;
                }
                line_number++; offset += chunk;
            } while (offset < length);
            start = i + 1;
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
        else if (tab->search_active)
        {
            const char *label = "Enter search term: ";
            XDrawString(display, window, gc, x, y, label, (int)strlen(label));
            int offset = XTextWidth(font, label, (int)strlen(label));
            XDrawString(display, window, gc, x + offset, y,
                        tab->search_query, (int)tab->search_length);
            offset += XTextWidth(font, tab->search_query, (int)tab->search_length);
            const char *middle = "  ";
            XDrawString(display, window, gc, x + offset, y, middle, (int)strlen(middle));
            offset += XTextWidth(font, middle, (int)strlen(middle));
            const char *result = tab->search_match_found ? tab->search_match : "";
            XDrawString(display, window, gc, x + offset, y, result, (int)strlen(result));
            y += LINE_HEIGHT;
        }
        else
        {
            size_t input_start = 0;
            size_t input_row = 0;
            for (size_t i = 0; i <= tab->input_length; i++)
            {
                if (i == tab->input_length || tab->input[i] == '\n')
                {
                    draw_input_segment(display, window, gc, font, tab, x, &y,
                                       window_width, input_start, i, &input_row, prompt);
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

static int history_similarity_score(const char *query, const char *candidate)
{
    if (strcmp(query, candidate) == 0) return INT_MAX;
    size_t a=strlen(query), b=strlen(candidate), best=0;
    for(size_t i=0;i<a;i++) for(size_t j=0;j<b;j++)
    { size_t n=0; while(i+n<a && j+n<b && query[i+n]==candidate[j+n]) n++; if(n>best) best=n; }
    return best>2 ? (int)best : 0;
}

static int tab_search_history(Tab *tab, int older)
{
    if (shared_command_history == NULL) return 0;
    while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
    size_t count = shared_command_history->count;
    size_t last = count == 0 ? 0 : count - 1;
    if (older && tab->search_match_found)
    {
        if (tab->search_match_index == 0) last = 0;
        else last = tab->search_match_index - 1;
    }
    int found = 0;
    int best_score = 0;
    size_t best_index = 0;
    if (count > 0 && !(older && tab->search_match_found && tab->search_match_index == 0))
    {
        for (size_t i = last + 1; i > 0; i--)
        {
            size_t index = i - 1;
            int score = history_similarity_score(tab->search_query,
                                                  shared_command_history->entries[index]);
            if (score > best_score)
            {
                best_score = score;
                best_index = index;
                found = 1;
            }
        }
    }
    tab->search_match_found = found;
    if (found)
    {
        tab->search_match_index = best_index;
        snprintf(tab->search_match, sizeof(tab->search_match), "%s",
                 shared_command_history->entries[best_index]);
    }
    else
    {
        tab->search_match[0] = '\0';
    }
    (void)sem_post(&shared_command_history->lock);
    return found;
}

static void tab_search_begin(Tab *tab)
{
    memcpy(tab->history_draft, tab->input, tab->input_length + 1);
    tab->selection_active = 0;
    tab->search_active = 1;
    tab->search_length = 0;
    tab->search_query[0] = '\0';
    tab->search_match_found = 0;
    (void)tab_search_history(tab, 0);
}

static void tab_search_cancel(Tab *tab)
{
    tab->search_active = 0;
    tab->selection_active = 0;
    tab_replace_input(tab, tab->history_draft);
    tab->history_position = SIZE_MAX;
}

static void tab_search_accept(Tab *tab)
{
    if (tab->search_match_found && shared_command_history != NULL)
    {
        while (sem_wait(&shared_command_history->lock) == -1 && errno == EINTR) {}
        int best=0; size_t exact_index=SIZE_MAX;
        for(size_t i=0;i<shared_command_history->count;i++)
        {
            int score=history_similarity_score(tab->search_query,shared_command_history->entries[i]);
            if(score==INT_MAX) exact_index=i;
            else if(score>best) best=score;
        }
        (void)text_buffer_append(&tab->history,"\n");
        if(exact_index!=SIZE_MAX)
        {
            (void)text_buffer_append(&tab->history,shared_command_history->entries[exact_index]);
            (void)text_buffer_append(&tab->history,"\n");
        }
        else for (size_t cursor = shared_command_history->count; cursor > 0; cursor--)
        {
            size_t i = cursor - 1;
            const char *candidate = shared_command_history->entries[i];
            if (history_similarity_score(tab->search_query, candidate) != best) continue;
            int duplicate = 0;
            for (size_t newer = i + 1; newer < shared_command_history->count; newer++)
                if (strcmp(candidate, shared_command_history->entries[newer]) == 0 &&
                    history_similarity_score(tab->search_query, shared_command_history->entries[newer]) == best)
                { duplicate = 1; break; }
            if (!duplicate)
            {
                (void)text_buffer_append(&tab->history, candidate);
                (void)text_buffer_append(&tab->history, "\n");
            }
        }
        (void)sem_post(&shared_command_history->lock);
    }
    else
    {
        char message[INPUT_CAPACITY + 64];
        snprintf(message,sizeof(message),"\nNo match for search term in history.\n");
        (void)text_buffer_append(&tab->history,message);
    }
    tab->input_length=0; tab->input[0]='\0'; tab->cursor_position=0; tab->scroll_offset=0;
    tab->search_active = 0;
    tab->selection_active = 0;
    tab->history_position = SIZE_MAX;
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

static int tab_complete_filename(Tab *tab)
{
    size_t start = tab->cursor_position;
    while (start > 0 && !isspace((unsigned char)tab->input[start - 1])) start--;
    size_t token_len = tab->cursor_position - start;
    char token[INPUT_CAPACITY];
    if (token_len >= sizeof(token)) return 0;
    memcpy(token, tab->input + start, token_len); token[token_len] = '\0';
    char *slash = strrchr(token, '/');
    const char *base = slash ? slash + 1 : token;
    char dirpath[PATH_MAX];
    if (slash)
    {
        size_t dlen = (size_t)(slash - token);
        char rel[INPUT_CAPACITY]; memcpy(rel, token, dlen); rel[dlen] = '\0';
        if (rel[0] == '/')
        {
            size_t rel_length = strlen(rel);
            if (rel_length >= sizeof(dirpath)) return 0;
            memcpy(dirpath, rel, rel_length + 1);
        }
        else
        {
            const char *relative = rel[0] ? rel : ".";
            size_t cwd_length = strlen(tab->cwd_path), rel_length = strlen(relative);
            if (cwd_length + 1 + rel_length >= sizeof(dirpath)) return 0;
            memcpy(dirpath, tab->cwd_path, cwd_length);
            dirpath[cwd_length] = '/';
            memcpy(dirpath + cwd_length + 1, relative, rel_length + 1);
        }
    }
    else
    {
        size_t cwd_length = strlen(tab->cwd_path);
        if (cwd_length >= sizeof(dirpath)) return 0;
        memcpy(dirpath, tab->cwd_path, cwd_length + 1);
    }
    DIR *dir = opendir(dirpath); if (!dir) return 0;
    tab->completion_count = 0;
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL && tab->completion_count < 128)
    {
        if (strncmp(entry->d_name, base, strlen(base)) == 0)
            snprintf(tab->completion_candidates[tab->completion_count++], NAME_MAX + 1, "%s", entry->d_name);
    }
    closedir(dir);
    if (!tab->completion_count) return 0;
    char replacement[INPUT_CAPACITY];
    size_t slash_len = slash ? (size_t)(slash - token) + 1 : 0;
    if (tab->completion_count == 1)
    {
        snprintf(replacement, sizeof(replacement), "%.*s%s",
                 (int)slash_len, token, tab->completion_candidates[0]);
        size_t old = token_len, newlen = strlen(replacement);
        if (newlen > old && tab->input_length + newlen - old >= sizeof(tab->input)) return 0;
        memmove(tab->input + start + newlen, tab->input + tab->cursor_position,
                tab->input_length - tab->cursor_position + 1);
        memcpy(tab->input + start, replacement, newlen);
        tab->input_length = tab->input_length - old + newlen;
        tab->cursor_position = start + newlen; tab->completion_count = 0; return 1;
    }
    size_t common = strlen(tab->completion_candidates[0]);
    for (size_t i=1; i<tab->completion_count; i++)
    {
        size_t j=0; while (j<common && tab->completion_candidates[i][j] == tab->completion_candidates[0][j]) j++;
        common=j;
    }
    if (common > strlen(base))
    {
        snprintf(replacement, sizeof(replacement), "%.*s%.*s", (int)slash_len, token,
                 (int)common, tab->completion_candidates[0]);
        size_t old=token_len, newlen=strlen(replacement);
        if (tab->input_length + newlen - old >= sizeof(tab->input)) return 0;
        memmove(tab->input+start+newlen,tab->input+tab->cursor_position,tab->input_length-tab->cursor_position+1);
        memcpy(tab->input+start,replacement,newlen); tab->input_length=tab->input_length-old+newlen;
        tab->cursor_position=start+newlen;
    }
    tab->completion_word_start=start; tab->completion_word_end=tab->cursor_position;
    snprintf(tab->completion_prefix,sizeof(tab->completion_prefix),"%.*s",(int)slash_len,token);
    (void)text_buffer_append(&tab->history,"\n");
    for(size_t i=0;i<tab->completion_count;i++)
    {
        char item[NAME_MAX+32]; snprintf(item,sizeof(item),"%zu. %s\n",i+1,tab->completion_candidates[i]);
        (void)text_buffer_append(&tab->history,item);
    }
    tab->scroll_offset=0; return 1;
}

static int tab_choose_completion(Tab *tab, unsigned int digit)
{
    if (!tab->completion_count || digit == 0 || digit > tab->completion_count) return 0;
    char replacement[INPUT_CAPACITY];
    snprintf(replacement,sizeof(replacement),"%s%s",tab->completion_prefix,
             tab->completion_candidates[digit-1]);
    size_t start=tab->completion_word_start, old=tab->completion_word_end-start, n=strlen(replacement);
    if(tab->input_length-old+n>=sizeof(tab->input)) {tab->completion_count=0;return 0;}
    memmove(tab->input+start+n,tab->input+tab->completion_word_end,tab->input_length-tab->completion_word_end+1);
    memcpy(tab->input+start,replacement,n); tab->input_length=tab->input_length-old+n;
    tab->cursor_position=start+n; tab->completion_count=0; return 1;
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

    if (control && (key == XK_t || key == XK_T))
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

int main(int argc, char **argv)
{
    if (argc > 2 || (argc == 2 && strcmp(argv[1], "useProcess=True") != 0))
    {
        fprintf(stderr, "Usage: %s [useProcess=True]\n", argv[0]);
        return 2;
    }
    use_process_mode = argc == 2;

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
    history_load_file();

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
    XStoreName(display, window, use_process_mode
        ? "Terminator - Task 11 (Process mode)"
        : "Terminator - Task 11 (Thread mode)");

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

                if (key == XK_Escape && tabs[active_tab].search_active)
                {
                    tab_search_cancel(&tabs[active_tab]);
                    request_redraw(display, window);
                    continue;
                }

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

                if (!tab->shell.command_running && tab->shell.alive &&
                    (event.xkey.state & ControlMask) && (key == XK_r || key == XK_R))
                {
                    if (tab->search_active)
                        (void)tab_search_history(tab, 1);
                    else
                        tab_search_begin(tab);
                    request_redraw(display, window);
                    continue;
                }
                if (tab->search_active && !tab->shell.command_running && tab->shell.alive)
                {
                    if (key == XK_Return || key == XK_KP_Enter)
                    {
                        tab_search_accept(tab);
                    }
                    else if (key == key_settings.backspace)
                    {
                        if (tab->search_length > 0)
                        {
                            tab->search_query[--tab->search_length] = '\0';
                            tab->search_match_found = 0;
                            (void)tab_search_history(tab, 0);
                        }
                        request_redraw(display, window);
                        continue;
                    }
                    else
                    {
                        for (int i = 0; i < n &&
                             tab->search_length < sizeof(tab->search_query) - 1; i++)
                        {
                            unsigned char ch = (unsigned char)key_buffer[i];
                            if (ch >= 32 && ch != 127 && !(event.xkey.state & ControlMask))
                            {
                                tab->search_query[tab->search_length++] = (char)ch;
                                tab->search_query[tab->search_length] = '\0';
                                tab->search_match_found = 0;
                            }
                        }
                        (void)tab_search_history(tab, 0);
                        request_redraw(display, window);
                        continue;
                    }
                }

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
                    if (tab->shell.is_thread)
                    {
                        if (tab->shell.thread_control != NULL)
                            (void)pthread_kill(tab->shell.thread_control->thread, SIGINT);
                    }
                    else if (tab->shell.pid > 0)
                        (void)kill(-tab->shell.pid, SIGINT);
                    changed = 1;
                }
                else if (tab->shell.command_running &&
                    (event.xkey.state & ControlMask) && (key == XK_z || key == XK_Z))
                {
                    if (tab->shell.is_thread)
                    {
                        if (tab->shell.thread_control != NULL)
                            (void)pthread_kill(tab->shell.thread_control->thread, SIGTSTP);
                    }
                    else if (tab->shell.pid > 0)
                        (void)kill(-tab->shell.pid, SIGTSTP);
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
                else if (tab->completion_count && key >= XK_1 && key <= XK_9)
                {
                    changed = tab_choose_completion(tab, (unsigned int)(key - XK_0));
                }
                else if (key == XK_Tab)
                {
                    changed = tab_complete_filename(tab);
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
                            tab_track_cd(tab, tab->input);
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
