/-
  Copyright 2012-2024 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Shell variable definitions and metadata for ShellCheck
-/

namespace ShellCheck.Data

/-- Version string for ShellCheck -/
def shellcheckVersion : String := "0.10.0-lean4"

/-- Shell types supported by ShellCheck -/
inductive Shell where
  | Ksh
  | Sh
  | Bash
  | Dash
  | BusyboxSh
  deriving Repr, BEq, Inhabited

/-- Internal shell variables recognized by ShellCheck -/
def internalVariables : List String := [
  -- Generic
  "", "_", "rest", "REST",
  -- POSIX
  "CDPATH", "ENV", "FCEDIT", "HISTFILE", "HISTSIZE", "HOME", "IFS", "LANG",
  "LC_ALL", "LC_COLLATE", "LC_CTYPE", "LC_MESSAGES", "LC_MONETARY",
  "LC_NUMERIC", "LC_TIME", "MAIL", "MAILCHECK", "MAILPATH", "OLDPWD",
  "OPTARG", "OPTIND", "PATH", "PWD",
  -- Bash
  "BASH", "BASHOPTS", "BASHPID", "BASH_ALIASES", "BASH_ARGC",
  "BASH_ARGV", "BASH_ARGV0", "BASH_CMDS", "BASH_COMMAND",
  "BASH_EXECUTION_STRING", "BASH_LINENO", "BASH_LOADABLES_PATH",
  "BASH_REMATCH", "BASH_SOURCE", "BASH_SUBSHELL", "BASH_VERSINFO",
  "BASH_VERSION", "COMP_CWORD", "COMP_KEY", "COMP_LINE", "COMP_POINT",
  "COMP_TYPE", "COMP_WORDBREAKS", "COMP_WORDS", "COPROC", "DIRSTACK",
  "EPOCHREALTIME", "EPOCHSECONDS", "EUID", "FUNCNAME", "GROUPS", "HISTCMD",
  "HOSTNAME", "HOSTTYPE", "MACHTYPE", "MAPFILE", "OSTYPE", "PIPESTATUS",
  "RANDOM", "READLINE_ARGUMENT", "READLINE_LINE", "READLINE_MARK",
  "READLINE_POINT", "REPLY", "SECONDS", "SHELLOPTS", "SHLVL", "SRANDOM",
  "UID", "BASH_COMPAT", "BASH_ENV", "BASH_XTRACEFD", "CHILD_MAX", "COLUMNS",
  "COMPREPLY", "EMACS", "EXECIGNORE", "FIGNORE", "FUNCNEST", "GLOBIGNORE",
  "HISTCONTROL", "HISTFILESIZE", "HISTIGNORE", "HISTTIMEFORMAT", "HOSTFILE",
  "IGNOREEOF", "INPUTRC", "INSIDE_EMACS", "LINES", "OPTERR",
  "POSIXLY_CORRECT", "PROMPT_COMMAND", "PROMPT_DIRTRIM", "PS0", "PS1", "PS2",
  "PS3", "PS4", "SHELL", "TIMEFORMAT", "TMOUT", "BASH_MONOSECONDS",
  "BASH_TRAPSIG", "GLOBSORT", "auto_resume", "histchars",
  -- Other
  "USER", "TZ", "TERM", "LOGNAME", "LD_LIBRARY_PATH", "LANGUAGE", "DISPLAY",
  "HOSTNAME", "KRB5CCNAME", "LINENO", "PPID", "TMPDIR", "XAUTHORITY",
  -- Ksh
  ".sh.version",
  -- shflags
  "FLAGS_ARGC", "FLAGS_ARGV", "FLAGS_ERROR", "FLAGS_FALSE", "FLAGS_HELP",
  "FLAGS_PARENT", "FLAGS_RESERVED", "FLAGS_TRUE", "FLAGS_VERSION",
  "flags_error", "flags_return",
  -- Bats
  "stderr", "stderr_lines"
]

def specialIntegerVariables : List String := ["$", "?", "!", "#"]

def specialVariablesWithoutSpaces : List String :=
  "-" :: specialIntegerVariables

def variablesWithoutSpaces : List String :=
  specialVariablesWithoutSpaces ++ [
    "BASHPID", "BASH_ARGC", "BASH_LINENO", "BASH_SUBSHELL", "EUID",
    "EPOCHREALTIME", "EPOCHSECONDS", "LINENO", "OPTIND", "PPID", "RANDOM",
    "READLINE_ARGUMENT", "READLINE_MARK", "READLINE_POINT", "SECONDS",
    "SHELLOPTS", "SHLVL", "SRANDOM", "UID", "COLUMNS", "HISTFILESIZE",
    "HISTSIZE", "LINES", "BASH_MONOSECONDS", "BASH_TRAPSIG",
    -- shflags
    "FLAGS_ERROR", "FLAGS_FALSE", "FLAGS_TRUE"
  ]

def specialVariables : List String :=
  specialVariablesWithoutSpaces ++ ["@", "*"]

def unbracedVariables : List String :=
  specialVariables ++ ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

def arrayVariables : List String := [
  "BASH_ALIASES", "BASH_ARGC", "BASH_ARGV", "BASH_CMDS", "BASH_LINENO",
  "BASH_REMATCH", "BASH_SOURCE", "BASH_VERSINFO", "COMP_WORDS", "COPROC",
  "DIRSTACK", "FUNCNAME", "GROUPS", "MAPFILE", "PIPESTATUS", "COMPREPLY"
]

def commonCommands : List String := [
  "admin", "alias", "ar", "asa", "at", "awk", "basename", "batch",
  "bc", "bg", "break", "c99", "cal", "cat", "cd", "cflow", "chgrp",
  "chmod", "chown", "cksum", "cmp", "colon", "comm", "command",
  "compress", "continue", "cp", "crontab", "csplit", "ctags", "cut",
  "cxref", "date", "dd", "delta", "df", "diff", "dirname", "dot",
  "du", "echo", "ed", "env", "eval", "ex", "exec", "exit", "expand",
  "export", "expr", "fc", "fg", "file", "find", "fold", "fuser",
  "gencat", "get", "getconf", "getopts", "gettext", "grep", "hash",
  "head", "iconv", "ipcrm", "ipcs", "jobs", "join", "kill", "lex",
  "link", "ln", "locale", "localedef", "logger", "logname", "lp",
  "ls", "m4", "mailx", "make", "man", "mesg", "mkdir", "mkfifo",
  "more", "msgfmt", "mv", "newgrp", "ngettext", "nice", "nl", "nm",
  "nohup", "od", "paste", "patch", "pathchk", "pax", "pr", "printf",
  "prs", "ps", "pwd", "read", "readlink", "readonly", "realpath",
  "renice", "return", "rm", "rmdel", "rmdir", "sact", "sccs", "sed",
  "set", "sh", "shift", "sleep", "sort", "split", "strings", "strip",
  "stty", "tabs", "tail", "talk", "tee", "test", "time", "timeout",
  "times", "touch", "tput", "tr", "trap", "tsort", "tty", "type",
  "ulimit", "umask", "unalias", "uname", "uncompress", "unexpand",
  "unget", "uniq", "unlink", "unset", "uucp", "uudecode", "uuencode",
  "uustat", "uux", "val", "vi", "wait", "wc", "what", "who", "write",
  "xargs", "xgettext", "yacc", "zcat"
]

def nonReadingCommands : List String := [
  "alias", "basename", "bg", "cal", "cd", "chgrp", "chmod", "chown",
  "cp", "du", "echo", "export", "fg", "fuser", "getconf",
  "getopt", "getopts", "ipcrm", "ipcs", "jobs", "kill", "ln", "ls",
  "locale", "mv", "printf", "ps", "pwd", "readlink", "realpath",
  "renice", "rm", "rmdir", "set", "sleep", "touch", "trap", "ulimit",
  "unalias", "uname"
]

def sampleWords : List String := [
  "alpha", "bravo", "charlie", "delta", "echo", "foxtrot",
  "golf", "hotel", "india", "juliett", "kilo", "lima", "mike",
  "november", "oscar", "papa", "quebec", "romeo", "sierra",
  "tango", "uniform", "victor", "whiskey", "xray", "yankee", "zulu"
]

def binaryTestOps : List String := [
  "-nt", "-ot", "-ef", "==", "!=", "<=", ">=", "-eq", "-ne", "-lt", "-le",
  "-gt", "-ge", "=~", ">", "<", "=", "\\<", "\\>", "\\<=", "\\>="
]

def arithmeticBinaryTestOps : List String := ["-eq", "-ne", "-lt", "-le", "-gt", "-ge"]

def unaryTestOps : List String := [
  "!", "-a", "-b", "-c", "-d", "-e", "-f", "-g", "-h", "-L", "-k", "-p",
  "-r", "-s", "-S", "-t", "-u", "-w", "-x", "-O", "-G", "-N", "-z", "-n",
  "-o", "-v", "-R"
]

/-- Get the shell type for a given executable name -/
def shellForExecutable (name : String) : Option Shell :=
  match name with
  | "sh" => some .Sh
  | "bash" => some .Bash
  | "bats" => some .Bash
  | "busybox" => some .BusyboxSh
  | "busybox sh" => some .BusyboxSh
  | "busybox ash" => some .BusyboxSh
  | "dash" => some .Dash
  | "ash" => some .Dash
  | "ksh" => some .Ksh
  | "ksh88" => some .Ksh
  | "ksh93" => some .Ksh
  | "oksh" => some .Ksh
  | _ => none

def flagsForRead : String := "sreu:n:N:i:p:a:t:"
def flagsForMapfile : String := "d:n:O:s:u:C:c:t"

def declaringCommands : List String := ["local", "declare", "export", "readonly", "typeset", "let"]

-- Theorems
theorem shellForExecutable_bash : shellForExecutable "bash" = some Shell.Bash := rfl
theorem shellForExecutable_sh : shellForExecutable "sh" = some Shell.Sh := rfl

end ShellCheck.Data
