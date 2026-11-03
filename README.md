# GUI Component

Interactive X11 terminal GUI and C++ command engine.

## Build and run

Build from the `GUI/` directory:

```bash
g++ -std=c++17 -pthread main.cpp -o main -I/opt/X11/include -L/opt/X11/lib -lX11
./main
```

XQuartz must be running on macOS and `$DISPLAY` must be set. The default mode is
Process Mode. Select a mode with `./main --mode thread` or
`./main --mode process`.

## Command engine

The application does not start or send commands to `/bin/sh`. Each tab has its
own C++ command worker. The worker dispatches built-ins itself and starts the
C++ executor directly for external commands. The executor parses arguments,
opens redirection files, creates pipeline processes with `fork()`, connects
their file descriptors with `dup2()`, and starts programs with `execvp()`.
Output is collected asynchronously so command execution does not block the X11
event loop.

Implemented command features include simple external commands, quoted
arguments, environment-variable and home-directory expansion, wildcard
expansion, `<`, `>`, `>>`, multi-stage pipelines, and combinations such as
`cat < input.txt | sort > output.txt`. Missing input files are reported before
pipeline stages start. Built-ins include `cd`, `pwd`, `history`, `jobs`, `fg`,
`bg`, `clear`, and `exit`. The current parser is a project command language,
not a complete Bash-compatible interpreter.

Thread Mode uses one worker thread per tab. Process Mode uses one worker process
per tab. Thread Mode protects shared history with a pthread mutex. Process Mode
uses a shared-memory mapping and process-shared synchronization; it attempts
`shm_open()` and falls back to an anonymous shared mapping where the host
restricts POSIX shared-memory objects. Both modes retain up to 10,000 history
entries and save them across restarts.

`multiWatch` launches each command through the same C++ executor, runs them
concurrently, and displays output as it arrives. The SIGCHLD self-pipe keeps
child reaping out of the signal handler.

## Controls

- **Ctrl+C** sends `SIGINT` to the selected tab's foreground process group.
- **Ctrl+Z** sends `SIGTSTP` to that process group.
- **`jobs`, `fg %N`, `bg %N`, and `&`** use the tab worker's job table.
- **Ctrl+T** creates a tab; **Ctrl+Tab** switches tabs; **Ctrl+W** closes a tab.
- **Ctrl+R** searches shared command history.

The display remains a simple text view; it does not interpret full ANSI terminal
control sequences or provide a complete Bash language implementation.
