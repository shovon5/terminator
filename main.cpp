#if !defined(__APPLE__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

#include <iostream>
#include <algorithm>
#include <cstring>
#include <cstdio>
#include <string>

#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <cerrno>
#include <poll.h>
#include <fcntl.h>
#include <vector>
#include <cctype>
#include <fstream>
#include <sstream>
#include <dirent.h>
#include <sys/stat.h>
#include <cstdlib>
#include <atomic>
#include <thread>
#include <memory>
#include <pthread.h>
#include <sys/mman.h>
#include <cstdint>
#include <semaphore.h>
#include <glob.h>
#include <fnmatch.h>
#include <map>
#include <set>
#include <deque>
#include <chrono>
#include <ctime>

extern char **environ;

const int MAX_LINES = 26;
const int MAX_LINE_LENGTH = 1000;
const int MAX_SCREEN_LINE_LENGTH = MAX_LINE_LENGTH + 32;
const int MAX_TABS = 10;
const int MAX_HISTORY_COMMANDS = 10000;
const size_t MAX_WORKER_MESSAGE_LENGTH = 1024 * 1024;

const int WINDOW_WIDTH = 800;
const int WINDOW_HEIGHT = 600;
const int TAB_WIDTH = 100;
const int TAB_HEIGHT = 30;
const int CONTENT_START_Y = 55;
const int LINE_HEIGHT = 20;

enum class ExecutionMode
{
    Thread,
    Process
};

ExecutionMode executionMode = ExecutionMode::Thread;   // ./terminator  -> Thread Mode (default)
int xConnectionFd = -1;
int childSignalPipe[2] = {-1, -1};

// Highest descriptor number we bother closing in a freshly forked child.
// Computed once at startup because sysconf() is not async-signal-safe.
int maxDescriptorToClose = 1024;

void childSignalHandler(int)
{
    int savedErrno = errno;
    if (childSignalPipe[1] != -1)
    {
        const char byte = 1;
        (void)!write(childSignalPipe[1], &byte, 1);
    }
    errno = savedErrno;
}

bool setCloseOnExec(int fd)
{
    int flags = fcntl(fd, F_GETFD, 0);
    return flags != -1 && fcntl(fd, F_SETFD, flags | FD_CLOEXEC) != -1;
}

bool setNonBlocking(int fd)
{
    int flags = fcntl(fd, F_GETFL, 0);
    return flags != -1 && fcntl(fd, F_SETFL, flags | O_NONBLOCK) != -1;
}

// Every internal pipe is close-on-exec, so programs started with execvp()
// never inherit another tab's (or the GUI's) descriptors.
bool makePipe(int fds[2])
{
#if defined(__linux__)
    return pipe2(fds, O_CLOEXEC) == 0;
#else
    if (pipe(fds) == -1)
        return false;
    setCloseOnExec(fds[0]);
    setCloseOnExec(fds[1]);
    return true;
#endif
}

// Only async-signal-safe calls: used in children between fork() and exec.
void closeDescriptorsFrom(int first)
{
    for (int fd = first; fd < maxDescriptorToClose; ++fd)
        close(fd);
}

bool initializeChildSignalPipe()
{
    if (!makePipe(childSignalPipe))
        return false;
    for (int fd : childSignalPipe)
    {
        if (!setNonBlocking(fd))
        {
            close(childSignalPipe[0]);
            close(childSignalPipe[1]);
            childSignalPipe[0] = childSignalPipe[1] = -1;
            return false;
        }
    }

    struct sigaction action{};
    action.sa_handler = childSignalHandler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    if (sigaction(SIGCHLD, &action, nullptr) == -1)
    {
        close(childSignalPipe[0]);
        close(childSignalPipe[1]);
        childSignalPipe[0] = childSignalPipe[1] = -1;
        return false;
    }
    return true;
}

// Messages sent from the GUI to a tab's command engine.
enum WorkerMessageType : uint32_t
{
    WorkerCommand = 1,  // a complete command line to interpret
    WorkerInput = 2,    // bytes typed while a command is running (its stdin)
    WorkerStop = 3,     // the tab is closing
    WorkerSignal = 4,   // Ctrl+C / Ctrl+Z: payload is an int signal number
    WorkerEof = 5       // Ctrl+D while a command is running
};

// Messages sent from a tab's command engine back to the GUI.
enum EngineMessageType : uint32_t
{
    EngineText = 1,     // output to append to the tab
    EngineDone = 2,     // the command finished; show the prompt again
    EngineCwd = 3,      // the tab's working directory changed
    EngineClear = 4,    // clear the tab's screen
    EngineExit = 5      // the user typed "exit"; close the tab
};

struct WorkerMessageHeader
{
    uint32_t type;
    uint32_t length;
};

struct Hotkey
{
    unsigned int modifiers = 0;
    KeySym key = NoSymbol;
    std::string action;
};

std::vector<Hotkey> hotkeys;
std::string configPath;

struct SharedHistoryRegion
{
    sem_t processSemaphore;
    uint32_t start;
    uint32_t count;
    char entries[MAX_HISTORY_COMMANDS][MAX_LINE_LENGTH];
};

SharedHistoryRegion *sharedHistory = nullptr;
pthread_mutex_t threadHistoryMutex = PTHREAD_MUTEX_INITIALIZER;
sem_t *macProcessHistorySemaphore = SEM_FAILED;
std::string macProcessHistorySemaphoreName;

// In Thread Mode a tab thread may fork() a subshell while another thread
// holds the history mutex. These handlers make sure the child never starts
// with a mutex that is locked by a thread that does not exist in the child.
void historyAtForkPrepare() { pthread_mutex_lock(&threadHistoryMutex); }
void historyAtForkParent() { pthread_mutex_unlock(&threadHistoryMutex); }
void historyAtForkChild() { pthread_mutex_unlock(&threadHistoryMutex); }

bool lockSharedHistory()
{
    if (executionMode == ExecutionMode::Thread)
        return pthread_mutex_lock(&threadHistoryMutex) == 0;
    if (sharedHistory == nullptr)
        return false;
#if defined(__APPLE__)
    if (macProcessHistorySemaphore == SEM_FAILED)
        return false;
    while (sem_wait(macProcessHistorySemaphore) == -1)
#else
    while (sem_wait(&sharedHistory->processSemaphore) == -1)
#endif
    {
        if (errno != EINTR)
            return false;
    }
    return true;
}

void unlockSharedHistory()
{
    if (executionMode == ExecutionMode::Thread)
        pthread_mutex_unlock(&threadHistoryMutex);
    else if (sharedHistory != nullptr)
#if defined(__APPLE__)
    {
        if (macProcessHistorySemaphore != SEM_FAILED)
            sem_post(macProcessHistorySemaphore);
    }
#else
        sem_post(&sharedHistory->processSemaphore);
#endif
}

bool initializeSharedHistory()
{
    void *memory = mmap(nullptr, sizeof(SharedHistoryRegion),
                        PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON, -1, 0);
    if (memory == MAP_FAILED)
        return false;

    sharedHistory = static_cast<SharedHistoryRegion *>(memory);
    memset(sharedHistory, 0, sizeof(*sharedHistory));
    if (executionMode == ExecutionMode::Process)
    {
#if defined(__APPLE__)
        macProcessHistorySemaphoreName = "/x11_terminal_history_" +
                                         std::to_string(getpid());
        sem_unlink(macProcessHistorySemaphoreName.c_str());
        macProcessHistorySemaphore = sem_open(
            macProcessHistorySemaphoreName.c_str(), O_CREAT | O_EXCL, 0600, 1);
        if (macProcessHistorySemaphore == SEM_FAILED)
        {
            munmap(sharedHistory, sizeof(SharedHistoryRegion));
            sharedHistory = nullptr;
            return false;
        }
#else
        if (sem_init(&sharedHistory->processSemaphore, 1, 1) == -1)
        {
            munmap(sharedHistory, sizeof(SharedHistoryRegion));
            sharedHistory = nullptr;
            return false;
        }
#endif
    }
    else
    {
        pthread_atfork(historyAtForkPrepare, historyAtForkParent,
                       historyAtForkChild);
    }
    return true;
}

void destroySharedHistory()
{
    if (sharedHistory != nullptr)
    {
        if (executionMode == ExecutionMode::Process)
#if defined(__APPLE__)
        {
            if (macProcessHistorySemaphore != SEM_FAILED)
            {
                sem_close(macProcessHistorySemaphore);
                sem_unlink(macProcessHistorySemaphoreName.c_str());
                macProcessHistorySemaphore = SEM_FAILED;
            }
        }
#else
            sem_destroy(&sharedHistory->processSemaphore);
#endif
        munmap(sharedHistory, sizeof(SharedHistoryRegion));
        sharedHistory = nullptr;
    }
}

std::vector<std::string> historySnapshot()
{
    std::vector<std::string> result;
    if (sharedHistory == nullptr || !lockSharedHistory())
        return result;

    result.reserve(sharedHistory->count);
    for (uint32_t i = 0; i < sharedHistory->count; ++i)
    {
        uint32_t index = (sharedHistory->start + i) % MAX_HISTORY_COMMANDS;
        result.emplace_back(sharedHistory->entries[index]);
    }
    unlockSharedHistory();
    return result;
}

void clearSharedHistory()
{
    if (sharedHistory == nullptr || !lockSharedHistory())
        return;
    sharedHistory->start = 0;
    sharedHistory->count = 0;
    unlockSharedHistory();
}

bool appendSharedHistory(const std::string &command)
{
    if (command.empty() || sharedHistory == nullptr ||
        !lockSharedHistory())
        return false;

    if (sharedHistory->count > 0)
    {
        uint32_t last = (sharedHistory->start + sharedHistory->count - 1) %
                        MAX_HISTORY_COMMANDS;
        if (command == sharedHistory->entries[last])
        {
            unlockSharedHistory();
            return false;
        }
    }

    uint32_t index;
    if (sharedHistory->count < MAX_HISTORY_COMMANDS)
    {
        index = (sharedHistory->start + sharedHistory->count) %
                MAX_HISTORY_COMMANDS;
        ++sharedHistory->count;
    }
    else
    {
        index = sharedHistory->start;
        sharedHistory->start = (sharedHistory->start + 1) %
                               MAX_HISTORY_COMMANDS;
    }

    size_t length = std::min(command.size(),
                             static_cast<size_t>(MAX_LINE_LENGTH - 1));
    memcpy(sharedHistory->entries[index], command.data(), length);
    sharedHistory->entries[index][length] = '\0';
    unlockSharedHistory();
    return true;
}

std::string getHistoryFilePath()
{
    const char *home = getenv("HOME");
    return std::string(home && *home ? home : ".") + "/.terminator_history";
}

void loadCommandHistory()
{
    clearSharedHistory();

    std::ifstream file(getHistoryFilePath());
    std::string line;

    while (std::getline(file, line))
    {
        if (line.empty())
            continue;

        appendSharedHistory(line);
    }
}

// Called by tab engines (threads or processes). Writes to a private temporary
// file and renames it, so two tabs saving at once never interleave lines.
void saveCommandHistory()
{
    static std::atomic<unsigned> saveCounter{0};
    std::string path = getHistoryFilePath();
    std::string tempPath = path + ".tmp." + std::to_string(getpid()) + "." +
                           std::to_string(saveCounter.fetch_add(1));
    {
        std::ofstream file(tempPath, std::ios::trunc);
        if (!file)
            return;
        for (const std::string &command : historySnapshot())
            file << command << '\n';
        if (!file)
        {
            unlink(tempPath.c_str());
            return;
        }
    }
    if (rename(tempPath.c_str(), path.c_str()) != 0)
        unlink(tempPath.c_str());
}

bool writeAll(int fd, const char *data, size_t length)
{
    size_t totalWritten = 0;

    while (totalWritten < length)
    {
        ssize_t written = write(fd, data + totalWritten,
                                length - totalWritten);

        if (written == -1)
        {
            if (errno == EINTR)
                continue;
            if (errno == EAGAIN)
            {
                pollfd pfd{};
                pfd.fd = fd;
                pfd.events = POLLOUT;
                poll(&pfd, 1, 100);
                continue;
            }
            return false;
        }

        if (written == 0)
            return false;

        totalWritten += static_cast<size_t>(written);
    }

    return true;
}

bool readAll(int fd, void *buffer, size_t length)
{
    size_t totalRead = 0;
    char *destination = static_cast<char *>(buffer);
    while (totalRead < length)
    {
        ssize_t count = read(fd, destination + totalRead, length - totalRead);
        if (count == -1 && errno == EINTR)
            continue;
        if (count <= 0)
            return false;
        totalRead += static_cast<size_t>(count);
    }
    return true;
}

bool waitForChildExit(pid_t pid, int timeoutMilliseconds)
{
    if (pid <= 0)
        return true;
    int elapsed = 0;
    while (elapsed <= timeoutMilliseconds)
    {
        pid_t result = waitpid(pid, nullptr, WNOHANG);
        if (result == pid || (result == -1 && errno == ECHILD))
            return true;
        if (result == -1 && errno != EINTR)
            return false;
        poll(nullptr, 0, 10);
        elapsed += 10;
    }
    return false;
}
// ===========================================================================
//  Our own command language: lexer + parser (no /bin/sh involved)
//  Words: '...' "..." \  $VAR ${VAR} $(...) ~ globs
//  Operators: | ; & && || < > >> 2> 2>&1 &>   Blocks: if / while / until / for
// ===========================================================================

enum class TokenType { Word, Operator, Newline, End };

struct Token
{
    TokenType type = TokenType::End;
    std::string text;
    bool quoted = false;
    int ioNumber = -1;      // the "2" in 2>file
};

enum class ParseStatus { Ok, Incomplete, Error };

bool isOperatorStart(char c)
{
    return c == '|' || c == '&' || c == ';' || c == '<' || c == '>' || c == '(' || c == ')';
}

ParseStatus skipParenthesized(const std::string &s, size_t &i);

// i is at the opening '"'; afterwards it is just past the closing '"'.
ParseStatus skipDoubleQuoted(const std::string &s, size_t &i)
{
    for (++i; i < s.size(); ++i)
    {
        if (s[i] == '\\') { ++i; continue; }
        if (s[i] == '"') { ++i; return ParseStatus::Ok; }
        if (s[i] == '$' && i + 1 < s.size() && s[i + 1] == '(')
        {
            i += 2;
            if (skipParenthesized(s, i) != ParseStatus::Ok) return ParseStatus::Incomplete;
            --i;
        }
    }
    return ParseStatus::Incomplete;
}

// i is just after "$("; afterwards it is just past the matching ')'.
ParseStatus skipParenthesized(const std::string &s, size_t &i)
{
    int depth = 1;
    while (i < s.size())
    {
        char c = s[i];
        if (c == '\\') { i += 2; continue; }
        if (c == '\'')
        {
            size_t e = s.find('\'', i + 1);
            if (e == std::string::npos) return ParseStatus::Incomplete;
            i = e + 1;
            continue;
        }
        if (c == '"')
        {
            if (skipDoubleQuoted(s, i) != ParseStatus::Ok) return ParseStatus::Incomplete;
            continue;
        }
        if (c == '(') ++depth;
        else if (c == ')' && --depth == 0) { ++i; return ParseStatus::Ok; }
        ++i;
    }
    return ParseStatus::Incomplete;
}

bool isAllDigits(const std::string &s)
{
    if (s.empty()) return false;
    for (char c : s)
        if (!std::isdigit(static_cast<unsigned char>(c))) return false;
    return true;
}

ParseStatus tokenize(const std::string &src, std::vector<Token> &tokens)
{
    static const char *operators[] = {"&&", "||", "&>", ">>", ">&", "|", "&", ";", "<", ">", "(", ")"};
    tokens.clear();
    size_t i = 0, n = src.size();
    while (i < n)
    {
        char c = src[i];
        if (c == ' ' || c == '\t' || c == '\r') { ++i; continue; }
        if (c == '#') { while (i < n && src[i] != '\n') ++i; continue; }
        if (c == '\\' && i + 1 < n && src[i + 1] == '\n')
        {
            if (i + 2 >= n) return ParseStatus::Incomplete;   // trailing "\": keep reading
            i += 2;
            continue;
        }
        Token t;
        if (c == '\n')
        {
            t.type = TokenType::Newline;
            tokens.push_back(t);
            ++i;
            continue;
        }
        if (isOperatorStart(c))
        {
            t.type = TokenType::Operator;
            for (const char *op : operators)
                if (src.compare(i, strlen(op), op) == 0) { t.text = op; break; }
            i += t.text.size();
            tokens.push_back(t);
            continue;
        }
        t.type = TokenType::Word;
        while (i < n)
        {
            c = src[i];
            size_t begin = i;
            if (c == '\\')
            {
                if (i + 1 >= n) return ParseStatus::Incomplete;
                if (src[i + 1] == '\n')
                {
                    if (i + 2 >= n) return ParseStatus::Incomplete;
                    i += 2;
                    continue;
                }
                i += 2;
                t.quoted = true;
            }
            else if (c == '\'')
            {
                size_t e = src.find('\'', i + 1);
                if (e == std::string::npos) return ParseStatus::Incomplete;
                i = e + 1;
                t.quoted = true;
            }
            else if (c == '"')
            {
                if (skipDoubleQuoted(src, i) != ParseStatus::Ok) return ParseStatus::Incomplete;
                t.quoted = true;
            }
            else if (c == '$' && i + 1 < n && src[i + 1] == '(')
            {
                i += 2;
                if (skipParenthesized(src, i) != ParseStatus::Ok) return ParseStatus::Incomplete;
            }
            else if (std::isspace(static_cast<unsigned char>(c)) || isOperatorStart(c))
                break;
            else
                ++i;
            t.text.append(src, begin, i - begin);
        }
        if (!t.quoted && i < n && (src[i] == '<' || src[i] == '>') && isAllDigits(t.text))
            t.ioNumber = std::atoi(t.text.c_str());
        tokens.push_back(t);
    }
    tokens.push_back(Token());
    return ParseStatus::Ok;
}

enum class NodeKind { Simple, Pipeline, AndOr, List, If, While, Until, For };

struct Redirection
{
    int fd = -1;
    std::string op;        // < > >> &> >&
    std::string target;    // raw word, expanded when the command runs
};

struct Node;
typedef std::shared_ptr<Node> NodePtr;

struct Node
{
    NodeKind kind = NodeKind::Simple;
    std::vector<std::pair<std::string, std::string>> assignments;  // Simple: X=1
    std::vector<std::string> words;          // Simple: argv; For: the list
    std::vector<Redirection> redirections;   // Simple
    std::vector<NodePtr> children;           // Pipeline stages, List items, If cond/body pairs ...
    std::vector<std::string> operators;      // AndOr: && ||    List: ; &
    NodePtr elseBody;                        // If
    std::string name;                        // For variable
    std::string text;                        // original text, for "jobs"
};

struct ParseFailure { bool incomplete; std::string message; };

bool isValidName(const std::string &name)
{
    if (name.empty() || std::isdigit(static_cast<unsigned char>(name[0]))) return false;
    for (char c : name)
        if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_') return false;
    return true;
}

bool isRedirectionOperator(const std::string &op)
{
    return op == "<" || op == ">" || op == ">>" || op == "&>" || op == ">&";
}

class Parser
{
public:
    explicit Parser(const std::vector<Token> &tokens) : tokens_(tokens) {}

    NodePtr parseProgram()
    {
        NodePtr list = parseList();
        if (peek().type != TokenType::End) fail("syntax error near unexpected token `" + peek().text + "'");
        return list;
    }

private:
    const std::vector<Token> &tokens_;
    size_t pos_ = 0;

    const Token &peek() const { return tokens_[pos_]; }
    Token next() { Token t = tokens_[pos_]; if (pos_ + 1 < tokens_.size()) ++pos_; return t; }
    void fail(const std::string &message) { throw ParseFailure{peek().type == TokenType::End, message}; }
    bool isWord(const char *w) const { return peek().type == TokenType::Word && !peek().quoted && peek().text == w; }
    bool isOp(const char *o) const { return peek().type == TokenType::Operator && peek().text == o; }
    void skipNewlines() { while (peek().type == TokenType::Newline) next(); }

    void expect(const char *word)
    {
        skipNewlines();
        if (!isWord(word)) fail(std::string("syntax error: expected `") + word + "'");
        next();
    }

    bool atTerminator() const
    {
        if (peek().type == TokenType::End || isOp(")")) return true;
        static const char *words[] = {"then", "else", "elif", "fi", "do", "done"};
        for (const char *w : words)
            if (isWord(w)) return true;
        return false;
    }

    NodePtr make(NodeKind kind) { NodePtr n = std::make_shared<Node>(); n->kind = kind; return n; }

    NodePtr parseList()
    {
        NodePtr list = make(NodeKind::List);
        skipNewlines();
        while (!atTerminator())
        {
            list->children.push_back(parseAndOr());
            std::string separator = ";";
            if (isOp(";") || isOp("&")) separator = next().text;
            else if (peek().type == TokenType::Newline) next();
            else if (!atTerminator()) fail("syntax error near unexpected token `" + peek().text + "'");
            list->operators.push_back(separator);
            skipNewlines();
        }
        return list;
    }

    NodePtr parseAndOr()
    {
        NodePtr node = parsePipeline();
        if (!isOp("&&") && !isOp("||")) return node;
        NodePtr chain = make(NodeKind::AndOr);
        chain->children.push_back(node);
        while (isOp("&&") || isOp("||"))
        {
            chain->operators.push_back(next().text);
            skipNewlines();
            chain->children.push_back(parsePipeline());
        }
        return chain;
    }

    NodePtr parsePipeline()
    {
        NodePtr first = parseCommand();
        if (!isOp("|")) return first;
        NodePtr pipeline = make(NodeKind::Pipeline);
        pipeline->children.push_back(first);
        while (isOp("|"))
        {
            next();
            skipNewlines();
            pipeline->children.push_back(parseCommand());
        }
        for (const NodePtr &stage : pipeline->children)
            pipeline->text += (pipeline->text.empty() ? "" : " | ") + stage->text;
        return pipeline;
    }

    NodePtr parseCommand()
    {
        if (peek().type == TokenType::End) fail("syntax error: unexpected end of input");
        if (isWord("if")) return parseIf();
        if (isWord("while") || isWord("until")) return parseLoop();
        if (isWord("for")) return parseFor();
        if (atTerminator() || (peek().type == TokenType::Operator && !isRedirectionOperator(peek().text)))
            fail("syntax error near unexpected token `" + peek().text + "'");
        return parseSimple();
    }

    NodePtr parseSimple()
    {
        NodePtr node = make(NodeKind::Simple);
        while (true)
        {
            const Token &t = peek();
            bool redirect = (t.type == TokenType::Word && t.ioNumber >= 0) ||
                            (t.type == TokenType::Operator && isRedirectionOperator(t.text));
            if (redirect)
            {
                Redirection r;
                if (t.type == TokenType::Word) r.fd = next().ioNumber;
                r.op = next().text;
                if (peek().type != TokenType::Word) fail("syntax error: missing redirection target");
                r.target = next().text;
                node->redirections.push_back(r);
                node->text += (node->text.empty() ? "" : " ") + (r.fd >= 0 ? std::to_string(r.fd) : "") + r.op + r.target;
                continue;
            }
            if (t.type != TokenType::Word) break;
            size_t equals = t.text.find('=');
            if (node->words.empty() && equals != std::string::npos && isValidName(t.text.substr(0, equals)))
                node->assignments.emplace_back(t.text.substr(0, equals), t.text.substr(equals + 1));
            else
                node->words.push_back(t.text);
            node->text += (node->text.empty() ? "" : " ") + next().text;
        }
        if (node->text.empty()) fail("syntax error near unexpected token `" + peek().text + "'");
        return node;
    }

    NodePtr parseIf()
    {
        NodePtr node = make(NodeKind::If);
        next();
        node->children.push_back(parseList());
        expect("then");
        node->children.push_back(parseList());
        while (isWord("elif"))
        {
            next();
            node->children.push_back(parseList());
            expect("then");
            node->children.push_back(parseList());
        }
        if (isWord("else")) { next(); node->elseBody = parseList(); }
        expect("fi");
        node->text = "if ...";
        return node;
    }

    NodePtr parseLoop()
    {
        NodePtr node = make(next().text == "while" ? NodeKind::While : NodeKind::Until);
        node->children.push_back(parseList());
        expect("do");
        node->children.push_back(parseList());
        expect("done");
        node->text = "while ...";
        return node;
    }

    NodePtr parseFor()
    {
        NodePtr node = make(NodeKind::For);
        next();
        if (peek().type != TokenType::Word || !isValidName(peek().text)) fail("syntax error: bad for variable");
        node->name = next().text;
        skipNewlines();
        if (isWord("in"))
        {
            next();
            while (peek().type == TokenType::Word) node->words.push_back(next().text);
        }
        else
            node->words.push_back("\"$@\"");
        if (isOp(";")) next();
        expect("do");
        node->children.push_back(parseList());
        expect("done");
        node->text = "for ...";
        return node;
    }
};

ParseStatus parseCommandText(const std::string &text, NodePtr &program, std::string &error)
{
    std::vector<Token> tokens;
    if (tokenize(text, tokens) != ParseStatus::Ok)
    {
        error = "unexpected end of input";
        return ParseStatus::Incomplete;
    }
    try
    {
        program = Parser(tokens).parseProgram();
    }
    catch (const ParseFailure &failure)
    {
        error = failure.message;
        return failure.incomplete ? ParseStatus::Incomplete : ParseStatus::Error;
    }
    return ParseStatus::Ok;
}

// Used by the GUI: Enter runs the command, or shows "> " and keeps reading
// (open quote, trailing | or \, unclosed $(, missing fi/done ...).
bool isCommandComplete(const std::string &command)
{
    NodePtr program;
    std::string error;
    return parseCommandText(command, program, error) != ParseStatus::Incomplete;
}

// multiWatch ["cmd1", "cmd2", ...]
bool parseMultiWatch(const std::string &input, std::vector<std::string> &commands)
{
    const std::string keyword = "multiWatch";
    if (input.compare(0, keyword.size(), keyword) != 0) return false;
    size_t pos = input.find_first_not_of(" \t\n", keyword.size());
    if (pos == std::string::npos || input[pos] != '[') return false;
    ++pos;
    while (pos < input.size())
    {
        while (pos < input.size() && (std::isspace(static_cast<unsigned char>(input[pos])) || input[pos] == ','))
            ++pos;
        if (pos < input.size() && input[pos] == ']')
            return input.find_first_not_of(" \t\n", pos + 1) == std::string::npos && !commands.empty();
        if (pos >= input.size() || (input[pos] != '"' && input[pos] != '\'')) return false;
        char quote = input[pos++];
        std::string command;
        bool closed = false;
        while (pos < input.size())
        {
            char ch = input[pos++];
            if (ch == '\\' && pos < input.size() && (input[pos] == quote || input[pos] == '\\'))
                command += input[pos++];
            else if (ch == quote) { closed = true; break; }
            else command += ch;
        }
        if (!closed || command.empty()) return false;
        commands.push_back(command);
    }
    return false;
}

// ===========================================================================
//  Per-tab command engine
//  Thread Mode: runs in the tab's thread.  Process Mode: in the tab's process.
//  The GUI sends command lines through a pipe; the engine parses them, runs
//  built-ins itself and starts every other program with fork() + execvp(),
//  connecting pipes / redirections with dup2() and collecting with waitpid().
// ===========================================================================

const int TERMINAL_FD = -1;   // "the tab": output goes to the GUI, input comes from it

struct IoContext { int in = TERMINAL_FD, out = TERMINAL_FD, err = TERMINAL_FD; };

enum class RedirectKind { Input, Output, Append, Both, Duplicate };

struct PreparedRedirection
{
    int fd = 1;
    RedirectKind kind = RedirectKind::Output;
    std::string path;          // expanded, absolute
    int sourceFd = -1;         // for 2>&1
    std::string errorPrefix;   // built before fork for the child
};

enum class CommandKind { Empty, Builtin, Script, External };

struct PreparedCommand
{
    CommandKind kind = CommandKind::Empty;
    std::vector<std::string> argv;
    std::vector<std::pair<std::string, std::string>> assignments;
    std::vector<PreparedRedirection> redirections;
    // Built before fork() so the child only makes async-signal-safe calls.
    std::vector<char *> argvPointers, environmentPointers;
    std::vector<std::string> environment;
    std::string notFoundMessage, errorPrefix;
};

struct StagePlan
{
    NodePtr node;
    bool prepared = false;     // simple command (already expanded)
    PreparedCommand command;
};

struct Job
{
    int id = 0;
    pid_t pgid = 0;
    std::vector<pid_t> pids;
    std::vector<int> state;    // 0 running, 1 stopped, 2 finished
    std::vector<int> rawStatus;
    std::string command;
    int outputFd = -1;         // engine reads the job's stdout + stderr
    int inputFd = -1;          // engine writes keystrokes to the job's stdin
    std::string watchLabel;    // multiWatch prefix
    std::string partialLine;

    bool finished() const { for (int s : state) if (s != 2) return false; return true; }
    bool stopped() const
    {
        bool any = false;
        for (int s : state) { if (s == 0) return false; if (s == 1) any = true; }
        return any;
    }
};

struct ShellState
{
    std::string cwd, previousCwd;
    std::map<std::string, std::string> variables;
    std::set<std::string> exported;
    std::vector<std::string> positional;
};

struct WordBuilder
{
    std::string text, quoted, splittable;   // per char: '1' quoted / '1' split, '2' forced break
    bool hadQuotes = false, dropIfEmpty = false;
    void add(char c, bool q, char s = '0') { text += c; quoted += q ? '1' : '0'; splittable += s; }
    void append(const std::string &v, bool q, char s = '0') { for (char c : v) add(c, q, s); }
};

int statusFromWait(int raw)
{
    if (WIFEXITED(raw)) return WEXITSTATUS(raw);
    if (WIFSIGNALED(raw)) return 128 + WTERMSIG(raw);
    if (WIFSTOPPED(raw)) return 128 + WSTOPSIG(raw);
    return 1;
}

const char *describeError(int error)
{
    switch (error)
    {
    case ENOENT: return "No such file or directory";
    case EACCES: return "Permission denied";
    case EISDIR: return "Is a directory";
    case ENOTDIR: return "Not a directory";
    case ENOEXEC: return "Exec format error";
    default: return "Operation failed";
    }
}

// ---- Used in the child between fork() and execvp(): async-signal-safe only.

void childWriteError(const std::string &prefix, int error)
{
    const char *reason = describeError(error);
    (void)!write(STDERR_FILENO, prefix.data(), prefix.size());
    (void)!write(STDERR_FILENO, reason, strlen(reason));
    (void)!write(STDERR_FILENO, "\n", 1);
}

void resetChildSignals()
{
    struct sigaction action{};
    action.sa_handler = SIG_DFL;
    sigemptyset(&action.sa_mask);
    for (int sig : {SIGINT, SIGQUIT, SIGTSTP, SIGTTIN, SIGTTOU, SIGPIPE, SIGCHLD, SIGTERM, SIGHUP})
        sigaction(sig, &action, nullptr);
    sigset_t none;
    sigemptyset(&none);
    sigprocmask(SIG_SETMASK, &none, nullptr);
}

int openFlags(RedirectKind kind)
{
    if (kind == RedirectKind::Input) return O_RDONLY;
    if (kind == RedirectKind::Append) return O_WRONLY | O_CREAT | O_APPEND;
    return O_WRONLY | O_CREAT | O_TRUNC;
}

bool childApplyRedirections(const std::vector<PreparedRedirection> &list)
{
    for (const PreparedRedirection &r : list)
    {
        if (r.kind == RedirectKind::Duplicate)
        {
            dup2(r.sourceFd, r.fd);
            continue;
        }
        int fd = open(r.path.c_str(), openFlags(r.kind), 0644);
        if (fd == -1)
        {
            childWriteError(r.errorPrefix, errno);
            return false;
        }
        if (r.kind == RedirectKind::Both)
        {
            dup2(fd, STDOUT_FILENO);
            dup2(fd, STDERR_FILENO);
        }
        else
            dup2(fd, r.fd);
        if (fd > STDERR_FILENO) close(fd);
    }
    return true;
}

std::string normalizePath(const std::string &path)
{
    std::vector<std::string> parts;
    std::stringstream stream(path);
    std::string part;
    while (std::getline(stream, part, '/'))
    {
        if (part.empty() || part == ".") continue;
        if (part == "..") { if (!parts.empty()) parts.pop_back(); continue; }
        parts.push_back(part);
    }
    std::string result;
    for (const std::string &p : parts) result += "/" + p;
    return result.empty() ? "/" : result;
}

// A file we interpret ourselves: "#!" naming sh/bash, or text with no "#!".
bool isShellScript(const std::string &path)
{
    struct stat info{};
    if (stat(path.c_str(), &info) != 0 || !S_ISREG(info.st_mode) || access(path.c_str(), X_OK) != 0)
        return false;
    std::ifstream file(path);
    std::string firstLine;
    std::getline(file, firstLine);
    if (firstLine.compare(0, 2, "#!") == 0)
        return firstLine.find("bash") != std::string::npos || firstLine.find("/sh") != std::string::npos ||
               firstLine.find(" sh") != std::string::npos;
    return firstLine.find('\0') == std::string::npos && path.size() > 3 &&
           path.compare(path.size() - 3, 3, ".sh") == 0;
}

class CommandEngine
{
public:
    CommandEngine(int controlFd, int outputFd, const std::string &cwd)
        : controlFd_(controlFd), outputFd_(outputFd)
    {
        for (char **entry = environ; entry && *entry; ++entry)
        {
            std::string value = *entry;
            size_t equals = value.find('=');
            if (equals == std::string::npos || equals == 0) continue;
            state_.variables[value.substr(0, equals)] = value.substr(equals + 1);
            state_.exported.insert(value.substr(0, equals));
        }
        state_.cwd = cwd.empty() ? "/" : cwd;
    }

    ~CommandEngine()
    {
        if (controlFd_ != -1) close(controlFd_);
        if (outputFd_ != -1) close(outputFd_);
    }

    void run()
    {
        sendFrame(EngineCwd, state_.cwd);
        while (!stopping_)
        {
            if (!pendingCommands_.empty())
            {
                std::string command = pendingCommands_.front();
                pendingCommands_.pop_front();
                executeTopLevel(command);
                continue;
            }
            reapBackgroundJobs();
            pumpEvents(jobs_.empty() ? -1 : 200);
        }
        shutdownJobs();
    }

private:
    int controlFd_, outputFd_;
    bool subshell_ = false;    // inside a forked child (builtin/loop in a pipeline)
    ShellState state_;
    int lastStatus_ = 0;
    std::vector<std::unique_ptr<Job>> jobs_;
    std::vector<Job *> foreground_;
    std::deque<std::string> pendingCommands_;
    bool stopping_ = false, interrupted_ = false, exitRequested_ = false;
    int exitStatus_ = 0;

    // ------------------------------------------------------------ GUI output

    void sendFrame(EngineMessageType type, const std::string &data)
    {
        if (subshell_ || outputFd_ == -1) return;
        size_t offset = 0;
        do
        {
            size_t length = std::min<size_t>(65536, data.size() - offset);
            WorkerMessageHeader header{static_cast<uint32_t>(type), static_cast<uint32_t>(length)};
            if (!writeAll(outputFd_, reinterpret_cast<const char *>(&header), sizeof(header)) ||
                (length && !writeAll(outputFd_, data.data() + offset, length)))
            {
                stopping_ = interrupted_ = true;
                return;
            }
            offset += length;
        } while (offset < data.size());
    }

    // TERMINAL_FD = the tab (a frame to the GUI); in a subshell it is fd 1/2.
    void emit(int fd, const std::string &text, bool isError = false)
    {
        if (text.empty()) return;
        if (fd != TERMINAL_FD) writeAll(fd, text.data(), text.size());
        else if (subshell_) writeAll(isError ? 2 : 1, text.data(), text.size());
        else sendFrame(EngineText, text);
    }

    void emitError(const IoContext &io, const std::string &text) { emit(io.err, text, true); }
    bool shouldStop() const { return stopping_ || interrupted_ || exitRequested_; }

    // ------------------------------------------- GUI messages and job events

    void handleControlMessage()
    {
        WorkerMessageHeader header{};
        bool ok = readAll(controlFd_, &header, sizeof(header)) && header.length <= MAX_WORKER_MESSAGE_LENGTH;
        std::string payload(ok ? header.length : 0, '\0');
        if (!ok || (header.length && !readAll(controlFd_, &payload[0], header.length)))
        {
            stopping_ = interrupted_ = true;   // GUI closed the tab
            return;
        }
        Job *input = nullptr;
        for (Job *job : foreground_)
            if (job->inputFd != -1) { input = job; break; }

        if (header.type == WorkerCommand)
            pendingCommands_.push_back(payload);
        else if (header.type == WorkerInput && input)
            (void)!write(input->inputFd, payload.data(), payload.size());   // non-blocking, best effort
        else if (header.type == WorkerEof && input)
        {
            close(input->inputFd);
            input->inputFd = -1;
        }
        else if (header.type == WorkerSignal && payload.size() == sizeof(int))
        {
            // Ctrl+C / Ctrl+Z: signal the whole foreground process group.
            int sig;
            memcpy(&sig, payload.data(), sizeof(sig));
            if (sig == SIGINT) interrupted_ = true;
            for (Job *job : foreground_)
                if (job->pgid > 0) kill(-job->pgid, sig);
        }
        else if (header.type == WorkerStop)
            stopping_ = interrupted_ = true;
    }

    void relayOutput(Job &job, const char *data, size_t length)
    {
        if (job.watchLabel.empty())
        {
            sendFrame(EngineText, std::string(data, length));
            return;
        }
        // multiWatch: each block of output is printed under  "cmd", <time>:
        std::string lines;
        for (size_t i = 0; i < length; ++i)
        {
            if (data[i] != '\n') { job.partialLine += data[i]; continue; }
            lines += job.partialLine + "\n";
            job.partialLine.clear();
        }
        if (!lines.empty())
            sendFrame(EngineText, "\"" + job.watchLabel + "\", " + std::to_string(time(nullptr)) + ":\n" + lines);
    }

    bool readJobOutput(Job &job)
    {
        if (job.outputFd == -1) return false;
        char buffer[65536];
        ssize_t count = read(job.outputFd, buffer, sizeof(buffer));
        if (count > 0) { relayOutput(job, buffer, static_cast<size_t>(count)); return true; }
        if (count == -1 && (errno == EINTR || errno == EAGAIN)) return false;
        close(job.outputFd);
        job.outputFd = -1;
        if (!job.partialLine.empty()) relayOutput(job, "\n", 1);
        return false;
    }

    void pumpEvents(int timeoutMs)
    {
        if (subshell_) return;
        std::vector<pollfd> fds;
        std::vector<Job *> owners;
        fds.push_back(pollfd{controlFd_, POLLIN, 0});
        owners.push_back(nullptr);
        for (const auto &job : jobs_)
            if (job->outputFd != -1)
            {
                fds.push_back(pollfd{job->outputFd, POLLIN, 0});
                owners.push_back(job.get());
            }
        if (poll(fds.data(), fds.size(), timeoutMs) <= 0) return;
        for (size_t i = 0; i < fds.size(); ++i)
        {
            if (!(fds[i].revents & (POLLIN | POLLHUP | POLLERR))) continue;
            if (owners[i]) readJobOutput(*owners[i]);
            else handleControlMessage();
        }
    }

    void reapJob(Job &job)
    {
        for (size_t k = 0; k < job.pids.size(); ++k)
        {
            if (job.state[k] == 2) continue;
            int status = 0;
            pid_t result = waitpid(job.pids[k], &status, WNOHANG | WUNTRACED | WCONTINUED);
            if (result == job.pids[k])
            {
                if (WIFSTOPPED(status)) job.state[k] = 1;
                else if (WIFCONTINUED(status)) job.state[k] = 0;
                else { job.state[k] = 2; job.rawStatus[k] = status; }
            }
            else if (result == -1 && errno == ECHILD)
                job.state[k] = 2;
        }
    }

    int nextJobId() const
    {
        int highest = 0;
        for (const auto &job : jobs_) highest = std::max(highest, job->id);
        return highest + 1;
    }

    void removeJob(Job *target)
    {
        for (auto it = jobs_.begin(); it != jobs_.end(); ++it)
            if (it->get() == target)
            {
                while (readJobOutput(*target)) {}
                if (target->outputFd != -1) close(target->outputFd);
                if (target->inputFd != -1) close(target->inputFd);
                jobs_.erase(it);
                return;
            }
    }

    std::string jobLine(const Job &job, const std::string &state)
    {
        std::string line = "[" + std::to_string(job.id) + "]+  " + state;
        line.resize(std::max<size_t>(line.size(), 30), ' ');
        return line + job.command + "\n";
    }

    void reapBackgroundJobs()
    {
        std::vector<Job *> done;
        for (const auto &job : jobs_)
        {
            reapJob(*job);
            if (job->finished()) done.push_back(job.get());
        }
        for (Job *job : done)
        {
            if (job->id == 0) { removeJob(job); continue; }
            int status = statusFromWait(job->rawStatus.back());
            std::string line = jobLine(*job, status == 0 ? "Done" : "Exit " + std::to_string(status));
            removeJob(job);
            sendFrame(EngineText, line);
        }
    }

    // Waits for foreground jobs without blocking the tab: keystrokes and
    // Ctrl+C / Ctrl+Z from the GUI are handled while waiting.
    int waitForJobs(const std::vector<Job *> &list)
    {
        foreground_ = list;
        while (!stopping_)
        {
            bool active = false;
            for (Job *job : list)
            {
                reapJob(*job);
                if (!job->finished() && !job->stopped()) active = true;
            }
            if (!active) break;
            pumpEvents(20);
        }
        foreground_.clear();
        int status = stopping_ ? 130 : 0;
        for (Job *job : list)
        {
            if (job->finished())
            {
                status = statusFromWait(job->rawStatus.back());
                removeJob(job);
            }
            else if (job->stopped())
            {
                if (job->id == 0) job->id = nextJobId();
                sendFrame(EngineText, jobLine(*job, "Stopped"));
                status = 128 + SIGTSTP;
            }
        }
        return status;
    }

    void shutdownJobs()
    {
        for (const auto &job : jobs_)
            if (job->pgid > 0) { kill(-job->pgid, SIGHUP); kill(-job->pgid, SIGCONT); }
        for (const auto &job : jobs_)
            for (pid_t pid : job->pids)
                if (!waitForChildExit(pid, 200))
                {
                    kill(-job->pgid, SIGKILL);
                    while (waitpid(pid, nullptr, 0) == -1 && errno == EINTR) {}
                }
        while (!jobs_.empty()) removeJob(jobs_.back().get());
    }

    // ---------------------------------------------------------------- expansion

    std::string getVariable(const std::string &name) const
    {
        if (name == "?") return std::to_string(lastStatus_);
        if (name == "$") return std::to_string(getpid());
        if (name == "#") return std::to_string(state_.positional.size());
        if (name == "PWD") return state_.cwd;
        if (name == "@" || name == "*")
        {
            std::string joined;
            for (const std::string &p : state_.positional) joined += (joined.empty() ? "" : " ") + p;
            return joined;
        }
        if (isAllDigits(name))
        {
            size_t index = std::atoi(name.c_str());
            return index >= 1 && index <= state_.positional.size() ? state_.positional[index - 1] : "";
        }
        auto it = state_.variables.find(name);
        return it == state_.variables.end() ? "" : it->second;
    }

    std::string resolvePath(const std::string &path) const
    {
        if (path.empty() || path[0] == '/') return path;
        return (state_.cwd == "/" ? "" : state_.cwd) + "/" + path;
    }

    // $(...): run the command with stdout in an unlinked temp file, read it back.
    std::string commandSubstitution(const std::string &script)
    {
        NodePtr program;
        std::string error;
        if (shouldStop() || parseCommandText(script, program, error) != ParseStatus::Ok) return "";
        char path[] = "/tmp/terminator-subst-XXXXXX";
        int fd = mkstemp(path);
        if (fd == -1) return "";
        unlink(path);
        setCloseOnExec(fd);
        ShellState saved = state_;       // like a subshell: cd inside does not leak
        IoContext io;
        io.out = fd;
        lastStatus_ = executeNode(program, io);
        state_ = saved;
        exitRequested_ = false;

        std::string output;
        char buffer[4096];
        ssize_t count;
        lseek(fd, 0, SEEK_SET);
        while ((count = read(fd, buffer, sizeof(buffer))) > 0) output.append(buffer, count);
        close(fd);
        while (!output.empty() && output.back() == '\n') output.pop_back();
        return output;
    }

    // $(( ... )): integers with + - * / % comparisons and parentheses.
    long long arithmetic(const std::string &s, size_t &i, int level)
    {
        static const std::vector<std::vector<std::string>> ops = {
            {"==", "!=", "<=", ">=", "<", ">"}, {"+", "-"}, {"*", "/", "%"}};
        while (i < s.size() && s[i] == ' ') ++i;
        if (level == 3)
        {
            if (i < s.size() && s[i] == '-') { ++i; return -arithmetic(s, i, 3); }
            if (i < s.size() && s[i] == '(')
            {
                long long v = arithmetic(s, ++i, 0);
                while (i < s.size() && s[i] == ' ') ++i;
                if (i < s.size() && s[i] == ')') ++i;
                return v;
            }
            size_t start = i;
            while (i < s.size() && (std::isalnum(static_cast<unsigned char>(s[i])) || s[i] == '_')) ++i;
            std::string token = s.substr(start, i - start);
            return std::atoll(isAllDigits(token) ? token.c_str() : getVariable(token).c_str());
        }
        long long left = arithmetic(s, i, level + 1);
        while (true)
        {
            while (i < s.size() && s[i] == ' ') ++i;
            std::string op;
            for (const std::string &o : ops[level])
                if (s.compare(i, o.size(), o) == 0) { op = o; break; }
            if (op.empty()) return left;
            i += op.size();
            long long right = arithmetic(s, i, level + 1);
            if (op == "+") left += right;
            else if (op == "-") left -= right;
            else if (op == "*") left *= right;
            else if (op == "/" || op == "%") left = right == 0 ? 0 : (op == "/" ? left / right : left % right);
            else if (op == "==") left = left == right;
            else if (op == "!=") left = left != right;
            else if (op == "<=") left = left <= right;
            else if (op == ">=") left = left >= right;
            else if (op == "<") left = left < right;
            else left = left > right;
        }
    }

    // i at '$'. Returns false if the '$' is a literal dollar sign.
    bool expandDollar(const std::string &raw, size_t &i, std::string &value)
    {
        if (i + 1 >= raw.size()) return false;
        char c = raw[i + 1];
        size_t j = i + 2;
        if (c == '(')
        {
            if (skipParenthesized(raw, j) != ParseStatus::Ok) return false;
            std::string inner = raw.substr(i + 2, j - i - 3);
            if (inner.size() >= 2 && inner.front() == '(' && inner.back() == ')')
            {
                size_t k = 0;
                value = std::to_string(arithmetic(expandString(inner.substr(1, inner.size() - 2)), k, 0));
            }
            else
                value = commandSubstitution(inner);
        }
        else if (c == '{')
        {
            j = raw.find('}', i);
            if (j == std::string::npos) return false;
            value = getVariable(raw.substr(i + 2, j - i - 2));
            ++j;
        }
        else if (std::strchr("?$#@*", c) || std::isdigit(static_cast<unsigned char>(c)))
            value = getVariable(std::string(1, c));
        else if (std::isalpha(static_cast<unsigned char>(c)) || c == '_')
        {
            j = i + 1;
            while (j < raw.size() && (std::isalnum(static_cast<unsigned char>(raw[j])) || raw[j] == '_')) ++j;
            value = getVariable(raw.substr(i + 1, j - i - 1));
        }
        else
            return false;
        i = j;
        return true;
    }

    // Quote removal + $VAR / $(...) / ~ expansion.
    void expandRaw(const std::string &raw, WordBuilder &b)
    {
        size_t i = 0, n = raw.size();
        if (n > 0 && raw[0] == '~' && (n == 1 || raw[1] == '/')) { b.append(getVariable("HOME"), true); i = 1; }
        while (i < n)
        {
            char c = raw[i];
            std::string value;
            if (c == '\\')
            {
                b.hadQuotes = true;
                if (i + 1 < n) b.add(raw[i + 1], true);
                i += 2;
            }
            else if (c == '\'')
            {
                size_t end = raw.find('\'', i + 1);
                if (end == std::string::npos) end = n;
                b.hadQuotes = true;
                b.append(raw.substr(i + 1, end - i - 1), true);
                i = end + 1;
            }
            else if (c == '"')
            {
                b.hadQuotes = true;
                for (++i; i < n && raw[i] != '"';)
                {
                    if (raw[i] == '\\' && i + 1 < n && std::strchr("$\"\\`", raw[i + 1]))
                    {
                        b.add(raw[i + 1], true);
                        i += 2;
                    }
                    else if (raw.compare(i, 2, "$@") == 0)
                    {
                        // "$@": every positional parameter stays a separate word
                        i += 2;
                        b.dropIfEmpty = state_.positional.empty();
                        for (size_t k = 0; k < state_.positional.size(); ++k)
                        {
                            if (k) b.add(' ', true, '2');
                            b.append(state_.positional[k], true);
                        }
                    }
                    else if (raw[i] == '$' && expandDollar(raw, i, value))
                        b.append(value, true);
                    else
                        b.add(raw[i++], true);
                }
                ++i;
            }
            else if (c == '$' && expandDollar(raw, i, value))
                b.append(value, false, '1');     // unquoted: subject to word splitting
            else
                b.add(raw[i++], false);
        }
    }

    std::string expandString(const std::string &raw)
    {
        WordBuilder b;
        expandRaw(raw, b);
        return b.text;
    }

    // Globbing against the tab's own directory (Thread Mode shares one cwd).
    void appendGlobbed(const WordBuilder &field, std::vector<std::string> &out)
    {
        std::string pattern;
        bool hasGlob = false;
        for (size_t k = 0; k < field.text.size(); ++k)
        {
            char c = field.text[k];
            if (field.quoted[k] == '0' && std::strchr("*?[", c)) hasGlob = true;
            if (field.quoted[k] == '1' && std::strchr("*?[]\\", c)) pattern += '\\';
            pattern += c;
        }
        if (!hasGlob) { out.push_back(field.text); return; }
        std::string prefix = pattern[0] == '/' ? "" : (state_.cwd == "/" ? "/" : state_.cwd + "/");
        glob_t matches{};
        if (glob((prefix + pattern).c_str(), 0, nullptr, &matches) == 0)
            for (size_t k = 0; k < matches.gl_pathc; ++k)
                out.push_back(std::string(matches.gl_pathv[k]).substr(prefix.size()));
        else
            out.push_back(field.text);
        globfree(&matches);
    }

    // Expansion, then word splitting, then globbing.
    std::vector<std::string> expandWords(const std::vector<std::string> &raws)
    {
        std::vector<std::string> out;
        for (const std::string &raw : raws)
        {
            WordBuilder b, current;
            expandRaw(raw, b);
            std::vector<WordBuilder> fields;
            bool hasContent = false;
            for (size_t k = 0; k < b.text.size(); ++k)
            {
                bool split = b.splittable[k] == '2' ||
                             (b.splittable[k] == '1' && std::isspace(static_cast<unsigned char>(b.text[k])));
                if (split)
                {
                    if (hasContent) fields.push_back(current);
                    current = WordBuilder();
                    hasContent = b.splittable[k] == '2';
                    continue;
                }
                current.add(b.text[k], b.quoted[k] == '1');
                hasContent = true;
            }
            if (hasContent) fields.push_back(current);
            if (fields.empty() && b.hadQuotes && !b.dropIfEmpty) out.push_back("");
            for (const WordBuilder &field : fields) appendGlobbed(field, out);
        }
        return out;
    }

    // --------------------------------------------------------- preparing commands

    bool isBuiltin(const std::string &name) const
    {
        static const std::set<std::string> names = {"cd", "pwd", "exit", "history", "jobs", "fg", "bg",
                                                     "export", "source", ".", "clear", "true", "false", ":"};
        return names.count(name) > 0;
    }

    void prepareSimple(const Node &node, PreparedCommand &command)
    {
        command.argv = expandWords(node.words);
        for (const auto &a : node.assignments) command.assignments.emplace_back(a.first, expandString(a.second));
        for (const Redirection &r : node.redirections)
        {
            PreparedRedirection p;
            std::string target = expandString(r.target);
            p.fd = r.fd >= 0 ? r.fd : (r.op == "<" ? 0 : 1);
            if (r.op == "<") p.kind = RedirectKind::Input;
            else if (r.op == ">>") p.kind = RedirectKind::Append;
            else if (r.op == "&>" || (r.op == ">&" && !isAllDigits(target))) p.kind = RedirectKind::Both;
            else if (r.op == ">&") { p.kind = RedirectKind::Duplicate; p.sourceFd = std::atoi(target.c_str()); }
            p.path = resolvePath(target);
            p.errorPrefix = "terminator: " + target + ": ";
            command.redirections.push_back(p);
        }
        if (command.argv.empty()) command.kind = CommandKind::Empty;
        else if (isBuiltin(command.argv[0])) command.kind = CommandKind::Builtin;
        else if (command.argv[0].find('/') != std::string::npos && isShellScript(resolvePath(command.argv[0])))
            command.kind = CommandKind::Script;
        else command.kind = CommandKind::External;
    }

    // argv[] and envp[] for execvp(), built before fork().
    void prepareForExec(PreparedCommand &command)
    {
        std::map<std::string, std::string> environment;
        for (const std::string &name : state_.exported)
            if (state_.variables.count(name)) environment[name] = state_.variables.at(name);
        environment["PWD"] = state_.cwd;
        for (const auto &a : command.assignments) environment[a.first] = a.second;
        for (const auto &e : environment) command.environment.push_back(e.first + "=" + e.second);
        for (std::string &a : command.argv) command.argvPointers.push_back(&a[0]);
        for (std::string &e : command.environment) command.environmentPointers.push_back(&e[0]);
        command.argvPointers.push_back(nullptr);
        command.environmentPointers.push_back(nullptr);
        command.notFoundMessage = command.argv[0] + ": command not found\n";
        command.errorPrefix = "terminator: " + command.argv[0] + ": ";
    }

    // ------------------------------------------------------- fork() + execvp()

    [[noreturn]] void runChild(StagePlan &stage, int in, int out, int err, bool newGroup, pid_t pgid)
    {
        if (newGroup) setpgid(0, pgid);        // all stages of a pipeline share one group
        resetChildSignals();
        if (in != 0) dup2(in, 0);
        if (out != 1) dup2(out, 1);
        if (err != 2) dup2(err, 2);
        closeDescriptorsFrom(3);
        if (chdir(state_.cwd.c_str()) != 0) {}  // the tab's own directory
        if (stage.prepared && !childApplyRedirections(stage.command.redirections)) _exit(1);

        if (stage.prepared && stage.command.kind == CommandKind::External)
        {
            environ = stage.command.environmentPointers.data();
            execvp(stage.command.argvPointers[0], stage.command.argvPointers.data());
            int error = errno;
            if (error == ENOENT)
                (void)!write(2, stage.command.notFoundMessage.data(), stage.command.notFoundMessage.size());
            else
                childWriteError(stage.command.errorPrefix, error);
            _exit(error == ENOENT ? 127 : 126);
        }

        // A built-in or a loop inside a pipeline runs in this forked subshell.
        subshell_ = true;
        controlFd_ = outputFd_ = -1;
        for (const auto &job : jobs_) job->outputFd = job->inputFd = -1;
        jobs_.clear();
        IoContext io;
        io.in = 0; io.out = 1; io.err = 2;
        int status;
        if (stage.prepared)
        {
            stage.command.redirections.clear();   // already applied
            status = runInEngine(stage.command, io);
        }
        else
            status = executeNode(stage.node, io);
        _exit((exitRequested_ ? exitStatus_ : status) & 0xff);
    }

    bool launch(std::vector<StagePlan> &stages, IoContext io, bool background, Job &job)
    {
        bool top = !subshell_;
        int outPipe[2] = {-1, -1}, inPipe[2] = {-1, -1}, devNull = -1;
        if (top && (io.out == TERMINAL_FD || io.err == TERMINAL_FD))
        {
            if (!makePipe(outPipe)) return false;
            setNonBlocking(outPipe[0]);
        }
        int firstIn = io.in;
        if (firstIn == TERMINAL_FD)
        {
            if (!top) firstIn = 0;
            else if (background) firstIn = devNull = open("/dev/null", O_RDONLY | O_CLOEXEC);
            else if (makePipe(inPipe)) { setNonBlocking(inPipe[1]); firstIn = inPipe[0]; }
        }
        int lastOut = io.out != TERMINAL_FD ? io.out : (top ? outPipe[1] : 1);
        int errFd = io.err != TERMINAL_FD ? io.err : (top ? outPipe[1] : 2);

        for (StagePlan &stage : stages)
            if (stage.prepared && stage.command.kind == CommandKind::External) prepareForExec(stage.command);

        size_t count = stages.size();
        std::vector<int> pipes(2 * (count - 1), -1);
        for (size_t k = 0; k + 1 < count; ++k) makePipe(&pipes[2 * k]);

        pid_t pgid = 0;
        for (size_t i = 0; i < count; ++i)
        {
            pid_t pid = fork();
            if (pid == 0)
                runChild(stages[i], i == 0 ? firstIn : pipes[2 * (i - 1)],
                         i + 1 == count ? lastOut : pipes[2 * i + 1], errFd, top, pgid);
            if (pid < 0) { emitError(io, "terminator: fork failed\n"); break; }
            if (top) { if (pgid == 0) pgid = pid; setpgid(pid, pgid); }
            job.pids.push_back(pid);
            job.state.push_back(0);
            job.rawStatus.push_back(0);
        }
        // Close the parent's copies, otherwise readers never see end-of-file.
        for (int fd : {outPipe[1], inPipe[0], devNull}) if (fd != -1) close(fd);
        for (int fd : pipes) if (fd != -1) close(fd);
        job.pgid = pgid;
        job.outputFd = outPipe[0];
        job.inputFd = inPipe[1];
        if (job.pids.empty())
        {
            for (int fd : {outPipe[0], inPipe[1]}) if (fd != -1) close(fd);
            return false;
        }
        return true;
    }

    void buildStages(const NodePtr &node, std::vector<StagePlan> &plans)
    {
        std::vector<NodePtr> nodes = node->kind == NodeKind::Pipeline ? node->children : std::vector<NodePtr>{node};
        plans.resize(nodes.size());
        for (size_t i = 0; i < nodes.size(); ++i)
        {
            plans[i].node = nodes[i];
            if (nodes[i]->kind == NodeKind::Simple)
            {
                plans[i].prepared = true;
                prepareSimple(*nodes[i], plans[i].command);
            }
        }
    }

    int runStages(std::vector<StagePlan> &stages, IoContext io, bool background, const std::string &text)
    {
        std::unique_ptr<Job> job(new Job());
        job->command = text;
        if (!launch(stages, io, background, *job)) return 1;
        if (subshell_)
        {
            if (background) return 0;
            int raw = 0;
            for (pid_t pid : job->pids)
                while (waitpid(pid, &raw, 0) == -1 && errno == EINTR) {}
            return statusFromWait(raw);
        }
        Job *raw = job.get();
        jobs_.push_back(std::move(job));
        if (!background) return waitForJobs({raw});
        raw->id = nextJobId();
        emit(TERMINAL_FD, "[" + std::to_string(raw->id) + "] " + std::to_string(raw->pids.back()) + "\n");
        return 0;
    }

    int runPipeline(const NodePtr &node, IoContext io, bool background)
    {
        std::vector<StagePlan> plans;
        buildStages(node, plans);
        if (shouldStop()) return 130;
        StagePlan &first = plans[0];
        if (plans.size() == 1 && !background)
        {
            if (first.prepared && first.command.kind != CommandKind::External) return runInEngine(first.command, io);
            if (!first.prepared) return executeNode(first.node, io);
        }
        return runStages(plans, io, background, node->text);
    }

    // -------------------------------------------------------- walking the tree

    int executeNode(const NodePtr &node, IoContext io)
    {
        int status = 0;
        switch (node->kind)
        {
        case NodeKind::List:
            for (size_t i = 0; i < node->children.size() && !shouldStop(); ++i)
                status = node->operators[i] == "&" ? runPipeline(node->children[i], io, true)
                                                   : executeNode(node->children[i], io);
            break;
        case NodeKind::AndOr:
            status = executeNode(node->children[0], io);
            for (size_t k = 0; k < node->operators.size() && !shouldStop(); ++k)
                if ((node->operators[k] == "&&") == (status == 0))
                    status = executeNode(node->children[k + 1], io);
            break;
        case NodeKind::Simple:
        case NodeKind::Pipeline:
            status = runPipeline(node, io, false);
            break;
        case NodeKind::If:
        {
            bool matched = false;
            for (size_t k = 0; k + 1 < node->children.size() && !matched && !shouldStop(); k += 2)
                if (executeNode(node->children[k], io) == 0)
                {
                    status = executeNode(node->children[k + 1], io);
                    matched = true;
                }
            if (!matched && node->elseBody && !shouldStop()) status = executeNode(node->elseBody, io);
            break;
        }
        case NodeKind::While:
        case NodeKind::Until:
            while (true)
            {
                pumpEvents(0);   // lets Ctrl+C stop loops of built-ins
                if (shouldStop() || (executeNode(node->children[0], io) == 0) == (node->kind == NodeKind::Until) ||
                    shouldStop())
                    break;
                status = executeNode(node->children[1], io);
            }
            break;
        case NodeKind::For:
            for (const std::string &value : expandWords(node->words))
            {
                pumpEvents(0);
                if (shouldStop()) break;
                state_.variables[node->name] = value;
                status = executeNode(node->children[0], io);
            }
            break;
        }
        lastStatus_ = status;
        return status;
    }

    // Built-ins, scripts and plain assignments run inside the engine (no fork).
    int runInEngine(PreparedCommand &command, IoContext io)
    {
        std::vector<int> opened;
        for (const PreparedRedirection &r : command.redirections)
        {
            int fd = r.kind == RedirectKind::Duplicate ? (r.sourceFd == 1 ? io.out : io.err)
                                                       : open(r.path.c_str(), openFlags(r.kind) | O_CLOEXEC, 0644);
            if (fd == -1 && r.kind != RedirectKind::Duplicate)
            {
                emitError(io, r.errorPrefix + describeError(errno) + "\n");
                for (int o : opened) close(o);
                return 1;
            }
            if (r.kind != RedirectKind::Duplicate) opened.push_back(fd);
            if (r.kind == RedirectKind::Both) io.out = io.err = fd;
            else if (r.fd == 0) io.in = fd;
            else if (r.fd == 1) io.out = fd;
            else if (r.fd == 2) io.err = fd;
        }
        int status = 0;
        if (command.kind == CommandKind::Empty)
            for (const auto &a : command.assignments) state_.variables[a.first] = a.second;
        else if (command.kind == CommandKind::Builtin)
            status = runBuiltin(command.argv, io);
        else
        {
            ShellState saved = state_;           // ./script.sh runs like a child shell
            status = runScript(resolvePath(command.argv[0]),
                               std::vector<std::string>(command.argv.begin() + 1, command.argv.end()), io);
            state_ = saved;
            if (exitRequested_) { status = exitStatus_; exitRequested_ = false; }
        }
        for (int fd : opened) close(fd);
        return status;
    }

    // Bash scripts are interpreted by this engine, not handed to /bin/bash.
    int runScript(const std::string &path, const std::vector<std::string> &arguments, IoContext io)
    {
        std::ifstream file(path);
        if (!file)
        {
            emitError(io, "terminator: " + path + ": No such file or directory\n");
            return 127;
        }
        std::stringstream contents;
        contents << file.rdbuf();
        NodePtr program;
        std::string error;
        if (parseCommandText(contents.str(), program, error) != ParseStatus::Ok)
        {
            emitError(io, "terminator: " + path + ": " + error + "\n");
            return 2;
        }
        std::vector<std::string> savedPositional = state_.positional;
        if (!arguments.empty() || state_.positional.empty()) state_.positional = arguments;
        int status = executeNode(program, io);
        state_.positional = savedPositional;
        return status;
    }

    // --------------------------------------------------------------- built-ins

    Job *findJob(const std::vector<std::string> &argv, IoContext io)
    {
        Job *found = nullptr;
        int wanted = argv.size() > 1 ? std::atoi(argv[1].c_str() + (argv[1][0] == '%')) : 0;
        for (const auto &job : jobs_)
            if (job->id > 0 && (wanted == 0 ? (!found || job->id > found->id) : job->id == wanted))
                found = job.get();
        if (!found) emitError(io, argv[0] + ": no such job\n");
        return found;
    }

    int runBuiltin(const std::vector<std::string> &argv, IoContext io)
    {
        const std::string &name = argv[0];
        if (name == "true" || name == ":") return 0;
        if (name == "false") return 1;
        if (name == "pwd") { emit(io.out, state_.cwd + "\n"); return 0; }
        if (name == "clear") { if (!subshell_) sendFrame(EngineClear, ""); return 0; }
        if (name == "exit")
        {
            exitStatus_ = argv.size() > 1 ? std::atoi(argv[1].c_str()) : lastStatus_;
            exitRequested_ = true;
            return exitStatus_;
        }
        if (name == "cd")
        {
            // Only the tab's directory string changes: chdir() in the engine would
            // change the directory of every tab in Thread Mode.
            std::string target = argv.size() < 2 ? getVariable("HOME")
                               : argv[1] == "-" ? state_.previousCwd : argv[1];
            std::string path = normalizePath(resolvePath(target));
            struct stat info{};
            const char *problem = target.empty() ? "not set"
                                : stat(path.c_str(), &info) != 0 ? describeError(errno)
                                : !S_ISDIR(info.st_mode) ? "Not a directory" : nullptr;
            if (problem)
            {
                emitError(io, "cd: " + target + ": " + problem + "\n");
                return 1;
            }
            if (argv.size() > 1 && argv[1] == "-") emit(io.out, path + "\n");
            state_.previousCwd = state_.cwd;
            state_.cwd = path;
            return 0;
        }
        if (name == "history")
        {
            std::vector<std::string> entries = historySnapshot();
            size_t first = argv.size() > 1 && isAllDigits(argv[1])
                               ? entries.size() - std::min(entries.size(), (size_t)std::atoi(argv[1].c_str())) : 0;
            std::string text;
            for (size_t i = first; i < entries.size(); ++i)
            {
                std::string number = std::to_string(i + 1);
                text += std::string(5 - std::min<size_t>(5, number.size()), ' ') + number + "  " + entries[i] + "\n";
            }
            emit(io.out, text);
            return 0;
        }
        if (name == "jobs")
        {
            std::string text;
            for (const auto &job : jobs_)
            {
                reapJob(*job);
                if (job->id > 0)
                    text += jobLine(*job, job->finished() ? "Done" : job->stopped() ? "Stopped" : "Running");
            }
            emit(io.out, text);
            return 0;
        }
        if (name == "fg" || name == "bg")
        {
            Job *job = subshell_ ? nullptr : findJob(argv, io);
            if (!job) return 1;
            for (int &s : job->state) if (s == 1) s = 0;
            kill(-job->pgid, SIGCONT);            // resume the whole process group
            if (name == "bg")
            {
                emit(io.out, "[" + std::to_string(job->id) + "]+ " + job->command + " &\n");
                return 0;
            }
            emit(io.out, job->command + "\n");
            return waitForJobs({job});
        }
        if (name == "export")
        {
            for (size_t i = 1; i < argv.size(); ++i)
            {
                size_t equals = argv[i].find('=');
                std::string variable = argv[i].substr(0, equals);
                if (equals != std::string::npos) state_.variables[variable] = argv[i].substr(equals + 1);
                state_.exported.insert(variable);
            }
            return 0;
        }
        if (name == "source" || name == ".")
        {
            if (argv.size() < 2) { emitError(io, name + ": filename argument required\n"); return 2; }
            return runScript(resolvePath(argv[1]), std::vector<std::string>(argv.begin() + 2, argv.end()), io);
        }
        return 127;
    }

    // multiWatch ["cmd1", "cmd2", ...]: like watch, every command runs in
    // parallel (own process group, own pipe) and is re-run every 2 seconds
    // after it finishes, until Ctrl+C. Output is printed as it arrives.

    void runMultiWatch(const std::string &text)
    {
        struct Watch { std::string command; NodePtr program; Job *job; double lastStart; };
        std::vector<std::string> commands;
        std::vector<Watch> watches;
        if (!parseMultiWatch(text, commands))
        {
            emit(TERMINAL_FD, "Usage: multiWatch [\"cmd1\", \"cmd2\"]\n");
            lastStatus_ = 2;
            return;
        }
        for (const std::string &command : commands)
        {
            NodePtr program;
            std::string error;
            if (parseCommandText(command, program, error) != ParseStatus::Ok)
                emit(TERMINAL_FD, "multiWatch: " + command + ": " + error + "\n");
            else
            {
                if (program->children.size() == 1 && program->operators[0] == ";") program = program->children[0];
                watches.push_back(Watch{command, program, nullptr, -1e9});
            }
        }
        if (watches.empty()) { lastStatus_ = 2; return; }
        emit(TERMINAL_FD, "multiWatch: watching " + std::to_string(watches.size()) +
                              " commands every 2s (Ctrl+C stops them)\n");

        while (!shouldStop())
        {
            double now = std::chrono::duration<double>(
                std::chrono::steady_clock::now().time_since_epoch()).count();
            foreground_.clear();
            for (Watch &w : watches)
            {
                if (w.job)
                {
                    reapJob(*w.job);
                    if (w.job->finished()) { removeJob(w.job); w.job = nullptr; }
                }
                if (!w.job && now - w.lastStart >= 2.0)
                {
                    std::vector<StagePlan> plans;
                    buildStages(w.program, plans);
                    std::unique_ptr<Job> job(new Job());
                    job->command = job->watchLabel = w.command;
                    if (launch(plans, IoContext(), true, *job))   // stdin from /dev/null
                    {
                        w.job = job.get();
                        jobs_.push_back(std::move(job));
                    }
                    w.lastStart = now;
                }
                if (w.job) foreground_.push_back(w.job);   // Ctrl+C reaches these groups
            }
            pumpEvents(100);   // relays output, handles Ctrl+C from the GUI
        }

        // Ctrl+C: stop all, then reap them.
        foreground_.clear();
        for (Watch &w : watches)
        {
            if (!w.job) continue;
            kill(-w.job->pgid, SIGKILL);
            for (size_t k = 0; k < w.job->pids.size(); ++k)
                if (w.job->state[k] != 2)
                    while (waitpid(w.job->pids[k], nullptr, 0) == -1 && errno == EINTR) {}
            removeJob(w.job);
        }
        emit(TERMINAL_FD, "multiWatch: stopped\n");
        lastStatus_ = 130;
    }

    void executeTopLevel(std::string text)
    {
        interrupted_ = exitRequested_ = false;
        while (!text.empty() && std::isspace(static_cast<unsigned char>(text.back()))) text.pop_back();
        size_t first = text.find_first_not_of(" \t\n");
        if (first == std::string::npos) { sendFrame(EngineDone, "0"); return; }
        text = text.substr(first);

        // Each tab writes the shared history itself (mutex / process-shared semaphore).
        if (appendSharedHistory(text)) saveCommandHistory();

        NodePtr program;
        std::string error;
        if (text.compare(0, 10, "multiWatch") == 0)
            runMultiWatch(text);
        else if (parseCommandText(text, program, error) != ParseStatus::Ok)
        {
            emit(TERMINAL_FD, "terminator: " + error + "\n", true);
            lastStatus_ = 2;
        }
        else
            lastStatus_ = executeNode(program, IoContext());

        reapBackgroundJobs();
        if (exitRequested_)
        {
            sendFrame(EngineExit, "");
            stopping_ = true;
            return;
        }
        sendFrame(EngineCwd, state_.cwd);
        sendFrame(EngineDone, std::to_string(lastStatus_));
    }
};

// ===========================================================================
//  GUI side of a tab
// ===========================================================================

struct TerminalTab
{
    // GUI <-> engine pipes. The engine is a thread (Thread Mode) or a forked
    // process (Process Mode); there is no /bin/sh anywhere.
    int workerInputFd = -1;              // GUI writes commands / keystrokes
    int workerOutputFd = -1;             // GUI reads framed engine output
    pid_t workerPid = -1;                // Process Mode
    std::thread *workerThread = nullptr; // Thread Mode
    std::string workerReadBuffer;
    bool commandRunning = false;
    bool closeRequested = false;
    std::string cwd;
    int escapeState = 0;

    char inputBuffer[MAX_LINE_LENGTH] = {};
    int inputLength = 0;
    int cursorPosition = 0;
    int historyPosition = -1;
    std::string historyDraft;
    bool reverseSearchActive = false;
    std::string reverseSearchQuery;
    int reverseSearchMatch = -1;

    std::string commandBuffer;
    bool continuationMode = false;
    std::string asynchronousOutputLine;

    std::vector<std::string> completionCandidates;
    std::string completionOriginal;
    int completionStart = -1;
    int completionCycle = -1;

    char screenBuffer[MAX_LINES][MAX_SCREEN_LINE_LENGTH] = {};
    int screenLineCount = 0;
};

bool sendWorkerMessage(TerminalTab &tab, WorkerMessageType type,
                       const char *data, size_t length)
{
    if (tab.workerInputFd == -1 || length > MAX_WORKER_MESSAGE_LENGTH)
        return false;
    WorkerMessageHeader header{static_cast<uint32_t>(type),
                               static_cast<uint32_t>(length)};
    return writeAll(tab.workerInputFd,
                    reinterpret_cast<const char *>(&header), sizeof(header)) &&
           (length == 0 || writeAll(tab.workerInputFd, data, length));
}
void reapExitedChildren(TerminalTab tabs[], int tabCount)
{
    char bytes[128];
    while (read(childSignalPipe[0], bytes, sizeof(bytes)) > 0)
    {
    }
    for (int i = 0; i < tabCount; ++i)
    {
        // In Thread Mode the tab thread owns and waits for its shell. In
        // Process Mode the GUI owns the worker process; that worker owns its
        // shell and reaps it during shutdown.
        if (executionMode == ExecutionMode::Process && tabs[i].workerPid > 0)
        {
            pid_t result = waitpid(tabs[i].workerPid, nullptr, WNOHANG);
            if (result == tabs[i].workerPid ||
                (result == -1 && errno == ECHILD))
                tabs[i].workerPid = -1;
        }
    }
}
Atom clipboardAtom;
Atom utf8StringAtom;
Atom targetsAtom;
Atom clipboardProperty;
Atom wmDeleteAtom;
std::string clipboardText;

struct TextSelection
{
    bool active = false;
    bool dragging = false;
    int tabIndex = -1;
    int startPosition = -1;
    int endPosition = -1;
};

TextSelection textSelection;
const int TERMINAL_CHAR_WIDTH = 6;

void setClipboardText(Display *display, Window window, const std::string &text)
{
    clipboardText = text;
    XSetSelectionOwner(display, clipboardAtom, window, CurrentTime);
    XSetSelectionOwner(display, XA_PRIMARY, window, CurrentTime);
    XFlush(display);
}

void requestClipboardPaste(Display *display, Window window)
{
    XConvertSelection(display, clipboardAtom, utf8StringAtom,
                      clipboardProperty, window, CurrentTime);
    XFlush(display);
}

void handleSelectionRequest(Display *display,
                            const XSelectionRequestEvent &request)
{
    XSelectionEvent response{};
    response.type = SelectionNotify;
    response.display = request.display;
    response.requestor = request.requestor;
    response.selection = request.selection;
    response.target = request.target;
    response.time = request.time;
    response.property = None;

    Atom property = request.property == None ? request.target : request.property;

    if (request.target == targetsAtom)
    {
        Atom supportedTargets[] = {targetsAtom, utf8StringAtom, XA_STRING};
        XChangeProperty(display, request.requestor, property, XA_ATOM, 32,
                        PropModeReplace,
                        reinterpret_cast<unsigned char *>(supportedTargets), 3);
        response.property = property;
    }
    else if (request.target == utf8StringAtom || request.target == XA_STRING)
    {
        XChangeProperty(display, request.requestor, property, request.target, 8,
                        PropModeReplace,
                        reinterpret_cast<const unsigned char *>(clipboardText.data()),
                        static_cast<int>(clipboardText.size()));
        response.property = property;
    }

    XSendEvent(display, request.requestor, False, 0,
               reinterpret_cast<XEvent *>(&response));
    XFlush(display);
}

void handleSelectionNotify(Display *display,
                           const XSelectionEvent &event,
                           TerminalTab &tab)
{
    if (event.property == None)
        return;

    Atom actualType;
    int actualFormat;
    unsigned long itemCount;
    unsigned long bytesAfter;
    unsigned char *data = nullptr;

    int status = XGetWindowProperty(display, event.requestor,
                                    event.property, 0, 1 << 16, True,
                                    AnyPropertyType, &actualType,
                                    &actualFormat, &itemCount,
                                    &bytesAfter, &data);

    if (status == Success && data != nullptr && actualFormat == 8)
    {
        std::string pasted(reinterpret_cast<char *>(data), itemCount);
        std::string filtered;
        filtered.reserve(pasted.size());

        // The input line is a single line, so newlines in pasted text become
        // spaces instead of being stored (and drawn) as raw '\n' characters.
        for (char ch : pasted)
        {
            if (ch == '\r')
                continue;
            if (ch == '\n')
                filtered += ' ';
            else if (ch == '\t' ||
                     static_cast<unsigned char>(ch) >= 32)
                filtered += ch;
        }

        if (tab.inputLength + static_cast<int>(filtered.size()) <
                 MAX_LINE_LENGTH)
        {
            int insertLength = static_cast<int>(filtered.size());

            memmove(tab.inputBuffer + tab.cursorPosition + insertLength,
                    tab.inputBuffer + tab.cursorPosition,
                    static_cast<size_t>(tab.inputLength - tab.cursorPosition));

            memcpy(tab.inputBuffer + tab.cursorPosition,
                   filtered.data(), filtered.size());

            tab.inputLength += insertLength;
            tab.cursorPosition += insertLength;
            tab.inputBuffer[tab.inputLength] = '\0';
        }
    }

    if (data != nullptr)
        XFree(data);

    XDeleteProperty(display, event.requestor, event.property);
}

void addScreenLine(TerminalTab &tab, const char *line)
{
    if (tab.screenLineCount >= MAX_LINES)
    {
        // Rows are about to shift, so a stored selection would point at the
        // wrong text. Drop it.
        textSelection.active = false;
        textSelection.dragging = false;

        for (int i = 0; i < MAX_LINES - 1; i++)
            strcpy(tab.screenBuffer[i], tab.screenBuffer[i + 1]);

        tab.screenLineCount = MAX_LINES - 1;
    }

    snprintf(tab.screenBuffer[tab.screenLineCount],
             MAX_SCREEN_LINE_LENGTH, "%s", line);

    tab.screenLineCount++;
}
void adjustSelectionForClosedTab(int closedIndex);

// ---------------------------------------------------------------------------
//  Starting and stopping a tab's command engine
// ---------------------------------------------------------------------------

bool startWorker(TerminalTab &tab, const std::string &initialCwd)
{
    int controlPipe[2] = {-1, -1};
    int outputPipe[2] = {-1, -1};
    if (!makePipe(controlPipe) || !makePipe(outputPipe))
    {
        if (controlPipe[0] >= 0) close(controlPipe[0]);
        if (controlPipe[1] >= 0) close(controlPipe[1]);
        if (outputPipe[0] >= 0) close(outputPipe[0]);
        if (outputPipe[1] >= 0) close(outputPipe[1]);
        return false;
    }
    tab.cwd = initialCwd;
    tab.workerReadBuffer.clear();
    tab.closeRequested = false;

    if (executionMode == ExecutionMode::Process)
    {
        pid_t workerPid = fork();
        if (workerPid == -1)
        {
            close(controlPipe[0]); close(controlPipe[1]);
            close(outputPipe[0]); close(outputPipe[1]);
            return false;
        }
        if (workerPid == 0)
        {
            // The tab process: drop the X connection, the SIGCHLD self-pipe
            // and every other tab's pipes; keep only our two pipe ends.
            signal(SIGCHLD, SIG_DFL);
            for (int fd = 3; fd < maxDescriptorToClose; ++fd)
                if (fd != controlPipe[0] && fd != outputPipe[1])
                    close(fd);
            {
                CommandEngine engine(controlPipe[0], outputPipe[1], initialCwd);
                engine.run();
            }
            _exit(0);
        }

        close(controlPipe[0]);
        close(outputPipe[1]);
        tab.workerPid = workerPid;
        tab.workerInputFd = controlPipe[1];
        tab.workerOutputFd = outputPipe[0];
        return true;
    }

    int engineControlFd = controlPipe[0];
    int engineOutputFd = outputPipe[1];
    try
    {
        std::string cwd = initialCwd;
        tab.workerThread = new std::thread([engineControlFd, engineOutputFd, cwd]() {
            CommandEngine engine(engineControlFd, engineOutputFd, cwd);
            engine.run();
        });
    }
    catch (...)
    {
        close(controlPipe[0]); close(controlPipe[1]);
        close(outputPipe[0]); close(outputPipe[1]);
        return false;
    }
    tab.workerInputFd = controlPipe[1];
    tab.workerOutputFd = outputPipe[0];
    return true;
}

void stopWorker(TerminalTab &tab)
{
    // Closing the GUI read end releases an engine blocked writing output;
    // closing the control pipe tells an idle engine to kill its jobs and quit.
    if (tab.workerOutputFd != -1)
    {
        close(tab.workerOutputFd);
        tab.workerOutputFd = -1;
    }
    if (tab.workerInputFd != -1)
    {
        close(tab.workerInputFd);
        tab.workerInputFd = -1;
    }

    if (tab.workerThread != nullptr)
    {
        if (tab.workerThread->joinable())
            tab.workerThread->join();
        delete tab.workerThread;
        tab.workerThread = nullptr;
    }

    if (tab.workerPid > 0)
    {
        pid_t workerPid = tab.workerPid;
        if (!waitForChildExit(workerPid, 1500))
        {
            kill(workerPid, SIGTERM);
            if (!waitForChildExit(workerPid, 300))
            {
                kill(workerPid, SIGKILL);
                while (waitpid(workerPid, nullptr, 0) == -1 && errno == EINTR)
                {
                }
            }
        }
        tab.workerPid = -1;
    }
    tab.commandRunning = false;
}

bool restartEngineIfNeeded(TerminalTab &tab)
{
    if (tab.workerOutputFd != -1)
        return true;

    stopWorker(tab);
    if (!startWorker(tab, tab.cwd))
    {
        addScreenLine(tab, "Error: could not restart the tab's command engine");
        return false;
    }
    addScreenLine(tab, "Command engine restarted");
    return true;
}

// Hands a complete command line to the tab's engine. The GUI never runs
// commands itself, so it stays responsive while the command executes.
void executeCommand(TerminalTab &tab, const std::string &command)
{
    if (!restartEngineIfNeeded(tab))
        return;
    tab.commandRunning = true;
    if (!sendWorkerMessage(tab, WorkerCommand, command.data(), command.size()))
    {
        tab.commandRunning = false;
        addScreenLine(tab, "Error: could not send command to the tab's engine");
    }
}

std::string displayDirectory(const std::string &cwd)
{
    const char *home = getenv("HOME");
    if (home != nullptr && *home != '\0')
    {
        std::string homeDirectory = home;
        if (cwd == homeDirectory)
            return "~";
        if (cwd.compare(0, homeDirectory.size() + 1, homeDirectory + "/") == 0)
            return "~" + cwd.substr(homeDirectory.size());
    }
    return cwd.empty() ? "~" : cwd;
}

std::string promptString(const TerminalTab &tab)
{
    return "shovon@mac:" + displayDirectory(tab.cwd) + "$ ";
}

const size_t OUTPUT_WRAP_COLUMNS =
    static_cast<size_t>((WINDOW_WIDTH - 40) / 6);

void flushOutputLine(TerminalTab &tab)
{
    if (!tab.asynchronousOutputLine.empty())
    {
        addScreenLine(tab, tab.asynchronousOutputLine.c_str());
        tab.asynchronousOutputLine.clear();
    }
}

// There is no terminal device: commands write into a pipe, and the GUI does
// the terminal's job of turning bytes into lines on the screen.
void appendOutputText(TerminalTab &tab, const std::string &text)
{
    std::string &line = tab.asynchronousOutputLine;
    for (char ch : text)
    {
        unsigned char c = static_cast<unsigned char>(ch);
        if (tab.escapeState == 1)
        {
            tab.escapeState = c == '[' ? 2 : 0;
            continue;
        }
        if (tab.escapeState == 2)
        {
            if (c >= 0x40 && c <= 0x7E)
                tab.escapeState = 0;
            continue;
        }
        if (c == 0x1B)
        {
            tab.escapeState = 1;
            continue;
        }
        if (c == '\n')
        {
            addScreenLine(tab, line.c_str());
            line.clear();
            continue;
        }
        if (c == '\r')
            continue;
        if (c == '\b')
        {
            if (!line.empty())
                line.pop_back();
            continue;
        }
        if (c == '\t')
        {
            do
                line += ' ';
            while (line.size() % 8 != 0);
        }
        else if (c >= 32 && c != 127)
            line += ch;
        else
            continue;

        if (line.size() >= OUTPUT_WRAP_COLUMNS)
        {
            addScreenLine(tab, line.c_str());
            line.clear();
        }
    }
}

void handleEngineEnded(TerminalTab &tab)
{
    if (tab.workerOutputFd != -1)
    {
        close(tab.workerOutputFd);
        tab.workerOutputFd = -1;
    }
    tab.commandRunning = false;
    flushOutputLine(tab);
    if (!tab.closeRequested)
        addScreenLine(tab, "[command engine stopped - press Enter to restart it]");
}

void handleEngineMessage(TerminalTab &tab, uint32_t type,
                         const std::string &payload)
{
    switch (type)
    {
    case EngineText:
        appendOutputText(tab, payload);
        break;
    case EngineDone:
        flushOutputLine(tab);
        tab.escapeState = 0;
        tab.commandRunning = false;
        break;
    case EngineCwd:
        tab.cwd = payload;
        break;
    case EngineClear:
        tab.screenLineCount = 0;
        tab.asynchronousOutputLine.clear();
        textSelection.active = false;
        textSelection.dragging = false;
        break;
    case EngineExit:
        tab.closeRequested = true;
        break;
    default:
        break;
    }
}

// Reads whatever the engine sent and decodes complete frames.
// Returns true if the tab's screen may have changed.
bool readEngineOutput(TerminalTab &tab)
{
    char chunk[65536];
    ssize_t count = read(tab.workerOutputFd, chunk, sizeof(chunk));
    if (count > 0)
    {
        tab.workerReadBuffer.append(chunk, static_cast<size_t>(count));
        size_t offset = 0;
        while (tab.workerReadBuffer.size() - offset >= sizeof(WorkerMessageHeader))
        {
            WorkerMessageHeader header{};
            memcpy(&header, tab.workerReadBuffer.data() + offset, sizeof(header));
            if (header.length > MAX_WORKER_MESSAGE_LENGTH)
            {
                tab.workerReadBuffer.clear();
                handleEngineEnded(tab);
                return true;
            }
            if (tab.workerReadBuffer.size() - offset < sizeof(header) + header.length)
                break;
            std::string payload = tab.workerReadBuffer.substr(
                offset + sizeof(header), header.length);
            offset += sizeof(header) + header.length;
            handleEngineMessage(tab, header.type, payload);
        }
        tab.workerReadBuffer.erase(0, offset);
        return true;
    }
    if (count == 0 || (count == -1 && errno != EINTR && errno != EAGAIN))
    {
        handleEngineEnded(tab);
        return true;
    }
    return false;
}

void closeTab(TerminalTab tabs[], int &tabCount, int &currentTab, int index)
{
    stopWorker(tabs[index]);
    adjustSelectionForClosedTab(index);

    for (int i = index; i < tabCount - 1; i++)
        tabs[i] = tabs[i + 1];

    tabCount--;
    tabs[tabCount] = TerminalTab{};

    if (index < currentTab)
        currentTab--;
    else if (currentTab >= tabCount)
        currentTab = tabCount - 1;
}
unsigned long getColor(Display *display, int screen, const char *name,
                       unsigned long fallback)
{
    XColor color;
    Colormap colormap = DefaultColormap(display, screen);

    if (XAllocNamedColor(display, colormap, name, &color, &color))
        return color.pixel;

    return fallback;
}

void drawTabs(Display *display, Window window, GC gc,
              int screen, int tabCount, int currentTab,
              unsigned long selectedColor, unsigned long inactiveColor,
              unsigned long inactiveText)
{
    const unsigned long selectedText = WhitePixel(display, screen);

    for (int i = 0; i < tabCount; i++)
    {
        int x = i * TAB_WIDTH;

        if (i == currentTab)
        {
            XSetForeground(display, gc, selectedColor);
            XFillRectangle(display, window, gc,
                           x, 0, TAB_WIDTH, TAB_HEIGHT);

            XSetForeground(display, gc, selectedText);
        }
        else
        {
            XSetForeground(display, gc, inactiveColor);
            XFillRectangle(display, window, gc,
                           x, 0, TAB_WIDTH, TAB_HEIGHT);

            XSetForeground(display, gc, inactiveText);
        }

        char tabName[20];
        snprintf(tabName, sizeof(tabName), "Tab %d", i + 1);

        XDrawString(display, window, gc,
                    x + 10, 20, tabName, strlen(tabName));

        int crossCenterX = x + TAB_WIDTH - 15;
        int crossCenterY = TAB_HEIGHT / 2;
        int crossSize = 4;

        XDrawLine(display, window, gc,
                  crossCenterX - crossSize, crossCenterY - crossSize,
                  crossCenterX + crossSize, crossCenterY + crossSize);

        XDrawLine(display, window, gc,
                  crossCenterX - crossSize, crossCenterY + crossSize,
                  crossCenterX + crossSize, crossCenterY - crossSize);
    }

    XSetForeground(display, gc, BlackPixel(display, screen));
    XDrawLine(display, window, gc,
              0, TAB_HEIGHT, WINDOW_WIDTH, TAB_HEIGHT);
}

void drawScreen(Display *display, Window window, GC gc, int screen,
                TerminalTab tabs[], int tabCount, int currentTab,
                unsigned long selectedColor, unsigned long inactiveColor,
                unsigned long inactiveText)
{
    XClearWindow(display, window);

    drawTabs(display, window, gc, screen, tabCount, currentTab,
             selectedColor, inactiveColor, inactiveText);

    TerminalTab &tab = tabs[currentTab];

    const int textX = 20;
    int textY = CONTENT_START_Y;

    XSetForeground(display, gc, BlackPixel(display, screen));

    for (int i = 0; i < tab.screenLineCount; i++)
    {
        int length = static_cast<int>(strlen(tab.screenBuffer[i]));
        int y = textY + i * LINE_HEIGHT;
        int begin = -1;
        int end = -1;

        if (textSelection.active && textSelection.tabIndex == currentTab)
        {
            int first = std::min(textSelection.startPosition, textSelection.endPosition);
            int last = std::max(textSelection.startPosition, textSelection.endPosition);
            int rowStart = i * MAX_SCREEN_LINE_LENGTH;
            if (rowStart <= last && rowStart + length >= first)
            {
                begin = std::max(0, first - rowStart);
                end = std::min(length, last - rowStart);
            }
        }

        if (begin >= 0 && end > begin)
        {
            // Reuse the already-allocated tab color instead of calling
            // XAllocNamedColor on every redraw.
            XSetForeground(display, gc, selectedColor);
            XFillRectangle(display, window, gc,
                           textX + begin * TERMINAL_CHAR_WIDTH, y - 14,
                           static_cast<unsigned int>((end - begin) * TERMINAL_CHAR_WIDTH),
                           LINE_HEIGHT);
            XSetForeground(display, gc, BlackPixel(display, screen));
            if (begin > 0)
                XDrawString(display, window, gc, textX, y, tab.screenBuffer[i], begin);
            XSetForeground(display, gc, WhitePixel(display, screen));
            XDrawString(display, window, gc, textX + begin * TERMINAL_CHAR_WIDTH,
                        y, tab.screenBuffer[i] + begin, end - begin);
            XSetForeground(display, gc, BlackPixel(display, screen));
            if (end < length)
                XDrawString(display, window, gc, textX + end * TERMINAL_CHAR_WIDTH,
                            y, tab.screenBuffer[i] + end, length - end);
        }
        else
        {
            XSetForeground(display, gc, BlackPixel(display, screen));
            XDrawString(display, window, gc, textX, y,
                        tab.screenBuffer[i], length);
        }
    }

    textY += tab.screenLineCount * LINE_HEIGHT;

    std::string prompt;
    std::string displayedInput;

    if (tab.reverseSearchActive)
    {
        prompt = "(reverse-i-search)`" + tab.reverseSearchQuery + "': ";
        std::vector<std::string> history = historySnapshot();
        if (tab.reverseSearchMatch >= 0 &&
            tab.reverseSearchMatch < static_cast<int>(history.size()))
            displayedInput = history[tab.reverseSearchMatch];
    }
    else if (tab.commandRunning)
    {
        // No prompt while a command runs: show its unfinished output line
        // (e.g. "Name: " from read -p) followed by what the user is typing.
        prompt = tab.asynchronousOutputLine;
        displayedInput.assign(tab.inputBuffer, tab.inputLength);
    }
    else
    {
        prompt = tab.continuationMode ? "> " : promptString(tab);
        displayedInput.assign(tab.inputBuffer, tab.inputLength);
    }

    XDrawString(display, window, gc, textX, textY, prompt.c_str(),
                static_cast<int>(prompt.size()));

    int inputX = textX + static_cast<int>(prompt.size()) * 6;
    XDrawString(display, window, gc, inputX, textY,
                displayedInput.c_str(), static_cast<int>(displayedInput.size()));

    int cursorX = inputX + (tab.reverseSearchActive
                                ? static_cast<int>(displayedInput.size())
                                : tab.cursorPosition) * 6;

    XDrawLine(display, window, gc,
              cursorX, textY - 15,
              cursorX, textY + 2);

    XFlush(display);
}
struct CompletionContext
{
    int start = 0;
    std::string token;
    std::string quote;
    bool commandPosition = false;
    std::string commandName;
    int tokenIndex = 0;
};

std::string getInputPrefix(const TerminalTab &tab)
{
    return std::string(tab.inputBuffer, tab.cursorPosition);
}

CompletionContext getCompletionContext(const TerminalTab &tab)
{
    CompletionContext context;
    std::string prefix = getInputPrefix(tab);

    bool singleQuoted = false;
    bool doubleQuoted = false;
    bool escaped = false;
    int tokenStart = 0;
    int tokenIndex = 0;
    std::vector<std::string> completedTokens;
    std::string current;

    for (int i = 0; i < static_cast<int>(prefix.size()); ++i)
    {
        char ch = prefix[i];

        if (escaped)
        {
            current += ch;
            escaped = false;
            continue;
        }

        if (!doubleQuoted && ch == '\'')
        {
            if (!singleQuoted && current.empty())
                tokenStart = i + 1;
            singleQuoted = !singleQuoted;
            continue;
        }

        if (!singleQuoted && ch == '"')
        {
            if (!doubleQuoted && current.empty())
                tokenStart = i + 1;
            doubleQuoted = !doubleQuoted;
            continue;
        }

        if (!singleQuoted && ch == '\\')
        {
            escaped = true;
            continue;
        }

        if (!singleQuoted && !doubleQuoted &&
            std::isspace(static_cast<unsigned char>(ch)))
        {
            if (!current.empty())
                completedTokens.push_back(current);
            current.clear();
            tokenStart = i + 1;
            tokenIndex = static_cast<int>(completedTokens.size());
            continue;
        }

        current += ch;
    }

    context.start = tokenStart;
    context.token = current;
    context.tokenIndex = tokenIndex;
    context.commandPosition = completedTokens.empty();

    if (!completedTokens.empty())
        context.commandName = completedTokens[0];

    if (singleQuoted)
        context.quote = "'";
    else if (doubleQuoted)
        context.quote = "\"";

    return context;
}

bool isExecutableFile(const std::string &path)
{
    struct stat info{};
    return stat(path.c_str(), &info) == 0 &&
           S_ISREG(info.st_mode) && access(path.c_str(), X_OK) == 0;
}

std::vector<std::string> getPathCommands()
{
    std::vector<std::string> results;
    const char *pathValue = std::getenv("PATH");
    if (!pathValue)
        return results;

    std::stringstream paths(pathValue);
    std::string directory;

    while (std::getline(paths, directory, ':'))
    {
        if (directory.empty())
            directory = ".";

        DIR *dir = opendir(directory.c_str());
        if (!dir)
            continue;

        while (dirent *entry = readdir(dir))
        {
            std::string name = entry->d_name;
            if (name.empty() || name[0] == '.')
                continue;

            if (isExecutableFile(directory + "/" + name))
                results.push_back(name);
        }

        closedir(dir);
    }

    std::sort(results.begin(), results.end());
    results.erase(std::unique(results.begin(), results.end()), results.end());
    return results;
}

std::vector<std::string> getGitSubcommands()
{
    return {
        "add", "bisect", "branch", "checkout", "cherry-pick",
        "clone", "commit", "diff", "fetch", "grep", "init",
        "log", "merge", "mv", "pull", "push", "rebase",
        "remote", "reset", "restore", "revert", "show",
        "status", "switch", "tag"
    };
}

std::string commonPrefix(const std::vector<std::string> &items)
{
    if (items.empty())
        return "";

    std::string prefix = items[0];
    for (size_t i = 1; i < items.size(); ++i)
    {
        size_t j = 0;
        while (j < prefix.size() && j < items[i].size() &&
               prefix[j] == items[i][j])
            ++j;
        prefix.resize(j);
        if (prefix.empty())
            break;
    }
    return prefix;
}

std::string escapeCompletion(const std::string &value,
                             const std::string &quote)
{
    std::string result;
    for (char ch : value)
    {
        if (quote == "'")
        {
            if (ch == '\'')
                result += "'\\''";
            else
                result += ch;
        }
        else if (quote == "\"")
        {
            if (ch == '"' || ch == '\\' || ch == '$' || ch == '`')
                result += '\\';
            result += ch;
        }
        else
        {
            if (std::isspace(static_cast<unsigned char>(ch)) ||
                ch == '\\' || ch == '\'' || ch == '"' ||
                ch == '$' || ch == '`' || ch == '&' ||
                ch == '(' || ch == ')' || ch == ';' ||
                ch == '|' || ch == '<' || ch == '>')
                result += '\\';
            result += ch;
        }
    }
    return result;
}

std::vector<std::string> getFileCompletions(const std::string &token,
                                            bool directoriesOnly,
                                            const std::string &baseDirectory)
{
    std::vector<std::string> results;
    size_t slash = token.find_last_of('/');
    std::string directoryPart = slash == std::string::npos
                                    ? ""
                                    : token.substr(0, slash + 1);
    std::string namePart = slash == std::string::npos
                               ? token
                               : token.substr(slash + 1);
    // Each tab has its own directory (the GUI process directory is shared).
    std::string base = baseDirectory.empty() ? "." : baseDirectory;
    std::string searchDirectory;
    if (!directoryPart.empty() && directoryPart[0] == '/')
        searchDirectory = directoryPart;
    else
        searchDirectory = base + "/" + directoryPart;

    DIR *dir = opendir(searchDirectory.c_str());
    if (!dir)
        return results;

    while (dirent *entry = readdir(dir))
    {
        std::string name = entry->d_name;
        if (name == "." || name == "..")
            continue;
        if (name.compare(0, namePart.size(), namePart) != 0)
            continue;
        if (!name.empty() && name[0] == '.' &&
            (namePart.empty() || namePart[0] != '.'))
            continue;

        std::string fullPath = searchDirectory;
        if (fullPath.back() != '/')
            fullPath += '/';
        fullPath += name;

        struct stat info{};
        if (stat(fullPath.c_str(), &info) != 0)
            continue;

        bool isDirectory = S_ISDIR(info.st_mode);
        if (directoriesOnly && !isDirectory)
            continue;

        std::string candidate = directoryPart + name;
        if (isDirectory)
            candidate += '/';
        results.push_back(candidate);
    }

    closedir(dir);
    std::sort(results.begin(), results.end());
    return results;
}

std::vector<std::string> findCompletionCandidates(
    const CompletionContext &context, const std::string &baseDirectory)
{
    std::vector<std::string> candidates;

    if (context.commandPosition)
    {
        if (context.token.find('/') != std::string::npos)
            return getFileCompletions(context.token, false, baseDirectory);

        std::vector<std::string> commands = getPathCommands();
        static const char *builtins[] = {
            "cd", "pwd", "exit", "history", "jobs", "fg", "bg", "export",
            "source", "bind", "multiWatch"};
        for (const char *name : builtins)
            commands.push_back(name);
        std::sort(commands.begin(), commands.end());
        commands.erase(std::unique(commands.begin(), commands.end()), commands.end());
        for (const std::string &name : commands)
            if (name.compare(0, context.token.size(), context.token) == 0)
                candidates.push_back(name);

        return candidates;
    }

    if (context.commandName == "git" && context.tokenIndex == 1)
    {
        for (const std::string &name : getGitSubcommands())
            if (name.compare(0, context.token.size(), context.token) == 0)
                candidates.push_back(name);
        return candidates;
    }

    bool directoriesOnly = context.commandName == "cd";
    return getFileCompletions(context.token, directoriesOnly, baseDirectory);
}

void resetCompletion(TerminalTab &tab)
{
    tab.completionCandidates.clear();
    tab.completionOriginal.clear();
    tab.completionStart = -1;
    tab.completionCycle = -1;
}

void replaceCompletionToken(TerminalTab &tab,
                            const CompletionContext &context,
                            const std::string &candidate)
{
    std::string escaped = escapeCompletion(candidate, context.quote);
    int start = context.start;
    int oldLength = tab.cursorPosition - start;
    int newLength = static_cast<int>(escaped.size());

    if (start < 0 || start > tab.cursorPosition ||
        tab.inputLength - oldLength + newLength >= MAX_LINE_LENGTH)
        return;

    std::string updated(tab.inputBuffer, tab.inputLength);
    updated.replace(static_cast<size_t>(start),
                    static_cast<size_t>(oldLength), escaped);

    tab.inputLength = static_cast<int>(updated.size());
    memcpy(tab.inputBuffer, updated.data(), updated.size());
    tab.inputBuffer[tab.inputLength] = '\0';
    tab.cursorPosition = start + newLength;
}

void handleAutoComplete(TerminalTab &tab)
{
    CompletionContext context = getCompletionContext(tab);

    bool tokenIsCurrentCandidate = false;
    if (tab.completionCycle >= 0 &&
        tab.completionCycle < static_cast<int>(tab.completionCandidates.size()))
    {
        tokenIsCurrentCandidate =
            context.token == tab.completionCandidates[tab.completionCycle];
    }

    bool sameCompletion =
        !tab.completionCandidates.empty() &&
        tab.completionStart == context.start &&
        (tab.completionOriginal == context.token || tokenIsCurrentCandidate);

    if (sameCompletion && tokenIsCurrentCandidate)
    {
        tab.completionCycle =
            (tab.completionCycle + 1) %
            static_cast<int>(tab.completionCandidates.size());

        replaceCompletionToken(
            tab, context,
            tab.completionCandidates[tab.completionCycle]);
        return;
    }

    if (!sameCompletion)
    {
        resetCompletion(tab);
        context = getCompletionContext(tab);

        if (context.token.empty())
        {
            addScreenLine(tab, "Type at least one character before pressing Tab");
            return;
        }

        tab.completionCandidates =
            findCompletionCandidates(context, tab.cwd);
        tab.completionOriginal = context.token;
        tab.completionStart = context.start;
    }

    if (tab.completionCandidates.empty())
    {
        addScreenLine(tab, "No completion found");
        resetCompletion(tab);
        return;
    }

    if (tab.completionCandidates.size() == 1)
    {
        replaceCompletionToken(tab, context, tab.completionCandidates[0]);
        resetCompletion(tab);
        return;
    }

    std::string prefix = commonPrefix(tab.completionCandidates);

    if (prefix.size() > context.token.size())
    {
        replaceCompletionToken(tab, context, prefix);
        tab.completionOriginal = prefix;
        tab.completionStart = context.start;
        tab.completionCandidates =
            findCompletionCandidates(getCompletionContext(tab), tab.cwd);
        tab.completionCycle = -1;
            return;
    }

    tab.completionCycle = 0;
    replaceCompletionToken(
        tab, context, tab.completionCandidates[tab.completionCycle]);
}

void insertInput(TerminalTab &tab, const char *text, int length)
{
    if (length <= 0 || tab.inputLength + length >= MAX_LINE_LENGTH)
        return;

    resetCompletion(tab);

    memmove(tab.inputBuffer + tab.cursorPosition + length,
            tab.inputBuffer + tab.cursorPosition,
            static_cast<size_t>(tab.inputLength - tab.cursorPosition));

    memcpy(tab.inputBuffer + tab.cursorPosition, text,
           static_cast<size_t>(length));

    tab.inputLength += length;
    tab.cursorPosition += length;
    tab.inputBuffer[tab.inputLength] = '\0';
}

void deleteBeforeCursor(TerminalTab &tab)
{
    if (tab.cursorPosition <= 0)
        return;

    resetCompletion(tab);

    memmove(tab.inputBuffer + tab.cursorPosition - 1,
            tab.inputBuffer + tab.cursorPosition,
            static_cast<size_t>(tab.inputLength - tab.cursorPosition));

    tab.cursorPosition--;
    tab.inputLength--;
    tab.inputBuffer[tab.inputLength] = '\0';
}

void deleteAtCursor(TerminalTab &tab)
{
    if (tab.cursorPosition >= tab.inputLength)
        return;

    resetCompletion(tab);

    memmove(tab.inputBuffer + tab.cursorPosition,
            tab.inputBuffer + tab.cursorPosition + 1,
            static_cast<size_t>(tab.inputLength - tab.cursorPosition - 1));

    tab.inputLength--;
    tab.inputBuffer[tab.inputLength] = '\0';
}

void showHistoryEntry(TerminalTab &tab, int direction)
{
    std::vector<std::string> history = historySnapshot();
    if (history.empty())
        return;

    if (tab.historyPosition == -1)
    {
        tab.historyDraft = tab.inputBuffer;
        tab.historyPosition = static_cast<int>(history.size());
    }

    tab.historyPosition += direction;

    if (tab.historyPosition < 0)
        tab.historyPosition = 0;

    if (tab.historyPosition > static_cast<int>(history.size()))
        tab.historyPosition = static_cast<int>(history.size());

    std::string value =
        tab.historyPosition == static_cast<int>(history.size())
            ? tab.historyDraft
            : history[tab.historyPosition];

    if (value.size() >= MAX_LINE_LENGTH)
        value.resize(MAX_LINE_LENGTH - 1);

    tab.inputLength = static_cast<int>(value.size());
    tab.cursorPosition = tab.inputLength;
    memcpy(tab.inputBuffer, value.c_str(), value.size() + 1);
}

// The tab's engine appends the command to the shared history (under the
// mutex or process-shared semaphore) when it receives it; the GUI only resets
// its Up/Down browsing position.
void resetHistoryBrowsing(TerminalTab &tab)
{
    tab.historyPosition = -1;
    tab.historyDraft.clear();
}

void killToStart(TerminalTab &tab)
{
    memmove(tab.inputBuffer,
            tab.inputBuffer + tab.cursorPosition,
            static_cast<size_t>(tab.inputLength - tab.cursorPosition));

    tab.inputLength -= tab.cursorPosition;
    tab.cursorPosition = 0;
    tab.inputBuffer[tab.inputLength] = '\0';
}

void killToEnd(TerminalTab &tab)
{
    tab.inputLength = tab.cursorPosition;
    tab.inputBuffer[tab.inputLength] = '\0';
}

void deletePreviousWord(TerminalTab &tab)
{
    while (tab.cursorPosition > 0 &&
           tab.inputBuffer[tab.cursorPosition - 1] == ' ')
        deleteBeforeCursor(tab);

    while (tab.cursorPosition > 0 &&
           tab.inputBuffer[tab.cursorPosition - 1] != ' ')
        deleteBeforeCursor(tab);
}

bool isValidHotkeyAction(const std::string &action)
{
    return action == "line-start" ||
           action == "line-end" ||
           action == "kill-to-start" ||
           action == "kill-to-end" ||
           action == "delete-word" ||
           action == "clear-screen" ||
           action == "copy" ||
           action == "paste" ||
           action == "reverse-search";
}

bool parseHotkeyModifier(const std::string &name, unsigned int &modifier)
{
    if (name == "Ctrl")
        modifier = ControlMask;
    else if (name == "Shift")
        modifier = ShiftMask;
    else if (name == "Alt")
        modifier = Mod1Mask;
    else
        return false;

    return true;
}

KeySym parseHotkeyKey(const std::string &name)
{
    if (name.empty())
        return NoSymbol;

    KeySym key = XStringToKeysym(name.c_str());

    if (key == NoSymbol)
        return NoSymbol;

    // Store keys in lowercase form; incoming key events are normalized the
    // same way, so Shift / Caps Lock do not break matching.
    KeySym lower, upper;
    XConvertCase(key, &lower, &upper);
    return lower;
}

bool parseHotkeyCombo(const std::string &combo,
                      unsigned int &modifiers,
                      KeySym &key,
                      std::string &error)
{
    std::stringstream stream(combo);
    std::string part;
    std::vector<std::string> pieces;

    while (std::getline(stream, part, '+'))
    {
        if (part.empty())
        {
            error = "empty key name in shortcut";
            return false;
        }
        pieces.push_back(part);
    }

    if (pieces.size() < 2)
    {
        error = "shortcut must include a modifier and a key";
        return false;
    }

    modifiers = 0;

    for (size_t i = 0; i + 1 < pieces.size(); ++i)
    {
        unsigned int modifier = 0;

        if (!parseHotkeyModifier(pieces[i], modifier))
        {
            error = "unknown modifier: " + pieces[i];
            return false;
        }

        if (modifiers & modifier)
        {
            error = "duplicate modifier: " + pieces[i];
            return false;
        }

        modifiers |= modifier;
    }

    key = parseHotkeyKey(pieces.back());

    if (key == NoSymbol)
    {
        error = "unknown key: " + pieces.back();
        return false;
    }

    return true;
}

// Shortcuts handled directly in main() before configurable hotkeys are
// consulted. Binding them would never work, so both the config loader and the
// runtime "bind" command reject them. Any combination that includes Ctrl with
// T/W/C/Z/D/Tab is caught by main() regardless of Shift/Alt, as is Ctrl+Shift+V.
bool isReservedShortcut(unsigned int modifiers, KeySym key)
{
    if (!(modifiers & ControlMask))
        return false;

    if (key == XK_t || key == XK_w || key == XK_c || key == XK_z ||
        key == XK_d || key == XK_Tab)
        return true;

    if ((modifiers & ShiftMask) && key == XK_v)
        return true;

    return false;
}

bool writeDefaultHotkeyConfig(const std::string &path)
{
    std::ofstream file(path);

    if (!file)
        return false;

    file << "bind Ctrl+A line-start\n";
    file << "bind Ctrl+E line-end\n";
    file << "bind Ctrl+U kill-to-start\n";
    file << "bind Ctrl+K kill-to-end\n";
    file << "bind Alt+BackSpace delete-word\n";
    file << "bind Ctrl+L clear-screen\n";
    file << "bind Ctrl+R reverse-search\n";

    return static_cast<bool>(file);
}

std::string hotkeyComboToString(const Hotkey &hotkey)
{
    std::string combo;
    if (hotkey.modifiers & ControlMask) combo += "Ctrl+";
    if (hotkey.modifiers & ShiftMask) combo += "Shift+";
    if (hotkey.modifiers & Mod1Mask) combo += "Alt+";
    const char *name = XKeysymToString(hotkey.key);
    if (name) combo += name;
    return combo;
}

bool saveHotkeyConfiguration()
{
    if (configPath.empty()) return false;
    std::string tempPath = configPath + ".tmp";
    std::ofstream file(tempPath, std::ios::trunc);
    if (!file) return false;

    for (const Hotkey &hotkey : hotkeys)
        file << "bind " << hotkeyComboToString(hotkey)
             << " " << hotkey.action << '\n';

    file.close();
    if (!file || rename(tempPath.c_str(), configPath.c_str()) != 0)
    {
        unlink(tempPath.c_str());
        return false;
    }
    return true;
}

// Shared by ~/.terminator loading and the runtime "bind" command.
// Returns an error message, or "" when the binding is valid.
std::string validateBinding(const std::string &combo, const std::string &action,
                            unsigned int &modifiers, KeySym &key)
{
    std::string error;
    if (!parseHotkeyCombo(combo, modifiers, key, error))
        return error;
    if (!isValidHotkeyAction(action))
        return "unknown action '" + action + "'";
    if (isReservedShortcut(modifiers, key))
        return "shortcut '" + combo + "' is reserved by the terminal";
    return "";
}

bool handleRuntimeBindCommand(TerminalTab &tab, const std::string &command)
{
    std::istringstream input(command);
    std::string directive, combo, action, extra;
    if (!(input >> directive) || directive != "bind")
        return false;
    if (!(input >> combo >> action) || (input >> extra))
    {
        addScreenLine(tab, "Usage: bind Ctrl+H reverse-search");
        return true;
    }
    unsigned int modifiers = 0;
    KeySym key = NoSymbol;
    std::string error = validateBinding(combo, action, modifiers, key);
    if (!error.empty())
    {
        addScreenLine(tab, ("bind: " + error).c_str());
        return true;
    }
    // One shortcut per key and one key per action.
    hotkeys.erase(std::remove_if(hotkeys.begin(), hotkeys.end(), [&](const Hotkey &h) {
                      return (h.key == key && h.modifiers == modifiers) || h.action == action;
                  }), hotkeys.end());
    hotkeys.push_back({modifiers, key, action});
    addScreenLine(tab, saveHotkeyConfiguration()
                           ? ("Hotkey updated and saved: " + combo + " -> " + action).c_str()
                           : "Hotkey updated in memory, but saving ~/.terminator failed");
    return true;
}


int selectionPositionFromMouse(const TerminalTab &tab, int x, int y)
{
    int row = (y - CONTENT_START_Y + LINE_HEIGHT / 2) / LINE_HEIGHT;
    int col = (x - 20 + TERMINAL_CHAR_WIDTH / 2) / TERMINAL_CHAR_WIDTH;

    if (row < 0) row = 0;
    if (row >= tab.screenLineCount)
        row = tab.screenLineCount > 0 ? tab.screenLineCount - 1 : 0;

    int lineLength = row < tab.screenLineCount
                         ? static_cast<int>(strlen(tab.screenBuffer[row])) : 0;
    if (col < 0) col = 0;
    if (col > lineLength) col = lineLength;

    return row * MAX_SCREEN_LINE_LENGTH + col;
}

std::string getSelectedTerminalText(const TerminalTab &tab)
{
    if (!textSelection.active || textSelection.tabIndex < 0)
        return "";

    int first = std::min(textSelection.startPosition, textSelection.endPosition);
    int last = std::max(textSelection.startPosition, textSelection.endPosition);
    int firstRow = first / MAX_SCREEN_LINE_LENGTH;
    int firstCol = first % MAX_SCREEN_LINE_LENGTH;
    int lastRow = last / MAX_SCREEN_LINE_LENGTH;
    int lastCol = last % MAX_SCREEN_LINE_LENGTH;

    if (firstRow >= tab.screenLineCount || lastRow >= tab.screenLineCount)
        return "";

    std::string result;
    for (int row = firstRow; row <= lastRow; ++row)
    {
        int length = static_cast<int>(strlen(tab.screenBuffer[row]));
        int begin = row == firstRow ? firstCol : 0;
        int end = row == lastRow ? lastCol : length;
        begin = std::min(begin, length);
        end = std::min(end, length);
        if (end > begin)
            result.append(tab.screenBuffer[row] + begin,
                          static_cast<size_t>(end - begin));
        if (row != lastRow)
            result += '\n';
    }
    return result;
}

// Copies the current mouse selection if there is one, otherwise the input
// line. Shared by the built-in Ctrl+Shift+C and the configurable "copy" action.
void copySelectionOrInput(Display *display, Window window,
                          const TerminalTab &tab, int tabIndex)
{
    if (textSelection.active && textSelection.tabIndex == tabIndex)
    {
        std::string selected = getSelectedTerminalText(tab);
        if (!selected.empty())
        {
            setClipboardText(display, window, selected);
            return;
        }
    }

    setClipboardText(display, window,
                     std::string(tab.inputBuffer, tab.inputLength));
}

// Keeps the selection pointing at the right tab after a tab is closed and
// the tabs after it shift down by one.
void adjustSelectionForClosedTab(int closedIndex)
{
    if (textSelection.tabIndex == closedIndex)
    {
        textSelection.active = false;
        textSelection.dragging = false;
        textSelection.tabIndex = -1;
    }
    else if (textSelection.tabIndex > closedIndex)
        textSelection.tabIndex--;
}

bool loadHotkeyConfiguration(TerminalTab &tab)
{
    const char *home = getenv("HOME");

    if (home == nullptr || *home == '\0')
    {
        addScreenLine(tab, "Hotkey config: HOME environment variable is not set");
        return false;
    }

    configPath = std::string(home) + "/.terminator";

    std::ifstream file(configPath);

    if (!file)
    {
        if (!writeDefaultHotkeyConfig(configPath))
        {
            addScreenLine(tab, "Hotkey config: could not create ~/.terminator");
            return false;
        }

        addScreenLine(tab, "Created default ~/.terminator configuration");
        file.open(configPath);
    }

    if (!file)
    {
        addScreenLine(tab, "Hotkey config: could not open ~/.terminator");
        return false;
    }

    hotkeys.clear();

    std::string line;
    int lineNumber = 0;
    int validCount = 0;

    while (std::getline(file, line))
    {
        ++lineNumber;
        size_t first = line.find_first_not_of(" \t\r");
        if (first == std::string::npos || line[first] == '#')
            continue;

        std::istringstream input(line);
        std::string directive, combo, action, extra, error;
        unsigned int modifiers = 0;
        KeySym key = NoSymbol;
        if (!(input >> directive >> combo >> action) || (input >> extra))
            error = "invalid format";
        else if (directive != "bind")
            error = "expected 'bind'";
        else
            error = validateBinding(combo, action, modifiers, key);
        for (const Hotkey &existing : hotkeys)
            if (error.empty() && existing.key == key && existing.modifiers == modifiers)
                error = "duplicate shortcut '" + combo + "'";
        if (!error.empty())
        {
            addScreenLine(tab, ("Config line " + std::to_string(lineNumber) + ": " + error).c_str());
            continue;   // invalid line: the default stays
        }

        // One shortcut per action: a later line for the same action replaces the earlier one.
        size_t before = hotkeys.size();
        hotkeys.erase(std::remove_if(hotkeys.begin(), hotkeys.end(),
                                     [&](const Hotkey &h) { return h.action == action; }),
                      hotkeys.end());
        if (hotkeys.size() != before)
            addScreenLine(tab, ("Config line " + std::to_string(lineNumber) + ": '" + action +
                                "' rebound, earlier shortcut removed").c_str());
        hotkeys.push_back({modifiers, key, action});
        validCount = static_cast<int>(hotkeys.size());
    }

    addScreenLine(tab, validCount == 0 ? "Hotkey config: no valid bindings were loaded"
                                       : ("Loaded " + std::to_string(validCount) + " hotkey bindings").c_str());
    return validCount > 0;
}

// Length of the longest common substring of a and b.
size_t longestCommonSubstring(const std::string &a, const std::string &b)
{
    std::vector<size_t> previous(b.size() + 1, 0), current(b.size() + 1, 0);
    size_t best = 0;
    for (size_t i = 1; i <= a.size(); ++i)
    {
        for (size_t j = 1; j <= b.size(); ++j)
        {
            current[j] = a[i - 1] == b[j - 1] ? previous[j - 1] + 1 : 0;
            best = std::max(best, current[j]);
        }
        std::swap(previous, current);
    }
    return best;
}


// Ctrl+R: scan from newest to oldest for an exact match; if there is none,
// pick the entry with the longest common substring longer than 2 characters.
// Pressing Ctrl+R again continues with older entries.
void updateReverseSearch(TerminalTab &tab, bool older)
{
    std::vector<std::string> history = historySnapshot();
    int start = static_cast<int>(history.size());
    if (older && tab.reverseSearchMatch >= 0)
        start = tab.reverseSearchMatch;

    tab.reverseSearchMatch = -1;
    if (tab.reverseSearchQuery.empty())
        return;
    for (int i = start - 1; i >= 0; --i)
        if (history[i] == tab.reverseSearchQuery)
        {
            tab.reverseSearchMatch = i;
            return;
        }
    size_t bestLength = 2;
    for (int i = start - 1; i >= 0; --i)
    {
        size_t length = longestCommonSubstring(history[i], tab.reverseSearchQuery);
        if (length > bestLength)
        {
            bestLength = length;
            tab.reverseSearchMatch = i;
        }
    }
}


// True if this key press matches whatever shortcut is currently bound to the
// "reverse-search" action (so "next older match" follows the user's binding
// instead of being hardcoded to Ctrl+R).
bool isReverseSearchHotkey(KeySym key, unsigned int state)
{
    const unsigned int relevantModifiers =
        ControlMask | ShiftMask | Mod1Mask;

    KeySym lower, upper;
    XConvertCase(key, &lower, &upper);

    for (const Hotkey &hotkey : hotkeys)
    {
        if (hotkey.action == "reverse-search" &&
            hotkey.key == lower &&
            hotkey.modifiers == (state & relevantModifiers))
            return true;
    }

    return false;
}

bool handleReverseSearchKey(TerminalTab &tab, KeySym key,
                            const char *text, int length, bool control,
                            unsigned int state)
{
    if (!tab.reverseSearchActive)
        return false;

    if (key == XK_Escape ||
        (control && (key == XK_g || key == XK_G ||
                     key == XK_c || key == XK_C)))
    {
        tab.reverseSearchActive = false;
        tab.reverseSearchQuery.clear();
        tab.reverseSearchMatch = -1;
        return true;
    }

    if (key == XK_Return || key == XK_KP_Enter)
    {
        std::vector<std::string> history = historySnapshot();
        if (tab.reverseSearchMatch >= 0 &&
            tab.reverseSearchMatch < static_cast<int>(history.size()))
        {
            const std::string &match = history[tab.reverseSearchMatch];
            size_t n = match.size();
            if (n >= MAX_LINE_LENGTH)
                n = MAX_LINE_LENGTH - 1;
            memcpy(tab.inputBuffer, match.data(), n);
            tab.inputBuffer[n] = '\0';
            tab.inputLength = static_cast<int>(n);
            tab.cursorPosition = tab.inputLength;
        }
        tab.reverseSearchActive = false;
        tab.reverseSearchQuery.clear();
        tab.reverseSearchMatch = -1;
        return true;
    }

    if (isReverseSearchHotkey(key, state))
    {
        updateReverseSearch(tab, true);
        return true;
    }

    if (key == XK_BackSpace)
    {
        if (!tab.reverseSearchQuery.empty())
            tab.reverseSearchQuery.pop_back();
        updateReverseSearch(tab, false);
        return true;
    }

    if (length > 0 && !control)
    {
        for (int i = 0; i < length; ++i)
        {
            unsigned char ch = static_cast<unsigned char>(text[i]);
            if (ch >= 32 && ch != 127)
                tab.reverseSearchQuery += text[i];
        }
        updateReverseSearch(tab, false);
        return true;
    }

    return true;
}

bool executeConfiguredHotkey(Display *display,
                             Window window,
                             TerminalTab &tab,
                             int tabIndex,
                             KeySym key,
                             unsigned int state)
{
    const unsigned int relevantModifiers =
        ControlMask | ShiftMask | Mod1Mask;

    unsigned int modifiers = state & relevantModifiers;

    // With Shift or Caps Lock the server reports e.g. XK_C instead of XK_c.
    KeySym lowerKey, upperKey;
    XConvertCase(key, &lowerKey, &upperKey);

    for (const Hotkey &hotkey : hotkeys)
    {
        if (hotkey.key != lowerKey || hotkey.modifiers != modifiers)
            continue;

        const std::string &action = hotkey.action;

        if (action == "line-start")
            tab.cursorPosition = 0;
        else if (action == "line-end")
            tab.cursorPosition = tab.inputLength;
        else if (action == "kill-to-start")
            killToStart(tab);
        else if (action == "kill-to-end")
            killToEnd(tab);
        else if (action == "delete-word")
            deletePreviousWord(tab);
        else if (action == "clear-screen")
        {
            tab.screenLineCount = 0;
            textSelection.active = false;
            textSelection.dragging = false;
        }
        else if (action == "copy")
            copySelectionOrInput(display, window, tab, tabIndex);
        else if (action == "paste")
            requestClipboardPaste(display, window);
        else if (action == "reverse-search")
        {
            tab.reverseSearchActive = true;
            tab.reverseSearchQuery.clear();
            tab.reverseSearchMatch = -1;
        }

        return true;
    }

    return false;
}
int main(int argc, char *argv[])
{
    signal(SIGPIPE, SIG_IGN);

    // ./terminator                      -> Thread Mode (default)
    // ./terminator useProcess = True    -> Process Mode
    // (also accepted: useProcess=True, --mode thread|process)
    std::string arguments;
    for (int i = 1; i < argc; ++i)
        arguments += argv[i];
    for (char &c : arguments)
        c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    if (arguments.empty() || arguments == "useprocess=false" || arguments == "--modethread" ||
        arguments == "--mode=thread")
        executionMode = ExecutionMode::Thread;
    else if (arguments == "useprocess=true" || arguments == "--modeprocess" || arguments == "--mode=process")
        executionMode = ExecutionMode::Process;
    else
    {
        std::cerr << "Usage: " << argv[0] << " [useProcess = True]\n";
        return 2;
    }

    long openMax = sysconf(_SC_OPEN_MAX);
    maxDescriptorToClose = openMax > 0 && openMax < 4096
                               ? static_cast<int>(openMax) : 4096;

    if (!initializeSharedHistory())
    {
        std::cerr << "Could not initialize shared command history\n";
        return 1;
    }
    loadCommandHistory();

    std::string startDirectory;
    {
        char buffer[4096];
        if (getcwd(buffer, sizeof(buffer)) != nullptr)
            startDirectory = buffer;
        else
        {
            const char *home = getenv("HOME");
            startDirectory = home ? home : "/";
        }
    }

    Display *display = XOpenDisplay(NULL);

    if (display == NULL)
    {
        std::cout << "Cannot connect to X server\n";
        destroySharedHistory();
        return 1;
    }

    xConnectionFd = ConnectionNumber(display);
    setCloseOnExec(xConnectionFd);

    int screen = DefaultScreen(display);

    Window window = XCreateSimpleWindow(
        display,
        RootWindow(display, screen),
        100, 100,
        WINDOW_WIDTH, WINDOW_HEIGHT,
        1,
        BlackPixel(display, screen),
        WhitePixel(display, screen));

    XStoreName(display, window, "Terminal");

    // Let the window manager's close button send us a message instead of
    // killing the connection, so we can stop the tab engines cleanly.
    wmDeleteAtom = XInternAtom(display, "WM_DELETE_WINDOW", False);
    XSetWMProtocols(display, window, &wmDeleteAtom, 1);

    GC gc = XCreateGC(display, window, 0, NULL);

    clipboardAtom = XInternAtom(display, "CLIPBOARD", False);
    utf8StringAtom = XInternAtom(display, "UTF8_STRING", False);
    targetsAtom = XInternAtom(display, "TARGETS", False);
    clipboardProperty = XInternAtom(display, "X11_TERMINAL_CLIPBOARD", False);

    XSelectInput(display, window,
                 KeyPressMask | ExposureMask | ButtonPressMask |
                 ButtonReleaseMask | PointerMotionMask);

    XMapWindow(display, window);

    unsigned long selectedColor =
        getColor(display, screen, "#2563EB", BlackPixel(display, screen));
    unsigned long inactiveColor =
        getColor(display, screen, "#444444", BlackPixel(display, screen));
    unsigned long inactiveText =
        getColor(display, screen, "#DDDDDD", WhitePixel(display, screen));

    if (!initializeChildSignalPipe())
    {
        std::cerr << "Could not initialize SIGCHLD self-pipe\n";
        XFreeGC(display, gc);
        XDestroyWindow(display, window);
        XCloseDisplay(display);
        destroySharedHistory();
        return 1;
    }

    TerminalTab tabs[MAX_TABS];
    int tabCount = 1;
    int currentTab = 0;

    if (!startWorker(tabs[0], startDirectory))
    {
        std::cerr << "Could not start the tab's command engine\n";
        XFreeGC(display, gc);
        XDestroyWindow(display, window);
        XCloseDisplay(display);
        close(childSignalPipe[0]);
        close(childSignalPipe[1]);
        childSignalPipe[0] = childSignalPipe[1] = -1;
        destroySharedHistory();
        return 1;
    }

    loadHotkeyConfiguration(tabs[0]);

    bool running = true;
    XEvent event;

    auto redraw = [&]() {
        drawScreen(display, window, gc, screen,
                   tabs, tabCount, currentTab,
                   selectedColor, inactiveColor, inactiveText);
    };

    // Tabs whose engine ran "exit" (or Ctrl+D on an empty line) close here.
    auto closeRequestedTabs = [&]() {
        bool changed = false;
        for (int i = tabCount - 1; i >= 0; --i)
        {
            if (!tabs[i].closeRequested)
                continue;
            changed = true;
            if (tabCount > 1)
                closeTab(tabs, tabCount, currentTab, i);
            else
            {
                tabs[i].closeRequested = false;
                running = false;
            }
        }
        return changed;
    };

    auto clearInputLine = [](TerminalTab &tab) {
        tab.inputLength = 0;
        tab.cursorPosition = 0;
        tab.inputBuffer[0] = '\0';
        resetCompletion(tab);
    };

    while (running)
    {
        if (XPending(display) == 0)
        {
            std::vector<pollfd> fds;
            std::vector<int> outputTabs;
            pollfd xfd{};
            xfd.fd = ConnectionNumber(display);
            xfd.events = POLLIN;
            fds.push_back(xfd);
            outputTabs.push_back(-1);

            pollfd childFd{};
            childFd.fd = childSignalPipe[0];
            childFd.events = POLLIN;
            fds.push_back(childFd);
            outputTabs.push_back(-2);

            for (int i = 0; i < tabCount; ++i)
            {
                if (tabs[i].workerOutputFd == -1)
                    continue;
                pollfd pfd{};
                pfd.fd = tabs[i].workerOutputFd;
                pfd.events = POLLIN | POLLHUP | POLLERR;
                fds.push_back(pfd);
                outputTabs.push_back(i);
            }

            int ready = poll(fds.data(), fds.size(), -1);
            if (ready == -1)
            {
                if (errno == EINTR)
                    continue;
                addScreenLine(tabs[currentTab], "Error: poll() failed");
                redraw();
                continue;
            }

            bool currentChanged = false;
            for (size_t i = 1; i < fds.size(); ++i)
            {
                if (!(fds[i].revents & (POLLIN | POLLHUP | POLLERR)))
                    continue;

                if (outputTabs[i] == -2)
                {
                    reapExitedChildren(tabs, tabCount);
                    continue;
                }

                int tabIndex = outputTabs[i];
                if (tabs[tabIndex].workerOutputFd == -1)
                    continue;
                if (readEngineOutput(tabs[tabIndex]) && tabIndex == currentTab)
                    currentChanged = true;
            }

            if (closeRequestedTabs())
                currentChanged = true;
            if (!running)
                break;
            if (currentChanged)
                redraw();

            if (!(fds[0].revents & POLLIN) && XPending(display) == 0)
                continue;
        }

        XNextEvent(display, &event);

        if (event.type == Expose)
            redraw();
        else if (event.type == ClientMessage)
        {
            if (static_cast<Atom>(event.xclient.data.l[0]) == wmDeleteAtom)
                running = false;
        }
        else if (event.type == ButtonPress)
        {
            int x = event.xbutton.x;
            int y = event.xbutton.y;

            if (y >= 0 && y < TAB_HEIGHT && x >= 0)
            {
                int clickedTab = x / TAB_WIDTH;

                if (clickedTab < tabCount)
                {
                    int positionInsideTab = x % TAB_WIDTH;

                    if (positionInsideTab >= TAB_WIDTH - 25)
                    {
                        if (tabCount > 1)
                            closeTab(tabs, tabCount, currentTab, clickedTab);
                    }
                    else
                        currentTab = clickedTab;
                }
            }
            else if (y >= CONTENT_START_Y && event.xbutton.button == Button1)
            {
                TerminalTab &tab = tabs[currentTab];
                int position = selectionPositionFromMouse(tab, x, y);
                textSelection.active = tab.screenLineCount > 0;
                textSelection.dragging = textSelection.active;
                textSelection.tabIndex = currentTab;
                textSelection.startPosition = position;
                textSelection.endPosition = position;
            }

            redraw();
        }
        else if (event.type == MotionNotify)
        {
            if (textSelection.dragging && textSelection.tabIndex == currentTab)
            {
                textSelection.endPosition =
                    selectionPositionFromMouse(tabs[currentTab],
                                               event.xmotion.x, event.xmotion.y);
                redraw();
            }
        }
        else if (event.type == ButtonRelease)
        {
            if (textSelection.dragging && event.xbutton.button == Button1)
            {
                textSelection.endPosition =
                    selectionPositionFromMouse(tabs[currentTab],
                                               event.xbutton.x, event.xbutton.y);
                textSelection.dragging = false;
                if (textSelection.startPosition == textSelection.endPosition)
                    textSelection.active = false;
                redraw();
            }
        }
        else if (event.type == SelectionRequest)
            handleSelectionRequest(display, event.xselectionrequest);
        else if (event.type == SelectionNotify)
        {
            if (tabCount > 0)
            {
                handleSelectionNotify(display, event.xselection, tabs[currentTab]);
                redraw();
            }
        }
        else if (event.type == KeyPress)
        {
            char buffer[10];
            KeySym keysym;

            int length = XLookupString(
                &event.xkey, buffer, sizeof(buffer), &keysym, NULL);

            bool controlPressed =
                (event.xkey.state & ControlMask) != 0;

            if (controlPressed && (keysym == XK_t || keysym == XK_T))
            {
                if (tabCount < MAX_TABS)
                {
                    tabs[tabCount] = TerminalTab{};

                    // A new tab starts in the current tab's directory.
                    if (startWorker(tabs[tabCount], tabs[currentTab].cwd))
                    {
                        currentTab = tabCount;
                        tabCount++;
                    }
                    else
                    {
                        stopWorker(tabs[tabCount]);
                        tabs[tabCount] = TerminalTab{};
                        addScreenLine(tabs[currentTab],
                                      "Error: could not create a new tab");
                    }
                }
                else
                {
                    addScreenLine(tabs[currentTab],
                                  "Maximum tab limit reached");
                }
            }
            else if (controlPressed && keysym == XK_Tab)
            {
                if (tabCount > 1)
                    currentTab = (currentTab + 1) % tabCount;
            }
            else if (controlPressed && (keysym == XK_w || keysym == XK_W))
            {
                if (tabCount > 1)
                    closeTab(tabs, tabCount, currentTab, currentTab);
                else
                    addScreenLine(tabs[currentTab],
                                  "Cannot close the last tab");
            }
            else if (controlPressed &&
                     (event.xkey.state & ShiftMask) &&
                     (keysym == XK_c || keysym == XK_C))
            {
                copySelectionOrInput(display, window, tabs[currentTab],
                                     currentTab);
            }
            else if (controlPressed &&
                     (event.xkey.state & ShiftMask) &&
                     (keysym == XK_v || keysym == XK_V))
            {
                requestClipboardPaste(display, window);
            }
            else if (controlPressed && (keysym == XK_c || keysym == XK_C || keysym == XK_z || keysym == XK_Z) &&
                     !tabs[currentTab].reverseSearchActive)
            {
                // There is no terminal driver: Ctrl+C / Ctrl+Z are X11 key events,
                // and the tab's engine turns them into kill(-pgid, SIGINT / SIGTSTP).
                TerminalTab &tab = tabs[currentTab];
                bool interrupt = keysym == XK_c || keysym == XK_C;
                std::string echoed = std::string(tab.inputBuffer, tab.inputLength) + (interrupt ? "^C" : "^Z");
                if (tab.commandRunning)
                {
                    int signalNumber = interrupt ? SIGINT : SIGTSTP;
                    sendWorkerMessage(tab, WorkerSignal, reinterpret_cast<const char *>(&signalNumber),
                                      sizeof(signalNumber));
                    addScreenLine(tab, (tab.asynchronousOutputLine + echoed).c_str());
                    tab.asynchronousOutputLine.clear();
                    clearInputLine(tab);
                }
                else if (interrupt)
                {
                    addScreenLine(tab, ((tab.continuationMode ? "> " : promptString(tab)) + echoed).c_str());
                    tab.commandBuffer.clear();
                    tab.continuationMode = false;
                    clearInputLine(tab);
                }
            }
            else if (controlPressed && (keysym == XK_d || keysym == XK_D))
            {
                TerminalTab &tab = tabs[currentTab];
                if (tab.commandRunning)
                {
                    // Like a terminal: pending text is flushed, an empty
                    // line means end-of-file for the program's stdin.
                    if (tab.inputLength > 0)
                    {
                        sendWorkerMessage(tab, WorkerInput, tab.inputBuffer,
                                          static_cast<size_t>(tab.inputLength));
                        tab.asynchronousOutputLine.append(tab.inputBuffer,
                                                          tab.inputLength);
                        clearInputLine(tab);
                    }
                    else
                        sendWorkerMessage(tab, WorkerEof, nullptr, 0);
                }
                else if (tab.inputLength == 0 && !tab.continuationMode)
                {
                    tab.closeRequested = true;
                    closeRequestedTabs();
                }
                else
                    deleteAtCursor(tab);
            }
            else if (keysym == XK_Escape && !tabs[currentTab].commandRunning &&
                     !tabs[currentTab].reverseSearchActive)
            {
                TerminalTab &tab = tabs[currentTab];

                if (tab.continuationMode || !tab.commandBuffer.empty())
                {
                    tab.commandBuffer.clear();
                    tab.continuationMode = false;
                    clearInputLine(tab);
                    addScreenLine(tab, "Multiline command cancelled");
                }
                else
                    running = false;
            }
            else
            {
                TerminalTab &tab = tabs[currentTab];

                if (!tab.commandRunning &&
                    handleReverseSearchKey(tab, keysym, buffer, length,
                                           controlPressed, event.xkey.state))
                {
                }
                else if (executeConfiguredHotkey(display, window, tab,
                                                 currentTab, keysym,
                                                 event.xkey.state))
                    tab.reverseSearchActive = tab.reverseSearchActive && !tab.commandRunning;
                else if (keysym == XK_Tab)
                {
                    if (!tab.commandRunning)
                        handleAutoComplete(tab);
                }
                else if (keysym == XK_Left)
                {
                    resetCompletion(tab);
                    if (tab.cursorPosition > 0)
                        tab.cursorPosition--;
                }
                else if (keysym == XK_Right)
                {
                    resetCompletion(tab);
                    if (tab.cursorPosition < tab.inputLength)
                        tab.cursorPosition++;
                }
                else if (keysym == XK_Up && !tab.commandRunning)
                {
                    resetCompletion(tab);
                    showHistoryEntry(tab, -1);
                }
                else if (keysym == XK_Down && !tab.commandRunning)
                {
                    resetCompletion(tab);
                    showHistoryEntry(tab, 1);
                }
                else if (keysym == XK_Home)
                {
                    resetCompletion(tab);
                    tab.cursorPosition = 0;
                }
                else if (keysym == XK_End)
                {
                    resetCompletion(tab);
                    tab.cursorPosition = tab.inputLength;
                }
                else if (keysym == XK_Delete)
                    deleteAtCursor(tab);
                else if (keysym == XK_BackSpace)
                    deleteBeforeCursor(tab);
                else if ((keysym == XK_Return || keysym == XK_KP_Enter) && tab.commandRunning)
                {
                    // A program is running: the typed line becomes its stdin
                    // (canonical mode, done by Terminator since there is no tty).
                    std::string line(tab.inputBuffer, tab.inputLength);
                    addScreenLine(tab, (tab.asynchronousOutputLine + line).c_str());
                    tab.asynchronousOutputLine.clear();
                    line += '\n';
                    sendWorkerMessage(tab, WorkerInput, line.data(), line.size());
                    clearInputLine(tab);
                }
                else if (keysym == XK_Return || keysym == XK_KP_Enter)
                {
                    std::string prompt = tab.continuationMode
                                             ? "> "
                                             : promptString(tab);
                    addScreenLine(tab, (prompt + tab.inputBuffer).c_str());

                    tab.commandBuffer += tab.inputBuffer;
                    tab.commandBuffer += '\n';
                    clearInputLine(tab);

                    // Our own parser decides whether the command is finished
                    // (open quote, trailing |, \, $(, missing fi/done ...).
                    if (isCommandComplete(tab.commandBuffer))
                    {
                        std::string completeCommand = tab.commandBuffer;
                        tab.commandBuffer.clear();
                        tab.continuationMode = false;
                        resetHistoryBrowsing(tab);

                        bool onlyWhitespace =
                            completeCommand.find_first_not_of(" \t\r\n") ==
                            std::string::npos;
                        if (!onlyWhitespace &&
                            !handleRuntimeBindCommand(tab, completeCommand))
                            executeCommand(tab, completeCommand);
                    }
                    else
                        tab.continuationMode = true;
                }
                else if (length > 0 && !controlPressed &&
                         static_cast<unsigned char>(buffer[0]) >= 32)
                {
                    insertInput(tab, buffer, length);
                }
            }

            if (running)
                redraw();
        }
    }

    for (int i = 0; i < tabCount; i++)
        stopWorker(tabs[i]);

    signal(SIGCHLD, SIG_DFL);
    close(childSignalPipe[0]);
    close(childSignalPipe[1]);
    childSignalPipe[0] = childSignalPipe[1] = -1;

    destroySharedHistory();

    XFreeGC(display, gc);
    XDestroyWindow(display, window);
    XCloseDisplay(display);
    
    return 0;
}