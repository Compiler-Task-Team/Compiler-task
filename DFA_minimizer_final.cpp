// DFA minimization with the Myhill-Nerode (table-filling) algorithm.
//
// Algorithm (as on the board):
//   iter 1 : mark every pair that differs on acceptance (final vs non-final,
//            or two different token types)
//   iter t : mark a pair {p,q} if for some symbol c, {delta(p,c), delta(q,c)}
//            was marked in iteration t-1
//   stop   : when an iteration marks nothing new; unmarked pairs are equivalent
//
// Instead of re-scanning every pair in every iteration (O(n^3 |Sigma|) in the
// worst case), each iteration only follows the PREDECESSORS of the pairs
// marked in the previous one. Every (a, b, c) triple is visited once, so the
// total is O(n^2 |Sigma|) and the iteration numbers are exactly the board's.
//
// Pipeline: read+validate -> drop unreachable states -> add dead state E if
// the DFA is partial -> table filling -> merge classes -> drop E -> renumber.
//
// Input (whitespace separated):
//   n k
//   sym_0 ... sym_{k-1}        symbols are strings: a b letter digit id ...
//   start f
//   s_1 ... s_f                final states; "s:t" gives state s token type t
//   n rows of k ints           next[state][symbol], -1 = no transition
//
// The result is printed in the same format, so it can be fed back in.
//
// Usage: ./dfa [--raw] [--table] [--keep-dead] [--demo N] < input.txt
//   --raw        print only the minimized DFA in input format
//   --table      print the iteration table (v = equivalent so far, X = marked)
//   --keep-dead  keep the dead state E in the output
//   --demo N     run demo DFA N (1-4 are the board examples, 5 uses tokens)

#include <cstdlib>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
using namespace std;

struct DFA {
    int n = 0, k = 0, start = 0;
    vector<string> alphabet;
    vector<int> label;         // -1 = non-accepting, >= 0 = token type
    vector<vector<int>> next;  // -1 = missing transition
};

// ---------------------------------------------------------------- input ---

static bool parseInt(const string& s, int& out) {
    char* end = nullptr;
    long v = strtol(s.c_str(), &end, 10);
    if (s.empty() || *end != '\0') return false;
    out = static_cast<int>(v);
    return true;
}

static bool readDFA(istream& in, DFA& d, string& err) {
    int n, k, f;
    if (!(in >> n >> k) || n <= 0 || k <= 0) { err = "n and k must be positive"; return false; }
    d.n = n;
    d.k = k;
    d.alphabet.resize(k);
    set<string> seen;
    for (auto& s : d.alphabet) {
        if (!(in >> s)) { err = "could not read the alphabet"; return false; }
        if (!seen.insert(s).second) { err = "duplicate symbol '" + s + "'"; return false; }
    }
    if (!(in >> d.start >> f) || d.start < 0 || d.start >= n || f < 0 || f > n) {
        err = "invalid start state or number of final states";
        return false;
    }
    d.label.assign(n, -1);
    for (int i = 0; i < f; i++) {
        string tok;
        if (!(in >> tok)) { err = "could not read final states"; return false; }
        size_t colon = tok.find(':');
        int state, token = 0;
        bool ok = parseInt(tok.substr(0, colon), state);
        if (ok && colon != string::npos) ok = parseInt(tok.substr(colon + 1), token);
        if (!ok || state < 0 || state >= n || token < 0) {
            err = "invalid final state '" + tok + "'";
            return false;
        }
        d.label[state] = token;
    }
    d.next.assign(n, vector<int>(k));
    for (int i = 0; i < n; i++)
        for (int c = 0; c < k; c++) {
            if (!(in >> d.next[i][c])) { err = "transition table is incomplete"; return false; }
            if (d.next[i][c] < -1 || d.next[i][c] >= n) {
                err = "transition target out of range at state " + to_string(i);
                return false;
            }
        }
    return true;
}

// ----------------------------------------------------------- transforms ---

// Keeps states reachable from start, renumbered in BFS order (start = 0).
// newToOld[i] = index of state i in `d`.
static DFA keepReachable(const DFA& d, vector<int>& newToOld) {
    vector<int> oldToNew(d.n, -1);
    newToOld.assign(1, d.start);
    oldToNew[d.start] = 0;
    for (size_t head = 0; head < newToOld.size(); head++) {
        int u = newToOld[head];
        for (int c = 0; c < d.k; c++) {
            int v = d.next[u][c];
            if (v >= 0 && oldToNew[v] < 0) {
                oldToNew[v] = newToOld.size();
                newToOld.push_back(v);
            }
        }
    }
    DFA r;
    r.n = newToOld.size();
    r.k = d.k;
    r.alphabet = d.alphabet;
    r.start = 0;
    r.label.resize(r.n);
    r.next.assign(r.n, vector<int>(r.k));
    for (int i = 0; i < r.n; i++) {
        int o = newToOld[i];
        r.label[i] = d.label[o];
        for (int c = 0; c < r.k; c++) {
            int v = d.next[o][c];
            r.next[i][c] = v < 0 ? -1 : oldToNew[v];
        }
    }
    return r;
}

// Adds the dead (error) state E if some transition is missing.
static bool completeWithDeadState(DFA& d) {
    bool missing = false;
    for (auto& row : d.next)
        for (int v : row) missing |= (v < 0);
    if (!missing) return false;
    int dead = d.n++;
    d.label.push_back(-1);
    d.next.push_back(vector<int>(d.k, dead));
    for (auto& row : d.next)
        for (int& v : row)
            if (v < 0) v = dead;
    return true;
}

// ------------------------------------------------- Myhill-Nerode table ---

// Triangular table: level = iteration in which the pair was marked
// (1, 2, 3, ...), or 0 if it was never marked (= the states are equivalent).
struct Levels {
    int m;
    vector<int> level;
    explicit Levels(int m) : m(m), level(static_cast<size_t>(m) * (m - 1) / 2, 0) {}
    size_t id(int i, int j) const {
        if (i < j) swap(i, j);
        return static_cast<size_t>(i) * (i - 1) / 2 + j;
    }
    int get(int i, int j) const { return level[id(i, j)]; }
    void set(int i, int j, int v) { level[id(i, j)] = v; }
};

using Pairs = vector<pair<int, int>>;

// Fills the table iteration by iteration and returns the per-iteration lists
// of newly marked pairs (perIter[t-1] = pairs marked in iteration t).
// Requires a complete DFA.
static vector<Pairs> fillTable(const DFA& d, Levels& t) {
    int m = d.n;
    vector<vector<vector<int>>> pred(d.k, vector<vector<int>>(m));
    for (int s = 0; s < m; s++)
        for (int c = 0; c < d.k; c++) pred[c][d.next[s][c]].push_back(s);

    vector<Pairs> perIter;
    Pairs first;
    for (int i = 0; i < m; i++)
        for (int j = 0; j < i; j++)
            if (d.label[i] != d.label[j]) {
                t.set(i, j, 1);
                first.push_back({j, i});
            }
    if (!first.empty()) perIter.push_back(first);

    while (!perIter.empty()) {
        int iter = perIter.size() + 1;
        Pairs fresh;
        for (auto [p, q] : perIter.back())
            for (int c = 0; c < d.k; c++)
                for (int a : pred[c][p])
                    for (int b : pred[c][q])
                        if (t.get(a, b) == 0) {
                            t.set(a, b, iter);
                            fresh.push_back({min(a, b), max(a, b)});
                        }
        if (fresh.empty()) break;
        perIter.push_back(fresh);
    }
    return perIter;
}

// Equivalence is transitive: group each state with every later unmarked one.
static vector<vector<int>> buildClasses(const Levels& t, vector<int>& group) {
    group.assign(t.m, -1);
    vector<vector<int>> classes;
    for (int i = 0; i < t.m; i++) {
        if (group[i] != -1) continue;
        int g = classes.size();
        classes.push_back({i});
        group[i] = g;
        for (int j = i + 1; j < t.m; j++)
            if (group[j] == -1 && t.get(i, j) == 0) {
                group[j] = g;
                classes[g].push_back(j);
            }
    }
    return classes;
}

// One state per class, taken from the class representative.
static DFA buildQuotient(const DFA& d, const vector<vector<int>>& classes,
                         const vector<int>& group) {
    DFA q;
    q.n = classes.size();
    q.k = d.k;
    q.alphabet = d.alphabet;
    q.start = group[d.start];
    q.label.resize(q.n);
    q.next.assign(q.n, vector<int>(q.k));
    for (int g = 0; g < q.n; g++) {
        int rep = classes[g][0];
        q.label[g] = d.label[rep];
        for (int c = 0; c < q.k; c++) q.next[g][c] = group[d.next[rep][c]];
    }
    return q;
}

// Turns the dead state back into "missing transitions" and renumbers.
static DFA dropDeadState(DFA q) {
    for (int g = 0; g < q.n; g++) {
        if (g == q.start || q.label[g] != -1) continue;
        bool trap = true;
        for (int v : q.next[g]) trap &= (v == g);
        if (!trap) continue;
        for (auto& row : q.next)
            for (int& v : row)
                if (v == g) v = -1;
        break;  // a minimal DFA has at most one dead state
    }
    vector<int> ignored;
    return keepReachable(q, ignored);  // the unreferenced dead state vanishes
}

// --------------------------------------------------------------- output ---

static void printRaw(const DFA& d, ostream& out) {
    vector<int> finals;
    for (int i = 0; i < d.n; i++)
        if (d.label[i] >= 0) finals.push_back(i);
    out << d.n << " " << d.k << "\n";
    for (int c = 0; c < d.k; c++) out << d.alphabet[c] << (c + 1 < d.k ? " " : "\n");
    out << d.start << " " << finals.size() << "\n";
    for (size_t i = 0; i < finals.size(); i++) {
        out << finals[i];
        if (d.label[finals[i]] != 0) out << ":" << d.label[finals[i]];
        out << (i + 1 < finals.size() ? " " : "");
    }
    out << "\n";
    for (int i = 0; i < d.n; i++)
        for (int c = 0; c < d.k; c++) out << d.next[i][c] << (c + 1 < d.k ? " " : "\n");
}

static void printIterations(const Levels& t, const vector<Pairs>& perIter,
                            const vector<string>& names) {
    int iters = perIter.size();
    cout << "\nPair\t";
    for (int it = 1; it <= iters; it++) cout << "iter " << it << "\t";
    cout << "\n";
    for (int i = 0; i < t.m; i++)
        for (int j = 0; j < i; j++) {
            cout << "(" << names[j] << "," << names[i] << ")\t";
            int lv = t.get(i, j);
            for (int it = 1; it <= iters; it++)
                cout << (lv != 0 && lv <= it ? "X" : "v") << "\t";
            cout << "\n";
        }
    cout << "\nNewly marked per iteration:\n";
    for (int it = 0; it < iters; it++) {
        cout << "  iter " << it + 1 << ": ";
        for (auto [a, b] : perIter[it]) cout << "(" << names[a] << "," << names[b] << ") ";
        cout << "\n";
    }
    cout << "  iter " << iters + 1 << ": nothing new -> stop\n";
}

static void printReport(const DFA& d) {
    cout << "Number of states: " << d.n << "\n";
    cout << "Start state: " << d.start << "\n";
    cout << "Final states: ";
    for (int i = 0; i < d.n; i++)
        if (d.label[i] >= 0) {
            cout << i;
            if (d.label[i] != 0) cout << "(token " << d.label[i] << ")";
            cout << " ";
        }
    cout << "\n\nTransition table ('-' = no transition):\nState\t";
    for (auto& s : d.alphabet) cout << s << "\t";
    cout << "\n";
    for (int i = 0; i < d.n; i++) {
        cout << i << "\t";
        for (int c = 0; c < d.k; c++) {
            if (d.next[i][c] < 0) cout << "-\t";
            else cout << d.next[i][c] << "\t";
        }
        cout << "\n";
    }
}

// ---------------------------------------------------------------- demos ---

// Demos 1-4 are the DFAs from the board (renumbered from 0, -1 = E).
// Demo 5 shows why token types matter: states 2 and 3 have identical
// transitions but different tokens, so they must not be merged.
static const char* DEMOS[] = {
    "4 2\n a b\n 0 1\n 3\n 1 2\n 3 1\n 3 2\n 3 3\n",
    "5 2\n a b\n 0 1\n 4\n 2 1\n 3 1\n 3 2\n 3 4\n 4 4\n",
    "4 2\n letter digit\n 0 3\n 1 2 3\n 1 -1\n 2 3\n 2 3\n 2 3\n",
    "3 2\n a b\n 0 3\n 0 1 2\n 1 2\n -1 2\n -1 2\n",
    "5 3\n i f x\n 0 4\n 1:2 2:2 3:1 4:2\n 1 2 2\n 4 3 4\n 2 2 2\n 2 2 2\n 2 2 2\n",
};

// ----------------------------------------------------------------- main ---

int main(int argc, char** argv) {
    bool raw = false, showTable = false, keepDead = false;
    int demo = 0;
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "--raw") raw = true;
        else if (a == "--table") showTable = true;
        else if (a == "--keep-dead") keepDead = true;
        else if (a == "--demo" && i + 1 < argc) demo = atoi(argv[++i]);
        else { cerr << "Unknown option: " << a << "\n"; return 2; }
    }

    DFA input;
    string err;
    bool ok;
    if (demo != 0) {
        if (demo < 1 || demo > 5) { cerr << "demo must be 1..5\n"; return 2; }
        istringstream ss(DEMOS[demo - 1]);
        ok = readDFA(ss, input, err);
    } else {
        ok = readDFA(cin, input, err);
    }
    if (!ok) { cerr << "Input error: " << err << "\n"; return 1; }

    // Reachable part, then completion with the dead state E.
    vector<int> newToOld;
    DFA d = keepReachable(input, newToOld);
    vector<string> names;
    for (int o : newToOld) names.push_back(to_string(o));
    if (completeWithDeadState(d)) names.push_back("E");

    // Myhill-Nerode table, classes, quotient automaton.
    Levels table(d.n);
    vector<Pairs> perIter = fillTable(d, table);
    vector<int> group;
    vector<vector<int>> classes = buildClasses(table, group);
    DFA minimized = buildQuotient(d, classes, group);
    if (!keepDead) minimized = dropDeadState(minimized);

    if (raw) {
        printRaw(minimized, cout);
        return 0;
    }

    cout << "Reachable states: " << newToOld.size() << " of " << input.n << "\n";
    if (showTable) printIterations(table, perIter, names);

    cout << "\nEquivalent states (merged):\n";
    for (size_t g = 0; g < classes.size(); g++) {
        cout << "  Class " << g << ": { ";
        for (int s : classes[g]) cout << names[s] << " ";
        cout << "}\n";
    }

    cout << "\nMinimized DFA:\n";
    printReport(minimized);
    cout << "\nMinimized DFA (input format, can be fed back in):\n";
    printRaw(minimized, cout);
    return 0;
}
