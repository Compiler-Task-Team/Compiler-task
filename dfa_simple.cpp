// Minimizing DFA in O(n^2 * |Sigma|) time  -- Myhill-Nerode (table filling)
//
// Idea (as on the board):
//   iter 1 : mark {p,q} if one is final and the other is not
//   iter t : mark {p,q} if for some symbol c, {delta(p,c), delta(q,c)} was marked in iter t-1
//   stop   : when an iteration marks nothing new -> unmarked pairs are equivalent (merge them)
//
// Why O(n^2 |Sigma|): we do NOT re-scan the whole table every iteration.
// For each pair marked in the previous iteration we only visit its PREDECESSORS
// (the pairs that reach it with a symbol c). Each pair {a,b} is reached at most
// once per symbol, so the total work is n^2 * |Sigma|.
//
// The error state E (missing transition) is added as a real dead state while
// we work, and removed again from the printed result.
//
// Output format (one line per transition):   {state we are in} {state we go to} symbol

#include <bits/stdc++.h>
using namespace std;

const int E = -1;  // "E" on the board = no transition

struct Test {
    string name;
    int first;                   // first state number (board uses 0 or 1)
    vector<string> sigma;        // alphabet
    int start;
    vector<int> finals;
    vector<vector<int>> delta;   // delta[state][symbol], E = missing
};

void solve(const Test& t) {
    int n = t.delta.size(), k = t.sigma.size();
    cout << "==================== " << t.name << " ====================\n";

    // ---- 1. convert to 0-based, E -> -1 ----
    vector<vector<int>> d(n, vector<int>(k));
    for (int i = 0; i < n; i++)
        for (int c = 0; c < k; c++)
            d[i][c] = (t.delta[i][c] == E) ? -1 : t.delta[i][c] - t.first;
    vector<bool> fin(n, false);
    for (int f : t.finals) fin[f - t.first] = true;
    int start = t.start - t.first;

    // ---- 2. add dead state E if the DFA is partial ----
    int dead = -1;
    bool partial = false;
    for (auto& row : d)
        for (int v : row) if (v < 0) partial = true;
    if (partial) {
        dead = n++;
        d.push_back(vector<int>(k, dead));
        fin.push_back(false);
        for (auto& row : d)
            for (int& v : row) if (v < 0) v = dead;
    }

    // ---- 3. keep only reachable states (BFS) ----
    vector<bool> reach(n, false);
    queue<int> q;
    reach[start] = true;
    q.push(start);
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int c = 0; c < k; c++)
            if (!reach[d[u][c]]) { reach[d[u][c]] = true; q.push(d[u][c]); }
    }

    auto name = [&](int i) { return i == dead ? string("E") : to_string(i + t.first); };

    // ---- 4. predecessors: pred[c][s] = states that go to s on symbol c ----
    vector<vector<vector<int>>> pred(k, vector<vector<int>>(n));
    for (int s = 0; s < n; s++)
        if (reach[s])
            for (int c = 0; c < k; c++) pred[c][d[s][c]].push_back(s);

    // ---- 5. table filling ----
    vector<vector<int>> level(n, vector<int>(n, 0));  // 0 = not marked, else iteration number
    vector<vector<pair<int, int>>> iters;             // iters[t-1] = pairs marked in iteration t

    vector<pair<int, int>> cur;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (reach[i] && reach[j] && fin[i] != fin[j]) {
                level[i][j] = level[j][i] = 1;
                cur.push_back({i, j});
            }
    while (!cur.empty()) {
        iters.push_back(cur);
        int it = iters.size() + 1;
        vector<pair<int, int>> next;
        for (auto [p, r] : cur)
            for (int c = 0; c < k; c++)
                for (int a : pred[c][p])
                    for (int b : pred[c][r])
                        if (a != b && level[a][b] == 0) {
                            level[a][b] = level[b][a] = it;
                            next.push_back({a, b});
                        }
        cur = next;
    }

    // ---- print the table like the board (v = still equivalent, X = marked) ----
    cout << "Pair\t";
    for (size_t it = 1; it <= iters.size(); it++) cout << "iter" << it << "\t";
    cout << "\n";
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) {
            if (!reach[i] || !reach[j]) continue;
            cout << "(" << name(i) << "," << name(j) << ")\t";
            for (size_t it = 1; it <= iters.size(); it++)
                cout << (level[i][j] != 0 && level[i][j] <= (int)it ? "X" : "v") << "\t";
            cout << "\n";
        }
    cout << "(iteration " << iters.size() + 1 << " marks nothing new -> stop)\n\n";

    // ---- 6. equivalence classes ----
    vector<int> group(n, -1);
    vector<vector<int>> classes;
    for (int i = 0; i < n; i++) {
        if (!reach[i] || group[i] != -1) continue;
        group[i] = classes.size();
        classes.push_back({i});
        for (int j = i + 1; j < n; j++)
            if (reach[j] && group[j] == -1 && level[i][j] == 0) {
                group[j] = group[i];
                classes[group[i]].push_back(j);
            }
    }
    int deadGroup = (dead == -1) ? -1 : group[dead];

    auto label = [&](int g) {
        string s = "{";
        bool firstItem = true;
        for (int st : classes[g]) {
            if (st == dead) continue;
            s += (firstItem ? "" : ",") + name(st);
            firstItem = false;
        }
        return s + "}";
    };

    // ---- 7. print the minimized DFA: {from} {to} symbol ----
    cout << "Minimized DFA:\n";
    for (int g = 0; g < (int)classes.size(); g++) {
        if (g == deadGroup) continue;
        int rep = classes[g][0];
        for (int c = 0; c < k; c++) {
            int to = group[d[rep][c]];
            if (to == deadGroup) continue;  // transition to E is not drawn
            cout << label(g) << " " << label(to) << " " << t.sigma[c] << "\n";
        }
    }
    cout << "Start: " << label(group[start]) << "\nFinal:";
    for (int g = 0; g < (int)classes.size(); g++)
        if (g != deadGroup && fin[classes[g][0]]) cout << " " << label(g);
    cout << "\n\n";
}

int main() {
    vector<Test> tests = {
        // Test 1: identifier  letter(letter|digit)*  (states 1..4, 1 -digit-> E)
        // the big subset-construction DFA {1},{2,3,4,5,7,10},{4,5,6,7,9,10},{4,5,7,8,9,10}
        // is exactly this DFA with renamed states.
        {"Test 1: identifier (letter / digit)", 1, {"letter", "digit"}, 1, {2, 3, 4},
         {{2, E}, {3, 4}, {3, 4}, {3, 4}}},

        // Test 2: table  1:(2,3)  2:(E,3)  3:(E,3)
        {"Test 2: a,b with error state E", 1, {"a", "b"}, 1, {1, 2, 3},
         {{2, 3}, {E, 3}, {E, 3}}},

        // Test 3: 4 states, iter 1..3
        {"Test 3: states 0..3", 0, {"a", "b"}, 0, {3},
         {{1, 2}, {3, 1}, {3, 2}, {3, 3}}},

        // Test 4: 5 states, iter 1..4
        {"Test 4: states 0..4", 0, {"a", "b"}, 0, {4},
         {{2, 1}, {3, 1}, {3, 2}, {3, 4}, {4, 4}}},
    };
    for (auto& t : tests) solve(t);
    return 0;
}
