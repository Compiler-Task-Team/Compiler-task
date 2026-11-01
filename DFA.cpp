#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
using namespace std;

int main() {
    int n, k;
    cin >> n >> k;

    // Read alphabet
    vector<char> alphabet(k);
    for (int i = 0; i < k; i++) {
        cin >> alphabet[i];
    }

    // Read start state and final states
    int start, f;
    cin >> start >> f;
    vector<bool> isFinal(n, false);
    for (int i = 0; i < f; i++) {
        int x;
        cin >> x;
        isFinal[x] = true;
    }

    // Read transition table
    vector<vector<int>> trans(n, vector<int>(k));
    for (int i = 0; i < n; i++) {
        for (int c = 0; c < k; c++) {
            cin >> trans[i][c];
        }
    }

    // Step 1: Remove unreachable states
    vector<bool> reachable(n, false);
    queue<int> q;
    reachable[start] = true;
    q.push(start);
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        for (int c = 0; c < k; c++) {
            int v = trans[u][c];
            if (!reachable[v]) {
                reachable[v] = true;
                q.push(v);
            }
        }
    }

    vector<int> oldToNew(n, -1);
    vector<int> newToOld;

    for (int i = 0; i < n; i++) {
        if (reachable[i]) {
            oldToNew[i] = newToOld.size();
            newToOld.push_back(i);
        }
    }

    int m = newToOld.size();

    // Build DFA using reachable states only
    vector<vector<int>> T(m, vector<int>(k));
    vector<bool> finalState(m, false);
    for (int i = 0; i < m; i++) {
        int oldState = newToOld[i];
        finalState[i] = isFinal[oldState];
        for (int c = 0; c < k; c++) {
            T[i][c] = oldToNew[trans[oldState][c]];
        }
    }

    int newStart = oldToNew[start];

    // Step 2: Build reverse dependencies
    auto pairId = [m](int i, int j) {
        if (i > j) swap(i, j);
        return i * m + j;
    };

    vector<bool> marked(m * m, false);
    vector<vector<int>> reverseDeps(m * m);

    for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
            int sourcePair = pairId(i, j);
            for (int c = 0; c < k; c++) {
                int p = T[i][c];
                int r = T[j][c];
                if (p != r) {
                    int targetPair = pairId(p, r);
                    reverseDeps[targetPair].push_back(sourcePair);
                }
            }
        }
    }

    // Step 3: Mark distinguishable pairs
    queue<int> worklist;
    for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
            if (finalState[i] != finalState[j]) {
                int id = pairId(i, j);
                marked[id] = true;
                worklist.push(id);
            }
        }
    }

    // Propagate distinguishability backwards
    while (!worklist.empty()) {
        int currentPair = worklist.front();
        worklist.pop();
        for (int previousPair : reverseDeps[currentPair]) {
            if (!marked[previousPair]) {
                marked[previousPair] = true;
                worklist.push(previousPair);
            }
        }
    }

    // Step 4: Build equivalence classes
    vector<int> group(m, -1);
    vector<vector<int>> classes;
    for (int i = 0; i < m; i++) {
        if (group[i] != -1)
            continue;
        int groupId = classes.size();
        classes.push_back({});
        for (int j = i; j < m; j++) {
            if (j == i ||
                (!marked[pairId(i, j)] && group[j] == -1)) {
                group[j] = groupId;
                classes[groupId].push_back(j);
            }
        }
    }

    // Step 5: Print equivalent states
    cout << "\nEquivalent States:\n";
    for (int g = 0; g < (int)classes.size(); g++) {
        cout << "Group " << g << ": { ";
        for (int state : classes[g]) {
            cout << newToOld[state] << " ";
        }
        cout << "}\n";
    }

    // Step 6: Build minimized DFA
    int numberOfGroups = classes.size();
    vector<vector<int>> minTrans(
        numberOfGroups, vector<int>(k)
    );

    vector<bool> minFinal(numberOfGroups, false);

    for (int g = 0; g < numberOfGroups; g++) {
        int representative = classes[g][0];
        minFinal[g] = finalState[representative];
        for (int c = 0; c < k; c++) {
            int destination = T[representative][c];
            minTrans[g][c] = group[destination];
        }
    }

    // Step 7: Print minimized DFA
    cout << "\nMinimized DFA:\n";
    cout << "Number of states: " << numberOfGroups << "\n";
    cout << "Start state: " << group[newStart] << "\n";
    cout << "Final states: ";
    for (int g = 0; g < numberOfGroups; g++) {
        if (minFinal[g]) {
            cout << g << " ";
        }
    }
    cout << "\n\nTransition Table:\n";
    cout << "State\t";
    for (char c : alphabet) {
        cout << c << "\t";
    }
    cout << "\n";
    for (int g = 0; g < numberOfGroups; g++) {
        cout << g << "\t";
        for (int c = 0; c < k; c++) {
            cout << minTrans[g][c] << "\t";
        }
        cout << "\n";
    }
    return 0;
}