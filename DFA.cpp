// Shams Ahmed Shalan Abdelhaleem | ID: 11422025462181
// Asmaa Shawky Abdel-salam Rizk  | ID: 11422025468423
#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <sstream>
using namespace std;

void runTest(const string& testInput, int testNumber) {
    stringstream in(testInput);
    int n, k;
    in >> n >> k;
    // Read alphabet
    vector<char> alphabet(k);
    for (int i = 0; i < k; i++) {
        in >> alphabet[i];
    }
    // Read start state and final states
    int start, f;
    in >> start >> f;
    vector<bool> isFinal(n, false);
    for (int i = 0; i < f; i++) {
        int x;
        in >> x;
        if (x < 0 || x >= n) {
            cout << "Invalid final state!\n";
            return;
        }
        isFinal[x] = true;
    }
    // Read transition table
    vector<vector<int>> trans(n, vector<int>(k));
    for (int i = 0; i < n; i++) {
        for (int c = 0; c < k; c++) {
            in >> trans[i][c];
        }
    }
    if (start < 0 || start >= n) {
        cout << "Invalid start state!\n";
        return;
    }
    // Step 0: Complete DFA using a Dead State if needed
    bool needDeadState = false;
    for (int i = 0; i < n; i++) {
        for (int c = 0; c < k; c++) {
            if (trans[i][c] == -1) {
                needDeadState = true;
            }
            else if (trans[i][c] < 0 || trans[i][c] >= n) {
                cout << "Invalid transition!\n";
                return;
            }
        }
    }
    int deadState = -1;
    if (needDeadState) {
        deadState = n;
        for (int i = 0; i < n; i++) {
            for (int c = 0; c < k; c++) {
                if (trans[i][c] == -1) {
                    trans[i][c] = deadState;
                }
            }
        }
        trans.push_back(vector<int>(k, deadState));
        isFinal.push_back(false);
        n++;
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
    // Step 2: Build predecessor lists
    vector<vector<vector<int>>> pred(
        k, vector<vector<int>>(m)
    );
    for (int s = 0; s < m; s++) {
        for (int c = 0; c < k; c++) {
            int destination = T[s][c];
            pred[c][destination].push_back(s);
        }
    }
    auto pairId = [m](int i, int j) {
        if (i > j)
            swap(i, j);
        return i * m + j;
    };
    // Step 3: Mark distinguishable pairs
    vector<bool> marked(m * m, false);
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
        int p = currentPair / m;
        int r = currentPair % m;
        for (int c = 0; c < k; c++) {
            for (int a : pred[c][p]) {
                for (int b : pred[c][r]) {
                    if (a != b) {
                        int previousPair = pairId(a, b);
                        if (!marked[previousPair]) {
                            marked[previousPair] = true;
                            worklist.push(previousPair);
                        }
                    }
                }
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
    // Step 5: Build minimized DFA
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
    int minStart = group[newStart];
    // Step 6: Identify the Dead State group
    int deadGroup = -1;
    if (deadState != -1 && oldToNew[deadState] != -1) {
        int deadNewState = oldToNew[deadState];
        deadGroup = group[deadNewState];
    }
    // Step 7: Remove Dead State group from printed DFA
    vector<int> groupToOutput(numberOfGroups, -1);
    vector<int> outputToGroup;
    for (int g = 0; g < numberOfGroups; g++) {
        if (g == deadGroup)
            continue;
        groupToOutput[g] = outputToGroup.size();
        outputToGroup.push_back(g);
    }
    int outputStates = outputToGroup.size();
    int outputStart = groupToOutput[minStart];
    // Step 8: Print result
    cout << "\n========== TEST CASE " << testNumber << " ==========\n";
    cout << "Start State: " << outputStart << "\n";
    cout << "Number of States: " << outputStates << "\n";
    cout << "Final Groups: ";
    for (int out = 0; out < outputStates; out++) {
        int g = outputToGroup[out];
        if (minFinal[g]) {
            cout << "{";
            for (int i = 0; i < classes[g].size(); i++) {
                cout << newToOld[classes[g][i]];
                if (i + 1 < classes[g].size())
                    cout << ",";
            }
            cout << "} ";
        }
    }
    cout << "\n\nTransitions:\n";
    for (int out = 0; out < outputStates; out++) {
        int g = outputToGroup[out];
        for (int c = 0; c < k; c++) {
            int destination = minTrans[g][c];
            // Hide transitions going to Dead State
            if (destination == deadGroup)
                continue;
            int destinationOutput = groupToOutput[destination];
            cout << "{";
            for (int i = 0; i < classes[g].size(); i++) {
                cout << newToOld[classes[g][i]];
                if (i + 1 < classes[g].size())
                    cout << ",";
            }
            cout << "} {";
            for (int i = 0; i < classes[destination].size(); i++) {
                cout << newToOld[classes[destination][i]];
                if (i + 1 < classes[destination].size())
                    cout << ",";
            }
            cout << "} " << alphabet[c] << "\n";
        }
    }
    cout << "====================================\n";
}

int main() {
    // Test Case 1: Identifier DFA
    const string test1 =
        "4 2\n"
        "l d\n"
        "0 3\n"
        "1 2 3\n"
        "1 -1\n"
        "2 3\n"
        "2 3\n"
        "2 3\n";
    // Test Case 2: (a|eps)b* DFA
    const string test2 =
        "3 2\n"
        "a b\n"
        "0 3\n"
        "0 1 2\n"
        "1 2\n"
        "-1 2\n"
        "-1 2\n";
    // Test Case 3
    const string test3 =
        "4 2\n"
        "a b\n"
        "0 1\n"
        "3\n"
        "1 2\n"
        "3 1\n"
        "3 2\n"
        "3 3\n";
    // Test Case 4
    const string test4 =
        "5 2\n"
        "a b\n"
        "0 1\n"
        "4\n"
        "2 1\n"
        "3 1\n"
        "3 2\n"
        "3 4\n"
        "4 4\n";
    const string test5 =
        "6 2\n"
        "a b\n"
        "0 2\n"
        "4 5\n"
        "1 2\n"
        "4 1\n"
        "4 3\n"
        "4 3\n"
        "4 5\n"
        "5 5\n";
    runTest(test1, 1);
    runTest(test2, 2);
    runTest(test3, 3);
    runTest(test4, 4);
    runTest(test5, 5);
    return 0;
}