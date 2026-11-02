#!/bin/bash
# Runs every test in testcases.txt against the compiled minimizer.
# Usage: ./run_tests.sh [path/to/dfa] [path/to/testcases.txt]

BIN=${1:-./dfa}
TESTS=${2:-testcases.txt}

if [ ! -x "$BIN" ]; then
    echo "Binary '$BIN' not found. Build it first:"
    echo "  g++ -std=c++17 -O2 -o dfa DFA_minimizer_final.cpp"
    exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Split testcases.txt into <n>.in, <n>.out and <n>.base
awk -v d="$tmp" '
/^### TEST/    { n = $3; base[n] = $5; mode = ""; order[++cnt] = n; next }
/^--- input/   { mode = "in";  next }
/^--- expected/{ mode = "out"; next }
/^#/           { next }
mode == "in"   { print > (d "/" n ".in") }
mode == "out"  { print > (d "/" n ".out") }
END { for (i = 1; i <= cnt; i++) print order[i], base[order[i]] > (d "/list") }
' "$TESTS"

pass=0
fail=0
while read -r n base; do
    actual=$("$BIN" --base "$base" < "$tmp/$n.in" 2>&1)
    if diff -B <(echo "$actual") "$tmp/$n.out" > "$tmp/$n.diff"; then
        echo "PASS  test $n"
        pass=$((pass + 1))
    else
        echo "FAIL  test $n"
        sed 's/^/      /' "$tmp/$n.diff"
        fail=$((fail + 1))
    fi
done < "$tmp/list"

echo "-----"
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
