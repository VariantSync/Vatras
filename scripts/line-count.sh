#!/usr/bin/env bash

cd "$(dirname ${BASH_SOURCE[0]})/../src"
projectDir="$PWD"

echo -n 'with empty lines and comments: '
fd '.agda$|.lagda.md$' | xargs cat | wc -l

echo -n 'without empty lines, with comments: '
fd '.agda$|.lagda.md$' | xargs cat | grep -v '^[[:space:]]*$' | wc -l

echo -n 'without empty lines, without comments: '
literate="$(fd '.lagda.md$' | xargs cat | grep -v '^[[:space:]]*--' | sed -n '/{-\([^#]\|$\)/,/-}/d; /```/,/```/ { /```/!p }' | wc -l)"
nonLiterate="$(fd '.agda$' | xargs cat | grep -v '^[[:space:]]*--' | sed '/{-\([^#]\|$\)/,/-}/d' | wc -l)"
expr "$literate" + "$nonLiterate"
