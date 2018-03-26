#! /bin/bash
stack build
if [ $# -gt 0 ]; then
    for f in $@; do
        stack exec typecheck -- -t $f
    done
else
    stack exec typecheck
fi
