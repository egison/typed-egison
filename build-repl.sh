#! /bin/bash
stack build || exit
if [ $# -gt 0 ]; then
    for f in $@; do
        stack exec egison -- -t $f
    done
else
    stack exec egison
fi
