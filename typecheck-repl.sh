#! /bin/bash
stack build || exit
if [ $# -gt 0 ]; then
    for f in $@; do
        stack exec egison -- --no-io -t $f
    done
else
    stack exec egison -- --no-io
fi
