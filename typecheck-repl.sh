#! /bin/bash
stack build
if [ $# -gt 0 ]; then
    for f in $@; do
        stack exec egison -- --no-io -t $f
    done
else
    stack exec egison -- --no-io
fi
