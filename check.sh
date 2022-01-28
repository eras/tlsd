#!/bin/zsh
typeset -a flags=()
if [ "$1" = "-dot" ]; then
    shift
    flags=($flags -dump dot,colorize,actionlabels System.dot)
fi
tlc -workers auto ${(@)flags} System
