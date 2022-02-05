#!/bin/zsh
typeset -a tlc_args=()
typeset -a dot_args=()

module=System

tlc_arg() {
    tlc_args=($tlc_args $@)
}

dot_arg() {
    dot_args=($dot_args $@)
}

dot=false
sany=false

tlc_arg -workers auto
tlc_arg -fpmem 0.1
tlc_arg -teSpecOutDir out

while [ -n "$1" ]; do
    arg="$1"
    shift
    case "$arg"; in
	-sany)
	    sany=true
	    ;;
	-dot)
	    dot=true
	    tlc_arg -dump dot,colorize,actionlabels,snapshot "$module".dot
	    ;;
	-sim)
	    tlc_arg -simulate ifile=trace.txt,num=100,stats=full -depth 20
	    ;;
	-diff)
	    tlc_arg -difftrace
	    ;;
	-lr)
	    dot_arg -lr
	    ;;
	*)
	    echo unknown argument "$arg"
	    exit 2
    esac
done

echo_and_run() {
    echo "$*"
    "$@"
}

if $sany; then
    echo_and_run sany "$module"
else
    echo_and_run nice tlc ${(@)tlc_args} "$module"
    if $dot; then
	(ulimit -v 1000000;
	 echo_and_run dot-tla-model ${(@)dot_args} "$module".dot > "$module".pdf)
    fi
fi
