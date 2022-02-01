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

tlc_arg -workers auto
tlc_arg -fpmem 0.1

while [ -n "$1" ]; do
    arg="$1"
    shift
    case "$arg"; in
	-dot)
	    dot=true
	    tlc_arg -dump dot,colorize,actionlabels,snapshot "$module".dot
	    ;;
	-sim)
	    tlc_arg -simulate num=10 -depth 1
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

echo_and_run tlc ${(@)tlc_args} "$module"
if $dot; then
    (ulimit -v 1000000;
     echo_and_run dot-tla-model ${(@)dot_args} "$module".dot > "$module".pdf)
fi
