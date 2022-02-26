#!/bin/zsh
typeset -a tlc_args=()
typeset -a dot_args=()

module=System

base_path=$(dirname "$0")

tlc_arg() {
    tlc_args=($tlc_args $@)
}

dot_arg() {
    dot_args=($dot_args $@)
}

dot=false
sany=false
messages=false

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
	-cont)
	    tlc_arg -continue
	    ;;
	-lr)
	    dot_arg -lr
	    ;;
	-messages)
	    messages=true
	    ;;
	-*)
	    echo unknown argument "$arg"
	    exit 2
	    ;;
	*)
	    module="$arg"
	    echo Checking module $module
    esac
done

if ! [ -r "$module.tla" ]; then
    echo "Cannot find $module.tla"
    exit 3
fi

echo_and_run() {
    echo "$*"
    "$@"
}

cfgfile=$(tempfile -s .cfg)
trap 'rm "$cfgfile"' EXIT


if $messages; then
    grep -v '^ALIAS' $module.cfg > $cfgfile
    echo ALIAS AliasMessage >> $cfgfile
else
    cat "$module.cfg" > $cfgfile
fi

if $sany; then
    echo_and_run sany "$module"
else
    echo_and_run nice tlc ${(@)tlc_args} -config $cfgfile "$module" | tee check.txt
    if $messages; then
	$base_path/parse_messages.py < check.txt
	inkscape --export-pdf=sequence.pdf sequence.svg
    fi
    if $dot; then
	(ulimit -v 1000000;
	 echo_and_run dot-tla-model ${(@)dot_args} "$module".dot > "$module".pdf)
    fi
    if $messages || $dot; then
	pkill -HUP llpp
    fi
fi
