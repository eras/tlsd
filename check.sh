#!/bin/sh
set -x
tlc -workers auto -dump dot,colorize,actionlabels System.dot System
