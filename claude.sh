#!/bin/sh

set -e -x

claude --dangerously-skip-permissions "$@"
