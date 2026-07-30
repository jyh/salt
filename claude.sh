#!/bin/sh

# MAX_SUBAGENTS is the documented knob (parallel subagent concurrency);
# the *_PER_SESSION spellings are not respected. Workflow agents have a
# separate hard cap of 16 concurrent regardless of this value.
export MAX_SUBAGENTS=1024

set -e -x

claude --dangerously-skip-permissions "$@"
