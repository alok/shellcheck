#!/usr/bin/env bash
# Batch 10: SC2312 extra masked returns (pipefail suppression)

set -o pipefail
false | true              # no SC2312 when pipefail is enabled

