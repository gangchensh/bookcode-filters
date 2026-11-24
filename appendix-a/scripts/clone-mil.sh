#!/usr/bin/env bash
set -eu
repo_url='https://mirror.sjtu.edu.cn/git/lean4-packages/mathematics_in_lean/'
git clone --depth 1 "$repo_url" mathematics_in_lean
