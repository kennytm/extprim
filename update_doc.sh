#!/bin/sh

set -euo pipefail

VERSION=$(grep -w version -m 1 Cargo.toml)
COMMIT=$(git rev-parse HEAD)

cargo doc --manifest-path extprim_literals/Cargo.toml
git worktree add doc gh-pages
mv extprim_literals/target/doc/* doc/
pushd doc
git rm -r .
git reset HEAD .gitignore index.html
git checkout -- .gitignore index.html
git add .
git commit -m "Update doc for ${VERSION} (${COMMIT})"
popd
rm -rf doc
git worktree prune

