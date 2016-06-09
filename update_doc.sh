#!/usr/bin/env bash

# Generate documentation and commit into the gh-pages branch.

set -euo pipefail

VERSION=$(grep -w version -m 1 Cargo.toml)
COMMIT=$(git rev-parse HEAD)

rustup default nightly
cargo doc --manifest-path extprim_literals/Cargo.toml --features doc_only
git worktree add doc gh-pages
cd doc
git rm -r .
git reset HEAD .gitignore index.html
git checkout -- .gitignore index.html
mv ../extprim_literals/target/doc/{extprim,extprim_literals} .
mv ../extprim_literals/target/doc/*.{txt,woff,js,css} .
mkdir src
mv ../extprim_literals/target/doc/src/{extprim,extprim_literals} src
git add .
git commit -m "Update doc for ${VERSION} (${COMMIT})"
cd ..
rm -rf doc
git worktree prune

