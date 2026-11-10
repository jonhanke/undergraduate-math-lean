# CI workflow, staged

When creating the repository, move `ci/build.yml` to `.github/workflows/build.yml` and delete this directory (`git mv ci/build.yml .github/workflows/build.yml`). It is staged here only because the branch was pushed with a token that may not write workflow files.
