# Lean 4 Project Template

This repository contains a template for blueprint-driven formalization projects in Lean 4.

## Use this Template

To create a new repository using this template, follow these steps:

1. Click the **Use this template** button located at the top right of the repository page.
2. Click the **Create a new repository** button.
3. Select the account or organization where you want to create it, choose a name for the new
repository, and click the **Create repository** button.

## Customize this Template

Requirements:

- [uv](https://docs.astral.sh/uv/getting-started/installation/)
- [gh](https://cli.github.com/)

Quickstart (one-shot):

```bash
# Set tokens in your shell (values provided by you)
export REPO_PAT_TOKEN=...   # GitHub PAT (needed for private repos and secret management)
export MORPH_GAUSS_TOKEN=...  # Morph Gauss API token

uv run lean_runbook.py quickstart --name MyProject --author "Jesse Han \and Math Inc"
```

The webhook for running github actions on MorphCloud should be set manually in the repo settings.

This performs (by default, in a fresh clone):

- Initialize/rename modules and README to `MyProject`
- Set author(s) in the generated documents: `Jesse Han \and Math Inc`. Multiple authors should be separated by ' \and ' as in the example.
- Best-effort GitHub setup: set repository secrets and configure Pages (requires `gh` CLI authenticated)
- Commit initial changes with author `Jesse Han <jessemhan@proton.me>`
- Initialize blueprint assets (requires `uvx`). The CLI auto-installs Graphviz dev packages when possible if pygraphviz fails.
- Install the appropriate Lean toolchain via `elan` (if missing), update dependencies, and run a Lean build (`lake update`, `lake exe cache get`, `lake build`)

Individual commands:

- `python lean_runbook.py init-project --name MyProject` — Rename `Project` to `MyProject` across files and directories, and refresh README
- `python lean_runbook.py set-secrets` — Set `REPO_PAT_TOKEN`, `MORPH_GAUSS_TOKEN` on the GitHub repo via `gh` (reads env vars)
- `python lean_runbook.py configure-pages` — Configure GitHub Pages to use GitHub Actions (best-effort)
- `python lean_runbook.py commit-initial --message "..."` — Commit staged changes with the requested identity
- `python lean_runbook.py push --branch main` — Push to `main` (or another branch)
- `python lean_runbook.py install-lean` — Install `elan` and the repo’s pinned toolchain (from `lean-toolchain`) and print versions
- `python lean_runbook.py blueprint-init` — Run `uvx leanblueprint new` (auto-installs Graphviz dev packages if needed)
- `python lean_runbook.py build-lean` — `lake exe cache get && lake build`
- `python lean_runbook.py blueprint-pdf` — Build the blueprint PDF
- `python lean_runbook.py blueprint-web` — Build and serve the blueprint web locally

Options:

- `--dest PATH` to specify the target directory for the new clone (defaults to a sibling folder named after `--name`).
- `--ref REF` to specify the git ref (defaults to origin’s default branch HEAD).
- `--source-url URL` to override the source repository URL (defaults to this repo’s origin).
- `--in-place` to run the setup in the current working tree instead of cloning (legacy behavior).

Notes:

- `set-secrets` and `configure-pages` require the GitHub CLI (`gh`) to be installed and authenticated (`gh auth login`).
- `blueprint-*` commands require `uv` installed (`uvx` available) and LaTeX for PDF.

### System dependencies (blueprint)

`leanblueprint` indirectly depends on `pygraphviz`, which may require system Graphviz headers when wheels are unavailable. If the CLI cannot auto-install, install manually:

- Debian/Ubuntu: `sudo apt-get update && sudo apt-get install -y graphviz libgraphviz-dev`
- Fedora: `sudo dnf install -y graphviz graphviz-devel`
- RHEL/CentOS: `sudo yum install -y graphviz graphviz-devel`
- Arch: `sudo pacman -Sy --noconfirm graphviz`
- macOS (Homebrew): `brew install graphviz`

## Gauss ChatOps (GitHub Actions)

This template ships with a workflow for running Gauss: `.github/workflows/gauss.yml`.

Requirements:

- Repository secrets: `MORPH_GAUSS_TOKEN` (required to access Gauss), `REPO_PAT_TOKEN` (required for private repos)
- A self-hosted runner with labels: `[self-hosted, linux, x64, morph]`. Should be set in the repo settings under "Webhooks" → "Add webhook" with content type `application/json`.

How to invoke:

- On a PR, comment: `@gauss-prove My.Namespace.theorem` or `@gauss-statement label1 label2`
- Or, run the "Gauss" workflow manually from the Actions tab (choose `gauss-prove` or `gauss-statement` and optional params)

What it does:

- Checks out the target ref, prepares a working branch, runs Gauss via `gauss-sdk` with your tokens, and applies returned updates
- If changes are produced, it pushes a branch and opens a PR with a summary and detailed analysis
