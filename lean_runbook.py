#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "click",
# ]
# ///
import os
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path

import click

# ----------------------------
# Utilities
# ----------------------------

REPO_ROOT = Path(__file__).resolve().parent


def run_cmd(cmd, cwd=None, check=True, env=None, capture=False):
    if isinstance(cmd, str):
        shell = True
    else:
        shell = False
    proc = subprocess.run(
        cmd if shell else list(cmd),
        cwd=cwd,
        env=env,
        shell=shell,
        check=False,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    if check and proc.returncode != 0:
        out = proc.stdout or ""
        raise subprocess.CalledProcessError(proc.returncode, cmd, output=out)
    return proc.stdout if capture else None


def ensure_git_repo():
    try:
        run_cmd(["git", "rev-parse", "--is-inside-work-tree"], cwd=REPO_ROOT)
    except subprocess.CalledProcessError:
        click.echo("Not a git repository at {}".format(REPO_ROOT), err=True)
        sys.exit(2)


def git_config_set(name: str, value: str):
    run_cmd(["git", "config", name, value], cwd=REPO_ROOT)


def parse_remote_owner_repo() -> tuple[str, str] | tuple[None, None]:
    try:
        url = run_cmd(["git", "config", "--get", "remote.origin.url"], cwd=REPO_ROOT, capture=True)
        if not url:
            return None, None
        url = url.strip()
    except subprocess.CalledProcessError:
        return None, None

    # Support git@github.com:owner/repo.git and https://github.com/owner/repo(.git)
    m = re.search(r"github\.com[:/]+([^/]+)/([^.]+)(?:\.git)?$", url)
    if not m:
        return None, None
    return m.group(1), m.group(2)


def gh_available() -> bool:
    try:
        run_cmd(["gh", "--version"], capture=True, check=True)
        return True
    except Exception:
        return False


def pkgmgr_available(name: str) -> bool:
    return shutil.which(name) is not None


def try_install_graphviz_dev(verbose: bool = True) -> bool:
    """Best-effort install of Graphviz headers needed by pygraphviz.

    Returns True if installation appears to succeed; False otherwise.
    """
    cmds: list[list[str]] = []
    if pkgmgr_available("apt-get"):
        cmds = [["bash", "-lc", "apt-get update -y && apt-get install -y graphviz libgraphviz-dev"]]
    elif pkgmgr_available("dnf"):
        cmds = [["dnf", "install", "-y", "graphviz", "graphviz-devel"]]
    elif pkgmgr_available("yum"):
        cmds = [["yum", "install", "-y", "graphviz", "graphviz-devel"]]
    elif pkgmgr_available("pacman"):
        cmds = [["bash", "-lc", "pacman -Sy --noconfirm graphviz"]]
    elif pkgmgr_available("brew"):
        cmds = [["brew", "install", "graphviz"]]

    if not cmds:
        if verbose:
            click.echo("No supported package manager detected for auto-install.")
        return False

    ok = True
    for cmd in cmds:
        try:
            run_cmd(cmd, cwd=REPO_ROOT, check=True)
        except subprocess.CalledProcessError as e:
            ok = False
            if verbose:
                click.echo(f"Dependency install failed: {e}", err=True)
            break

    return ok


def with_elan_env(base: dict[str, str] | None = None) -> dict[str, str]:
    env = dict(os.environ if base is None else base)
    elan_bin = str(Path.home() / ".elan" / "bin")
    env_path = env.get("PATH", "")
    if elan_bin not in env_path.split(":"):
        env["PATH"] = f"{elan_bin}:{env_path}" if env_path else elan_bin
    return env


def ensure_elan_and_toolchain() -> dict[str, str]:
    """Ensure elan is installed and the repo's toolchain is available.

    Returns an environment dict with ~/.elan/bin on PATH for downstream commands.
    """
    env = with_elan_env()
    elan_exe = shutil.which("elan", path=env.get("PATH"))
    if elan_exe is None:
        # Attempt non-interactive install of elan
        click.echo("elan not found; attempting installation...")
        install_cmds = [
            [
                "bash",
                "-lc",
                "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
            ],
            [
                "bash",
                "-lc",
                "wget -qO- https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
            ],
        ]
        installed = False
        for cmd in install_cmds:
            try:
                run_cmd(cmd, check=True)
                installed = True
                break
            except subprocess.CalledProcessError:
                continue
        if not installed:
            click.echo("Failed to install elan automatically. Please install elan and retry:", err=True)
            click.echo("https://leanprover-community.github.io/install/project.html#elan", err=True)
            sys.exit(1)
        # refresh env
        env = with_elan_env(env)

    # Ensure toolchain from lean-toolchain is installed
    toolchain_file = REPO_ROOT / "lean-toolchain"
    if toolchain_file.exists():
        toolchain = toolchain_file.read_text(encoding="utf-8").strip()
        try:
            run_cmd(["elan", "toolchain", "install", toolchain], env=env, check=False)
        except subprocess.CalledProcessError as e:
            if "is already installed" in (e.output if hasattr(e, "output") else ""):
                pass  # already installed
            else:
                click.echo("Failed to install Lean toolchain from lean-toolchain:", err=True)
                click.echo(e.output if hasattr(e, "output") else str(e), err=True)
                sys.exit(e.returncode)
    else:
        click.echo("Warning: lean-toolchain file not found; proceeding with current Lean toolchain.")

    # Validate lake availability
    lake_exe = shutil.which("lake", path=env.get("PATH"))
    if lake_exe is None:
        click.echo("Lake not found on PATH even after toolchain install.", err=True)
        click.echo("Please ensure elan installed correctly and restart your shell.", err=True)
        sys.exit(1)

    return env


def replace_text_in_file(path: Path, old: str, new: str):
    if not path.exists():
        return
    content = path.read_text(encoding="utf-8")
    content = content.replace(old, new)
    path.write_text(content, encoding="utf-8")


def write_readme_for_project(project_name: str):
    text = f"""# {project_name}

## Commands

Building Lean files:

```bash
lake exe cache get && lake build
```

For blueprint, please install [uv](https://docs.astral.sh/uv/getting-started/installation/) and latex first.

Building blueprint (PDF):

```bash
uvx leanblueprint pdf
```

Building blueprint (web local server):

```bash
uvx leanblueprint web && uvx leanblueprint serve
```
"""
    (REPO_ROOT / "README.md").write_text(text, encoding="utf-8")


# ----------------------------
# CLI
# ----------------------------


@click.group()
def cli():
    """LeanProject runbook CLI.

    Subcommands wrap the template customization, secret setup, Lean build, and blueprint flows.
    """


@cli.command("init-project")
@click.option("--name", required=True, help="New project name (replaces 'Project').")
def init_project(name: str):
    """Customize template files and rename modules to the given project name."""
    # Rename and replace occurrences of 'Project' in select files
    lakefile = REPO_ROOT / "lakefile.toml"
    build_yml = REPO_ROOT / ".github" / "workflows" / "build-project.yml"
    project_dir = REPO_ROOT / "Project"
    project_lean = REPO_ROOT / "Project.lean"

    # 1) Replace names where needed
    replace_text_in_file(lakefile, "Project", name)
    replace_text_in_file(build_yml, "Project", name)

    # 2) Rename directory and top-level .lean
    if project_dir.exists():
        project_dir.rename(REPO_ROOT / name)
    if project_lean.exists():
        new_lean = REPO_ROOT / f"{name}.lean"
        project_lean.rename(new_lean)
        replace_text_in_file(new_lean, "Project", name)

    # 3) Update README to standard commands for new project
    write_readme_for_project(name)

    click.echo(f"Initialized project as '{name}'.")


@cli.command("set-secrets")
@click.option("--owner", default=None, help="GitHub owner (auto-detected if omitted)")
@click.option("--repo", default=None, help="GitHub repo name (auto-detected if omitted)")
def set_secrets(owner: str | None, repo: str | None):
    """Set GitHub repository secrets from environment variables using gh CLI.

    Reads REPO_PAT_TOKEN, MORPH_GAUSS_TOKEN from the environment.
    """
    ensure_git_repo()
    if not gh_available():
        click.echo("gh CLI not found; install https://cli.github.com/ and authenticate.", err=True)
        sys.exit(1)

    env_vals = {
        "REPO_PAT_TOKEN": os.getenv("REPO_PAT_TOKEN", ""),
        "MORPH_GAUSS_TOKEN": os.getenv("MORPH_GAUSS_TOKEN", ""),
    }
    if not env_vals["MORPH_GAUSS_TOKEN"]:
        click.echo("MORPH_GAUSS_TOKEN is required in environment.", err=True)
        sys.exit(2)

    if not owner or not repo:
        det_owner, det_repo = parse_remote_owner_repo()
        owner = owner or det_owner
        repo = repo or det_repo
    if not owner or not repo:
        click.echo("Could not determine owner/repo; specify --owner and --repo.", err=True)
        sys.exit(3)

    full_repo = f"{owner}/{repo}"
    for key, val in env_vals.items():
        if not val:
            click.echo(f"Skipping {key}: not set.")
            continue
        # Use printf to avoid adding a trailing newline
        cmd = f"printf %s {shlex.quote(val)} | gh secret set {shlex.quote(key)} -R {shlex.quote(full_repo)}"
        run_cmd(cmd, cwd=REPO_ROOT, check=True)
        click.echo(f"Set secret {key} for {full_repo}.")


@cli.command("configure-pages")
@click.option("--owner", default=None, help="GitHub owner (auto-detected if omitted)")
@click.option("--repo", default=None, help="GitHub repo name (auto-detected if omitted)")
def configure_pages(owner: str | None, repo: str | None):
    """Configure GitHub Pages to use GitHub Actions (best-effort) via gh api."""
    ensure_git_repo()
    if not gh_available():
        click.echo("gh CLI not found; install https://cli.github.com/ and authenticate.", err=True)
        sys.exit(1)

    if not owner or not repo:
        det_owner, det_repo = parse_remote_owner_repo()
        owner = owner or det_owner
        repo = repo or det_repo
    if not owner or not repo:
        click.echo("Could not determine owner/repo; specify --owner and --repo.", err=True)
        sys.exit(3)

    run_cmd(
        [
            "gh",
            "api",
            "--method",
            "PUT",
            f"/repos/{owner}/{repo}/pages",
            "-f",
            'source={"type":"workflow"}',
        ],
        cwd=REPO_ROOT,
        check=False,
    )
    click.echo("Attempted to configure Pages to use GitHub Actions.")


@cli.command("commit-initial")
@click.option(
    "--message", default=None, help="Commit message; defaults to template customization message if not provided."
)
def commit_initial(message: str | None):
    """Commit all changes with requested identity."""
    ensure_git_repo()
    run_cmd(["git", "add", "-A"], cwd=REPO_ROOT)
    # Choose a sensible default commit message
    if not message:
        message = "Customize project template"
    # Only commit if there are staged changes
    diff = run_cmd(["git", "diff", "--cached", "--quiet"], cwd=REPO_ROOT, check=False)
    if isinstance(diff, str):
        pass  # won't be reached when --quiet
    # git diff --quiet returns 1 when there are changes
    ret = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=REPO_ROOT).returncode
    if ret == 0:
        click.echo("No staged changes to commit.")
        return
    run_cmd(["git", "commit", "-m", message], cwd=REPO_ROOT)
    click.echo("Committed changes.")


@cli.command("push")
@click.option("--branch", default="main", help="Branch to push to (default: main)")
def push(branch: str):
    """Push to the given branch (default: main)."""
    ensure_git_repo()
    try:
        run_cmd(["git", "push", "origin", branch], cwd=REPO_ROOT, check=True)
        click.echo(f"Pushed to {branch}.")
    except subprocess.CalledProcessError as e:
        click.echo("Failed to push. Ensure you have write access or provide credentials.", err=True)
        click.echo(str(e), err=True)
        sys.exit(e.returncode)


@cli.command("blueprint-init")
@click.option(
    "--auto-install-deps/--no-auto-install-deps",
    default=True,
    help="Attempt to install system deps (Graphviz) if missing.",
)
@click.option(
    "--author",
    required=True,
    help="Author name(s) to appear in the generated documents. Multiple authors should be separated by ' \\and '.",
)
def blueprint_init(auto_install_deps: bool, author: str):
    """Run `uvx leanblueprint new` and auto-resolve Graphviz headers if needed.

    Tries to install `graphviz` + headers using the available package manager (apt/dnf/yum/pacman/brew)
    when pygraphviz fails due to missing `graphviz/cgraph.h`.
    """
    try:
        run_cmd(["uv", "run", "scripts/leanblueprint.py", "new", "--author", author], cwd=REPO_ROOT, check=True)
        click.echo("Initialized blueprint.")

        # Remove the Python script
        py_script = REPO_ROOT / "scripts" / "leanblueprint.py"
        if py_script.exists():
            try:
                py_script.unlink()
            except Exception:
                pass

        return
    except FileNotFoundError:
        click.echo("uv not found; install uv: https://docs.astral.sh/uv/getting-started/installation/", err=True)
        sys.exit(1)
    except subprocess.CalledProcessError:
        # Retry with capture to inspect the error
        out = (
            run_cmd(
                ["uv", "run", "scripts/leanblueprint.py", "new", "--author", author],
                cwd=REPO_ROOT,
                check=False,
                capture=True,
            )
            or ""
        )
        if "graphviz/cgraph.h" in out or "pygraphviz" in out:
            click.echo("Detected missing Graphviz headers required by pygraphviz.", err=True)
            if auto_install_deps:
                click.echo("Attempting to install Graphviz development packages...")
                if try_install_graphviz_dev(verbose=True):
                    # retry
                    try:
                        run_cmd(
                            ["uv", "run", "scripts/leanblueprint.py", "new", "--author", author],
                            cwd=REPO_ROOT,
                            check=True,
                        )
                        click.echo("Initialized blueprint after installing Graphviz.")

                        # Remove the Python script
                        py_script = REPO_ROOT / "scripts" / "leanblueprint.py"
                        if py_script.exists():
                            try:
                                py_script.unlink()
                            except Exception:
                                pass

                        return
                    except subprocess.CalledProcessError as e2:
                        click.echo("Blueprint init failed after dependency install.", err=True)
                        click.echo(e2.stdout if hasattr(e2, "stdout") else str(e2), err=True)
                        sys.exit(e2.returncode)
                else:
                    click.echo(
                        "Auto-install failed or not supported. Please install Graphviz headers manually.", err=True
                    )
            # Provide manual instructions
            click.echo("Manual install suggestions:", err=True)
            click.echo(
                "- Debian/Ubuntu: sudo apt-get update && sudo apt-get install -y graphviz libgraphviz-dev", err=True
            )
            click.echo("- Fedora: sudo dnf install -y graphviz graphviz-devel", err=True)
            click.echo("- RHEL/CentOS: sudo yum install -y graphviz graphviz-devel", err=True)
            click.echo("- Arch: sudo pacman -Sy --noconfirm graphviz", err=True)
            click.echo("- macOS (Homebrew): brew install graphviz", err=True)
            sys.exit(1)
        else:
            click.echo("Failed to initialize blueprint.", err=True)
            click.echo(out, err=True)
            sys.exit(1)


@cli.command("build-lean")
def build_lean():
    """Build Lean project locally: lake cache + build."""
    env = ensure_elan_and_toolchain()
    # Update deps and fetch mathlib cache (best-effort), then build
    run_cmd(["lake", "update"], cwd=REPO_ROOT, check=False, env=env)
    run_cmd("lake exe cache get || true", cwd=REPO_ROOT, check=False, env=env)
    run_cmd(["lake", "build"], cwd=REPO_ROOT, check=True, env=env)
    click.echo("Lean build complete.")


@cli.command("blueprint-pdf")
def blueprint_pdf():
    """Build blueprint PDF using uvx leanblueprint pdf."""
    try:
        run_cmd(["uvx", "leanblueprint", "pdf"], cwd=REPO_ROOT, check=True)
        click.echo("Blueprint PDF built.")
    except FileNotFoundError:
        click.echo("uvx not found; install uv: https://docs.astral.sh/uv/getting-started/installation/", err=True)
        sys.exit(1)


@cli.command("blueprint-web")
def blueprint_web():
    """Build and serve blueprint web locally."""
    try:
        run_cmd(["uvx", "leanblueprint", "web"], cwd=REPO_ROOT, check=True)
        run_cmd(["uvx", "leanblueprint", "serve"], cwd=REPO_ROOT, check=True)
        click.echo("Blueprint web built and serving.")
    except FileNotFoundError:
        click.echo("uvx not found; install uv: https://docs.astral.sh/uv/getting-started/installation/", err=True)
        sys.exit(1)


def _detect_origin_default_branch() -> str | None:
    try:
        out = run_cmd(["git", "remote", "show", "origin"], cwd=REPO_ROOT, capture=True)
        if out:
            for line in out.splitlines():
                line = line.strip()
                if line.lower().startswith("head branch:"):
                    return line.split(":", 1)[1].strip()
    except subprocess.CalledProcessError:
        return None
    return None


def _resolve_remote_commit(remote_url: str, ref: str) -> str | None:
    # Try to resolve ref to a commit on the remote URL
    try:
        out = run_cmd(["git", "ls-remote", remote_url, ref], capture=True)
        if out:
            first = out.splitlines()[0].split() if out.splitlines() else []
            if first:
                return first[0]
    except subprocess.CalledProcessError:
        pass
    return None


def _run_cli_in(dest: Path, *args: str):
    # Invoke this CLI in another working tree
    exe = sys.executable
    cmd = [exe, str(dest / "lean_runbook.py"), *args]
    run_cmd(cmd, cwd=dest, check=True)


@cli.command("quickstart")
@click.option("--name", required=True, help="New project name (replaces 'Project').")
@click.option(
    "--author",
    required=True,
    help="Author name(s) to appear in the generated documents. Multiple authors should be separated by ' \\and '.",
)
@click.option(
    "--dest",
    type=click.Path(path_type=Path),
    default=None,
    help="Destination directory to clone into (defaults to parent/name).",
)
@click.option("--source-url", default=None, help="Override source repo URL (defaults to this repo's origin).")
@click.option("--ref", default=None, help="Git ref to clone (defaults to origin's default branch HEAD).")
@click.option(
    "--configure-gh/--no-configure-gh", default=True, help="Attempt to set secrets and Pages via gh in the cloned repo."
)
@click.option(
    "--auto-install-deps/--no-auto-install-deps",
    default=True,
    help="Attempt to install Graphviz dev packages if needed (in the cloned repo).",
)
@click.option(
    "--install-lean/--no-install-lean",
    default=True,
    help="Ensure Lean toolchain + Lake are installed, then build (in the cloned repo).",
)
@click.option("--in-place/--clone", default=True, help="Run in-place instead of cloning (legacy behavior).")
def quickstart(
    name: str,
    author: str,
    dest: Path | None,
    source_url: str | None,
    ref: str | None,
    configure_gh: bool,
    auto_install_deps: bool,
    install_lean: bool,
    in_place: bool,
):
    """Quickstart a new project. By default, clones the repo at a stable commit and specializes there.

    When --in-place is used, performs the setup in the current working tree (legacy behavior).
    """

    if in_place:
        # Legacy behavior within current repo
        init_project.callback(name=name)  # type: ignore[attr-defined]
        if configure_gh:
            try:
                set_secrets.callback(owner=None, repo=None)  # type: ignore[attr-defined]
            except SystemExit:
                pass
            try:
                configure_pages.callback(owner=None, repo=None)  # type: ignore[attr-defined]
            except SystemExit:
                pass
        commit_initial.callback(message=f"Customize project template for {name}")  # type: ignore[attr-defined]
        if install_lean:
            build_lean.callback()  # type: ignore[attr-defined]
        try:
            blueprint_init.callback(auto_install_deps=auto_install_deps, author=author)  # type: ignore[attr-defined]
        except SystemExit:
            pass
        click.echo("Quickstart complete (in-place).")
        return

    # Clone-and-specialize behavior (default)
    # Determine source URL
    if not source_url:
        owner, repo = parse_remote_owner_repo()
        if not owner or not repo:
            click.echo("Could not determine origin URL; specify --source-url.", err=True)
            sys.exit(2)
        try:
            source_url = run_cmd(["git", "config", "--get", "remote.origin.url"], cwd=REPO_ROOT, capture=True).strip()
        except subprocess.CalledProcessError:
            click.echo("Could not read origin URL; specify --source-url.", err=True)
            sys.exit(2)

    # Determine ref to clone
    ref_to_use = ref
    if not ref_to_use:
        head_branch = _detect_origin_default_branch() or "main"
        ref_to_use = f"refs/heads/{head_branch}"
    commit = _resolve_remote_commit(source_url, ref_to_use)
    if not commit:
        click.echo(f"Could not resolve commit for ref {ref_to_use} on {source_url}.", err=True)
        sys.exit(3)

    # Destination directory
    if dest is None:
        dest = (REPO_ROOT.parent / name).resolve()
    if dest.exists() and any(dest.iterdir()):
        click.echo(f"Destination {dest} already exists and is not empty. Choose a different --dest.", err=True)
        sys.exit(4)

    # Clone and checkout the exact commit
    click.echo(f"Cloning {source_url} to {dest}...")
    run_cmd(["git", "clone", "--no-tags", "--depth", "1", source_url, str(dest)], check=True)
    # Ensure the specific commit is available and checked out
    run_cmd(["git", "fetch", "origin", commit, "--depth", "1"], cwd=dest, check=True)
    run_cmd(["git", "checkout", "-q", commit], cwd=dest, check=True)

    # Specialize within the cloned repo using this CLI inside that repo
    _run_cli_in(dest, "init-project", "--name", name)
    if configure_gh:
        try:
            _run_cli_in(dest, "set-secrets")
        except subprocess.CalledProcessError:
            pass
        try:
            _run_cli_in(dest, "configure-pages")
        except subprocess.CalledProcessError:
            pass
    _run_cli_in(dest, "commit-initial", "--message", f"Customize project template for {name}")
    if install_lean:
        try:
            _run_cli_in(dest, "build-lean")
        except subprocess.CalledProcessError:
            # Surface error but keep destination for inspection
            click.echo("Lean build failed in cloned repo.", err=True)
            raise
    try:
        args = ["blueprint-init"] + (["--no-auto-install-deps"] if not auto_install_deps else [])
        _run_cli_in(dest, *args)
    except subprocess.CalledProcessError:
        pass

    click.echo(f"Quickstart complete. New project at: {dest}")


@cli.command("install-lean")
def install_lean_cmd():
    """Ensure elan + toolchain are installed and print versions."""
    env = ensure_elan_and_toolchain()
    out_lean = run_cmd(["lean", "--version"], env=env, capture=True) or ""
    out_lake = run_cmd(["lake", "--version"], env=env, capture=True) or ""
    click.echo(out_lean.strip())
    click.echo(out_lake.strip())


if __name__ == "__main__":
    cli()
