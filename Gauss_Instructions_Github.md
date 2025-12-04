# Using Gauss through GitHub UI

## Layout

- `blueprint/src/content.tex`: main blueprint file where all the latex content is written
- `<project-name>/Main.lean`: main Lean file where the formalization is happening by default

You can add new latex files and Lean files as needed. Here is how to proceed:

1. LaTeX files should be referenced by `blueprint/src/web.tex` so that Gauss can find them.
2. Lean files should be referenced by `<project-name>.lean` so that they are part of the Lean project.

## Quick overview: Actions tab → "Gauss" → Run workflow

- Go to GitHub → Actions (tab at the top) → Gauss (left) → Run workflow (right)
- Inputs:
  - Command: `gauss-prove` or `gauss-statement`
  - Params: space-separated names or labels (optional). If omitted, Gauss will auto-discover all targets.
  - Budget: `very-low`, `low`, `medium`, `high`, `heavy`. We recommend `heavy`.
  
Remaining optional inputs (we recommend keeping the defaults):

- Max labels: limit the number of statements to process for `gauss-statement` ("0" = no limit) in one workflow run
- Base ref: the branch/ref to run against (defaults to the repo's default branch)
- Init command: an optional shell command run after cloning (e.g., to prepare tools).

## End-to-end loop: Gauss workflow → PR → merge → manual edits → Gauss workflow

The typical workflow uses two complementary commands:

1. **`gauss-statement`**: Formalizes LaTeX statements into Lean (with `sorry` placeholders)
2. **`gauss-prove`**: Proves the Lean statements containing `sorry`

### Best Practices

- **Do not manually add `\leanok` tags** in your LaTeX, `gauss-statement` adds these automatically when formalization succeeds. This allows Gauss to detect which statements still need formalization. `gauss-statement` will skip statements that already have `\leanok` tags. However, it can be useful to manually add `\leanok` to statements you don't want Gauss to formalize. For example, it can be a way to indicate to Gauss to use a certain definition or lemma from Mathlib instead of trying to re-formalize it.
- The `\lean{...}` tags are also added automatically by the `gauss-statement` workflow.

### Important Notes

The project should be compilable, i.e. `lake build` should succeed before running Gauss.

### Step 1: Run Gauss

- Trigger via Actions UI as explained above.
- Choose the command:
  - **`gauss-statement`**: Formalizes LaTeX statements into Lean statements (written to `Main.lean` by default). It automatically detects statements without `\leanok` tags for formalization and adds `\leanok` and `\lean{...}` tags upon success. Uses `sorry` placeholders for proofs.
  - **`gauss-prove`**: Attempts to prove Lean statements that contain `sorry` in their proofs.
- Choose the compute budget. Higher compute budget means higher chance of success but longer wait time.
  - **Recommendation**: Use `heavy` budget for `gauss-statement` to maximize success rate.
- Expected run time: from ~30min (few statements, low budget) to several hours (many statements, high budget).
- A PR will be created/updated if Gauss succeeds at least partially.

### Step 2: Review the PR

- The PR title will be "gauss-prove updates" or "gauss-statement updates".
- The message body may include:
  - Formalization/Proof Summary
  - Collapsible Analysis
- (optional) Push any manual changes to the base branch to update the PR.
- Once satisfied, merge the generated PR to bring Gauss updates into your main branch.

### Step 3: Manual edits

- Make any hand-tuned changes in the repo (fix style, naming, blueprint, comments, refactors, etc.).

### Step 4: Re-run the Gauss workflow

- Trigger Gauss again using the updated main branch.
- Iterate until everything is formalized/proved.
