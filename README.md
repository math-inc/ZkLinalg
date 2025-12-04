# ZkLinalg

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
