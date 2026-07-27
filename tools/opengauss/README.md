# OpenGauss integration for the percolation project

This directory provides a pinned, project-local OpenGauss installation and a
bounded Codex launcher. It deliberately does not vendor generated environments,
credentials, or the 20 MB upstream source tree into Git; `bootstrap.sh`
downloads the audited source into the ignored `.state/` directory.

## Pinned upstream

- Repository: `math-inc/OpenGauss`
- Commit: `f87633900ae185b8037bf451a914fe7eeae1eb08`
- Upstream package version: `0.2.2`
- Archive SHA-256:
  `05410730774ba7957678184bf2c2a7bc7ce7238e1a873277371e4d586f7cd301`
- License: MIT

The commit was the tip of `main` returned by GitHub on 2026-07-26. The pin and
checksum live in `pins.env`, so installation is reproducible and reviewable.

Install and verify with:

```bash
./tools/opengauss/bootstrap.sh
./tools/opengauss/verify.sh
```

To install upstream's test dependencies in the same isolated environment:

```bash
./tools/opengauss/bootstrap.sh --dev
./tools/opengauss/verify.sh --upstream-tests
```

The bootstrap uses an isolated uv-managed Python 3.13 environment. It does not
run upstream's `scripts/install.sh`, install Homebrew packages, create tmux
sessions, modify `~/.gauss`, or change the repository's Git state.

The upstream editable-package metadata omits the top-level `swarm_manager.py`
module even though the interactive frontend imports it. `run.sh` therefore adds
the pinned source root to `PYTHONPATH`; this is a project-local packaging adapter,
not a modification of the downloaded source.

## What OpenGauss actually provides

OpenGauss is a terminal frontend around separate Claude Code or Codex CLI
processes. For Lean projects it:

1. registers a project through `.gauss/project.yaml`;
2. downloads and stages `cameronfreer/lean4-skills`;
3. configures `lean-lsp-mcp` through `uv`/`uvx`;
4. maps commands such as `/prove` and `/autoformalize` to the corresponding
   `/lean4:*` workflow contract;
5. tracks child CLI processes in its in-process `SwarmManager` and exposes them
   through `/swarm`.

It is not a Python theorem prover, a replacement for Lean, or an API that can
adopt already-running Codex collaboration agents.

## Compatibility with this Codex session

There is no direct integration. The Codex collaboration tools used in this
session are host-managed and expose no process or mailbox handle to OpenGauss.
OpenGauss's `SwarmManager` only knows subprocesses that OpenGauss starts itself.
Starting those subprocesses would create a second, independent agent team that
shares the same files but not task state, approvals, messages, or lifecycle.

Upstream 0.2.2 also launches the Codex backend with
`--dangerously-bypass-approvals-and-sandbox`. That is inappropriate as an
unqualified default in this repository. `run.sh` places `bin/codex` first on
`PATH`; the shim removes that flag and enforces:

```text
--sandbox workspace-write --ask-for-approval never
```

The safe policy contains file writes to the selected workspace and makes
out-of-policy operations fail instead of silently escalating. This is a local
adapter; upstream source is left unchanged.

For the active theorem-11.11 effort, use the host's native collaboration agents.
They are the only agents the current session can supervise. OpenGauss is suitable
for a later, exclusive terminal run or a dedicated worktree, not for supervising
the agents already active here.

## Running OpenGauss separately

Non-agent diagnostics do not require an opt-in. `doctor` may initialize files
inside the ignored project-local `.state/gauss-home`, but it does not launch a
model-backed child:

```bash
./tools/opengauss/run.sh version
./tools/opengauss/run.sh doctor
```

Before launching an interactive or managed workflow, ensure no other agent is
editing that worktree. Then explicitly opt in:

```bash
PERCOLATION_OPENGAUSS_ALLOW_NESTED_AGENTS=1 ./tools/opengauss/run.sh
```

Inside Gauss, register the current Lean repository and select the safe Codex
backend:

```text
/project init
/autoformalize-backend codex
/doctor
/autoformalize Grimmett Theorem 11.11
/swarm
```

`/project init` intentionally has not been run by this integration: it creates
`.gauss/project.yaml` and runtime directories at the repository root, which is a
separate project-state decision. OpenGauss may also stage Codex authentication
inside ignored `.state/managed`; never commit `.state/`.

## Validated host status

On 2026-07-26, `run.sh doctor` exited successfully and found Python 3.13,
`codex`, Codex login credentials, `uvx`, `lake`, `git`, and `rg`. It correctly
reported that this repository is not yet an active Gauss project because the
root `.gauss/project.yaml` was intentionally not created. Optional Gauss API
provider setup, a project template source, tmux, and messaging/browser extras
are not required by this adapter's smoke test and remain unconfigured.

## Verification scope

`verify.sh` checks the archive checksum and revision marker, imports the installed
package, parses the theorem-11.11 `/autoformalize` workflow, registers a queued
task in `SwarmManager`, confirms the CLI version, and exercises the safety shim.
The smoke test never starts a model-backed agent or modifies Lean files.

With `--upstream-tests`, it also runs the pinned upstream
`test_swarm_manager.py` and `test_autoformalize.py` suites. At the recorded pin,
that is 108 tests.

This proves the local package and adapter are runnable. It does not prove that an
external model session is authenticated, that `lean4-skills` can be fetched at a
future date, or that an OpenGauss child can formalize Theorem 11.11.
