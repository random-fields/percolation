#!/usr/bin/env python3
"""Side-effect-free smoke test for the vendored OpenGauss orchestration API."""

from __future__ import annotations

import json

import gauss_cli
from gauss_cli.autoformalize import (
    _parse_managed_workflow_command,
    normalize_autoformalize_backend_name,
)
from swarm_manager import SwarmManager


def main() -> None:
    assert normalize_autoformalize_backend_name("openai_codex") == "codex"

    workflow = _parse_managed_workflow_command(
        "/autoformalize formalize Grimmett Theorem 11.11"
    )
    assert workflow.workflow_kind == "autoformalize"
    assert workflow.backend_command == (
        "/lean4:autoformalize formalize Grimmett Theorem 11.11"
    )

    SwarmManager.reset()
    manager = SwarmManager()
    task = manager.spawn(
        theorem="Grimmett Theorem 11.11",
        description="registration-only smoke test",
        workflow_kind=workflow.workflow_kind,
        workflow_command=workflow.backend_command,
        backend_name="codex",
    )
    assert task.status == "queued"
    assert manager.get_task(task.task_id) is task
    SwarmManager.reset()

    print(
        json.dumps(
            {
                "opengauss_version": gauss_cli.__version__,
                "backend": "codex",
                "workflow": workflow.backend_command,
                "swarm_registration": "ok",
                "subprocess_spawned": False,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
