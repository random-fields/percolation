# Assurance Conventions

This project follows `math-commons/formalization-assurance`: verification, validation,
faithfulness, axiom vetting, `formalization.yaml`, and comparator-style source alignment.

| Setting | Where |
|---|---|
| Project card | `formalization.yaml` |
| Axiom audit | `AXIOM_AUDIT.md` |
| Faithfulness index | `audit/FAITHFULNESS.md` |
| Validation index | `audit/VALIDATION.md` |
| Per-topic comparator cards | `audit/topics/` |
| Axiom vetting records | `audit/vetting/` |
| Large-scale automated review protocol | `AUTOMATED_REVIEW.md` |
| Per-run review evidence | `audit/reviews/` |

Comparator cards should map source location to Lean declaration, state any divergence, and record
review/validation status.

Chapter-scale and generated batches additionally follow `AUTOMATED_REVIEW.md`; a topic card alone
is not enough to support a batch-level fidelity claim.
