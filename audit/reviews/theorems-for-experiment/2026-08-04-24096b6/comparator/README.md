# Comparator status

`Challenge.lean` restates the three source-facing types, and `Solution.lean` wraps the production
declarations without adding `sorry`. Both files compile locally, which checks type agreement but
is not a trusted Comparator pass.

Trusted Comparator was not run. The requested declarations are statement-only design targets
whose production bodies intentionally contain `sorry`, and `sorryAx` is deliberately absent from
`config.json`'s permitted axiom list. Comparator and proof-trust gates remain open until the three
proofs are supplied.
