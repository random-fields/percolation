# Chapter 11 Comparator challenge

`Challenge.lean` was authored by the independent Claude reviewer from Grimmett's statements.  It
contains the only intentional `sorry` terms in this review run.  Its ten challenges include the
complete three-part statement of Theorem 11.24.  `Solution.lean` independently wraps the
production declarations with the same theorem names and exact types.

Local development checks:

```sh
lake env lean Challenge.lean
lake env lean Solution.lean
```

Both pass.  These ordinary Lean checks are not a trusted Comparator pass.  The local macOS host
does not provide `landrun`, `lean4export`, or Comparator.  The trusted command runs only in the
pinned Linux workflow `.github/workflows/chapter11-comparator.yml`, using:

- Lean `v4.30.0`;
- Comparator revision `099775bf2e6073fcb22aacd3a2809fdeac3fc84a`;
- Landrun revision `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`.

Until that CI job passes, Comparator status is **pending / not run locally**, never `PASS`.
