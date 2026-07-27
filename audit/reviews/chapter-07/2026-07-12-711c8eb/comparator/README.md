# Comparator challenge status

The challenge statement was independently authored after inspecting Grimmett's source quantifier
order. The function `pi` is selected after fixed `d,k` and before `delta` and the probability law;
the subtype neighborhood at `1 : I` is the one-sided endpoint limit inside `[0,1]`. The explicit
`k≥1` source-range premise is harmless because the production theorem is stronger and also covers
range zero.

`Solution.lean` is a no-`sorry` wrapper around the production cubic theorem and compiles directly.
`Challenge.lean` contains the one intentional open proof accepted by the Comparator protocol and
is not imported anywhere else.

Comparator was **not run locally**. This macOS environment lacks the pinned Linux `landrun`,
Lean-compatible `lean4export`, and Comparator toolchain. A Lean compilation is not reported as a
Comparator pass. The follow-up CI task must hash the challenge before exposing the solution, run
the pinned upstream workflow in an unprivileged Linux sandbox, and record tool revisions, exact
command, exit status, and stable log link here.
