# Chapter 11 adversarial checks

`Chapter11Counterexamples.lean` checks the totalized-logarithm, density-zero, density-one,
tube-width-zero, and degenerate RSW endpoints.  In particular, the unguarded external Lemma
11.73 input is consistent at `l=0`: the corresponding crossing event is `Set.univ`.

Further dispositions:

- Removing `p>1/2` from Lemma 11.22 is rejected.  At density zero every positive crossing count
  fails almost surely, so an exponentially small lower-tail conclusion cannot hold.
- The proved centered version of Lemma 11.22 concerns `[0,n+1]×[-n,n]`; no coercion or monotone
  event inclusion silently turns it into the literal `[0,n+1]×[0,n]` statement.  The literal
  source theorem remains the explicitly cited external axiom.
- A literal uniqueness theorem for a based, oriented `DualCircuit` record is rejected: cyclic
  rebasing and reversal create different records for the same geometric circuit.  Proposition
  11.2 therefore states uniqueness of the crossed primal-edge finset.
- The strict `<1` assumptions in Theorems 11.115–11.116 are not erased by the unit-interval type;
  the value `1 : I` is admitted by the type and is explicitly excluded by the public hypotheses.

Failure to find an additional counterexample is not treated as a proof.
