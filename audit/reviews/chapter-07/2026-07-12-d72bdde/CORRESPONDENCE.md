# Theorem 7.65 focused correspondence review

Reviewed commit: `d72bdde`

| Source | Natural-language statement | Lean declaration | Review disposition |
|---|---|---|---|
| (7.63), p. 179 | `X` dominates `Y` when every bounded increasing measurable observable has at least as large an expectation under `X`. | `StochasticallyDominates` | Exact orientation and observable class. |
| (7.64), p. 179 | Uniform one-step conditional lower bounds along an enumeration imply domination of iid sites. | `sequentialLowerBound_stochasticallyDominates` | Exact, with ratio-free prefix inequalities covering null histories. |
| Theorem 7.65 / (7.66)–(7.67), p. 179 | There exists one nondecreasing `π : [0,1] → [0,1]`, tending to one as `δ→1`, such that one-site density at least `δ` implies domination of iid density `π(δ)`. | `exists_lssDominationDensity` at reviewed commit `d72bdde` | **FAIL:** the declaration at this commit proved only `∀q<1, ∃δ<1`. The independent report identified the missing function, monotonicity, limit, and `δ=1` endpoint. |
| (7.114)–(7.122), pp. 193–195 | Independent dilution plus a history partition proves the finite LSS comparison. | `lssConstraintLowerBound`, `finite_lssDomination`, `lss_stochasticallyDominates` | The finite induction is followed by a proved countable regularity lift; no monotone-class premise is assumed. |

The target density in the fixed-target corollary is required to be strictly below one.
`LSSCounterexamples.lean` proves that removing this restriction while retaining an input threshold
strictly below one is false even for a one-site iid field. The literal source theorem was not
present at this frozen revision; it is repaired in the subsequent review run. Time and token fields
remain unreported because this review and theorem window occurred after the active tracker pause.
