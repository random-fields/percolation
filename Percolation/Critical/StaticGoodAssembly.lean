import Percolation.Critical.StaticCoalescence

/-!
# Assembling static good-box conditions

Grimmett defines `M(n)` as a component largest by cardinality, but controls competing clusters
by diameter.  Passing between these notions requires a geometric cardinality bound; uniqueness
of a macroscopic crossing component alone does not definitionally identify it with `M(n)`.
This file makes that implicit step explicit and packages the deterministic final assembly used
after Lemmas 7.97 and 7.104.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- A finite-box component of diameter below `m` lies in a radius-`m` coordinate box around any
one of its vertices.  Hence it contains at most `(2m+1)^d` vertices. -/
theorem finiteBoxGraphComponentCard_le_boxCard_of_diameter_lt
    {d : ℕ} {x : Cubic d} {n m : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent)
    (hdiam : finiteBoxGraphComponentDiameter C < m) :
    finiteBoxGraphComponentCard C ≤ (2 * m + 1) ^ d := by
  classical
  obtain ⟨u, hu⟩ := finiteBoxGraphComponentVertices_nonempty C
  have hsubset : finiteBoxGraphComponentVertices C ⊆ cubicMetricBox d u m := by
    intro v hv
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    have hdist : cubicLInfDist u v ≤ finiteBoxGraphComponentDiameter C := by
      calc
        cubicLInfDist u v ≤
            (finiteBoxGraphComponentVertices C).sup fun z ↦ cubicLInfDist u z :=
          Finset.le_sup hv
        _ ≤ (finiteBoxGraphComponentVertices C).sup fun y ↦
            (finiteBoxGraphComponentVertices C).sup fun z ↦ cubicLInfDist y z :=
          Finset.le_sup (f := fun y ↦
            (finiteBoxGraphComponentVertices C).sup fun z ↦ cubicLInfDist y z) hu
        _ = finiteBoxGraphComponentDiameter C := rfl
    exact hdist.trans hdiam.le
  rw [finiteBoxGraphComponentCard]
  exact (Finset.card_le_card hsubset).trans_eq (cubicMetricBox_card d u m)

/-- Cardinality of every component is bounded by that of the canonical largest component. -/
theorem finiteBoxGraphComponentCard_le_largest {d : ℕ} (x : Cubic d) (n : ℕ)
    (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n})
    (C : G.ConnectedComponent) :
    finiteBoxGraphComponentCard C ≤
      finiteBoxGraphComponentCard (finiteBoxGraphLargestComponent x n G) := by
  have hkey := finiteBoxGraphComponentKey_le_largest x n G C
  exact (Prod.Lex.toLex_le_toLex.mp hkey).elim (fun h ↦ h.le) (fun h ↦ h.1.le)

/-- Deterministic assembly of Grimmett's three good-box clauses.

The parameter `m` is the diameter scale at which a second-cluster estimate is available.  The
strict volume comparison ensures that a component at least as large as the crossing component
cannot have diameter below `m`; this identifies the cardinality-largest component with the
crossing component. -/
theorem FiniteBoxGraph.isEpsilonGood_of_largeCrossing_of_noSecondMacroscopic
    {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n m q : ℕ)
    (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n})
    (hmn : m ≤ n)
    (hqBox : (2 * m + 1) ^ d < q)
    (hqDensity : (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q)
    (hlarge : FiniteBoxGraph.HasLargeCrossing q G)
    (hnoSecond : ¬ FiniteBoxGraph.HasSecondMacroscopic m G) :
    FiniteBoxGraph.IsEpsilonGood p ε x n G := by
  let M := finiteBoxGraphLargestComponent x n G
  obtain ⟨C, hCcross, hqC⟩ := hlarge
  have hCMcard : finiteBoxGraphComponentCard C ≤ finiteBoxGraphComponentCard M :=
    finiteBoxGraphComponentCard_le_largest x n G C
  have hMdiam : m ≤ finiteBoxGraphComponentDiameter M := by
    apply le_of_not_gt
    intro hdiam
    have hMcard := finiteBoxGraphComponentCard_le_boxCard_of_diameter_lt M hdiam
    omega
  have hCM : C = M := by
    by_contra hne
    exact hnoSecond ⟨C, M, hne, hCcross, hMdiam⟩
  subst C
  refine ⟨hCcross, ?_, ?_⟩
  · intro D hDn
    by_contra hDM
    exact hnoSecond ⟨M, D, Ne.symm hDM, hCcross, hmn.trans hDn⟩
  · exact hqDensity.trans (by exact_mod_cast hqC)

/-- Event-level form of the deterministic assembly. -/
theorem mem_epsilonGoodBoxEvent_of_largeCrossing_of_not_secondMacroscopic
    {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n m q : ℕ)
    (hmn : m ≤ n)
    (hqBox : (2 * m + 1) ^ d < q)
    (hqDensity : (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q)
    {ω : EdgeConfiguration d}
    (hlarge : ω ∈ largeCrossingClusterEvent d q n x)
    (hnoSecond : ω ∉ secondMacroscopicClusterEvent d m n x) :
    ω ∈ epsilonGoodBoxEvent d p ε x n := by
  exact FiniteBoxGraph.isEpsilonGood_of_largeCrossing_of_noSecondMacroscopic
    p ε x n m q (finiteBoxOpenGraph d ω x n) hmn hqBox hqDensity hlarge hnoSecond

/-- The bad-box event is covered by failure of the large crossing event or occurrence of a
second macroscopic component. -/
theorem epsilonGoodBoxEvent_compl_subset_largeCrossing_compl_union_secondMacroscopic
    {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n m q : ℕ)
    (hmn : m ≤ n)
    (hqBox : (2 * m + 1) ^ d < q)
    (hqDensity : (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q) :
    (epsilonGoodBoxEvent d p ε x n)ᶜ ⊆
      (largeCrossingClusterEvent d q n x)ᶜ ∪
        secondMacroscopicClusterEvent d m n x := by
  intro ω hbad
  by_cases hlarge : ω ∈ largeCrossingClusterEvent d q n x
  · by_cases hsecond : ω ∈ secondMacroscopicClusterEvent d m n x
    · exact Or.inr hsecond
    · exact False.elim (hbad
        (mem_epsilonGoodBoxEvent_of_largeCrossing_of_not_secondMacroscopic
          p ε x n m q hmn hqBox hqDensity hlarge hsecond))
  · exact Or.inl hlarge

/-- Probability-level union bound for the final static-good-box assembly. -/
theorem one_sub_bernoulliBondMeasure_real_epsilonGoodBoxEvent_le
    {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n m q : ℕ)
    (hmn : m ≤ n)
    (hqBox : (2 * m + 1) ^ d < q)
    (hqDensity : (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q) :
    1 - (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε x n) ≤
      1 - (bernoulliBondMeasure d p).real (largeCrossingClusterEvent d q n x) +
        (bernoulliBondMeasure d p).real (secondMacroscopicClusterEvent d m n x) := by
  rw [← probReal_compl_eq_one_sub (measurableSet_epsilonGoodBoxEvent d p ε x n),
    ← probReal_compl_eq_one_sub (measurableSet_largeCrossingClusterEvent d q n x)]
  exact (measureReal_mono
    (epsilonGoodBoxEvent_compl_subset_largeCrossing_compl_union_secondMacroscopic
      p ε x n m q hmn hqBox hqDensity)
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)

/-- Analytic final step of Theorem 7.61.  Once a suitably large crossing cluster occurs with
probability tending to one and a competing diameter-`m(n)` cluster occurs with probability
tending to zero, the deterministic good-box assembly upgrades these estimates to the full
`ε`-good event. -/
theorem epsilonGoodBox_probability_tendsto_one_of_largeCrossing_of_second
    {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (m q : ℕ → ℕ)
    (hconstraints : ∀ᶠ n in Filter.atTop,
      m n ≤ n ∧ (2 * m n + 1) ^ d < q n ∧
        (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤ q n)
    (hlarge : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (largeCrossingClusterEvent d (q n) n x))
      Filter.atTop (nhds 1))
    (hsecond : Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d (m n) n x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p ε x n))
      Filter.atTop (nhds 1) := by
  let μ := bernoulliBondMeasure d p
  let G : ℕ → Set (EdgeConfiguration d) := fun n ↦ epsilonGoodBoxEvent d p ε x n
  let L : ℕ → Set (EdgeConfiguration d) := fun n ↦ largeCrossingClusterEvent d (q n) n x
  let S : ℕ → Set (EdgeConfiguration d) := fun n ↦
    secondMacroscopicClusterEvent d (m n) n x
  have hlargeFail : Filter.Tendsto (fun n ↦ 1 - μ.real (L n))
      Filter.atTop (nhds 0) := by
    simpa [μ, L] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlarge
  have hrhs : Filter.Tendsto (fun n ↦ 1 - μ.real (L n) + μ.real (S n))
      Filter.atTop (nhds 0) := by
    simpa [μ, S] using hlargeFail.add hsecond
  have hbad : Filter.Tendsto (fun n ↦ 1 - μ.real (G n))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦ sub_nonneg.mpr measureReal_le_one)
      (hconstraints.mono fun n hn ↦ ?_) hrhs
    simpa [μ, G, L, S] using
      one_sub_bernoulliBondMeasure_real_epsilonGoodBoxEvent_le
        p ε x n (m n) (q n) hn.1 hn.2.1 hn.2.2
  have hEq : (fun n ↦ μ.real (G n)) = fun n ↦ 1 - (1 - μ.real (G n)) := by
    funext n
    ring
  rw [hEq]
  simpa [μ, G] using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad

end Percolation
