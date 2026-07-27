import Percolation.Bernoulli.FKGInfinite
import Percolation.Critical.Basic

/-!
# Vertex-independence of the critical probability (Theorem 2.8)

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.2, Theorem (2.8), p. 35
(source id `grimmett-percolation-1999`), for bond percolation on the cubic lattice.

Grimmett's argument: by the FKG inequality,
`θ(p, y) ≥ P_p(y ↔ x) · θ(p, x)`, and `P_p(y ↔ x) > 0` for `p > 0`, so the vertex-rooted
percolation probabilities vanish together and the critical probability does not depend on
the reference vertex. This file provides

* `Percolation.thetaFrom`, `Percolation.cubicCriticalProbabilityFrom` — the vertex-rooted
  percolation probability and critical probability;
* `Percolation.connectionEvent` and its measurability, via the direction-word reindexing of
  lattice walks;
* `Percolation.bernoulliBondMeasure_real_connectionEvent_thetaFrom_le` — the FKG surgery
  step;
* `Percolation.cubicCriticalProbabilityFrom_eq` — **Theorem (2.8)**:
  `p_c` is independent of the reference vertex.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

/-! ### Vertex-rooted percolation probability -/

instance (d : ℕ) (p : I) : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
  dsimp [bernoulliBondMeasure]
  infer_instance

/-- The vertex-rooted percolation probability `θ(p, x)`: the probability that `x` lies in
an infinite open cluster (Grimmett p. 35). -/
noncomputable def thetaFrom (d : ℕ) (p : I) (x : Cubic d) : ℝ :=
  (bernoulliBondMeasure d p).real {ω | hasInfiniteOpenClusterFrom d ω x}

@[simp] theorem thetaFrom_origin (d : ℕ) (p : I) :
    thetaFrom d p cubicOrigin = theta d p :=
  rfl

/-- The vertex-rooted critical probability, mirroring
`Percolation.cubicCriticalProbability`. -/
noncomputable def cubicCriticalProbabilityFrom (d : ℕ) (x : Cubic d) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | thetaFrom d p x = 0}) : Set ℝ)

theorem cubicCriticalProbabilityFrom_origin (d : ℕ) :
    cubicCriticalProbabilityFrom d cubicOrigin = cubicCriticalProbability d :=
  rfl

/-! ### Measurability of the vertex-rooted events -/

/-- The vertex-rooted length-at-least event is measurable: lattice walks from `x` are
reindexed by their finite direction words. -/
theorem measurableSet_hasOpenPathOfLengthAtLeastFrom (d : ℕ) (x : Cubic d) (n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
  have hrepr : {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} =
      ⋃ (steps : List (CubicDirection d))
        (_ : n ≤ steps.length ∧ (cubicWalkFrom x steps).IsPath),
        {ω : EdgeConfiguration d | walkIsOpen ω (cubicWalkFrom x steps)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨v, w, hpath, hlen, hopen⟩
      obtain ⟨steps, hend, hcopy, hsteps_len⟩ := exists_cubicWalkFrom_copy_eq w
      refine ⟨steps, ⟨?_, ?_⟩, ?_⟩
      · omega
      · have : ((cubicWalkFrom x steps).copy rfl hend).IsPath := hcopy ▸ hpath
        simpa using this
      · have : walkIsOpen ω ((cubicWalkFrom x steps).copy rfl hend) := hcopy ▸ hopen
        exact (walkIsOpen_copy _ rfl hend).mp this
    · rintro ⟨steps, ⟨hlen, hpath⟩, hopen⟩
      exact ⟨cubicEndpointFrom x steps, cubicWalkFrom x steps, hpath,
        by simpa [cubicWalkFrom_length] using hlen, hopen⟩
  rw [hrepr]
  exact MeasurableSet.iUnion fun steps => MeasurableSet.iUnion fun _ =>
    measurableSet_walkIsOpen (cubicWalkFrom x steps)

/-- The vertex-rooted infinite-cluster event is measurable. -/
theorem measurableSet_hasInfiniteOpenClusterFrom (d : ℕ) (x : Cubic d) :
    MeasurableSet {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} := by
  have hrepr : {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} =
      ⋂ n : ℕ, {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeastFrom d ω x n} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    simpa [hasArbitrarilyLongOpenPathsFrom] using
      hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom (d := d) (ω := ω)
        (x := x)
  rw [hrepr]
  exact MeasurableSet.iInter fun n => measurableSet_hasOpenPathOfLengthAtLeastFrom d x n

/-- The two-point connection event `x ↔ y` (an open walk from `x` to `y`). -/
def connectionEvent (d : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | ∃ w : (cubicGraph d).Walk x y, walkIsOpen ω w}

theorem measurableSet_connectionEvent (d : ℕ) (x y : Cubic d) :
    MeasurableSet (connectionEvent d x y) := by
  have hrepr : connectionEvent d x y =
      ⋃ (steps : List (CubicDirection d)) (h : cubicEndpointFrom x steps = y),
        {ω : EdgeConfiguration d | walkIsOpen ω ((cubicWalkFrom x steps).copy rfl h)} := by
    ext ω
    simp only [connectionEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hopen⟩
      obtain ⟨steps, hend, hcopy, -⟩ := exists_cubicWalkFrom_copy_eq w
      exact ⟨steps, hend, hcopy ▸ hopen⟩
    · rintro ⟨steps, hend, hopen⟩
      exact ⟨(cubicWalkFrom x steps).copy rfl hend, hopen⟩
  rw [hrepr]
  exact MeasurableSet.iUnion fun steps => MeasurableSet.iUnion fun h =>
    measurableSet_walkIsOpen _

/-! ### Monotonicity of the vertex-rooted events -/

theorem isIncreasingEvent_connectionEvent (d : ℕ) (x y : Cubic d) :
    IsIncreasingEvent (connectionEvent d x y) := by
  rintro ω η hωη ⟨w, hopen⟩
  exact ⟨w, fun e he => hωη (hopen e he)⟩

theorem isIncreasingEvent_hasInfiniteOpenClusterFrom (d : ℕ) (x : Cubic d) :
    IsIncreasingEvent {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} := by
  intro ω η hωη hω
  refine Set.Infinite.mono ?_ hω
  rintro y ⟨w, hw⟩
  exact ⟨w, fun e he => hωη (hw e he)⟩

/-! ### Existence of lattice walks and positivity of connections -/

/-- The cubic lattice is connected: any two vertices are joined by a walk (built by moving
one coordinate at a time toward the target). -/
theorem nonempty_cubicWalk (d : ℕ) (x y : Cubic d) :
    Nonempty ((cubicGraph d).Walk x y) := by
  classical
  suffices h : ∀ (n : ℕ) (x : Cubic d), (∑ i, (y i - x i).natAbs) = n →
      Nonempty ((cubicGraph d).Walk x y) from h _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases hxy : x = y
    · subst hxy
      exact ⟨SimpleGraph.Walk.nil⟩
    · have hne : ∃ i, x i ≠ y i := by
        by_contra hall
        refine hxy (funext fun i => ?_)
        by_contra hne'
        exact hall ⟨i, hne'⟩
      obtain ⟨i, hi⟩ := hne
      set a : CubicDirection d := (i, decide (x i < y i)) with ha
      set x' := cubicStepFrom x a with hx'
      have hstep_i : x' i = if x i < y i then x i + 1 else x i - 1 := by
        rw [hx', cubicStepFrom, ha]
        by_cases hlt : x i < y i
        · simp [cubicDirectionIncrement, hlt]
        · simp [cubicDirectionIncrement, hlt, sub_eq_neg_add, add_comm]
      have hstep_ne : ∀ j, j ≠ i → x' j = x j := by
        intro j hj
        rw [hx', cubicStepFrom, ha]
        simp [hj]
      have hdrop : (y i - x' i).natAbs + 1 = (y i - x i).natAbs := by
        rw [hstep_i]
        by_cases hlt : x i < y i
        · simp only [hlt, if_true]
          omega
        · simp only [hlt, if_false]
          have : y i < x i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hi)
          omega
      have hsum : (∑ j, (y j - x' j).natAbs) + 1 = n := by
        rw [← hx]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
          ← Finset.sum_erase_add _ (fun j => (y j - x j).natAbs) (Finset.mem_univ i)]
        have herase : ∑ j ∈ Finset.univ.erase i, (y j - x' j).natAbs =
            ∑ j ∈ Finset.univ.erase i, (y j - x j).natAbs :=
          Finset.sum_congr rfl fun j hj =>
            by rw [hstep_ne j (Finset.mem_erase.mp hj).1]
        omega
      obtain ⟨w⟩ := ih (n - 1) (by omega) x' (by omega)
      exact ⟨SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x a) w⟩

/-- Connections have positive probability for positive densities. -/
theorem bernoulliBondMeasure_real_connectionEvent_pos (d : ℕ) {p : I}
    (hp : 0 < (p : ℝ)) (x y : Cubic d) :
    0 < (bernoulliBondMeasure d p).real (connectionEvent d x y) := by
  obtain ⟨w⟩ := nonempty_cubicWalk d x y
  have hsub : {ω : EdgeConfiguration d |
      walkIsOpen ω (w.toPath : (cubicGraph d).Walk x y)} ⊆ connectionEvent d x y :=
    fun ω hω => ⟨(w.toPath : (cubicGraph d).Walk x y), hω⟩
  refine lt_of_lt_of_le ?_ (measureReal_mono hsub)
  exact bernoulliBondMeasure_real_walkIsOpen_pos p _ w.toPath.2.isTrail hp

/-! ### The FKG surgery step -/

/-- Grafting a connection onto an infinite cluster: if `y` is joined to `x` and `x` lies in
an infinite open cluster, then so does `y`. -/
theorem connectionEvent_inter_subset (d : ℕ) (x y : Cubic d) :
    connectionEvent d y x ∩ {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} ⊆
      {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω y} := by
  rintro ω ⟨⟨w, hw⟩, hx⟩
  refine Set.Infinite.mono ?_ hx
  rintro z ⟨wz, hwz⟩
  exact ⟨w.append wz, walkIsOpen_append hw hwz⟩

/-- **The FKG step of Theorem (2.8)** (Grimmett p. 35):
`P_p(y ↔ x) · θ(p, x) ≤ θ(p, y)`. -/
theorem bernoulliBondMeasure_real_connectionEvent_thetaFrom_le (d : ℕ) (p : I)
    (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (connectionEvent d y x) * thetaFrom d p x ≤
      thetaFrom d p y := by
  have hfkg := bernoulliBondMeasure_real_fkg p (isIncreasingEvent_connectionEvent d y x)
    (isIncreasingEvent_hasInfiniteOpenClusterFrom d x)
    (measurableSet_connectionEvent d y x) (measurableSet_hasInfiniteOpenClusterFrom d x)
  refine hfkg.trans ?_
  exact measureReal_mono (connectionEvent_inter_subset d x y)

/-! ### Vanishing at density zero and the zero-set identification -/

/-- At density zero, every vertex-rooted percolation probability vanishes: an infinite
cluster forces at least one open edge incident to the root. -/
theorem thetaFrom_eq_zero_of_coe_eq_zero (d : ℕ) {p : I} (hp : (p : ℝ) = 0)
    (x : Cubic d) : thetaFrom d p x = 0 := by
  classical
  have hsub : {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} ⊆
      ⋃ a ∈ (Finset.univ : Finset (CubicDirection d)),
        openEdgeSetEvent d {⟨s(x, cubicStepFrom x a),
          (cubicGraph d).mem_edgeSet.mpr (cubicGraph_adj_stepFrom x a)⟩} := by
    intro ω hω
    have hpath : hasOpenPathOfLengthAtLeastFrom d ω x 1 := by
      have := (hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom).mp hω
      exact this 1
    obtain ⟨v, w, -, hlen, hopen⟩ := hpath
    cases w with
    | nil => simp at hlen
    | @cons _ b _ hadj wtail =>
      obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom x b).mp hadj
      subst ha
      refine Set.mem_biUnion (Finset.mem_univ a) ?_
      intro e he
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at he
      subst he
      exact hopen _ (by simp [SimpleGraph.Walk.edges_cons])
  have hle := (measureReal_mono (μ := bernoulliBondMeasure d p) hsub
      (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le Finset.univ _)
  have hzero : ∀ a ∈ (Finset.univ : Finset (CubicDirection d)),
      (bernoulliBondMeasure d p).real (openEdgeSetEvent d {⟨s(x, cubicStepFrom x a),
        (cubicGraph d).mem_edgeSet.mpr (cubicGraph_adj_stepFrom x a)⟩}) = 0 := by
    intro a _
    rw [bernoulliBondMeasure_real_openEdgeSetEvent]
    simp [hp]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hle
  exact le_antisymm (by simpa [thetaFrom] using hle) measureReal_nonneg

/-- The vertex-rooted percolation probabilities vanish together. -/
theorem thetaFrom_eq_zero_iff (d : ℕ) (p : I) (x y : Cubic d) :
    thetaFrom d p x = 0 ↔ thetaFrom d p y = 0 := by
  by_cases hp : (p : ℝ) = 0
  · simp [thetaFrom_eq_zero_of_coe_eq_zero d hp]
  · have hp' : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp)
    have key : ∀ u v : Cubic d, thetaFrom d p u = 0 → thetaFrom d p v = 0 := by
      intro u v hu
      have hstep := bernoulliBondMeasure_real_connectionEvent_thetaFrom_le d p v u
      rw [hu] at hstep
      have hpos := bernoulliBondMeasure_real_connectionEvent_pos d hp' u v
      refine le_antisymm ?_ measureReal_nonneg
      by_contra h
      rw [not_le] at h
      exact absurd hstep (not_le.mpr (mul_pos hpos h))
    exact ⟨key x y, key y x⟩

/-- **Theorem (2.8)** (Grimmett p. 35, bond percolation on the cubic lattice): the critical
probability does not depend on the reference vertex. -/
theorem cubicCriticalProbabilityFrom_eq (d : ℕ) (x : Cubic d) :
    cubicCriticalProbabilityFrom d x = cubicCriticalProbability d := by
  rw [← cubicCriticalProbabilityFrom_origin d, cubicCriticalProbabilityFrom,
    cubicCriticalProbabilityFrom]
  congr 2
  ext p
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  exact thetaFrom_eq_zero_iff d p x cubicOrigin

end Percolation
