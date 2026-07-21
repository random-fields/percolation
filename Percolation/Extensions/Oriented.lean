import Percolation.Bernoulli.Basic
import Percolation.Bernoulli.Coupling
import Percolation.Planar.Peierls
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Oriented bond percolation on the cubic lattice

This file formalizes the directed model in Grimmett, Chapter 12, equations (12.31)--(12.32).
Only positive coordinate steps are allowed.  The origin cluster is encoded as an actual set and
its size as an extended cardinality, so an infinite directed cluster is never assigned size zero.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

/-- The positively oriented edge leaving `x` in coordinate direction `i`. -/
def northEastEdge {d : ℕ} (x : Cubic d) (i : Fin d) : CubicEdge d :=
  ⟨s(x, cubicStepFrom x (i, true)), by
    rw [SimpleGraph.mem_edgeSet]
    exact cubicGraph_adj_stepFrom x (i, true)⟩

/-- Endpoint obtained by following a finite word of positive coordinate directions. -/
def northEastPathEnd {d : ℕ} : Cubic d → List (Fin d) → Cubic d
  | x, [] => x
  | x, i :: is => northEastPathEnd (cubicStepFrom x (i, true)) is

/-- Finite set of unoriented cubic bonds traversed by a directed path word. -/
def northEastPathEdges {d : ℕ} : Cubic d → List (Fin d) → Finset (CubicEdge d)
  | _, [] => ∅
  | x, i :: is => insert (northEastEdge x i)
      (northEastPathEdges (cubicStepFrom x (i, true)) is)

@[simp]
theorem northEastPathEnd_nil {d : ℕ} (x : Cubic d) :
    northEastPathEnd x [] = x := rfl

@[simp]
theorem northEastPathEnd_cons {d : ℕ} (x : Cubic d) (i : Fin d)
    (is : List (Fin d)) :
    northEastPathEnd x (i :: is) =
      northEastPathEnd (cubicStepFrom x (i, true)) is := rfl

@[simp]
theorem northEastPathEdges_nil {d : ℕ} (x : Cubic d) :
    northEastPathEdges x [] = ∅ := rfl

@[simp]
theorem northEastPathEdges_cons {d : ℕ} (x : Cubic d) (i : Fin d)
    (is : List (Fin d)) :
    northEastPathEdges x (i :: is) =
      insert (northEastEdge x i)
        (northEastPathEdges (cubicStepFrom x (i, true)) is) := rfl

/-- A finite directed path word is open when every bond it traverses is open. -/
def NorthEastPathOpen {d : ℕ} (ω : EdgeConfiguration d) (x : Cubic d)
    (is : List (Fin d)) : Prop :=
  (northEastPathEdges x is : Set (CubicEdge d)) ⊆ ω

@[simp]
theorem northEastPathOpen_nil {d : ℕ} (ω : EdgeConfiguration d) (x : Cubic d) :
    NorthEastPathOpen ω x [] := by
  simp [NorthEastPathOpen]

theorem northEastPathOpen_cons_iff {d : ℕ} (ω : EdgeConfiguration d)
    (x : Cubic d) (i : Fin d) (is : List (Fin d)) :
    NorthEastPathOpen ω x (i :: is) ↔
      northEastEdge x i ∈ ω ∧
        NorthEastPathOpen ω (cubicStepFrom x (i, true)) is := by
  rw [NorthEastPathOpen, northEastPathEdges_cons, Finset.coe_insert,
    Set.insert_subset_iff]
  rfl

/-- The graph walk traced by a positive-coordinate word. -/
def northEastWalk {d : ℕ} (x : Cubic d) :
    (is : List (Fin d)) → (cubicGraph d).Walk x (northEastPathEnd x is)
  | [] => SimpleGraph.Walk.nil
  | i :: is =>
      SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x (i, true))
        (northEastWalk (cubicStepFrom x (i, true)) is)

@[simp]
theorem northEastWalk_length {d : ℕ} (x : Cubic d) (is : List (Fin d)) :
    (northEastWalk x is).length = is.length := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
      change (northEastWalk (cubicStepFrom x (i, true)) is).length + 1 = is.length + 1
      rw [ih]

/-- Openness of the finite edge set is exactly what is needed for the corresponding graph walk. -/
theorem walkIsOpen_northEastWalk {d : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    {is : List (Fin d)} (hopen : NorthEastPathOpen ω x is) :
    walkIsOpen ω (northEastWalk x is) := by
  induction is generalizing x with
  | nil =>
      intro e he
      cases he
  | cons i is ih =>
      have h := (northEastPathOpen_cons_iff ω x i is).mp hopen
      intro e he
      simp only [northEastWalk, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact h.1
      · exact ih h.2 e he

/-- Directed reachability, represented by a finite positive-coordinate word. -/
def NorthEastReachable {d : ℕ} (ω : EdgeConfiguration d) (x y : Cubic d) : Prop :=
  ∃ is : List (Fin d), NorthEastPathOpen ω x is ∧ northEastPathEnd x is = y

@[refl]
theorem northEastReachable_refl {d : ℕ} (ω : EdgeConfiguration d) (x : Cubic d) :
    NorthEastReachable ω x x := by
  exact ⟨[], northEastPathOpen_nil ω x, rfl⟩

/-- The directed open cluster of the origin. -/
def northEastCluster (d : ℕ) (ω : EdgeConfiguration d) : Set (Cubic d) :=
  {y | NorthEastReachable ω cubicOrigin y}

@[simp]
theorem cubicOrigin_mem_northEastCluster (d : ℕ) (ω : EdgeConfiguration d) :
    cubicOrigin ∈ northEastCluster d ω :=
  northEastReachable_refl ω cubicOrigin

/-- Extended cardinality of the directed origin cluster. -/
noncomputable def northEastClusterSize (d : ℕ) (ω : EdgeConfiguration d) : ℝ≥0∞ :=
  by
    classical
    exact ∑' y : Cubic d, if y ∈ northEastCluster d ω then 1 else 0

theorem northEastClusterSize_eq_encard (d : ℕ) (ω : EdgeConfiguration d) :
    northEastClusterSize d ω = (northEastCluster d ω).encard := by
  classical
  rw [← ENNReal.tsum_set_one]
  change (∑' y : Cubic d,
    (northEastCluster d ω).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
      ∑' _ : northEastCluster d ω, (1 : ℝ≥0∞)
  exact (tsum_subtype (northEastCluster d ω) fun _ ↦ (1 : ℝ≥0∞)).symm

/-- Reachability of a fixed endpoint is a measurable countable union of cylinder events. -/
theorem measurableSet_northEastReachable {d : ℕ} (x y : Cubic d) :
    MeasurableSet {ω : EdgeConfiguration d | NorthEastReachable ω x y} := by
  classical
  rw [show {ω : EdgeConfiguration d | NorthEastReachable ω x y} =
      ⋃ is : List (Fin d),
        if northEastPathEnd x is = y then
          openEdgeSetEvent d (northEastPathEdges x is) else ∅ by
    ext ω
    simp only [Set.mem_setOf_eq, NorthEastReachable, Set.mem_iUnion,
      Set.mem_ite_empty_right, mem_openEdgeSetEvent]
    constructor
    · rintro ⟨is, hopen, hend⟩
      exact ⟨is, hend, hopen⟩
    · rintro ⟨is, hend, hopen⟩
      exact ⟨is, hopen, hend⟩]
  exact MeasurableSet.iUnion fun is ↦ by
    split_ifs
    · exact measurableSet_openEdgeSetEvent d (northEastPathEdges x is)
    · exact MeasurableSet.empty

/-- The directed cluster size is a measurable extended random variable. -/
theorem measurable_northEastClusterSize (d : ℕ) :
    Measurable (northEastClusterSize d) := by
  classical
  unfold northEastClusterSize
  apply Measurable.tsum
  intro y
  rw [show (fun ω : EdgeConfiguration d ↦
      if y ∈ northEastCluster d ω then (1 : ℝ≥0∞) else 0) =
      {ω : EdgeConfiguration d | NorthEastReachable ω cubicOrigin y}.indicator
        (fun _ ↦ 1) by
    funext ω
    rfl]
  exact measurable_const.indicator (measurableSet_northEastReachable cubicOrigin y)

/-- Event that the directed origin cluster is infinite. -/
def hasInfiniteNorthEastCluster (d : ℕ) : Set (EdgeConfiguration d) :=
  {ω | northEastClusterSize d ω = ⊤}

theorem measurableSet_hasInfiniteNorthEastCluster (d : ℕ) :
    MeasurableSet (hasInfiniteNorthEastCluster d) :=
  (measurable_northEastClusterSize d) (measurableSet_singleton ⊤)

theorem mem_hasInfiniteNorthEastCluster_iff (d : ℕ) (ω : EdgeConfiguration d) :
    ω ∈ hasInfiniteNorthEastCluster d ↔ (northEastCluster d ω).Infinite := by
  rw [hasInfiniteNorthEastCluster, Set.mem_setOf_eq,
    northEastClusterSize_eq_encard, ENat.toENNReal_eq_top, Set.encard_eq_top_iff]

/-- Oriented bond-percolation probability from the origin, equation (12.32). -/
noncomputable def orientedTheta (d : ℕ) (p : I) : ℝ :=
  (bernoulliBondMeasure d p).real (hasInfiniteNorthEastCluster d)

/-- Critical probability of positively oriented bond percolation. -/
noncomputable def orientedCriticalProbability (d : ℕ) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | orientedTheta d p = 0}) : Set ℝ)

/-- Exact-size event for the directed origin cluster. -/
def finiteNorthEastClusterSizeEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  {ω | northEastClusterSize d ω = n}

theorem measurableSet_finiteNorthEastClusterSizeEvent (d n : ℕ) :
    MeasurableSet (finiteNorthEastClusterSizeEvent d n) :=
  (measurable_northEastClusterSize d) (measurableSet_singleton (n : ℝ≥0∞))

/-- Probability that the directed origin cluster is finite and has at least `n` vertices. -/
noncomputable def orientedFiniteClusterTail (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real
    {ω | (n : ℝ≥0∞) ≤ northEastClusterSize d ω ∧ northEastClusterSize d ω < ⊤}

theorem measurableSet_orientedFiniteClusterTail (d n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d |
      (n : ℝ≥0∞) ≤ northEastClusterSize d ω ∧ northEastClusterSize d ω < ⊤} :=
  ((measurable_northEastClusterSize d) measurableSet_Ici).inter
    ((measurable_northEastClusterSize d) measurableSet_Iio)

/-! ### Monotonicity and endpoint cases -/

theorem northEastPathOpen_mono {d : ℕ} {ω η : EdgeConfiguration d} (hωη : ω ⊆ η)
    {x : Cubic d} {is : List (Fin d)} (hopen : NorthEastPathOpen ω x is) :
    NorthEastPathOpen η x is :=
  fun _ he ↦ hωη (hopen he)

theorem northEastCluster_mono {d : ℕ} {ω η : EdgeConfiguration d} (hωη : ω ⊆ η) :
    northEastCluster d ω ⊆ northEastCluster d η := by
  rintro y ⟨is, hopen, hend⟩
  exact ⟨is, northEastPathOpen_mono hωη hopen, hend⟩

/-- A directed open connection is, after forgetting orientation, an ordinary open connection. -/
theorem northEastCluster_subset_cubicOpenCluster (d : ℕ) (ω : EdgeConfiguration d) :
    northEastCluster d ω ⊆ cubicOpenCluster d ω := by
  rintro y ⟨is, hopen, hend⟩
  subst y
  exact ⟨northEastWalk cubicOrigin is, walkIsOpen_northEastWalk hopen⟩

theorem isIncreasingEvent_hasInfiniteNorthEastCluster (d : ℕ) :
    IsIncreasingEvent (hasInfiniteNorthEastCluster d) := by
  intro ω η hωη hω
  rw [mem_hasInfiniteNorthEastCluster_iff] at hω ⊢
  exact hω.mono (northEastCluster_mono hωη)

theorem orientedTheta_mono (d : ℕ) : Monotone (orientedTheta d) := by
  intro p q hpq
  exact (isIncreasingEvent_hasInfiniteNorthEastCluster d).setBernoulli_real_mono
    (measurableSet_hasInfiniteNorthEastCluster d) hpq

theorem orientedTheta_le_theta (d : ℕ) (p : I) :
    orientedTheta d p ≤ theta d p := by
  haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    rw [bernoulliBondMeasure]
    infer_instance
  unfold orientedTheta theta
  apply measureReal_mono
  · intro ω hω
    have hinf : (northEastCluster d ω).Infinite :=
      (mem_hasInfiniteNorthEastCluster_iff d ω).mp hω
    exact hinf.mono (northEastCluster_subset_cubicOpenCluster d ω)
  · exact measure_ne_top _ _

theorem northEastPathOpen_empty_iff {d : ℕ} (x : Cubic d) (is : List (Fin d)) :
    NorthEastPathOpen (∅ : EdgeConfiguration d) x is ↔ is = [] := by
  induction is generalizing x with
  | nil => simp
  | cons i is ih =>
      rw [northEastPathOpen_cons_iff]
      simp

@[simp]
theorem northEastCluster_empty (d : ℕ) :
    northEastCluster d (∅ : EdgeConfiguration d) = {cubicOrigin} := by
  ext y
  constructor
  · rintro ⟨is, hopen, hend⟩
    have his := (northEastPathOpen_empty_iff cubicOrigin is).mp hopen
    subst is
    simpa using hend.symm
  · intro hy
    have hy' : y = cubicOrigin := by simpa using hy
    subst y
    exact cubicOrigin_mem_northEastCluster d ∅

@[simp]
theorem northEastClusterSize_empty (d : ℕ) :
    northEastClusterSize d (∅ : EdgeConfiguration d) = 1 := by
  rw [northEastClusterSize_eq_encard, northEastCluster_empty, Set.encard_singleton]
  exact ENat.toENNReal_one

@[simp]
theorem orientedTheta_zero (d : ℕ) : orientedTheta d (0 : I) = 0 := by
  rw [orientedTheta, bernoulliBondMeasure, setBernoulli_zero, Measure.real,
    Measure.dirac_apply' _ (measurableSet_hasInfiniteNorthEastCluster d)]
  simp [hasInfiniteNorthEastCluster]

theorem northEastPathEnd_replicate_apply_same {d : ℕ} (x : Cubic d) (i : Fin d)
    (n : ℕ) :
    northEastPathEnd x (List.replicate n i) i = x i + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, northEastPathEnd_cons, ih]
      simp [cubicStepFrom, cubicDirectionIncrement]
      ring

theorem northEastCluster_univ_infinite {d : ℕ} (hd : 0 < d) :
    (northEastCluster d (Set.univ : EdgeConfiguration d)).Infinite := by
  let i : Fin d := ⟨0, hd⟩
  let f : ℕ → Cubic d := fun n ↦
    northEastPathEnd cubicOrigin (List.replicate n i)
  have hf : Function.Injective f := by
    intro m n hmn
    have hi := congrFun hmn i
    change northEastPathEnd cubicOrigin (List.replicate m i) i =
      northEastPathEnd cubicOrigin (List.replicate n i) i at hi
    rw [northEastPathEnd_replicate_apply_same,
      northEastPathEnd_replicate_apply_same] at hi
    simpa [cubicOrigin] using hi
  have hrange : Set.range f ⊆ northEastCluster d (Set.univ : EdgeConfiguration d) := by
    rintro y ⟨n, rfl⟩
    refine ⟨List.replicate n i, ?_, rfl⟩
    intro e _he
    exact Set.mem_univ e
  exact (Set.infinite_range_of_injective hf).mono hrange

@[simp]
theorem orientedTheta_one {d : ℕ} (hd : 0 < d) : orientedTheta d (1 : I) = 1 := by
  rw [orientedTheta, bernoulliBondMeasure, setBernoulli_one, Measure.real,
    Measure.dirac_apply' _ (measurableSet_hasInfiniteNorthEastCluster d)]
  simp [mem_hasInfiniteNorthEastCluster_iff, northEastCluster_univ_infinite hd]

private theorem orientedCriticalZeroSet_nonempty (d : ℕ) :
    (((fun p : I ↦ (p : ℝ)) '' {p : I | orientedTheta d p = 0}) : Set ℝ).Nonempty := by
  exact ⟨0, ⟨(0 : I), orientedTheta_zero d, rfl⟩⟩

private theorem orientedCriticalZeroSet_bddAbove (d : ℕ) :
    BddAbove (((fun p : I ↦ (p : ℝ)) ''
      {p : I | orientedTheta d p = 0}) : Set ℝ) := by
  refine ⟨1, ?_⟩
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

theorem orientedCriticalProbability_nonneg (d : ℕ) :
    0 ≤ orientedCriticalProbability d := by
  rw [orientedCriticalProbability]
  exact le_csSup (orientedCriticalZeroSet_bddAbove d)
    ⟨(0 : I), orientedTheta_zero d, rfl⟩

theorem orientedCriticalProbability_le_one (d : ℕ) :
    orientedCriticalProbability d ≤ 1 := by
  rw [orientedCriticalProbability]
  apply csSup_le (orientedCriticalZeroSet_nonempty d)
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

/-- Forgetting orientation shows that the oriented threshold is no smaller than the ordinary
bond threshold. -/
theorem cubicCriticalProbability_le_orientedCriticalProbability (d : ℕ) :
    cubicCriticalProbability d ≤ orientedCriticalProbability d := by
  rw [cubicCriticalProbability, orientedCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I), by
      apply le_antisymm
      · exact (theta_le_selfAvoidingWalkCount_mul_pow d 1 (0 : I)).trans_eq (by simp)
      · exact measureReal_nonneg, rfl⟩⟩
  · rintro q ⟨p, hpzero, rfl⟩
    have horiented : orientedTheta d p = 0 := by
      apply le_antisymm
      · exact (orientedTheta_le_theta d p).trans_eq hpzero
      · exact measureReal_nonneg
    exact le_csSup (orientedCriticalZeroSet_bddAbove d) ⟨p, horiented, rfl⟩

theorem orientedCriticalProbability_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < orientedCriticalProbability d :=
  (cubicCriticalProbability_pos_lt_one hd).1.trans_le
    (cubicCriticalProbability_le_orientedCriticalProbability d)

end Percolation
