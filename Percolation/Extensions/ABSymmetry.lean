import Percolation.Bernoulli.Inhomogeneous
import Percolation.Extensions.PeriodicMixed

/-!
# Atom-swap symmetry for AB percolation

Swapping labels `A` and `B` does not change the open graph.  This file supplies the missing
measurability proof for rooted AB percolation and combines it with the Bernoulli-complement
pushforward to prove `theta_AB(p) = theta_AB(1-p)`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped unitInterval

/-- An ambient walk is AB-open when the labels at the endpoints of every traversed dart differ. -/
def ABWalkOpen {V : Type*} {G : SimpleGraph V} (labels : Set V)
    {x y : V} (w : G.Walk x y) : Prop :=
  ∀ dart ∈ w.darts, (dart.fst ∈ labels ↔ dart.snd ∉ labels)

@[simp]
theorem abWalkOpen_nil {V : Type*} {G : SimpleGraph V} (labels : Set V) (x : V) :
    ABWalkOpen labels (SimpleGraph.Walk.nil : G.Walk x x) := by
  simp [ABWalkOpen]

theorem abWalkOpen_cons_iff {V : Type*} {G : SimpleGraph V} (labels : Set V)
    {x y z : V} (hxy : G.Adj x y) (w : G.Walk y z) :
    ABWalkOpen labels (SimpleGraph.Walk.cons hxy w) ↔
      (x ∈ labels ↔ y ∉ labels) ∧ ABWalkOpen labels w := by
  simp [ABWalkOpen, SimpleGraph.Walk.darts_cons]

/-- Reachability in the AB graph is equivalent to an AB-open walk in the ambient graph. -/
theorem abOpenGraph_reachable_iff_exists_abWalkOpen
    {V : Type*} (G : SimpleGraph V) (labels : Set V) (x y : V) :
    (abOpenGraph G labels).Reachable x y ↔
      ∃ w : G.Walk x y, ABWalkOpen labels w := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨SimpleGraph.Walk.nil, abWalkOpen_nil labels x⟩
    | @cons u v z huv w ih =>
        obtain ⟨q, hq⟩ := ih
        refine ⟨SimpleGraph.Walk.cons huv.1 q, ?_⟩
        exact (abWalkOpen_cons_iff labels huv.1 q).2 ⟨huv.2, hq⟩
  · rintro ⟨w, hw⟩
    induction w with
    | nil => exact ⟨SimpleGraph.Walk.nil⟩
    | @cons u v z huv w ih =>
        have hopen := (abWalkOpen_cons_iff labels huv w).1 hw
        obtain ⟨q⟩ := ih hopen.2
        exact ⟨SimpleGraph.Walk.cons ⟨huv, hopen.1⟩ q⟩

/-- Rooted AB connection event. -/
def abConnectionEvent {V : Type*} (G : SimpleGraph V) (x y : V) : Set (Set V) :=
  {labels | (abOpenGraph G labels).Reachable x y}

private theorem measurableSet_abEndpointLabelsDiffer {V : Type*} (x y : V) :
    MeasurableSet {labels : Set V | x ∈ labels ↔ y ∉ labels} := by
  let A : Set (Set V) := {labels | x ∈ labels}
  let B : Set (Set V) := {labels | y ∈ labels}
  have hrepr : {labels : Set V | x ∈ labels ↔ y ∉ labels} =
      (A ∩ Bᶜ) ∪ (Aᶜ ∩ B) := by
    ext labels
    simp [A, B]
    tauto
  rw [hrepr]
  exact ((measurableSet_mem x).inter (measurableSet_mem y).compl).union
    ((measurableSet_mem x).compl.inter (measurableSet_mem y))

private theorem measurableSet_abWalkOpen
    {V : Type*} {G : SimpleGraph V} {x y : V} (w : G.Walk x y) :
    MeasurableSet {labels : Set V | ABWalkOpen labels w} := by
  induction w with
  | nil => simp [ABWalkOpen]
  | @cons u v z huv w ih =>
      have hrepr : {labels : Set V | ABWalkOpen labels (SimpleGraph.Walk.cons huv w)} =
          {labels : Set V | u ∈ labels ↔ v ∉ labels} ∩
            {labels : Set V | ABWalkOpen labels w} := by
        ext labels
        simp [abWalkOpen_cons_iff]
      rw [hrepr]
      exact (measurableSet_abEndpointLabelsDiffer u v).inter ih

theorem measurableSet_abConnectionEvent
    {V : Type*} [Countable V] (G : SimpleGraph V) (x y : V) :
    MeasurableSet (abConnectionEvent G x y) := by
  classical
  letI : Countable (G.Walk x y) :=
    (show Function.Injective (fun w : G.Walk x y ↦ w.support) from
      fun _ _ h ↦ SimpleGraph.Walk.ext_support h).countable
  have hrepr : abConnectionEvent G x y =
      ⋃ w : G.Walk x y, {labels : Set V | ABWalkOpen labels w} := by
    ext labels
    simp only [abConnectionEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    exact abOpenGraph_reachable_iff_exists_abWalkOpen G labels x y
  rw [hrepr]
  exact MeasurableSet.iUnion measurableSet_abWalkOpen

/-- The rooted infinite AB-cluster event is measurable. -/
theorem measurableSet_infinite_abOpenCluster
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) :
    MeasurableSet {labels : Set V | (abOpenCluster G labels root).Infinite} := by
  classical
  have hrepr : {labels : Set V | (abOpenCluster G labels root).Infinite} =
      ⋂ s : Finset V, ⋃ y : V, ⋃ (_hy : y ∉ s), abConnectionEvent G root y := by
    ext labels
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hinfinite s
      obtain ⟨y, hy, hys⟩ := hinfinite.exists_notMem_finset s
      exact ⟨y, hys, hy⟩
    · intro h
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨y, hys, hy⟩ := h hfinite.toFinset
      exact hys (hfinite.mem_toFinset.mpr hy)
  rw [hrepr]
  exact MeasurableSet.iInter fun s ↦ MeasurableSet.iUnion fun y ↦
    MeasurableSet.iUnion fun _hy ↦ measurableSet_abConnectionEvent G root y

@[simp]
theorem abOpenCluster_compl_labels {V : Type*} (G : SimpleGraph V)
    (labels : Set V) (root : V) :
    abOpenCluster G labelsᶜ root = abOpenCluster G labels root := by
  unfold abOpenCluster
  rw [abOpenGraph_compl_labels]

/-- AB percolation is invariant under interchanging the two atom types. -/
theorem abTheta_complementary_density
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) (p : I) :
    abTheta G root p = abTheta G root (σ p) := by
  let A : Set (Set V) := {labels | (abOpenCluster G labels root).Infinite}
  have hA : MeasurableSet A := measurableSet_infinite_abOpenCluster G root
  have hpre : (fun labels : Set V ↦ labelsᶜ) ⁻¹' A = A := by
    ext labels
    simp only [Set.mem_preimage, A, Set.mem_setOf_eq]
    rw [abOpenCluster_compl_labels]
  have hmap := setBernoulli_map_compl_univ (ι := V) p
  have hmeasure := congrArg (fun μ : Measure (Set V) ↦ μ.real A) hmap
  dsimp only at hmeasure
  rw [Measure.real, Measure.map_apply measurable_compl hA, hpre] at hmeasure
  simpa [abTheta, A] using hmeasure

@[simp]
theorem abTheta_zero {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) :
    abTheta G root (0 : I) = 0 := by
  rw [abTheta, setBernoulli_zero, Measure.real,
    Measure.dirac_apply' _ (measurableSet_infinite_abOpenCluster G root)]
  have hfinite : (abOpenCluster G (∅ : Set V) root).Finite := by
    rw [abOpenCluster, abOpenGraph_empty]
    simpa only [SimpleGraph.reachable_bot, Set.setOf_eq_eq_singleton'] using
      Set.finite_singleton root
  simp [hfinite]

@[simp]
theorem abTheta_one {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) :
    abTheta G root (1 : I) = 0 := by
  have h := abTheta_complementary_density G root (0 : I)
  rw [abTheta_zero] at h
  simpa using h.symm

end Percolation
