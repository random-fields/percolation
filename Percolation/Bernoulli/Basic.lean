import Percolation.Core.Configuration
import Percolation.Core.Cubic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.UnitInterval

/-!
# Bernoulli percolation scaffold

The first production target here is the finite-edge product measure, followed by increasing
events, FKG, BK/Reimer, and Russo's formula.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval BigOperators

/-- Independent product measures project along coordinate embeddings. This is the product-measure
coupling behind dimension monotonicity: sampling all target coordinates and then forgetting the
coordinates outside an embedded source has the same law as sampling the source directly. -/
theorem infinitePi_map_precomp_embedding {α β : Type*} (f : α ↪ β)
    (μ : β → Measure Prop) [∀ b, IsProbabilityMeasure (μ b)] :
    (Measure.infinitePi μ).map (fun x : β → Prop ↦ fun a : α ↦ x (f a)) =
      Measure.infinitePi (fun a : α ↦ μ (f a)) := by
  classical
  refine Measure.eq_infinitePi (fun a : α ↦ μ (f a)) ?_
  intro s t ht
  rw [Measure.map_apply]
  · let T : β → Set Prop := fun b ↦ if hb : b ∈ Set.range f then
        t (Classical.choose hb) else Set.univ
    have hpre :
        (fun x : β → Prop ↦ fun a : α ↦ x (f a)) ⁻¹'
            Set.pi ((s : Finset α) : Set α) t =
          Set.pi (((s.map f : Finset β) : Set β)) T := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_preimage, Set.mem_pi] at hx
        rw [Set.mem_pi]
        intro b hbmap
        rcases Finset.mem_map.mp hbmap with ⟨a, ha, rfl⟩
        have hfa : f a ∈ Set.range f := ⟨a, rfl⟩
        have hchoose : Classical.choose hfa = a :=
          f.injective (Classical.choose_spec hfa)
        have hxchoose : x (f a) ∈ t (Classical.choose hfa) := by
          rw [hchoose]
          exact hx a ha
        simpa [T, hfa] using hxchoose
      · intro hx
        rw [Set.mem_preimage, Set.mem_pi]
        intro a ha
        rw [Set.mem_pi] at hx
        have hfa : f a ∈ Set.range f := ⟨a, rfl⟩
        have hmap : f a ∈ ((s.map f : Finset β) : Set β) :=
          Finset.mem_map.mpr ⟨a, ha, rfl⟩
        have hchoose : Classical.choose hfa = a :=
          f.injective (Classical.choose_spec hfa)
        have hxchoose : x (f a) ∈ t (Classical.choose hfa) := by
          simpa [T, hfa] using hx (f a) hmap
        rw [hchoose] at hxchoose
        exact hxchoose
    rw [hpre]
    rw [Measure.infinitePi_pi]
    · rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro a _ha
      have hfa : f a ∈ Set.range f := ⟨a, rfl⟩
      have hchoose : Classical.choose hfa = a :=
        f.injective (Classical.choose_spec hfa)
      dsimp [T]
      rw [dif_pos hfa, hchoose]
    · intro b hb
      by_cases hb' : b ∈ Set.range f
      · dsimp [T]
        rw [dif_pos hb']
        exact ht (Classical.choose hb')
      · dsimp [T]
        rw [dif_neg hb']
        exact MeasurableSet.univ
  · fun_prop
  · exact MeasurableSet.pi (Finset.countable_toSet s) (fun i _hi ↦ ht i)

/-- The coordinate restriction map on `Set` spaces induced by an embedding is measurable. -/
theorem measurable_preimage_embedding {α β : Type*} (f : α ↪ β) :
    Measurable (fun s : Set β ↦ f ⁻¹' s) := by
  classical
  change Measurable
    (MeasurableEquiv.setOf ∘ (fun x : β → Prop ↦ fun a : α ↦ x (f a)) ∘
      MeasurableEquiv.setOf.symm)
  fun_prop

/-- The Bernoulli law on all target coordinates projects to the Bernoulli law on all source
coordinates along any embedding. -/
theorem setBernoulli_map_preimage_univ {α β : Type*} (f : α ↪ β) (p : I) :
    (setBer((Set.univ : Set β), p)).map (fun s : Set β ↦ f ⁻¹' s) =
      setBer((Set.univ : Set α), p) := by
  classical
  let μβ : β → Measure Prop := fun i ↦
    unitInterval.toNNReal p • Measure.dirac (i ∈ (Set.univ : Set β)) +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  let μα : α → Measure Prop := fun i ↦
    unitInterval.toNNReal p • Measure.dirac (i ∈ (Set.univ : Set α)) +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  rw [setBernoulli_eq_map, setBernoulli_eq_map]
  change (Measure.map (fun p : β → Prop ↦ {i | p i}) (Measure.infinitePi μβ)).map
      (fun s : Set β ↦ f ⁻¹' s) =
    Measure.map (fun p : α → Prop ↦ {i | p i}) (Measure.infinitePi μα)
  rw [Measure.map_map (measurable_preimage_embedding f)
    (by fun_prop : Measurable (fun p : β → Prop ↦ {i | p i}))]
  have hprod : (Measure.infinitePi μβ).map (fun x : β → Prop ↦ fun a : α ↦ x (f a)) =
      Measure.infinitePi μα := by
    simpa [μβ, μα] using infinitePi_map_precomp_embedding f μβ
  rw [← hprod]
  rw [Measure.map_map
    (by fun_prop : Measurable (fun p : α → Prop ↦ {i | p i}))
    (by fun_prop : Measurable (fun x : β → Prop ↦ fun a : α ↦ x (f a)))]
  congr 1

/-- Parameters for Bernoulli bond percolation on a graph. -/
structure BernoulliBond (V : Type u) where
  graph : BaseGraph V
  p : ℝ
  hp_nonneg : 0 ≤ p
  hp_le_one : p ≤ 1

/-- Placeholder for the percolation probability `θ(p)`. The production definition should use
the probability that the origin cluster is infinite on the chosen lattice. -/
structure PercolationProbability (V : Type u) where
  model : BernoulliBond V
  theta : ℝ

/-- Bernoulli bond percolation on the fixed edge set of the cubic lattice. -/
noncomputable def bernoulliBondMeasure (d : ℕ) (p : I) : Measure (EdgeConfiguration d) :=
  setBer((Set.univ : Set (CubicEdge d)), p)

/-- The finite-cylinder event that every edge in `s` is open. This is the reusable form of the
finite open event that later supplies Grimmett's `G_m`. -/
def openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) : Set (EdgeConfiguration d) :=
  {ω | (s : Set (CubicEdge d)) ⊆ ω}

@[simp]
theorem mem_openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) (ω : EdgeConfiguration d) :
    ω ∈ openEdgeSetEvent d s ↔ (s : Set (CubicEdge d)) ⊆ ω :=
  Iff.rfl

/-- The finite-cylinder event that every edge in `s` is closed. -/
def closedEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) : Set (EdgeConfiguration d) :=
  {ω | Disjoint (s : Set (CubicEdge d)) ω}

@[simp]
theorem mem_closedEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) (ω : EdgeConfiguration d) :
    ω ∈ closedEdgeSetEvent d s ↔ Disjoint (s : Set (CubicEdge d)) ω :=
  Iff.rfl

/-- Pulling back Bernoulli bond percolation along a coordinate embedding of cubic lattices
preserves the Bernoulli bond law. -/
theorem bernoulliBondMeasure_map_cubicConfigurationPullback {m d : ℕ} (hmd : m ≤ d)
    (p : I) :
    (bernoulliBondMeasure d p).map (cubicConfigurationPullback hmd) =
      bernoulliBondMeasure m p := by
  simpa [bernoulliBondMeasure, cubicConfigurationPullback] using
    setBernoulli_map_preimage_univ (cubicEdgeEmbed hmd) p

/-- The event that all coordinates in a fixed finite set are present is measurable. -/
theorem measurableSet_superset_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    MeasurableSet {t : Set ι | (s : Set ι) ⊆ t} := by
  classical
  apply (MeasurableEquiv.setOf.measurableSet_preimage).mp
  change MeasurableSet {P : ι → Prop | ∀ i, i ∈ s → P i}
  have hset : ({P : ι → Prop | ∀ i, i ∈ s → P i} : Set (ι → Prop)) =
      Set.pi ((s : Finset ι) : Set ι) (fun _ : ι ↦ ({True} : Set Prop)) := by
    ext P
    simp [Set.mem_pi]
  rw [hset]
  exact MeasurableSet.pi (Finset.countable_toSet s)
    (fun _ _ ↦ measurableSet_singleton True)

/-- The event that all coordinates in a fixed finite set are absent is measurable. -/
theorem measurableSet_disjoint_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    MeasurableSet {t : Set ι | Disjoint (s : Set ι) t} := by
  classical
  apply (MeasurableEquiv.setOf.measurableSet_preimage).mp
  change MeasurableSet {P : ι → Prop | Disjoint ((s : Finset ι) : Set ι) {i | P i}}
  have hset :
      ({P : ι → Prop | Disjoint ((s : Finset ι) : Set ι) {i | P i}} :
        Set (ι → Prop)) =
        Set.pi ((s : Finset ι) : Set ι) (fun _ : ι ↦ ({False} : Set Prop)) := by
    ext P
    simp [Set.mem_pi, Set.disjoint_left]
  rw [hset]
  exact MeasurableSet.pi (Finset.countable_toSet s)
    (fun _ _ ↦ measurableSet_singleton False)

/-- A finite open-edge event is measurable. -/
theorem measurableSet_openEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    MeasurableSet (openEdgeSetEvent d s) :=
  measurableSet_superset_finset s

/-- A finite closed-edge event is measurable. -/
theorem measurableSet_closedEdgeSetEvent (d : ℕ) (s : Finset (CubicEdge d)) :
    MeasurableSet (closedEdgeSetEvent d s) :=
  measurableSet_disjoint_finset s

/-- In the Bernoulli product measure on all coordinates, the finite cylinder that prescribes
an arbitrary Boolean value on each coordinate in `s` has the expected product probability. This
is the common finite product-measure calculation behind fixed open paths and fixed closed
dual circuits in Grimmett's proof. -/
theorem setBernoulli_real_eqOn_finset_univ {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → Prop) [DecidablePred v] (p : I) :
    setBer((Set.univ : Set ι), p).real
        {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)} =
      ∏ i : s, if v i then (p : ℝ) else (1 - (p : ℝ)) := by
  classical
  rw [measureReal_def, ProbabilityTheory.setBernoulli_apply']
  let μ : ι → Measure Prop := fun i ↦
    unitInterval.toNNReal p • Measure.dirac (i ∈ (Set.univ : Set ι)) +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  have hpre :
      ((fun p : ι → Prop ↦ {i | p i}) ⁻¹'
        {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)}) =
        cylinder s {f : ∀ i : s, Prop | ∀ i : s, f i = v i} := by
    ext f
    simp [cylinder, Finset.restrict]
  change ((Measure.infinitePi μ) ((fun p : ι → Prop ↦ {i | p i}) ⁻¹'
      {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)})).toReal =
      ∏ i : s, if v i then (p : ℝ) else (1 - (p : ℝ))
  rw [hpre, MeasureTheory.Measure.infinitePi_cylinder]
  · have hset : ({f : ∀ i : s, Prop | ∀ i : s, f i = v i} :
        Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun i : s ↦ ({v i} : Set Prop)) := by
      ext f
      simp
    rw [hset, Measure.pi_pi]
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hvi : v i <;> simp [μ, hvi]
  · rw [show ({f : ∀ i : s, Prop | ∀ i : s, f i = v i} :
        Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun i : s ↦ ({v i} : Set Prop)) by
      ext f
      simp]
    exact MeasurableSet.univ_pi fun i ↦ measurableSet_singleton (v i)

/-- The same finite assignment-cylinder probability, indexed as a product over the underlying
finset rather than over its attached subtype. -/
theorem setBernoulli_real_eqOn_finset_univ' {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → Prop) [DecidablePred v] (p : I) :
    setBer((Set.univ : Set ι), p).real
        {t : Set ι | ∀ i, i ∈ s → ((i ∈ t) = v i)} =
      ∏ i ∈ s, if v i then (p : ℝ) else (1 - (p : ℝ)) := by
  rw [setBernoulli_real_eqOn_finset_univ]
  exact Finset.prod_coe_sort s (fun i ↦ if v i then (p : ℝ) else (1 - (p : ℝ)))

/-- In the Bernoulli product measure on all coordinates, the event that a fixed finite set of
coordinates is present has probability `p ^ |s|`. This is the cylinder-probability calculation
used for a fixed open path in Grimmett's proof. -/
theorem setBernoulli_real_superset_finset_univ {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : I) :
    setBer((Set.univ : Set ι), p).real {t : Set ι | (s : Set ι) ⊆ t} =
      (p : ℝ) ^ s.card := by
  classical
  rw [measureReal_def, ProbabilityTheory.setBernoulli_apply']
  let μ : ι → Measure Prop := fun i ↦
    unitInterval.toNNReal p • Measure.dirac (i ∈ (Set.univ : Set ι)) +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  have hpre :
      ((fun p : ι → Prop ↦ {i | p i}) ⁻¹' {t : Set ι | (s : Set ι) ⊆ t}) =
        cylinder s {f : ∀ i : s, Prop | ∀ i : s, f i} := by
    ext f
    simp [cylinder, Finset.restrict, Set.subset_def]
  change ((Measure.infinitePi μ) ((fun p : ι → Prop ↦ {i | p i}) ⁻¹'
      {t : Set ι | (s : Set ι) ⊆ t})).toReal = (p : ℝ) ^ s.card
  rw [hpre, MeasureTheory.Measure.infinitePi_cylinder]
  · have hset : ({f : ∀ i : s, Prop | ∀ i : s, f i} : Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun _ : s ↦ ({True} : Set Prop)) := by
      ext f
      simp
    rw [hset, Measure.pi_pi]
    simp [μ]
  · rw [show ({f : ∀ i : s, Prop | ∀ i : s, f i} : Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun _ : s ↦ ({True} : Set Prop)) by
      ext f
      simp]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_singleton True

/-- Under the Bernoulli product measure on all coordinates, the coordinate-open events are
independent. This is the sigma-algebra-level product-measure input used to turn finite-support
disjointness into independence of more complicated finite events. -/
theorem setBernoulli_iIndepSet_mem_univ {ι : Type*} [DecidableEq ι] (p : I) :
    iIndepSet (fun i : ι ↦ {ω : Set ι | i ∈ ω}) setBer((Set.univ : Set ι), p) := by
  classical
  rw [iIndepSet_iff_meas_biInter]
  · intro s
    have hleft_ne_top : setBer((Set.univ : Set ι), p)
        (⋂ i ∈ s, {ω : Set ι | i ∈ ω}) ≠ ∞ := by
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    have hright_ne_top :
        (∏ i ∈ s, setBer((Set.univ : Set ι), p) {ω : Set ι | i ∈ ω}) ≠ ∞ := by
      exact ENNReal.prod_ne_top fun i _hi ↦ by
        refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
        rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
        exact ENNReal.one_lt_top
    rw [← ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top]
    have hevent : (⋂ i ∈ s, {ω : Set ι | i ∈ ω}) =
        {ω : Set ι | (s : Set ι) ⊆ ω} := by
      ext ω
      simp [Set.subset_def]
    rw [hevent]
    rw [ENNReal.toReal_prod]
    change setBer((Set.univ : Set ι), p).real {ω : Set ι | (s : Set ι) ⊆ ω} =
      ∏ i ∈ s, setBer((Set.univ : Set ι), p).real {ω : Set ι | i ∈ ω}
    rw [setBernoulli_real_superset_finset_univ]
    have hcoord : ∀ i ∈ s,
        setBer((Set.univ : Set ι), p).real {ω : Set ι | i ∈ ω} = (p : ℝ) := by
      intro i _hi
      have hsingle := setBernoulli_real_superset_finset_univ ({i} : Finset ι) p
      simpa [Set.singleton_subset_iff] using hsingle
    rw [Finset.prod_eq_pow_card hcoord]
  · intro i
    simpa [Set.singleton_subset_iff] using measurableSet_superset_finset ({i} : Finset ι)

/-- The coordinate-open events of Bernoulli bond percolation on `L^d` are independent. -/
theorem bernoulliBondMeasure_iIndepSet_edgeOpen (d : ℕ) (p : I) :
    iIndepSet (fun e : CubicEdge d ↦ {ω : EdgeConfiguration d | e ∈ ω})
      (bernoulliBondMeasure d p) := by
  simpa [bernoulliBondMeasure] using
    (setBernoulli_iIndepSet_mem_univ (ι := CubicEdge d) p)

/-- The coordinate-open events generated by a finite set of cubic-lattice edges. -/
def edgeCoordinateEvents (d : ℕ) (s : Finset (CubicEdge d)) :
    Set (Set (EdgeConfiguration d)) :=
  {A | ∃ e ∈ s, {ω : EdgeConfiguration d | e ∈ ω} = A}

/-- The measurable space generated by the coordinate-open events in a finite edge set. Events
measurable for this structure depend only on the open/closed status of edges in `s`. -/
@[reducible]
def edgeCoordinateMeasurableSpace (d : ℕ) (s : Finset (CubicEdge d)) :
    MeasurableSpace (EdgeConfiguration d) :=
  MeasurableSpace.generateFrom (edgeCoordinateEvents d s)

/-- Each coordinate event in `s` is measurable in the finite coordinate sigma-algebra generated by
`s`. -/
theorem measurableSet_edgeCoordinateEvent_of_mem (d : ℕ) (s : Finset (CubicEdge d))
    {e : CubicEdge d} (he : e ∈ s) :
    MeasurableSet[edgeCoordinateMeasurableSpace d s]
      {ω : EdgeConfiguration d | e ∈ ω} :=
  MeasurableSpace.measurableSet_generateFrom (by
    exact ⟨e, he, rfl⟩)

/-- The finite coordinate sigma-algebra generated by `s` is a sub-sigma-algebra of the ambient
configuration sigma-algebra. -/
theorem edgeCoordinateMeasurableSpace_le (d : ℕ) (s : Finset (CubicEdge d)) :
    edgeCoordinateMeasurableSpace d s ≤
      (inferInstance : MeasurableSpace (EdgeConfiguration d)) := by
  rw [edgeCoordinateMeasurableSpace]
  exact MeasurableSpace.generateFrom_le fun A hA ↦ by
    rcases hA with ⟨e, _he, rfl⟩
    simpa [Set.singleton_subset_iff] using
      measurableSet_superset_finset ({e} : Finset (CubicEdge d))

/-- The finite coordinate sigma-algebra is monotone in the finite edge support. -/
theorem edgeCoordinateMeasurableSpace_mono (d : ℕ) {s t : Finset (CubicEdge d)}
    (hst : s ⊆ t) :
    edgeCoordinateMeasurableSpace d s ≤ edgeCoordinateMeasurableSpace d t := by
  rw [edgeCoordinateMeasurableSpace, edgeCoordinateMeasurableSpace]
  exact MeasurableSpace.generateFrom_le fun A hA ↦ by
    rcases hA with ⟨e, he, rfl⟩
    exact measurableSet_edgeCoordinateEvent_of_mem d t (hst he)

/-- A finite open-edge cylinder is measurable with respect to the coordinate sigma-algebra
generated by its own finite support. -/
theorem measurableSet_openEdgeSetEvent_edgeCoordinateMeasurableSpace
    (d : ℕ) (s : Finset (CubicEdge d)) :
    MeasurableSet[edgeCoordinateMeasurableSpace d s] (openEdgeSetEvent d s) := by
  classical
  rw [show openEdgeSetEvent d s =
      ⋂ e ∈ s, {ω : EdgeConfiguration d | e ∈ ω} by
    ext ω
    simp [openEdgeSetEvent, Set.subset_def]]
  exact MeasurableSet.biInter (Finset.countable_toSet s) fun e he ↦
    measurableSet_edgeCoordinateEvent_of_mem d s he

/-- A finite closed-edge cylinder is measurable with respect to the coordinate sigma-algebra
generated by its own finite support. -/
theorem measurableSet_closedEdgeSetEvent_edgeCoordinateMeasurableSpace
    (d : ℕ) (s : Finset (CubicEdge d)) :
    MeasurableSet[edgeCoordinateMeasurableSpace d s] (closedEdgeSetEvent d s) := by
  classical
  rw [show closedEdgeSetEvent d s =
      ⋂ e ∈ s, ({ω : EdgeConfiguration d | e ∈ ω})ᶜ by
    ext ω
    simp [closedEdgeSetEvent, Set.disjoint_left]]
  exact MeasurableSet.biInter (Finset.countable_toSet s) fun e he ↦
    (measurableSet_edgeCoordinateEvent_of_mem d s he).compl

/-- The finite coordinate sigma-algebras generated by two disjoint edge sets are independent under
Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_indep_edgeCoordinateMeasurableSpace_of_disjoint
    (d : ℕ) (p : I) (s t : Finset (CubicEdge d))
    (hdisj : Disjoint (s : Set (CubicEdge d)) (t : Set (CubicEdge d))) :
    Indep (edgeCoordinateMeasurableSpace d s) (edgeCoordinateMeasurableSpace d t)
      (bernoulliBondMeasure d p) := by
  classical
  have hsm : ∀ e : CubicEdge d, MeasurableSet {ω : EdgeConfiguration d | e ∈ ω} := by
    intro e
    simpa [Set.singleton_subset_iff] using
      measurableSet_superset_finset ({e} : Finset (CubicEdge d))
  simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
    (ProbabilityTheory.iIndepSet.indep_generateFrom_of_disjoint
      (μ := bernoulliBondMeasure d p)
      (s := fun e : CubicEdge d ↦ {ω : EdgeConfiguration d | e ∈ ω})
      hsm (bernoulliBondMeasure_iIndepSet_edgeOpen d p)
      ((s : Set (CubicEdge d))) ((t : Set (CubicEdge d))) hdisj)

/-- Any two events depending only on disjoint finite edge sets are independent under Bernoulli
bond percolation. -/
theorem bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace
    (d : ℕ) (p : I) (s t : Finset (CubicEdge d))
    {A B : Set (EdgeConfiguration d)}
    (hdisj : Disjoint (s : Set (CubicEdge d)) (t : Set (CubicEdge d)))
    (hA : MeasurableSet[edgeCoordinateMeasurableSpace d s] A)
    (hB : MeasurableSet[edgeCoordinateMeasurableSpace d t] B) :
    IndepSet A B (bernoulliBondMeasure d p) := by
  classical
  haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  have hIndep :=
    bernoulliBondMeasure_indep_edgeCoordinateMeasurableSpace_of_disjoint d p s t hdisj
  have hAamb : MeasurableSet A := (edgeCoordinateMeasurableSpace_le d s) A hA
  have hBamb : MeasurableSet B := (edgeCoordinateMeasurableSpace_le d t) B hB
  rw [indepSet_iff_measure_inter_eq_mul (μ := bernoulliBondMeasure d p) hAamb hBamb]
  exact (Indep_iff _ _ (bernoulliBondMeasure d p)).1 hIndep A B hA hB

/-- In the Bernoulli product measure on all coordinates, the event that a fixed finite set of
coordinates is absent has probability `(1 - p) ^ |s|`. This is the finite closed-circuit
probability calculation needed for the planar Peierls half of Grimmett's proof. -/
theorem setBernoulli_real_disjoint_finset_univ {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : I) :
    setBer((Set.univ : Set ι), p).real {t : Set ι | Disjoint (s : Set ι) t} =
      (1 - (p : ℝ)) ^ s.card := by
  classical
  rw [measureReal_def, ProbabilityTheory.setBernoulli_apply']
  let μ : ι → Measure Prop := fun i ↦
    unitInterval.toNNReal p • Measure.dirac (i ∈ (Set.univ : Set ι)) +
      unitInterval.toNNReal (σ p) • Measure.dirac False
  have hpre :
      ((fun p : ι → Prop ↦ {i | p i}) ⁻¹' {t : Set ι | Disjoint (s : Set ι) t}) =
        cylinder s {f : ∀ i : s, Prop | ∀ i : s, ¬ f i} := by
    ext f
    simp [cylinder, Finset.restrict, Set.disjoint_left]
  change ((Measure.infinitePi μ) ((fun p : ι → Prop ↦ {i | p i}) ⁻¹'
      {t : Set ι | Disjoint (s : Set ι) t})).toReal = (1 - (p : ℝ)) ^ s.card
  rw [hpre, MeasureTheory.Measure.infinitePi_cylinder]
  · have hset : ({f : ∀ i : s, Prop | ∀ i : s, ¬ f i} : Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun _ : s ↦ ({False} : Set Prop)) := by
      ext f
      simp
    rw [hset, Measure.pi_pi]
    simp [μ]
  · rw [show ({f : ∀ i : s, Prop | ∀ i : s, ¬ f i} : Set (∀ i : s, Prop)) =
        Set.pi Set.univ (fun _ : s ↦ ({False} : Set Prop)) by
      ext f
      simp]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_singleton False

/-- Mixed finite-cylinder probability: all coordinates in `s` are present and all disjoint
coordinates in `t` are absent. This is the finite product calculation used when the open event
`G_m` is separated from closed dual-circuit coordinates in Grimmett's Peierls argument. -/
theorem setBernoulli_real_open_closed_on_finset_univ {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (p : I) (hdisj : Disjoint (s : Set ι) (t : Set ι)) :
    setBer((Set.univ : Set ι), p).real
      {ω : Set ι | (s : Set ι) ⊆ ω ∧ Disjoint (t : Set ι) ω} =
      (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ t.card := by
  classical
  have hevent : {ω : Set ι | (s : Set ι) ⊆ ω ∧ Disjoint (t : Set ι) ω} =
      {ω : Set ι | ∀ i, i ∈ s ∪ t → ((i ∈ ω) = (i ∈ s))} := by
    ext ω
    constructor
    · rintro ⟨hs, ht⟩ i hi
      rw [Finset.mem_union] at hi
      by_cases his : i ∈ s
      · simp [his, hs his]
      · have hit : i ∈ t := hi.resolve_left his
        have hiω : i ∉ ω := (Set.disjoint_left.mp ht) hit
        simp [his, hiω]
    · intro h
      constructor
      · intro i hi
        have hi_eq := h i (Finset.mem_union_left t hi)
        have hiω_iff : i ∈ ω ↔ i ∈ s := by simpa using hi_eq
        exact hiω_iff.mpr hi
      · rw [Set.disjoint_left]
        intro i hit hiω
        have his : i ∉ s := by
          intro his
          exact (Set.disjoint_left.mp hdisj) his hit
        have hi_eq := h i (Finset.mem_union_right s hit)
        have hiω_iff : i ∈ ω ↔ i ∈ s := by simpa using hi_eq
        exact his (hiω_iff.mp hiω)
  have hfin_disj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i his hit
    exact (Set.disjoint_left.mp hdisj) his hit
  rw [hevent, setBernoulli_real_eqOn_finset_univ']
  rw [Finset.prod_union hfin_disj]
  have hsprod : (∏ x ∈ s, if x ∈ s then (p : ℝ) else 1 - (p : ℝ)) =
      (p : ℝ) ^ s.card := by
    exact Finset.prod_eq_pow_card (s := s)
      (f := fun x ↦ if x ∈ s then (p : ℝ) else 1 - (p : ℝ)) (b := (p : ℝ))
      (by intro x hx; simp [hx])
  have htprod : (∏ x ∈ t, if x ∈ s then (p : ℝ) else 1 - (p : ℝ)) =
      (1 - (p : ℝ)) ^ t.card := by
    exact Finset.prod_eq_pow_card (s := t)
      (f := fun x ↦ if x ∈ s then (p : ℝ) else 1 - (p : ℝ))
      (b := (1 - (p : ℝ))) (by
        intro x hx
        have hxs : x ∉ s := by
          intro hxs
          exact (Set.disjoint_left.mp hdisj) hxs hx
        simp [hxs])
  rw [hsprod, htprod]

/-- The probability that all edges in a fixed finite set are open. -/
theorem bernoulliBondMeasure_real_openOn_finset (d : ℕ) (p : I)
    (s : Finset (CubicEdge d)) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | (s : Set (CubicEdge d)) ⊆ ω} =
      (p : ℝ) ^ s.card := by
  simpa [bernoulliBondMeasure] using setBernoulli_real_superset_finset_univ s p

/-- Probability of the named finite open-edge event. -/
theorem bernoulliBondMeasure_real_openEdgeSetEvent (d : ℕ) (p : I)
    (s : Finset (CubicEdge d)) :
    (bernoulliBondMeasure d p).real (openEdgeSetEvent d s) = (p : ℝ) ^ s.card :=
  bernoulliBondMeasure_real_openOn_finset d p s

/-- A finite open-edge event has positive probability when `p > 0`. This is the positivity
ingredient for Grimmett's finite event `G_m`. -/
theorem bernoulliBondMeasure_real_openEdgeSetEvent_pos (d : ℕ) (p : I)
    (s : Finset (CubicEdge d)) (hp : 0 < (p : ℝ)) :
    0 < (bernoulliBondMeasure d p).real (openEdgeSetEvent d s) := by
  rw [bernoulliBondMeasure_real_openEdgeSetEvent]
  exact pow_pos hp s.card

/-- The probability that all edges in a fixed finite set are closed. -/
theorem bernoulliBondMeasure_real_closedOn_finset (d : ℕ) (p : I)
    (s : Finset (CubicEdge d)) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        Disjoint (s : Set (CubicEdge d)) ω} =
      (1 - (p : ℝ)) ^ s.card := by
  simpa [bernoulliBondMeasure] using setBernoulli_real_disjoint_finset_univ s p

/-- Probability of the named finite closed-edge event. -/
theorem bernoulliBondMeasure_real_closedEdgeSetEvent (d : ℕ) (p : I)
    (s : Finset (CubicEdge d)) :
    (bernoulliBondMeasure d p).real (closedEdgeSetEvent d s) =
      (1 - (p : ℝ)) ^ s.card :=
  bernoulliBondMeasure_real_closedOn_finset d p s

/-- Probability of a finite open-edge event intersected with a disjoint finite closed-edge
event. -/
theorem bernoulliBondMeasure_real_openEdgeSetEvent_inter_closedEdgeSetEvent
    (d : ℕ) (p : I) (s t : Finset (CubicEdge d))
    (hdisj : Disjoint (s : Set (CubicEdge d)) (t : Set (CubicEdge d))) :
    (bernoulliBondMeasure d p).real (openEdgeSetEvent d s ∩ closedEdgeSetEvent d t) =
      (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ t.card := by
  have hset : openEdgeSetEvent d s ∩ closedEdgeSetEvent d t =
      {ω : EdgeConfiguration d | (s : Set (CubicEdge d)) ⊆ ω ∧
        Disjoint (t : Set (CubicEdge d)) ω} := by
    ext ω
    rfl
  rw [hset]
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_open_closed_on_finset_univ s t p hdisj

/-- Finite disjoint open and closed edge cylinders are independent under Bernoulli bond
percolation. This is the reusable finite independence input for Grimmett's `G_m`/`F_m`
Peierls step. -/
theorem bernoulliBondMeasure_indepSet_openEdgeSetEvent_closedEdgeSetEvent
    (d : ℕ) (p : I) (s t : Finset (CubicEdge d))
    (hdisj : Disjoint (s : Set (CubicEdge d)) (t : Set (CubicEdge d))) :
    IndepSet (openEdgeSetEvent d s) (closedEdgeSetEvent d t) (bernoulliBondMeasure d p) := by
  classical
  haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  rw [indepSet_iff_measure_inter_eq_mul (μ := bernoulliBondMeasure d p)
    (measurableSet_openEdgeSetEvent d s) (measurableSet_closedEdgeSetEvent d t)]
  rw [← ENNReal.toReal_eq_toReal_iff']
  · rw [ENNReal.toReal_mul]
    change (bernoulliBondMeasure d p).real (openEdgeSetEvent d s ∩ closedEdgeSetEvent d t) =
      (bernoulliBondMeasure d p).real (openEdgeSetEvent d s) *
        (bernoulliBondMeasure d p).real (closedEdgeSetEvent d t)
    rw [bernoulliBondMeasure_real_openEdgeSetEvent_inter_closedEdgeSetEvent d p s t hdisj]
    rw [bernoulliBondMeasure_real_openEdgeSetEvent, bernoulliBondMeasure_real_closedEdgeSetEvent]
  · refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top
  · exact ENNReal.mul_ne_top
      (by
        refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
        rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
        exact ENNReal.one_lt_top)
      (by
        refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
        rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
        exact ENNReal.one_lt_top)

/-- The event that a walk is open is the finite cylinder event that all of its traversed edges
are open. -/
theorem walkIsOpen_event_eq_openOn_walkEdgeFinset {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    {ω : EdgeConfiguration d | walkIsOpen ω w} =
      {ω : EdgeConfiguration d | (walkEdgeFinset w : Set (CubicEdge d)) ⊆ ω} := by
  ext ω
  constructor
  · intro h e he
    have hew : (e : Sym2 (Cubic d)) ∈ w.edges := (mem_walkEdgeFinset_iff w e).mp he
    have hopen : edgeOpen ω ⟨(e : Sym2 (Cubic d)), w.edges_subset_edgeSet hew⟩ := h _ hew
    simpa [edgeOpen] using
      (Subtype.ext (show ((⟨(e : Sym2 (Cubic d)), w.edges_subset_edgeSet hew⟩ :
          CubicEdge d) : Sym2 (Cubic d)) = e from rfl) ▸ hopen)
  · intro h e he
    exact h (a := ⟨e, w.edges_subset_edgeSet he⟩) ((mem_walkEdgeFinset_iff w _).mpr he)

/-- If a walk uses only edges from a finite open-edge event that occurs, then the walk is open. -/
theorem walkIsOpen_of_mem_openEdgeSetEvent_of_walkEdgeFinset_subset
    {d : ℕ} {u v : Cubic d} {ω : EdgeConfiguration d} {s : Finset (CubicEdge d)}
    (hω : ω ∈ openEdgeSetEvent d s) (w : (cubicGraph d).Walk u v)
    (hsub : walkEdgeFinset w ⊆ s) :
    walkIsOpen ω w := by
  intro e he
  exact hω (hsub ((mem_walkEdgeFinset_iff w _).mpr he))

/-- The open-walk event is a measurable finite cylinder. -/
theorem measurableSet_walkIsOpen {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    MeasurableSet {ω : EdgeConfiguration d | walkIsOpen ω w} := by
  rw [walkIsOpen_event_eq_openOn_walkEdgeFinset]
  exact measurableSet_superset_finset (walkEdgeFinset w)

/-- A fixed open trail of length `n` has probability `p^n`. For self-avoiding paths, use the
included coercion from `IsPath` to `IsTrail`. -/
theorem bernoulliBondMeasure_real_walkIsOpen {d : ℕ} (p : I) {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (h : w.IsTrail) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} =
      (p : ℝ) ^ w.length := by
  rw [walkIsOpen_event_eq_openOn_walkEdgeFinset]
  rw [bernoulliBondMeasure_real_openOn_finset, walkEdgeFinset_card_of_isTrail h]

/-- A fixed open trail has positive probability when `p > 0`. -/
theorem bernoulliBondMeasure_real_walkIsOpen_pos {d : ℕ} (p : I) {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (h : w.IsTrail) (hp : 0 < (p : ℝ)) :
    0 < (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω w} := by
  rw [bernoulliBondMeasure_real_walkIsOpen p w h]
  exact pow_pos hp w.length

/-- A counted self-avoiding direction word is open in a bond configuration when its represented
graph walk is open. -/
def selfAvoidingWalkIsOpen {d n : ℕ} (ω : EdgeConfiguration d)
    (steps : SelfAvoidingWalk d n) : Prop :=
  walkIsOpen ω (selfAvoidingWalkWalk steps)

/-- The open event for one counted self-avoiding walk is measurable. -/
theorem measurableSet_selfAvoidingWalkIsOpen {d n : ℕ}
    (steps : SelfAvoidingWalk d n) :
    MeasurableSet {ω : EdgeConfiguration d | selfAvoidingWalkIsOpen ω steps} := by
  unfold selfAvoidingWalkIsOpen
  exact measurableSet_walkIsOpen (selfAvoidingWalkWalk steps)

/-- The open event for one counted self-avoiding walk of length `n` has probability `p^n`. -/
theorem bernoulliBondMeasure_real_selfAvoidingWalkIsOpen (d n : ℕ) (p : I)
    (steps : SelfAvoidingWalk d n) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        selfAvoidingWalkIsOpen ω steps} =
      (p : ℝ) ^ n := by
  unfold selfAvoidingWalkIsOpen
  rw [bernoulliBondMeasure_real_walkIsOpen p (selfAvoidingWalkWalk steps)
    (selfAvoidingWalkWalk_isPath steps).isTrail]
  simp

/-- There is at least one open counted self-avoiding direction word of length `n`. -/
def existsOpenSelfAvoidingWalk (d n : ℕ) (ω : EdgeConfiguration d) : Prop :=
  ∃ steps : SelfAvoidingWalk d n, selfAvoidingWalkIsOpen ω steps

/-- The finite union of open events over all counted self-avoiding walks of length `n` is
measurable. -/
theorem measurableSet_existsOpenSelfAvoidingWalk (d n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalk d n ω} := by
  classical
  rw [show {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalk d n ω} =
      ⋃ steps : SelfAvoidingWalk d n,
        {ω : EdgeConfiguration d | selfAvoidingWalkIsOpen ω steps} by
    ext ω
    simp [existsOpenSelfAvoidingWalk]]
  exact MeasurableSet.iUnion measurableSet_selfAvoidingWalkIsOpen

/-- Finite union bound over all counted self-avoiding walks of length `n`. -/
theorem bernoulliBondMeasure_real_existsOpenSelfAvoidingWalk_le (d n : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        existsOpenSelfAvoidingWalk d n ω} ≤
      (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
  classical
  calc
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        existsOpenSelfAvoidingWalk d n ω}
        = (bernoulliBondMeasure d p).real
            (⋃ steps : SelfAvoidingWalk d n,
              {ω : EdgeConfiguration d | selfAvoidingWalkIsOpen ω steps}) := by
          congr 1
          ext ω
          simp [existsOpenSelfAvoidingWalk]
    _ ≤ ∑ steps : SelfAvoidingWalk d n,
          (bernoulliBondMeasure d p).real
            {ω : EdgeConfiguration d | selfAvoidingWalkIsOpen ω steps} :=
        measureReal_iUnion_fintype_le _
    _ = (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
        simp [bernoulliBondMeasure_real_selfAvoidingWalkIsOpen, selfAvoidingWalkCount]

/-- Any open graph-theoretic self-avoiding path of length `n` from the origin is represented by
one of the counted signed-direction self-avoiding walks of length `n`. -/
theorem hasOpenPathOfLengthExactly_imp_existsOpenSelfAvoidingWalk {d n : ℕ}
    {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthExactly d ω n → existsOpenSelfAvoidingWalk d n ω := by
  rintro ⟨v, w, hwpath, hwlen, hopen⟩
  rcases exists_cubicWalkFrom_copy_eq w with ⟨steps, hend, heq, hlen⟩
  let vec : List.Vector (CubicDirection d) n := ⟨steps, by rw [hlen, hwlen]⟩
  have hnodup : cubicVectorSelfAvoiding vec := by
    unfold cubicVectorSelfAvoiding cubicVectorVertices
    have hcopy_nodup : ((cubicWalkFrom cubicOrigin steps).copy rfl hend).support.Nodup := by
      rw [heq]
      exact hwpath.support_nodup
    simpa [vec, SimpleGraph.Walk.support_copy, cubicWalkFrom_support] using hcopy_nodup
  refine ⟨⟨vec, hnodup⟩, ?_⟩
  unfold selfAvoidingWalkIsOpen selfAvoidingWalkWalk
  intro e he
  have hcopyopen : walkIsOpen ω ((cubicWalkFrom cubicOrigin steps).copy rfl hend) := by
    rw [heq]
    exact hopen
  have hecopy : e ∈ ((cubicWalkFrom cubicOrigin steps).copy rfl hend).edges := by
    simpa [SimpleGraph.Walk.edges_copy] using he
  exact hcopyopen e hecopy

/-- A counted open self-avoiding direction word gives an open graph-theoretic path of the same
length from the origin. -/
theorem existsOpenSelfAvoidingWalk_imp_hasOpenPathOfLengthExactly {d n : ℕ}
    {ω : EdgeConfiguration d} :
    existsOpenSelfAvoidingWalk d n ω → hasOpenPathOfLengthExactly d ω n := by
  rintro ⟨steps, hopen⟩
  exact ⟨cubicEndpointFrom cubicOrigin steps.1.toList, selfAvoidingWalkWalk steps,
    selfAvoidingWalkWalk_isPath steps, selfAvoidingWalkWalk_length steps, hopen⟩

/-- The graph-theoretic and counted direction-word exact-length open-path events agree. -/
theorem hasOpenPathOfLengthExactly_iff_existsOpenSelfAvoidingWalk {d n : ℕ}
    {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthExactly d ω n ↔ existsOpenSelfAvoidingWalk d n ω :=
  ⟨hasOpenPathOfLengthExactly_imp_existsOpenSelfAvoidingWalk,
    existsOpenSelfAvoidingWalk_imp_hasOpenPathOfLengthExactly⟩

/-- The exact-length open-path event is measurable. -/
theorem measurableSet_hasOpenPathOfLengthExactly (d n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasOpenPathOfLengthExactly d ω n} := by
  rw [show {ω : EdgeConfiguration d | hasOpenPathOfLengthExactly d ω n} =
      {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalk d n ω} by
    ext ω
    exact hasOpenPathOfLengthExactly_iff_existsOpenSelfAvoidingWalk]
  exact measurableSet_existsOpenSelfAvoidingWalk d n

/-- The length-at-least open-path event is measurable. -/
theorem measurableSet_hasOpenPathOfLengthAtLeast (d n : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} := by
  rw [show {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} =
      {ω : EdgeConfiguration d | hasOpenPathOfLengthExactly d ω n} by
    ext ω
    exact hasOpenPathOfLengthAtLeast_iff_hasOpenPathOfLengthExactly]
  exact measurableSet_hasOpenPathOfLengthExactly d n

/-- The infinite open-cluster event is measurable as a countable intersection of finite path
events. -/
theorem measurableSet_hasInfiniteOpenCluster (d : ℕ) :
    MeasurableSet {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} := by
  rw [show {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} =
      ⋂ n : ℕ, {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    simpa [hasArbitrarilyLongOpenPaths] using
      (hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths (d := d) (ω := ω))]
  exact MeasurableSet.iInter (fun n ↦ measurableSet_hasOpenPathOfLengthAtLeast d n)

/-- Grimmett's finite path-counting bound for open graph-theoretic self-avoiding paths of
exact length `n`: the event is bounded by `σ(n) p^n`. -/
theorem bernoulliBondMeasure_real_hasOpenPathOfLengthExactly_le (d n : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        hasOpenPathOfLengthExactly d ω n} ≤
      (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
  calc
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        hasOpenPathOfLengthExactly d ω n} ≤
        (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
          existsOpenSelfAvoidingWalk d n ω} := by
      refine measureReal_mono
        (fun _ hω ↦ hasOpenPathOfLengthExactly_imp_existsOpenSelfAvoidingWalk hω) ?_
      change setBer((Set.univ : Set (CubicEdge d)), p)
          {ω : EdgeConfiguration d | existsOpenSelfAvoidingWalk d n ω} ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    _ ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
      bernoulliBondMeasure_real_existsOpenSelfAvoidingWalk_le d n p

/-- Grimmett's finite path-counting bound in the “length at least `n`” form. The initial segment
of length `n` reduces the event to the exact-length union bound. -/
theorem bernoulliBondMeasure_real_hasOpenPathOfLengthAtLeast_le (d n : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        hasOpenPathOfLengthAtLeast d ω n} ≤
      (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
  calc
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
        hasOpenPathOfLengthAtLeast d ω n} ≤
        (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
          hasOpenPathOfLengthExactly d ω n} := by
      refine measureReal_mono
        (fun _ hω ↦ hasOpenPathOfLengthAtLeast_imp_hasOpenPathOfLengthExactly hω) ?_
      change setBer((Set.univ : Set (CubicEdge d)), p)
          {ω : EdgeConfiguration d | hasOpenPathOfLengthExactly d ω n} ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    _ ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
      bernoulliBondMeasure_real_hasOpenPathOfLengthExactly_le d n p

/-- Percolation probability for the origin in `L^d`: the probability that Grimmett's open cluster
`C_0(ω)` is infinite. The path-counting lemmas use the equivalent arbitrarily-long-open-path
formulation proved in `hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths`. -/
noncomputable def theta (d : ℕ) (p : I) : ℝ :=
  (bernoulliBondMeasure d p).real {ω | hasInfiniteOpenCluster d ω}

/-- Increasing the ambient cubic-lattice dimension can only increase the origin percolation
probability. This is the measure-theoretic half of Grimmett's dimension-monotonicity argument,
using the coordinate embedding of lower-dimensional configurations. -/
theorem theta_le_theta_of_le_dimension {m d : ℕ} (hmd : m ≤ d) (p : I) :
    theta m p ≤ theta d p := by
  unfold theta
  have hmeas_pullback : Measurable (cubicConfigurationPullback hmd) := by
    simpa [cubicConfigurationPullback] using
      measurable_preimage_embedding (cubicEdgeEmbed hmd)
  calc
    (bernoulliBondMeasure m p).real {ω : EdgeConfiguration m |
        hasInfiniteOpenCluster m ω}
        = ((bernoulliBondMeasure d p).map (cubicConfigurationPullback hmd)).real
            {ω : EdgeConfiguration m | hasInfiniteOpenCluster m ω} := by
          rw [bernoulliBondMeasure_map_cubicConfigurationPullback hmd p]
    _ = (bernoulliBondMeasure d p).real
          ((cubicConfigurationPullback hmd) ⁻¹'
            {ω : EdgeConfiguration m | hasInfiniteOpenCluster m ω}) := by
          exact MeasureTheory.map_measureReal_apply hmeas_pullback
            (measurableSet_hasInfiniteOpenCluster m)
    _ ≤ (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
          hasInfiniteOpenCluster d ω} := by
          refine measureReal_mono
            (fun _ hω ↦ hasInfiniteOpenCluster_cubicConfigurationPullback hmd hω) ?_
          change setBer((Set.univ : Set (CubicEdge d)), p)
              {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} ≠ ∞
          refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
          rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
          exact ENNReal.one_lt_top

/-- Vanishing of the origin percolation probability in a higher-dimensional cubic lattice
implies vanishing in any embedded lower-dimensional cubic lattice. -/
theorem theta_eq_zero_of_le_dimension {m d : ℕ} (hmd : m ≤ d) {p : I}
    (h : theta d p = 0) :
    theta m p = 0 := by
  apply le_antisymm
  · exact (theta_le_theta_of_le_dimension hmd p).trans_eq h
  · exact measureReal_nonneg

/-- Grimmett's finite tail estimate for the origin percolation event: if the origin is in an
infinite open cluster, then it has an open self-avoiding path of length at least `n`. -/
theorem theta_le_selfAvoidingWalkCount_mul_pow (d n : ℕ) (p : I) :
    theta d p ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
  unfold theta
  calc
    (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | hasInfiniteOpenCluster d ω} ≤
        (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d |
          hasOpenPathOfLengthAtLeast d ω n} := by
      refine measureReal_mono
        (fun _ hω ↦
          (hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths.mp hω) n) ?_
      change setBer((Set.univ : Set (CubicEdge d)), p)
          {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    _ ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
      bernoulliBondMeasure_real_hasOpenPathOfLengthAtLeast_le d n p

/-- If Grimmett's finite path-counting upper bound tends to zero, then the percolation
probability is zero. This isolates the remaining connective-constant/Fekete limit step from the
measure and union-bound formalization. -/
theorem theta_eq_zero_of_tendsto_selfAvoidingWalkCount_mul_pow (d : ℕ) (p : I)
    (hlim : Filter.Tendsto
      (fun n : ℕ ↦ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n)
      Filter.atTop (nhds 0)) :
    theta d p = 0 := by
  apply le_antisymm
  · have hconst : Filter.Tendsto (fun _ : ℕ ↦ theta d p) Filter.atTop
        (nhds (theta d p)) :=
      tendsto_const_nhds
    have hle :
        (fun _ : ℕ ↦ theta d p) ≤ᶠ[Filter.atTop]
          fun n : ℕ ↦ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
      filter_upwards [Filter.eventually_ge_atTop 0] with n hn
      exact theta_le_selfAvoidingWalkCount_mul_pow d n p
    simpa using le_of_tendsto_of_tendsto hconst hlim hle
  · unfold theta
    exact measureReal_nonneg

/-- If the self-avoiding-walk counts are eventually bounded by `c^n` and `pc < 1`, then
Grimmett's finite path-counting upper bound tends to zero. -/
theorem tendsto_selfAvoidingWalkCount_mul_pow_of_eventually_le_pow (d : ℕ) (p : I)
    {c : ℝ} (hc0 : 0 ≤ c) (hpc : (p : ℝ) * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    Filter.Tendsto
      (fun n : ℕ ↦ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hnonneg :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
    Filter.Eventually.of_forall fun n ↦ by
      exact mul_nonneg (by positivity) (pow_nonneg hp0 n)
  have hle :
      ∀ᶠ n : ℕ in Filter.atTop,
        (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n ≤ (c * (p : ℝ)) ^ n := by
    filter_upwards [hbound] with n hn
    calc
      (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n ≤ c ^ n * (p : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hn (pow_nonneg hp0 n)
      _ = (c * (p : ℝ)) ^ n := by rw [mul_pow]
  exact squeeze_zero' hnonneg hle <|
    tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hc0 hp0) (by simpa [mul_comm] using hpc)

/-- A bundled lower-tail criterion: an eventual exponential bound with `pc < 1` forces
`θ(p) = 0`. -/
theorem theta_eq_zero_of_eventually_selfAvoidingWalkCount_le_pow (d : ℕ) (p : I)
    {c : ℝ} (hc0 : 0 ≤ c) (hpc : (p : ℝ) * c < 1)
    (hbound : ∀ᶠ n in Filter.atTop, (selfAvoidingWalkCount d n : ℝ) ≤ c ^ n) :
    theta d p = 0 :=
  theta_eq_zero_of_tendsto_selfAvoidingWalkCount_mul_pow d p
    (tendsto_selfAvoidingWalkCount_mul_pow_of_eventually_le_pow d p hc0 hpc hbound)

end Percolation
