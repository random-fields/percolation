import Percolation.Bernoulli.Inhomogeneous

/-!
# Finite plaquette surfaces

This file supplies the parity boundary and probability core of Grimmett's Chapter 12 surface
model.  Geometry is separated from probability: a finite plaquette system specifies the four
dual edges bounding each plaquette, while the Bernoulli coordinate indexed by a plaquette is the
state of the unique primal edge crossing it.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

/-- Finite boundary data for plaquettes.  The concrete cubic system has four boundary edges per
plaquette; keeping the parity construction generic makes its algebra reusable. -/
structure PlaquetteBoundarySystem (P D : Type*) [DecidableEq P] [DecidableEq D] where
  boundary : P → Finset D

namespace PlaquetteBoundarySystem

variable {P D : Type*} [DecidableEq P] [DecidableEq D]
    (B : PlaquetteBoundarySystem P D)

/-- Number of plaquettes of `S` incident to a dual edge. -/
def incidenceCount (S : Finset P) (e : D) : ℕ :=
  (S.filter fun π ↦ e ∈ B.boundary π).card

/-- Mod-two boundary of a finite plaquette collection. -/
def surfaceBoundary (S : Finset P) : Finset D :=
  (S.biUnion B.boundary).filter fun e ↦ Odd (B.incidenceCount S e)

theorem mem_surfaceBoundary_iff (S : Finset P) (e : D) :
    e ∈ B.surfaceBoundary S ↔ Odd (B.incidenceCount S e) := by
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro hodd
    apply Finset.mem_filter.mpr
    refine ⟨?_, hodd⟩
    rw [Finset.mem_biUnion]
    obtain ⟨π, hπ⟩ := Finset.card_pos.mp (Odd.pos hodd)
    have hπS := (Finset.mem_filter.mp hπ).1
    have heπ := (Finset.mem_filter.mp hπ).2
    exact ⟨π, hπS, heπ⟩

@[simp]
theorem surfaceBoundary_empty : B.surfaceBoundary ∅ = ∅ := by
  ext e
  simp [surfaceBoundary, incidenceCount]

end PlaquetteBoundarySystem

/-- Plaquette configurations record the open plaquettes (equivalently open crossing primal
edges).  A surface is closed when it is disjoint from this set. -/
abbrev PlaquetteConfiguration (P : Type*) := Set P

/-- Event that the prescribed dual boundary is spanned by some finite closed plaquette surface. -/
def closedPlaquetteSurfaceEvent {P D : Type*} [DecidableEq P] [DecidableEq D]
    (B : PlaquetteBoundarySystem P D) (C : Finset D) :
    Set (PlaquetteConfiguration P) :=
  {ω | ∃ S : Finset P, B.surfaceBoundary S = C ∧ Disjoint (S : Set P) ω}

theorem measurableSet_closedPlaquetteSurfaceEvent
    {P D : Type*} [Countable P] [DecidableEq P] [DecidableEq D]
    (B : PlaquetteBoundarySystem P D) (C : Finset D) :
    MeasurableSet (closedPlaquetteSurfaceEvent B C) := by
  rw [show closedPlaquetteSurfaceEvent B C =
      ⋃ S : Finset P, if B.surfaceBoundary S = C then
        {ω : Set P | Disjoint (S : Set P) ω} else ∅ by
    ext ω
    simp [closedPlaquetteSurfaceEvent]]
  exact MeasurableSet.iUnion fun S ↦ by
    split_ifs
    · exact measurableSet_disjoint_finset S
    · exact MeasurableSet.empty

/-- The closed cylinder of any explicit spanning surface is contained in the surface event. -/
theorem disjoint_surface_subset_closedPlaquetteSurfaceEvent
    {P D : Type*} [DecidableEq P] [DecidableEq D]
    (B : PlaquetteBoundarySystem P D) (C : Finset D) (S : Finset P)
    (hSC : B.surfaceBoundary S = C) :
    {ω : Set P | Disjoint (S : Set P) ω} ⊆ closedPlaquetteSurfaceEvent B C := by
  intro ω hω
  exact ⟨S, hSC, hω⟩

/-- Abstract form of (12.20): one explicit `N`-plaquette spanning surface gives the lower
bound `(1-p)^N`. -/
theorem closedPlaquetteSurface_probability_ge
    {P D : Type*} [Countable P] [DecidableEq P] [DecidableEq D]
    (B : PlaquetteBoundarySystem P D) (C : Finset D) (S : Finset P)
    (hSC : B.surfaceBoundary S = C) (p : I) :
    (1 - (p : ℝ)) ^ S.card ≤
      (setBernoulli (Set.univ : Set P) p).real
        (closedPlaquetteSurfaceEvent B C) := by
  rw [← setBernoulli_real_disjoint_finset_univ S p]
  exact measureReal_mono
    (disjoint_surface_subset_closedPlaquetteSurfaceEvent B C S hSC)
    (measure_ne_top _ _)

/-- A block fails when not all plaquettes in it are open. -/
def plaquetteBlockFailureEvent {P : Type*} (S : Finset P) : Set (Set P) :=
  {ω | ¬(S : Set P) ⊆ ω}

theorem plaquetteBlockFailureEvent_eq_compl {P : Type*} (S : Finset P) :
    plaquetteBlockFailureEvent S = {ω : Set P | (S : Set P) ⊆ ω}ᶜ := by
  rfl

theorem measurableSet_plaquetteBlockFailureEvent {P : Type*} [DecidableEq P]
    (S : Finset P) :
    MeasurableSet (plaquetteBlockFailureEvent S) := by
  rw [plaquetteBlockFailureEvent_eq_compl]
  exact (measurableSet_superset_finset S).compl

theorem dependsOn_plaquetteBlockFailureEvent {P : Type*} [DecidableEq P]
    (S : Finset P) : DependsOn S (plaquetteBlockFailureEvent S) := by
  intro ω η hagree
  simp only [plaquetteBlockFailureEvent, Set.mem_setOf_eq]
  constructor
  · intro hω hSη
    apply hω
    intro x hx
    exact (hagree x hx).mpr (hSη hx)
  · intro hη hSω
    apply hη
    intro x hx
    exact (hagree x hx).mp (hSω hx)

theorem setBernoulli_real_plaquetteBlockFailureEvent
    {P : Type*} [DecidableEq P] (S : Finset P) (p : I) :
    (setBernoulli (Set.univ : Set P) p).real (plaquetteBlockFailureEvent S) =
      1 - (p : ℝ) ^ S.card := by
  rw [plaquetteBlockFailureEvent_eq_compl,
    probReal_compl_eq_one_sub (measurableSet_superset_finset S),
    setBernoulli_real_superset_finset_univ]

/-- Failure events attached to pairwise-disjoint plaquette blocks factor exactly.  This is the
probabilistic calculation used in the upper surface bound (12.21); the geometric part of that
argument is the construction of the disjoint four-plaquette blocks along the prescribed
boundary. -/
theorem setBernoulli_real_iInter_plaquetteBlockFailureEvent
    {P κ : Type*} [DecidableEq P] [DecidableEq κ] [Fintype κ]
    (block : κ → Finset P)
    (hpair : Set.PairwiseDisjoint (Set.univ : Set κ) block) (p : I) :
    (setBernoulli (Set.univ : Set P) p).real
        (⋂ k : κ, plaquetteBlockFailureEvent (block k)) =
      ∏ k : κ, (1 - (p : ℝ) ^ (block k).card) := by
  classical
  have hi : iIndepSet (fun k : κ ↦ plaquetteBlockFailureEvent (block k))
      (setBernoulli (Set.univ : Set P) p) := by
    rw [← inhomogeneousSetBernoulli_const p]
    exact inhomogeneousSetBernoulli_iIndepSet_of_pairwiseDisjoint_dependsOn
      (fun _ : P ↦ p) block (fun k ↦ plaquetteBlockFailureEvent (block k))
        (fun k ↦ dependsOn_plaquetteBlockFailureEvent (block k)) hpair
  have hmeasure := hi.meas_biInter (Finset.univ : Finset κ)
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_prod] at hreal
  have hset :
      (⋂ k ∈ (Finset.univ : Finset κ), plaquetteBlockFailureEvent (block k)) =
        ⋂ k : κ, plaquetteBlockFailureEvent (block k) := by
    ext ω
    simp
  rw [hset] at hreal
  calc
    (setBernoulli (Set.univ : Set P) p).real
        (⋂ k : κ, plaquetteBlockFailureEvent (block k)) =
        ∏ k : κ, (setBernoulli (Set.univ : Set P) p).real
          (plaquetteBlockFailureEvent (block k)) := by
      simpa only [measureReal_def] using hreal
    _ = ∏ k : κ, (1 - (p : ℝ) ^ (block k).card) := by
      apply Finset.prod_congr rfl
      intro k _hk
      exact setBernoulli_real_plaquetteBlockFailureEvent (block k) p

/-- If every closed spanning surface must fail every member of a pairwise-disjoint family of
`m`-plaquette blocks, its probability is at most `(1-p^m)^numberOfBlocks`. -/
theorem closedPlaquetteSurface_probability_le_of_blocks
    {P D κ : Type*} [Countable P] [DecidableEq P] [DecidableEq D]
    [DecidableEq κ] [Fintype κ]
    (B : PlaquetteBoundarySystem P D) (C : Finset D) (block : κ → Finset P)
    (m : ℕ) (hcard : ∀ k, (block k).card = m)
    (hpair : Set.PairwiseDisjoint (Set.univ : Set κ) block)
    (hforce : closedPlaquetteSurfaceEvent B C ⊆
      ⋂ k : κ, plaquetteBlockFailureEvent (block k)) (p : I) :
    (setBernoulli (Set.univ : Set P) p).real
        (closedPlaquetteSurfaceEvent B C) ≤
      (1 - (p : ℝ) ^ m) ^ Fintype.card κ := by
  calc
    (setBernoulli (Set.univ : Set P) p).real
        (closedPlaquetteSurfaceEvent B C) ≤
        (setBernoulli (Set.univ : Set P) p).real
          (⋂ k : κ, plaquetteBlockFailureEvent (block k)) :=
      measureReal_mono hforce (measure_ne_top _ _)
    _ = ∏ k : κ, (1 - (p : ℝ) ^ (block k).card) :=
      setBernoulli_real_iInter_plaquetteBlockFailureEvent block hpair p
    _ = (1 - (p : ℝ) ^ m) ^ Fintype.card κ := by
      simp_rw [hcard]
      simp

end Percolation
