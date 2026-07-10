import Percolation.Critical.CubicTorus
import Percolation.Critical.GhostField

/-!
# The ghost field on a periodic cubic lattice

This is the finite-volume model used for Grimmett's differential inequalities (5.51) and (5.53).
The edge and green-site fields remain separate product factors, so their two partial derivatives
can be handled independently by Russo's formula.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

abbrev CubicTorusEdge (d N : ℕ) :=
  {e : Sym2 (CubicTorus d N) // e ∈ (cubicTorusGraph d N).edgeSet}

abbrev CubicTorusEdgeConfiguration (d N : ℕ) := Set (CubicTorusEdge d N)

def cubicTorusOrigin (d N : ℕ) : CubicTorus d N := 0

def torusWalkIsOpen {d N : ℕ} (ω : CubicTorusEdgeConfiguration d N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v) : Prop :=
  ∀ e, ∀ he : e ∈ w.edges, (⟨e, w.edges_subset_edgeSet he⟩ : CubicTorusEdge d N) ∈ ω

def cubicTorusOpenClusterFrom (d N : ℕ) (ω : CubicTorusEdgeConfiguration d N)
    (x : CubicTorus d N) : Set (CubicTorus d N) :=
  {y | ∃ w : (cubicTorusGraph d N).Walk x y, torusWalkIsOpen ω w}

def cubicTorusOpenCluster (d N : ℕ) (ω : CubicTorusEdgeConfiguration d N) :
    Set (CubicTorus d N) :=
  cubicTorusOpenClusterFrom d N ω (cubicTorusOrigin d N)

theorem cubicTorusOrigin_mem_openCluster (d N : ℕ)
    (ω : CubicTorusEdgeConfiguration d N) :
    cubicTorusOrigin d N ∈ cubicTorusOpenCluster d N ω := by
  exact ⟨.nil, by intro e he; cases he⟩

theorem cubicTorusOpenCluster_nonempty (d N : ℕ)
    (ω : CubicTorusEdgeConfiguration d N) :
    (cubicTorusOpenCluster d N ω).Nonempty :=
  ⟨cubicTorusOrigin d N, cubicTorusOrigin_mem_openCluster d N ω⟩

noncomputable def torusBondMeasure (d N : ℕ) (p : I) :
    Measure (CubicTorusEdgeConfiguration d N) :=
  setBer((Set.univ : Set (CubicTorusEdge d N)), p)

noncomputable instance torusBondMeasure_isProbabilityMeasure (d N : ℕ) (p : I) :
    IsProbabilityMeasure (torusBondMeasure d N p) := by
  unfold torusBondMeasure
  infer_instance

abbrev TorusGhostConfiguration (d N : ℕ) :=
  CubicTorusEdgeConfiguration d N × Set (CubicTorus d N)

noncomputable def torusGhostMeasure (d N : ℕ) (p γ : I) :
    Measure (TorusGhostConfiguration d N) :=
  (torusBondMeasure d N p).prod setBer((Set.univ : Set (CubicTorus d N)), γ)

noncomputable instance torusGhostMeasure_isProbabilityMeasure (d N : ℕ) (p γ : I) :
    IsProbabilityMeasure (torusGhostMeasure d N p γ) := by
  unfold torusGhostMeasure
  infer_instance

def torusGhostHitEvent (d N : ℕ) : Set (TorusGhostConfiguration d N) :=
  {ξ | ∃ y : CubicTorus d N, y ∈ cubicTorusOpenCluster d N ξ.1 ∧ y ∈ ξ.2}

def torusConnectionEvent (d N : ℕ) (x y : CubicTorus d N) :
    Set (CubicTorusEdgeConfiguration d N) :=
  {ω | y ∈ cubicTorusOpenClusterFrom d N ω x}

theorem torusGhostHitEvent_eq_iUnion (d N : ℕ) :
    torusGhostHitEvent d N = ⋃ y : CubicTorus d N,
      Prod.fst ⁻¹' (torusConnectionEvent d N (cubicTorusOrigin d N) y) ∩
        Prod.snd ⁻¹' {G : Set (CubicTorus d N) | y ∈ G} := by
  ext ξ
  simp [torusGhostHitEvent, torusConnectionEvent, cubicTorusOpenCluster]

noncomputable def cubicTorusEdgeFinset (d N : ℕ) (hN : 2 ≤ N) :
    Finset (CubicTorusEdge d N) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  exact Finset.univ

noncomputable def cubicTorusVertexFinset (d N : ℕ) (hN : 2 ≤ N) :
    Finset (CubicTorus d N) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  exact Finset.univ

@[simp]
theorem mem_cubicTorusEdgeFinset {d N : ℕ} (hN : 2 ≤ N)
    (e : CubicTorusEdge d N) : e ∈ cubicTorusEdgeFinset d N hN := by
  unfold cubicTorusEdgeFinset
  simp

@[simp]
theorem mem_cubicTorusVertexFinset {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) : x ∈ cubicTorusVertexFinset d N hN := by
  unfold cubicTorusVertexFinset
  simp

theorem dependsOn_torusConnectionEvent (d N : ℕ) (hN : 2 ≤ N)
    (x y : CubicTorus d N) :
    DependsOn (cubicTorusEdgeFinset d N hN) (torusConnectionEvent d N x y) := by
  intro ω η htrace
  have hall : ω = η := by
    ext e
    apply htrace e
    unfold cubicTorusEdgeFinset
    simp
  subst η
  rfl

theorem measurableSet_torusConnectionEvent (d N : ℕ) (hN : 2 ≤ N)
    (x y : CubicTorus d N) :
    MeasurableSet (torusConnectionEvent d N x y) := by
  exact (dependsOn_torusConnectionEvent d N hN x y).measurableSet

theorem measurableSet_torusGhostHitEvent (d N : ℕ) (hN : 2 ≤ N) :
    MeasurableSet (torusGhostHitEvent d N) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  rw [torusGhostHitEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro y
  exact ((measurableSet_torusConnectionEvent d N hN (cubicTorusOrigin d N) y).preimage
    measurable_fst).inter ((measurableSet_mem y).preimage measurable_snd)

/-- Finite-volume ghost order parameter. -/
noncomputable def torusGhostTheta (d N : ℕ) (p γ : I) : ℝ :=
  (torusGhostMeasure d N p γ).real (torusGhostHitEvent d N)

theorem torusGhostTheta_nonneg (d N : ℕ) (p γ : I) :
    0 ≤ torusGhostTheta d N p γ := measureReal_nonneg

theorem torusGhostTheta_le_one (d N : ℕ) (p γ : I) :
    torusGhostTheta d N p γ ≤ 1 := by
  calc
    torusGhostTheta d N p γ ≤ (torusGhostMeasure d N p γ).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := probReal_univ

end Percolation
