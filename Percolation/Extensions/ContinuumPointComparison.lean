import Percolation.Extensions.ContinuumPointProcess
import Percolation.Extensions.ContinuumSiteApproximation

/-!
# Comparing the marked Boolean model with its occupied-cube process

This file proves the deterministic implication used in (12.39) for the actual marked Poisson
sample: an infinite Boolean component projects to an infinite occupied component of `L₁`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal NNReal unitInterval

theorem continuumPoissonPointActive_count_ne_zero {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d} {a : Cubic d × ℕ}
    (ha : continuumPoissonPointActive Xi a) :
    continuumPoissonCubeCounts Xi a.1 ≠ 0 := by
  exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) ha)

/-- A walk in the fixed-index Boolean graph projects to occupied-cube reachability.  Repeated
cube indices are contracted. -/
theorem continuumPoissonWalk_projects_to_occupiedCubes
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d} {a b : Cubic d × ℕ}
    (w : (continuumPoissonAmbientGraph Xi).Walk a b)
    (ha : continuumPoissonPointActive Xi a) :
    ∃ hb : continuumPoissonPointActive Xi b,
      (continuumApproximationGraph d 1).induce
          (continuumOccupiedSites (continuumPoissonCubeCounts Xi)) |>.Reachable
        ⟨a.1, continuumPoissonPointActive_count_ne_zero ha⟩
        ⟨b.1, continuumPoissonPointActive_count_ne_zero hb⟩ := by
  induction w with
  | nil =>
      refine ⟨ha, ?_⟩
      exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v z huv w ih =>
      have hv : continuumPoissonPointActive Xi v :=
        (continuumPoissonAmbientGraph_adj.mp huv).2.2.1
      obtain ⟨hz, hvz⟩ := ih hv
      let uI : continuumOccupiedSites (continuumPoissonCubeCounts Xi) :=
        ⟨u.1, continuumPoissonPointActive_count_ne_zero ha⟩
      let vI : continuumOccupiedSites (continuumPoissonCubeCounts Xi) :=
        ⟨v.1, continuumPoissonPointActive_count_ne_zero hv⟩
      have huvCubes : u.1 = v.1 ∨ (continuumApproximationGraph d 1).Adj u.1 v.1 := by
        by_cases hcube : u.1 = v.1
        · exact Or.inl hcube
        · exact Or.inr ⟨hcube,
            continuumPoissonPoint Xi u, continuumPoissonPoint_mem_unitCube Xi u,
            continuumPoissonPoint Xi v, continuumPoissonPoint_mem_unitCube Xi v,
            (continuumPoissonAmbientGraph_adj.mp huv).2.2.2⟩
      have huvReach : ((continuumApproximationGraph d 1).induce
          (continuumOccupiedSites (continuumPoissonCubeCounts Xi))).Reachable uI vI := by
        rcases huvCubes with hcube | hadj
        · have huvI : uI = vI := Subtype.ext hcube
          rw [huvI]
        · exact (SimpleGraph.induce_adj.mpr hadj).reachable
      exact ⟨hz, huvReach.trans hvz⟩

/-- If an ambient Boolean component is infinite, its root must be active; inactive potential
marks are isolated. -/
theorem continuumPoissonPointActive_of_infiniteCluster
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d} {a : Cubic d × ℕ}
    (hinf : {b | (continuumPoissonAmbientGraph Xi).Reachable a b}.Infinite) :
    continuumPoissonPointActive Xi a := by
  by_contra ha
  apply hinf
  have hsubset : {b | (continuumPoissonAmbientGraph Xi).Reachable a b} ⊆ {a} := by
    intro b hb
    obtain ⟨w⟩ := hb
    cases w with
    | nil => simp
    | @cons u v z huv w =>
        exact (ha (continuumPoissonAmbientGraph_adj.mp huv).2.1).elim
  exact Set.finite_singleton a |>.subset hsubset

private theorem finite_reachableCube_fiber
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d} {a : Cubic d × ℕ}
    (ha : continuumPoissonPointActive Xi a)
    (z : Cubic d) :
    let C := {b | (continuumPoissonAmbientGraph Xi).Reachable a b}
    let f : C → Cubic d := fun b ↦ b.1.1
    {b : C | f b = z}.Finite := by
  dsimp only
  let C := {b | (continuumPoissonAmbientGraph Xi).Reachable a b}
  let f : C → Cubic d := fun b ↦ b.1.1
  let pairs : Finset (Cubic d × ℕ) :=
    ({z} : Finset (Cubic d)).product (Finset.range (Xi z).1)
  apply Set.Finite.of_finite_image (f := fun b : C ↦ b.1)
  · apply pairs.finite_toSet.subset
    rintro q ⟨b, hb, rfl⟩
    have hcube : b.1.1 = z := hb
    have hbActive := (continuumPoissonWalk_projects_to_occupiedCubes
      (Classical.choice b.2) ha).choose
    apply Finset.mem_product.mpr
    constructor
    · simpa using hcube
    · exact Finset.mem_range.mpr (hcube ▸ hbActive)
  · exact Subtype.val_injective.injOn

/-- Deterministic form of (12.39) at unit mesh. -/
theorem continuumApproximationPercolates_of_continuumPoissonPercolates
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (hinf : continuumPoissonPercolates Xi) :
    continuumPoissonCubeCounts Xi ∈ continuumApproximationPercolatesEvent d 1 := by
  obtain ⟨a, haInf⟩ := hinf
  have ha := continuumPoissonPointActive_of_infiniteCluster haInf
  let C := {b | (continuumPoissonAmbientGraph Xi).Reachable a b}
  let f : C → Cubic d := fun b ↦ b.1.1
  haveI : Infinite C := Set.infinite_coe_iff.mpr haInf
  have hUniv : (Set.univ : Set C).Infinite := Set.infinite_univ
  have himage : (f '' (Set.univ : Set C)).Infinite := by
    intro hfinite
    apply hUniv
    apply Set.Finite.of_finite_fibers f hfinite
    intro z hz
    simpa using finite_reachableCube_fiber ha z
  let G := continuumApproximationGraph d 1
  let eta := continuumOccupiedSites (continuumPoissonCubeCounts Xi)
  let projectToSiteOpen : G.induce eta →g siteOpenGraph G eta :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        exact siteOpenGraph_adj.mpr
          ⟨SimpleGraph.induce_adj.mp hxy, x.2, y.2⟩ }
  refine ⟨a.1, ?_⟩
  rw [siteOpenCluster_eq_reachable]
  refine himage.mono ?_
  rintro z ⟨b, _hbC, rfl⟩
  refine ⟨continuumPoissonPointActive_count_ne_zero ha, ?_⟩
  exact ((continuumPoissonWalk_projects_to_occupiedCubes
    (Classical.choice b.2) ha).choose_spec).map projectToSiteOpen

/-- Probability comparison corresponding to (12.39), for the unit-mesh marginal. -/
theorem continuumTheta_le_continuumApproximationTheta_one
    (d : ℕ) (intensity : ℝ≥0) :
    continuumTheta d intensity ≤ continuumApproximationTheta d intensity 1 := by
  calc
    continuumTheta d intensity ≤
        (continuumPoissonMeasure d intensity).real
          (continuumPoissonCubeCounts ⁻¹'
            continuumApproximationPercolatesEvent d 1) := by
      unfold continuumTheta
      exact measureReal_mono fun Xi hXi ↦
        continuumApproximationPercolates_of_continuumPoissonPercolates
          (continuumPoissonPercolates_of_mem_continuumOriginPercolatesEvent hXi)
    _ = (Measure.map continuumPoissonCubeCounts
          (continuumPoissonMeasure d intensity)).real
          (continuumApproximationPercolatesEvent d 1) := by
      rw [Measure.real, Measure.real, Measure.map_apply
        measurable_continuumPoissonCubeCounts
        (measurableSet_continuumApproximationPercolatesEvent d 1)]
    _ = continuumApproximationTheta d intensity 1 := by
      unfold continuumApproximationTheta
      rw [continuumPoissonMeasure_map_cubeCounts]

end Percolation
