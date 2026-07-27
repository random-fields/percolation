import Percolation.Critical.DynamicSteering
import Percolation.Critical.SiteExplorationDomination

/-!
# Canonical rooted site explorations

Grimmett's dynamic construction explores the vertices of an arbitrary connected region in a
fixed deterministic order.  This file instantiates the generic `SiteExploration` state machine
with the actual neighbor finsets of a locally finite graph and proves the initial connectivity
invariants required by Lemma 7.24.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Breadth-first-style deterministic exploration rooted at `root`; the globally fixed linear
order chooses the next frontier vertex.  The root is accepted initially, corresponding to
conditioning the block construction on its first seed. -/
noncomputable def rootedSiteExploration
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) : SiteExploration V where
  graph := G
  neighbors := neighbors
  mem_neighbors := mem_neighbors
  initial :=
    { occupied := {root}
      rejected := ∅
      frontier := neighbors root
      history := [(root, true)] }

theorem rootedSiteExploration_initial_wellFormed
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) :
    (rootedSiteExploration G neighbors mem_neighbors root).initial.WellFormed := by
  classical
  constructor
  · simp [rootedSiteExploration]
  · rw [Finset.disjoint_left]
    intro v hv hdecided
    have hvr : v = root := by
      simpa [rootedSiteExploration, SiteExplorationState.decided] using hdecided
    subst v
    exact (G.ne_of_adj (mem_neighbors.mp hv)) rfl

theorem rootedSiteExploration_initial_openRootedAt
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) :
    (rootedSiteExploration G neighbors mem_neighbors root).OpenRootedAt root
      (rootedSiteExploration G neighbors mem_neighbors root).initial := by
  classical
  refine ⟨by simp [rootedSiteExploration], ?_, ?_⟩
  · intro v hv
    simp [rootedSiteExploration] at hv
    subst v
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro z hz
    simpa [rootedSiteExploration] using hz
  · intro v hv
    refine ⟨root, by simp [rootedSiteExploration], ?_⟩
    exact mem_neighbors.mp (by simpa [rootedSiteExploration] using hv)

/-- Finite neighbor list of a vertex of an induced cubic region. -/
noncomputable def cubicRegionNeighborFinset
    (d : ℕ) (F : Set (Cubic d)) (x : F) : Finset F := by
  classical
  exact Finset.subtype F <|
    (Finset.univ : Finset (CubicDirection d)).image fun a ↦ cubicStepFrom x a

@[simp]
theorem mem_cubicRegionNeighborFinset_iff
    {d : ℕ} {F : Set (Cubic d)} {x y : F} :
    y ∈ cubicRegionNeighborFinset d F x ↔ (cubicRegionGraph d F).Adj x y := by
  classical
  rw [cubicRegionGraph, SimpleGraph.induce_adj,
    cubicGraph_adj_iff_exists_stepFrom]
  constructor
  · intro hy
    rw [cubicRegionNeighborFinset] at hy
    have hy' : (y : Cubic d) ∈
        (Finset.univ : Finset (CubicDirection d)).image (fun a ↦ cubicStepFrom x a) :=
      Finset.mem_subtype.mp hy
    rw [Finset.mem_image] at hy'
    obtain ⟨a, _ha, hstep⟩ := hy'
    exact ⟨a, hstep.symm⟩
  · rintro ⟨a, hstep⟩
    rw [cubicRegionNeighborFinset]
    apply Finset.mem_subtype.mpr
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, hstep.symm⟩

/-- The canonical exploration of the induced cubic graph on a region. -/
noncomputable def cubicRegionSiteExploration
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) : SiteExploration F :=
  rootedSiteExploration (cubicRegionGraph d F) (cubicRegionNeighborFinset d F)
    mem_cubicRegionNeighborFinset_iff root

theorem cubicRegionSiteExploration_initial_wellFormed
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) :
    (cubicRegionSiteExploration d F root).initial.WellFormed :=
  rootedSiteExploration_initial_wellFormed (cubicRegionGraph d F)
    (cubicRegionNeighborFinset d F) mem_cubicRegionNeighborFinset_iff root

theorem cubicRegionSiteExploration_initial_openRootedAt
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F) :
    (cubicRegionSiteExploration d F root).OpenRootedAt root
      (cubicRegionSiteExploration d F root).initial :=
  rootedSiteExploration_initial_openRootedAt (cubicRegionGraph d F)
    (cubicRegionNeighborFinset d F) mem_cubicRegionNeighborFinset_iff root

/-- Direct Lemma 7.24 adapter for the canonical exploration on `F`.  The remaining dynamic-block
proof must supply the finite-prefix lower bounds for its actual answer law. -/
theorem cubicRegionSiteExploration_infinite_probability_pos
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (μ : Measure (Set F)) [IsProbabilityMeasure μ]
    (e : ℕ ≃ F) (p : I) (hp : 0 < (p : ℝ))
    (hseq : (cubicRegionSiteExploration d F root).OccupiedLimitHasPrefixLowerBound
      μ e (p : ℝ)) :
    0 < μ.real {η : Set F |
      hasInfiniteSiteCluster (cubicRegionGraph d F)
        ((cubicRegionSiteExploration d F root).occupiedLimit (configurationAnswer η))} := by
  simpa [cubicRegionSiteExploration, rootedSiteExploration] using
    siteExploration_infinite_probability_pos
      (cubicRegionSiteExploration d F root) μ e p hp root
      (cubicRegionSiteExploration_initial_openRootedAt d F root) hseq

end Percolation
