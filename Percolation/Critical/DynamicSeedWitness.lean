import Percolation.Critical.DynamicFramedRestart

/-!
# Finite deterministic seed witnesses for dynamic restarts

A successful restart supplies an existential boundary point and seed center.  The next block,
however, must be a deterministic function of the revealed labels: its center and transverse
steering signs are computed from that seed.  This file packages all possible witnesses as a
finite type and selects one canonical (classical but fixed) witness.  Recording this value in a
later reveal cell is therefore finite data, not an unresolved theorem parameter.
-/

namespace Percolation

open scoped unitInterval

/-- A boundary point in the reference target quadrant. -/
abbrev RestartBoundaryPoint (d : ℕ) (i : Fin d) (n : ℕ) :=
  {y : Cubic d // y ∈ seededBoundaryQuadrant d i n}

/-- A seed center in the finite ambient box containing every possible target seed. -/
abbrev RestartSeedCenter (d m n : ℕ) :=
  {c : Cubic d // c ∈ seededBoundaryPossibleCenters d m n}

noncomputable instance restartBoundaryPointFintype
    (d : ℕ) (i : Fin d) (n : ℕ) : Fintype (RestartBoundaryPoint d i n) :=
  Fintype.ofFinite _

noncomputable instance restartSeedCenterFintype
    (d m n : ℕ) : Fintype (RestartSeedCenter d m n) :=
  Fintype.ofFinite _

/-- Finite data naming both the boundary contact and the seed it enters. -/
structure RestartSeedWitnessIndex (d : ℕ) (i : Fin d) (m n : ℕ) where
  boundaryPoint : RestartBoundaryPoint d i n
  seedCenter : RestartSeedCenter d m n

noncomputable instance restartSeedWitnessIndexDecidableEq
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    DecidableEq (RestartSeedWitnessIndex d i m n) :=
  Classical.decEq _

def restartSeedWitnessIndexEquiv (d : ℕ) (i : Fin d) (m n : ℕ) :
    RestartSeedWitnessIndex d i m n ≃
      RestartBoundaryPoint d i n × RestartSeedCenter d m n where
  toFun W := (W.boundaryPoint, W.seedCenter)
  invFun W := ⟨W.1, W.2⟩
  left_inv W := by cases W; rfl
  right_inv W := by cases W; rfl

noncomputable instance restartSeedWitnessIndexFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (RestartSeedWitnessIndex d i m n) :=
  Fintype.ofEquiv
    (RestartBoundaryPoint d i n × RestartSeedCenter d m n)
    (restartSeedWitnessIndexEquiv d i m n).symm

namespace RestartSeedWitnessIndex

variable {d m n : ℕ} {i : Fin d}

/-- The named center is an actual open seed entered by the named boundary edge. -/
def IsRealized (W : RestartSeedWitnessIndex d i m n)
    (omega : EdgeConfiguration d) : Prop :=
  cubicStepEdge W.boundaryPoint.1 (i, true) ∈ omega ∧
    cubicStepFrom W.boundaryPoint.1 (i, true) ∈
      cubicMetricBox d W.seedCenter.1 m ∧
    SeedBoxWithinBoundaryLayer d i m n W.seedCenter.1 ∧
    omega ∈ cubicSeedEvent d W.seedCenter.1 m

/-- Realization is monotone in the edge configuration; its geometric fields are unchanged and
only the entry bond and internal seed bonds need to be preserved. -/
theorem IsRealized.mono
    {W : RestartSeedWitnessIndex d i m n} {omega eta : EdgeConfiguration d}
    (hsub : omega ⊆ eta) (hW : W.IsRealized omega) : W.IsRealized eta := by
  exact ⟨hsub hW.1, hW.2.1, hW.2.2.1,
    isIncreasingEvent_cubicSeedEvent d W.seedCenter.1 m hsub hW.2.2.2⟩

/-- A realized target seed connects its boundary contact to its named center.  The first edge
enters the seed, and a coordinate-monotone walk inside the seed box finishes the connection. -/
theorem IsRealized.mem_connectionEvent_boundaryPoint_seedCenter
    {W : RestartSeedWitnessIndex d i m n} {omega : EdgeConfiguration d}
    (hW : W.IsRealized omega) :
    omega ∈ connectionEvent d W.boundaryPoint.1 W.seedCenter.1 := by
  let entry := cubicStepFrom W.boundaryPoint.1 (i, true)
  obtain ⟨q, hqBetween⟩ := exists_cubicWalk_support_between d entry W.seedCenter.1
  have hcenterBox : W.seedCenter.1 ∈ cubicMetricBox d W.seedCenter.1 m := by
    rw [mem_cubicMetricBox]
    intro j
    omega
  have hqBox : ∀ z ∈ q.support, z ∈ cubicMetricBox d W.seedCenter.1 m := by
    intro z hz
    have hzBetween := hqBetween z hz
    have hentryBox := hW.2.1
    rw [mem_cubicMetricBox] at hentryBox hcenterBox ⊢
    intro j
    rcases hzBetween j with hzj | hzj
    · exact ⟨(hentryBox j).1.trans hzj.1, hzj.2.trans (hcenterBox j).2⟩
    · exact ⟨(hcenterBox j).1.trans hzj.1, hzj.2.trans (hentryBox j).2⟩
  have hqEdges : walkEdgeFinset q ⊆ cubicBoxEdges d W.seedCenter.1 m :=
    walkEdgeFinset_subset_cubicBoxEdges_of_support q hqBox
  have hqOpen : walkIsOpen omega q := by
    intro e he
    exact hW.2.2.2 (hqEdges ((mem_walkEdgeFinset_iff q _).mpr he))
  have hadj : (cubicGraph d).Adj W.boundaryPoint.1 entry :=
    cubicGraph_adj_stepFrom W.boundaryPoint.1 (i, true)
  let step : (cubicGraph d).Walk W.boundaryPoint.1 entry :=
    SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
  have hstepOpen : walkIsOpen omega step := by
    intro e he
    have heq :
        (⟨e, step.edges_subset_edgeSet he⟩ : CubicEdge d) =
          cubicStepEdge W.boundaryPoint.1 (i, true) := by
      apply Subtype.ext
      simpa [step, cubicStepEdge] using he
    simpa [heq] using hW.1
  exact ⟨step.append q, walkIsOpen_append hstepOpen hqOpen⟩

theorem isSeededBoundaryPoint_of_isRealized
    (W : RestartSeedWitnessIndex d i m n) {omega : EdgeConfiguration d}
    (hW : W.IsRealized omega) :
    IsSeededBoundaryPoint d i m n omega W.boundaryPoint.1 := by
  exact ⟨W.boundaryPoint.2, hW.1, W.seedCenter.1,
    hW.2.1, hW.2.2.1, hW.2.2.2⟩

/-- Every seeded target admits finite witness data naming one of its seed centers. -/
theorem exists_of_isSeededBoundaryPoint
    {omega : EdgeConfiguration d} {y : Cubic d}
    (hy : IsSeededBoundaryPoint d i m n omega y) :
    ∃ W : RestartSeedWitnessIndex d i m n,
      W.boundaryPoint.1 = y ∧ W.IsRealized omega := by
  rcases hy with ⟨hyQuadrant, hyEdge, c, hyc, hcLayer, hcSeed⟩
  let W : RestartSeedWitnessIndex d i m n :=
    { boundaryPoint := ⟨y, hyQuadrant⟩
      seedCenter := ⟨c,
        seedCenter_mem_seededBoundaryPossibleCenters hyQuadrant hyc⟩ }
  exact ⟨W, rfl, hyEdge, hyc, hcLayer, hcSeed⟩

end RestartSeedWitnessIndex

namespace RestartSeedWitnessIndex

/-- A named witness for the actual mixed-threshold restart, before any later uniform-density
completion is applied.  The named seed is open in the cleared `p`-configuration, its boundary
point is joined to the outside endpoint of a region exit using only exterior box edges, and
that exit label lies in its individual sprinkling interval. -/
def IsMixedRestartWitness
    {d m n : ℕ} {i : Fin d} (W : RestartSeedWitnessIndex d i m n)
    (R : Finset (Cubic d)) (p : I) (beta : CubicEdge d → I) (delta : ℝ)
    (X : CubicEdge d → ℝ) : Prop :=
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let omega := clearedThreshold E p X
  W.IsRealized omega ∧
    ∃ e ∈ E,
      omega ∈ connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) W.boundaryPoint.1 ∧
      X e < (beta e : ℝ) + delta

/-- Forgetting the cleared-boundary restriction of a mixed witness leaves an ordinary seed
realized at the background density. -/
theorem isRealized_thresholdConfiguration_of_isMixedRestartWitness
    {d m n : ℕ} {i : Fin d} {W : RestartSeedWitnessIndex d i m n}
    {R : Finset (Cubic d)} {p : I} {beta : CubicEdge d → I}
    {delta : ℝ} {X : CubicEdge d → ℝ}
    (hW : W.IsMixedRestartWitness R p beta delta X) :
    W.IsRealized (thresholdConfiguration p X) := by
  rcases hW.1 with ⟨houtward, hentry, hgeom, hseed⟩
  refine ⟨houtward.1, hentry, hgeom, ?_⟩
  intro e he
  exact (hseed he).1

/-- The particular mixed witness retained by the runtime, rather than merely some witness of
the same successful event, is connected to the inlet seed box at every final density dominating
both the background and accumulated boundary thresholds.  This witness-preserving form is what
allows the deterministic runtime to concatenate successive restart paths. -/
theorem exists_inlet_connection_to_boundaryPoint_of_isMixedRestartWitness
    {d m n : ℕ} {i : Fin d} {W : RestartSeedWitnessIndex d i m n}
    {X : CubicEdge d → ℝ} {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hW : W.IsMixedRestartWitness
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n)
      p beta delta X)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (restartExploredRegion d (heterogeneousThresholdConfiguration beta X) m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ)) :
    ∃ z ∈ cubicMetricBox d cubicOrigin m,
      thresholdConfiguration pFinal X ∈
        connectionEventIn d (cubicBoxEdges d cubicOrigin n) z W.boundaryPoint.1 := by
  let omegaBeta : EdgeConfiguration d := heterogeneousThresholdConfiguration beta X
  let omegaFinal : EdgeConfiguration d := thresholdConfiguration pFinal X
  let R := restartExploredRegion d omegaBeta m n
  have hbetaSub : omegaBeta ⊆ omegaFinal := by
    intro e he
    change X e < (beta e : ℝ) at he
    change X e < (pFinal : ℝ)
    exact he.trans_le (hbetaFinal e)
  have hclearedSub : clearedThreshold
      (cubicRegionBoundaryEdgesWithinBox d R n) p X ⊆ omegaFinal := by
    intro e he
    change X e < (p : ℝ) ∧
      e ∉ cubicRegionBoundaryEdgesWithinBox d R n at he
    change X e < (pFinal : ℝ)
    exact he.1.trans_le hpFinal
  rcases hW.2 with ⟨e, heBoundary, houtside, heIncrement⟩
  let inside := cubicRegionBoundaryInsideEndpoint R e
  let outside := cubicRegionBoundaryOutsideEndpoint R e
  have heBoundaryR : e ∈ cubicRegionBoundaryEdgesWithinBox d R n := by
    simpa [R, omegaBeta] using heBoundary
  have houtsideR : clearedThreshold (cubicRegionBoundaryEdgesWithinBox d R n) p X ∈
      connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
        (cubicRegionBoundaryOutsideEndpoint R e) W.boundaryPoint.1 := by
    simpa [R, omegaBeta] using houtside
  have hinsideR : inside ∈ R := cubicRegionBoundaryInsideEndpoint_mem heBoundaryR
  obtain ⟨hinsideBox, z, hzSeed, hzinsideReach⟩ :=
    mem_restartExploredRegion_iff.mp hinsideR
  have hzinsideBeta : omegaBeta ∈
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) z inside :=
    mem_connectionEventIn_of_finiteBoxOpenGraph_reachable hzinsideReach
  have hzinsideFinal : omegaFinal ∈
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) z inside :=
    isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin n) z inside
      hbetaSub hzinsideBeta
  have houtsideEdge : outside ∈ (e : Sym2 (Cubic d)) := by
    rw [← cubicRegionBoundaryEndpoints_edge heBoundaryR]
    simp [outside]
  have houtsideBox : outside ∈ cubicMetricBox d cubicOrigin n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundaryR).1 houtsideEdge
  have hadj : (cubicGraph d).Adj inside outside := by
    rw [← (cubicGraph d).mem_edgeSet, cubicRegionBoundaryEndpoints_edge heBoundaryR]
    exact e.2
  have hedgeOpen :
      (⟨s(inside, outside), (cubicGraph d).mem_edgeSet.mpr hadj⟩ : CubicEdge d) ∈
        omegaFinal := by
    have hedgeEq :
        (⟨s(inside, outside), (cubicGraph d).mem_edgeSet.mpr hadj⟩ : CubicEdge d) = e := by
      apply Subtype.ext
      exact cubicRegionBoundaryEndpoints_edge heBoundaryR
    rw [hedgeEq]
    change X e < (pFinal : ℝ)
    exact heIncrement.trans_le (hboundaryFinal e heBoundary)
  have hzoutsideFinal : omegaFinal ∈
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) z outside :=
    mem_connectionEventIn_of_mem_of_adj hzinsideFinal hinsideBox houtsideBox hadj hedgeOpen
  have houtsideFinal : omegaFinal ∈
      connectionEventIn d (cubicRegionExteriorEdgesWithinBox d R n)
        outside W.boundaryPoint.1 :=
    isIncreasingEvent_connectionEventIn d
      (cubicRegionExteriorEdgesWithinBox d R n) outside W.boundaryPoint.1
      hclearedSub (by simpa [outside] using houtsideR)
  rcases hzoutsideFinal with ⟨q, hqOpen, hqBox⟩
  rcases houtsideFinal with ⟨w, hwOpen, hwExterior⟩
  refine ⟨z, hzSeed, q.append w, walkIsOpen_append hqOpen hwOpen, ?_⟩
  intro f hf
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append, List.mem_append] at hf
  rcases hf with hf | hf
  · exact hqBox ((mem_walkEdgeFinset_iff q f).mpr hf)
  · exact (mem_cubicRegionExteriorEdgesWithinBox_iff.mp
      (hwExterior ((mem_walkEdgeFinset_iff w f).mpr hf))).1

end RestartSeedWitnessIndex

/-- Finite table of the seeds reached by the literal heterogeneous restart.  Unlike the older
uniform-density table, this records the very seed whose last-exit certificate caused the
source edge exploration to succeed. -/
noncomputable def mixedRestartSeedWitnesses
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) (X : CubicEdge d → ℝ) :
    Finset (RestartSeedWitnessIndex d i m n) := by
  classical
  exact Finset.univ.filter fun W ↦
    W.IsMixedRestartWitness R p beta delta X

@[simp]
theorem mem_mixedRestartSeedWitnesses_iff
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X : CubicEdge d → ℝ}
    {W : RestartSeedWitnessIndex d i m n} :
    W ∈ mixedRestartSeedWitnesses d i m n R p beta delta X ↔
      W.IsMixedRestartWitness R p beta delta X := by
  classical
  simp [mixedRestartSeedWitnesses]

/-- A mixed-threshold restart succeeds exactly when its finite table contains a named reached
seed.  This is the witness-sensitive replacement for selecting a possibly new seed only after
raising every edge to a later final density. -/
theorem mem_sprinkledRestartEvent_iff_exists_mixedRestartSeedWitness
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X : CubicEdge d → ℝ} :
    X ∈ sprinkledRestartEvent d i m n R p beta delta ↔
      ∃ W : RestartSeedWitnessIndex d i m n,
        W ∈ mixedRestartSeedWitnesses d i m n R p beta delta X := by
  classical
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let omega := clearedThreshold E p X
  constructor
  · rintro ⟨e, heAvailable, heIncrement⟩
    change e ∈ seededRegionAvailableExitEdges d i m n R omega at heAvailable
    rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff] at heAvailable
    obtain ⟨heBoundary, y, hySeed, hconnection⟩ := heAvailable
    obtain ⟨W, hWy, hW⟩ := RestartSeedWitnessIndex.exists_of_isSeededBoundaryPoint
      (mem_seededBoundaryPointFinset_iff.mp hySeed)
    refine ⟨W, mem_mixedRestartSeedWitnesses_iff.mpr ⟨hW, e, heBoundary, ?_, heIncrement⟩⟩
    simpa [hWy] using hconnection
  · rintro ⟨W, hW⟩
    rw [mem_mixedRestartSeedWitnesses_iff] at hW
    rcases hW with ⟨hrealized, e, heBoundary, hconnection, heIncrement⟩
    refine ⟨e, ?_, heIncrement⟩
    change e ∈ seededRegionAvailableExitEdges d i m n R omega
    rw [seededRegionAvailableExitEdges, mem_regionAvailableExitEdges_iff]
    refine ⟨heBoundary, W.boundaryPoint.1, ?_, hconnection⟩
    exact mem_seededBoundaryPointFinset_iff.mpr
      (RestartSeedWitnessIndex.isSeededBoundaryPoint_of_isRealized W hrealized)

theorem mixedRestartSeedWitnesses_nonempty_iff
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X : CubicEdge d → ℝ} :
    (mixedRestartSeedWitnesses d i m n R p beta delta X).Nonempty ↔
      X ∈ sprinkledRestartEvent d i m n R p beta delta := by
  constructor
  · rintro ⟨W, hW⟩
    exact mem_sprinkledRestartEvent_iff_exists_mixedRestartSeedWitness.mpr ⟨W, hW⟩
  · intro hX
    obtain ⟨W, hW⟩ :=
      mem_sprinkledRestartEvent_iff_exists_mixedRestartSeedWitness.mp hX
    exact ⟨W, hW⟩

/-- Deterministically select one seed that was actually reached by the mixed-threshold
restart. -/
noncomputable def selectedMixedRestartSeedWitness
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) (X : CubicEdge d → ℝ) :
    Option (RestartSeedWitnessIndex d i m n) :=
  if h : (mixedRestartSeedWitnesses d i m n R p beta delta X).Nonempty then
    some h.choose
  else none

theorem selectedMixedRestartSeedWitness_eq_some_of_success
    {d m n : ℕ} {i : Fin d} {R : Finset (Cubic d)} {p : I}
    {beta : CubicEdge d → I} {delta : ℝ} {X : CubicEdge d → ℝ}
    (hX : X ∈ sprinkledRestartEvent d i m n R p beta delta) :
    ∃ W : RestartSeedWitnessIndex d i m n,
      selectedMixedRestartSeedWitness d i m n R p beta delta X = some W ∧
        W.IsMixedRestartWitness R p beta delta X := by
  classical
  have hne : (mixedRestartSeedWitnesses d i m n R p beta delta X).Nonempty :=
    mixedRestartSeedWitnesses_nonempty_iff.mpr hX
  rw [selectedMixedRestartSeedWitness, dif_pos hne]
  exact ⟨hne.choose, rfl, mem_mixedRestartSeedWitnesses_iff.mp hne.choose_spec⟩

/-- Finite set of realized target seeds that are connected to the inlet seed box. -/
noncomputable def restartConnectedSeedWitnesses
    (d : ℕ) (i : Fin d) (m n : ℕ) (omega : EdgeConfiguration d) :
    Finset (RestartSeedWitnessIndex d i m n) := by
  classical
  exact Finset.univ.filter fun W ↦
      W.IsRealized omega ∧
        ∃ z ∈ cubicMetricBox d cubicOrigin m,
          omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n)
            z W.boundaryPoint.1

@[simp]
theorem mem_restartConnectedSeedWitnesses_iff
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d}
    {W : RestartSeedWitnessIndex d i m n} :
    W ∈ restartConnectedSeedWitnesses d i m n omega ↔
      W.IsRealized omega ∧
        ∃ z ∈ cubicMetricBox d cubicOrigin m,
          omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n)
            z W.boundaryPoint.1 := by
  classical
  simp [restartConnectedSeedWitnesses]

theorem restartConnectedSeedWitnesses_nonempty_of_inlet_connection
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d}
    (h : ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d i m n omega,
        omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) z y) :
    (restartConnectedSeedWitnesses d i m n omega).Nonempty := by
  rcases h with ⟨z, hz, y, hy, hzy⟩
  obtain ⟨W, hWy, hW⟩ :=
    RestartSeedWitnessIndex.exists_of_isSeededBoundaryPoint
      (mem_seededBoundaryPointFinset_iff.mp hy)
  refine ⟨W, mem_restartConnectedSeedWitnesses_iff.mpr ⟨hW, ?_⟩⟩
  exact ⟨z, hz, by simpa [hWy] using hzy⟩

/-- The full finite witness table is decided by the same support as the original seeded
connection event.  In particular, retaining the chosen seed does not enlarge a restart's label
budget. -/
theorem restartConnectedSeedWitnesses_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seedConnectionSupport d i m n,
      (e ∈ omega ↔ e ∈ eta)) :
    restartConnectedSeedWitnesses d i m n omega =
      restartConnectedSeedWitnesses d i m n eta := by
  classical
  ext W
  rw [mem_restartConnectedSeedWitnesses_iff,
    mem_restartConnectedSeedWitnesses_iff]
  have hedgeSupport :
      cubicStepEdge W.boundaryPoint.1 (i, true) ∈
        seedConnectionSupport d i m n := by
    rw [seedConnectionSupport]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨W.boundaryPoint.1, W.boundaryPoint.2, rfl⟩
  have hrealized : W.IsRealized omega ↔ W.IsRealized eta := by
    constructor
    · rintro ⟨hedge, hentry, hcLayer, hcSeed⟩
      refine ⟨(hagree _ hedgeSupport).mp hedge, hentry, hcLayer, ?_⟩
      intro e he
      apply (hagree e ?_).mp (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨W.seedCenter.1,
        mem_seededBoundaryAdmissibleCenters_iff.mpr
          ⟨W.seedCenter.2, hcLayer⟩, he⟩
    · rintro ⟨hedge, hentry, hcLayer, hcSeed⟩
      refine ⟨(hagree _ hedgeSupport).mpr hedge, hentry, hcLayer, ?_⟩
      intro e he
      apply (hagree e ?_).mpr (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨W.seedCenter.1,
        mem_seededBoundaryAdmissibleCenters_iff.mpr
          ⟨W.seedCenter.2, hcLayer⟩, he⟩
  have hconnection : ∀ z : Cubic d,
      (omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n)
          z W.boundaryPoint.1 ↔
        eta ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n)
          z W.boundaryPoint.1) := by
    intro z
    apply dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n)
      z W.boundaryPoint.1
    intro e he
    exact hagree e (cubicBoxEdges_subset_seedConnectionSupport d i m n he)
  constructor
  · rintro ⟨hW, z, hz, hzy⟩
    exact ⟨hrealized.mp hW, z, hz, (hconnection z).mp hzy⟩
  · rintro ⟨hW, z, hz, hzy⟩
    exact ⟨hrealized.mpr hW, z, hz, (hconnection z).mpr hzy⟩

/-- Deterministic finite-valued witness selection.  `none` is reserved for configurations in
which no inlet-to-target restart succeeds. -/
noncomputable def selectedRestartSeedWitness
    (d : ℕ) (i : Fin d) (m n : ℕ) (omega : EdgeConfiguration d) :
    Option (RestartSeedWitnessIndex d i m n) :=
  if h : (restartConnectedSeedWitnesses d i m n omega).Nonempty then
    some h.choose
  else none

theorem selectedRestartSeedWitness_congr_of_eqOn_seedConnectionSupport
    {d m n : ℕ} {i : Fin d} {omega eta : EdgeConfiguration d}
    (hagree : ∀ e ∈ seedConnectionSupport d i m n,
      (e ∈ omega ↔ e ∈ eta)) :
    selectedRestartSeedWitness d i m n omega =
      selectedRestartSeedWitness d i m n eta := by
  rw [selectedRestartSeedWitness, selectedRestartSeedWitness,
    restartConnectedSeedWitnesses_congr_of_eqOn_seedConnectionSupport hagree]

/-- Every exact selected-witness fiber is a cylinder on the original restart support. -/
theorem dependsOn_selectedRestartSeedWitnessFiber
    (d : ℕ) (i : Fin d) (m n : ℕ)
    (value : Option (RestartSeedWitnessIndex d i m n)) :
    DependsOn (seedConnectionSupport d i m n)
      {omega : EdgeConfiguration d |
        selectedRestartSeedWitness d i m n omega = value} := by
  intro omega eta hagree
  change (selectedRestartSeedWitness d i m n omega = value ↔
    selectedRestartSeedWitness d i m n eta = value)
  rw [selectedRestartSeedWitness_congr_of_eqOn_seedConnectionSupport hagree]

theorem selectedRestartSeedWitness_eq_some_of_nonempty
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d}
    (h : (restartConnectedSeedWitnesses d i m n omega).Nonempty) :
    ∃ W : RestartSeedWitnessIndex d i m n,
      selectedRestartSeedWitness d i m n omega = some W ∧
        W ∈ restartConnectedSeedWitnesses d i m n omega := by
  classical
  rw [selectedRestartSeedWitness, dif_pos h]
  exact ⟨h.choose, rfl, h.choose_spec⟩

theorem selectedRestartSeedWitness_eq_some_of_inlet_connection
    {d m n : ℕ} {i : Fin d} {omega : EdgeConfiguration d}
    (h : ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d i m n omega,
        omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) z y) :
    ∃ W : RestartSeedWitnessIndex d i m n,
      selectedRestartSeedWitness d i m n omega = some W ∧
        W ∈ restartConnectedSeedWitnesses d i m n omega :=
  selectedRestartSeedWitness_eq_some_of_nonempty
    (restartConnectedSeedWitnesses_nonempty_of_inlet_connection h)

/-- Reference-coordinate final configuration read through a full physical restart frame. -/
def framedReferenceThresholdConfiguration {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (p : I) (X : CubicEdge d → ℝ) : EdgeConfiguration d :=
  thresholdConfiguration p
    (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X)

/-- Explored reference region at the heterogeneous thresholds of a full-frame query. -/
noncomputable def framedReferenceRestartExploredRegion {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) (transverseFlip : Fin d → Bool)
    (beta : CubicEdge d → I) (X : CubicEdge d → ℝ) (m n : ℕ) :
    Finset (Cubic d) :=
  restartExploredRegion d
    (heterogeneousThresholdConfiguration beta
      (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a transverseFlip) X))
    m n

/-- Once the reference-coordinate inlet connection is known, deterministic witness selection
produces a concrete next seed and transports its connection to physical coordinates.  Keeping
this theorem separate from the probabilistic restart certificate avoids coupling the finite
selector to the long list of threshold hypotheses; callers compose it with
`exists_framedInletSeed_connectionToSeededTarget_of_sprinkledRestart`. -/
theorem exists_selectedFramedRestartSeed_of_inletConnection
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (pFinal : I) (X : CubicEdge d → ℝ)
    (hconnection : ∃ z ∈ cubicMetricBox d cubicOrigin m,
      ∃ y ∈ seededBoundaryPointFinset d a.1 m n
          (framedReferenceThresholdConfiguration center a transverseFlip pFinal X),
        framedReferenceThresholdConfiguration center a transverseFlip pFinal X ∈
          connectionEventIn d (cubicBoxEdges d cubicOrigin n) z y) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      selectedRestartSeedWitness d a.1 m n
          (framedReferenceThresholdConfiguration center a transverseFlip pFinal X) = some W ∧
      W.IsRealized
        (framedReferenceThresholdConfiguration center a transverseFlip pFinal X) ∧
      ∃ z ∈ cubicMetricBox d cubicOrigin m,
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d center n)
            (cubicRestartFrameIso center a transverseFlip z)
            (cubicRestartFrameIso center a transverseFlip W.boundaryPoint.1) := by
  let F := cubicRestartFrameIso center a transverseFlip
  let omegaRef : EdgeConfiguration d :=
    framedReferenceThresholdConfiguration center a transverseFlip pFinal X
  obtain ⟨W, hselected, hWmem⟩ :=
    selectedRestartSeedWitness_eq_some_of_inlet_connection
      (omega := omegaRef) hconnection
  have hW := mem_restartConnectedSeedWitnesses_iff.mp hWmem
  rcases hW.2 with ⟨z', hz', hz'W⟩
  refine ⟨W, hselected, hW.1, z', hz', ?_⟩
  simpa [F, cubicRestartFrameIso_image_cubicBoxEdges_eq] using
    thresholdConfiguration_mem_framedConnectionEventIn
      center a transverseFlip pFinal X (cubicBoxEdges d cubicOrigin n)
        z' W.boundaryPoint.1 hz'W

/-- Source-facing composition: every successful full-frame sprinkled restart selects a concrete
next seed, and that seed is connected to the inlet in the final physical configuration. -/
theorem exists_selectedFramedRestartSeed_of_sprinkledRestart
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) {X : CubicEdge d → ℝ}
    {p pFinal : I} {beta : CubicEdge d → I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hbetaFinal : ∀ e, (beta e : ℝ) ≤ (pFinal : ℝ))
    (hboundaryFinal : ∀ e ∈ cubicRegionBoundaryEdgesWithinBox d
      (framedReferenceRestartExploredRegion center a transverseFlip beta X m n) n,
      (beta e : ℝ) + delta ≤ (pFinal : ℝ))
    (hAvoid : RegionAvoidsSeededBoundaryQuadrant d a.1 n
      (framedReferenceRestartExploredRegion center a transverseFlip beta X m n))
    (hsuccess : X ∈ framedSprinkledRestartEvent center a transverseFlip m n
      (framedReferenceRestartExploredRegion center a transverseFlip beta X m n)
      p beta delta) :
    ∃ W : RestartSeedWitnessIndex d a.1 m n,
      selectedRestartSeedWitness d a.1 m n
          (framedReferenceThresholdConfiguration center a transverseFlip pFinal X) = some W ∧
      W.IsRealized
        (framedReferenceThresholdConfiguration center a transverseFlip pFinal X) ∧
      ∃ z ∈ cubicMetricBox d cubicOrigin m,
        thresholdConfiguration pFinal X ∈
          connectionEventIn d (cubicBoxEdges d center n)
            (cubicRestartFrameIso center a transverseFlip z)
            (cubicRestartFrameIso center a transverseFlip W.boundaryPoint.1) := by
  have hconnection :=
    exists_framedReferenceInletSeed_connectionToSeededTarget_of_sprinkledRestart
      center a transverseFlip hpFinal hbetaFinal
      hboundaryFinal hAvoid hsuccess
  exact exists_selectedFramedRestartSeed_of_inletConnection
    center a transverseFlip pFinal X hconnection

end Percolation
