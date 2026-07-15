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
  have hseed :
      (omega ∈ cubicSeedEvent d W.seedCenter.1 m ↔
        eta ∈ cubicSeedEvent d W.seedCenter.1 m) := by
    constructor <;> intro h e he
    · exact (hagree e (by
        rw [seedConnectionSupport]
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨W.seedCenter.1, W.seedCenter.2, he⟩)).mp (h he)
    · exact (hagree e (by
        rw [seedConnectionSupport]
        apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        exact ⟨W.seedCenter.1, W.seedCenter.2, he⟩)).mpr (h he)
  have hrealized : W.IsRealized omega ↔ W.IsRealized eta := by
    simp only [RestartSeedWitnessIndex.IsRealized]
    exact and_congr (hagree _ hedgeSupport)
      (and_congr Iff.rfl (and_congr Iff.rfl hseed))
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
