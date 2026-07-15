import Percolation.Critical.DynamicInitializedProgram
import Percolation.Critical.DynamicFramedRestart

/-!
# The special root block in the Grimmett--Marstrand construction

The origin is not queried by the same `2d+1`-extension law as later coarse sites.  Grimmett first
conditions on a central seed, then asks simultaneously for one seeded branch in every signed
coordinate direction.  This file defines that literal finite event and proves the source union
bound `(1-2dε)`, its positive probability, and the exact central-seed probability under the
common uniform coupling.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Common-uniform-label event that the central box is a seed at density `p`. -/
def rootSeedLabelEvent (d m : ℕ) (p : I) : Set (CubicEdge d → ℝ) :=
  (thresholdConfiguration p) ⁻¹' cubicSeedEvent d cubicOrigin m

theorem measurableSet_rootSeedLabelEvent (d m : ℕ) (p : I) :
    MeasurableSet (rootSeedLabelEvent d m p) :=
  (measurableSet_cubicSeedEvent d cubicOrigin m).preimage
    (measurable_thresholdConfiguration p)

/-- The root seed reads exactly the internal edges of its central box. -/
theorem measurableSet_rootSeedLabelEvent_coordSigma (d m : ℕ) (p : I) :
    MeasurableSet[coordSigma (CubicEdge d)
      (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d))]
      (rootSeedLabelEvent d m p) := by
  apply measurableSet_coordSigma_of_eqOn
    (measurableSet_rootSeedLabelEvent d m p)
  intro X Y hXY
  change (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d)) ⊆
      thresholdConfiguration p X ↔
    (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d)) ⊆
      thresholdConfiguration p Y
  constructor
  · intro h e he
    have heX := h he
    simpa [thresholdConfiguration, hXY e he] using heX
  · intro h e he
    have heY := h he
    simpa [thresholdConfiguration, hXY e he] using heY

/-- Exact finite-product mass of the root seed under the common coupling. -/
theorem couplingMeasure_real_rootSeedLabelEvent (d m : ℕ) (p : I) :
    (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) =
      (p : ℝ) ^ (cubicBoxEdges d cubicOrigin m).card := by
  rw [← bernoulliBondMeasure_real_cubicSeedEvent d p cubicOrigin m]
  unfold bernoulliBondMeasure
  rw [← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_thresholdConfiguration p)
    (measurableSet_cubicSeedEvent d cubicOrigin m)]
  rfl

theorem couplingMeasure_real_rootSeedLabelEvent_pos
    (d m : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    0 < (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) := by
  rw [couplingMeasure_real_rootSeedLabelEvent]
  exact pow_pos hp _

/-- The first move uses Grimmett's reversed transverse quadrant `T*(n)`. -/
def rootBranchTransverseFlip {d : ℕ} (a : CubicDirection d) : Fin d → Bool :=
  fun j ↦ decide (j ≠ a.1)

/-- Reference data for one of the simultaneous root branches.  The boundary threshold is zero,
as in equations (7.28)--(7.29); the background density `p` is supplied when reading the event. -/
noncomputable def rootBranchQuery
    (d m : ℕ) (a : CubicDirection d) : FramedRestartQuery d where
  center := cubicOrigin
  direction := a
  transverseFlip := rootBranchTransverseFlip a
  region := cubicMetricBox d cubicOrigin m
  beta := fun _ ↦ 0

def rootBranchSuccessEvent
    (d m n : ℕ) (p : I) (delta : ℝ) (a : CubicDirection d) :
    Set (CubicEdge d → ℝ) :=
  (rootBranchQuery d m a).successEvent m n p delta

theorem measurableSet_rootBranchSuccessEvent
    (d m n : ℕ) (p : I) (delta : ℝ) (a : CubicDirection d) :
    MeasurableSet (rootBranchSuccessEvent d m n p delta a) := by
  exact (coordSigma_le _) _
    ((rootBranchQuery d m a).measurableSet_successEvent_coordSigma m n p delta)

/-- Central seed edges are part of the frozen region's internal support. -/
theorem rootSeedSupport_subset_internalEdges
    {d m n : ℕ} (hmn : m ≤ n) :
    cubicBoxEdges d cubicOrigin m ⊆
      cubicRegionInternalEdgesWithinBox d (cubicMetricBox d cubicOrigin m) n := by
  intro e he
  rw [mem_cubicRegionInternalEdgesWithinBox_iff]
  refine ⟨cubicBoxEdges_mono_radius hmn he, ?_⟩
  intro x hx
  exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges he hx

/-- Every exterior vertex neighbor of the central `m`-box lies in the `(m+1)`-box. -/
theorem cubicRegionExteriorVertexBoundary_centralBox_subset
    (d m : ℕ) :
    cubicRegionExteriorVertexBoundary d (cubicMetricBox d cubicOrigin m) ⊆
      cubicMetricBox d cubicOrigin (m + 1) := by
  classical
  intro y hy
  simp only [cubicRegionExteriorVertexBoundary, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨⟨x, hx, a, rfl⟩, _hyOutside⟩ := hy
  apply mem_cubicMetricBox_iff_lInfDist_le.mpr
  calc
    cubicLInfDist cubicOrigin (cubicStepFrom x a) ≤
        cubicLInfDist cubicOrigin x + cubicLInfDist x (cubicStepFrom x a) :=
      cubicLInfDist_triangle _ _ _
    _ ≤ m + 1 := Nat.add_le_add
      (mem_cubicMetricBox_iff_lInfDist_le.mp hx)
      (cubicLInfDist_stepFrom_le_one x a)

/-- The central root region and its exterior vertex boundary cannot meet the target face once
there is at least one untouched layer between radii `m+1` and `n`. -/
theorem regionAvoidsSeededBoundaryQuadrant_centralBox
    {d m n : ℕ} (hmn : m + 1 < n) (i : Fin d) :
    RegionAvoidsSeededBoundaryQuadrant d i n (cubicMetricBox d cubicOrigin m) := by
  rw [RegionAvoidsSeededBoundaryQuadrant, Finset.disjoint_left]
  intro x hx hxQ
  have hxBox : x ∈ cubicMetricBox d cubicOrigin (m + 1) := by
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans (by omega))
    · exact cubicRegionExteriorVertexBoundary_centralBox_subset d m hx
  have hxBound := mem_cubicMetricBox.mp hxBox i
  have hxFace := (mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hxQ).1).1
  simp [cubicOrigin] at hxBound hxFace
  omega

/-- Exact freshness of the central seed from every framed root branch. -/
theorem disjoint_rootSeedSupport_rootBranchRestartSupport
    {d m n : ℕ} (hmn : m ≤ n) (a : CubicDirection d) :
    Disjoint (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d))
      ((rootBranchQuery d m a).restartSupport m n : Set (CubicEdge d)) := by
  let F := cubicRestartFrameIso cubicOrigin a (rootBranchTransverseFlip a)
  rw [Set.disjoint_left]
  intro e heSeed heRestart
  change e ∈ framedRestartSupport cubicOrigin a (rootBranchTransverseFlip a) m n
    (cubicMetricBox d cubicOrigin m) at heRestart
  rw [framedRestartSupport, Finset.mem_image] at heRestart
  obtain ⟨f, hfRestart, hfe⟩ := heRestart
  have heImage : e ∈
      (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet := by
    rw [show (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet =
        cubicBoxEdges d cubicOrigin m by
      simpa [F] using (cubicRestartFrameIso_image_cubicBoxEdges_eq
        (n := m) cubicOrigin a (rootBranchTransverseFlip a))]
    exact heSeed
  rw [Finset.mem_image] at heImage
  obtain ⟨g, hgSeed, hge⟩ := heImage
  have hfg : f = g := F.mapEdgeSet.injective (hfe.trans hge.symm)
  subst g
  exact Set.disjoint_left.mp
    (disjoint_cubicRegionInternalEdgesWithinBox_restartEventSupport d
      (cubicMetricBox d cubicOrigin m) a.1 m n)
    (rootSeedSupport_subset_internalEdges hmn hgSeed) hfRestart

/-- A framed Lemma 7.17 estimate factors strictly through the positive central seed. -/
theorem rootBranchSuccess_inter_rootSeed_gt
    {d m n : ℕ} (hmn : m ≤ n) {p : I} (hp : 0 < (p : ℝ))
    (delta epsilon : ℝ) (a : CubicDirection d)
    (hbranch : (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          ((rootBranchQuery d m a).boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        ((rootBranchQuery d m a).successEvent m n p delta ∩
          (rootBranchQuery d m a).boundaryHistoryEvent n)) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) <
      (couplingMeasure (CubicEdge d)).real
        (rootBranchSuccessEvent d m n p delta a ∩ rootSeedLabelEvent d m p) := by
  let Q := rootBranchQuery d m a
  let seed := rootSeedLabelEvent d m p
  let G := Q.successEvent m n p delta
  let H := Q.boundaryHistoryEvent n
  let support := Q.restartSupport m n
  have hseedMeas : MeasurableSet[coordSigma (CubicEdge d)
      (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d))] seed :=
    measurableSet_rootSeedLabelEvent_coordSigma d m p
  have hG : MeasurableSet[coordSigma (CubicEdge d)
      (support : Set (CubicEdge d))] G :=
    Q.measurableSet_successEvent_coordSigma m n p delta
  have hHsmall : MeasurableSet[coordSigma (CubicEdge d)
      (framedBoundaryHistorySupport cubicOrigin a (rootBranchTransverseFlip a)
        (cubicMetricBox d cubicOrigin m) n : Set (CubicEdge d))] H :=
    measurableSet_framedBoundaryClosedHistoryEvent_coordSigma
      cubicOrigin a (rootBranchTransverseFlip a)
        (cubicMetricBox d cubicOrigin m) n (fun _ ↦ 0)
  have hH : MeasurableSet[coordSigma (CubicEdge d)
      (support : Set (CubicEdge d))] H :=
    (coordSigma_mono fun e he ↦
      framedBoundaryHistorySupport_subset_restartSupport
        cubicOrigin a (rootBranchTransverseFlip a)
          (cubicMetricBox d cubicOrigin m) he) H hHsmall
  have hfresh : Disjoint
      (cubicBoxEdges d cubicOrigin m : Set (CubicEdge d))
      (support : Set (CubicEdge d)) :=
    disjoint_rootSeedSupport_rootBranchRestartSupport hmn a
  have hseedH : IndepSet seed H (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hseedMeas hH
  have hseedGH : IndepSet seed (G ∩ H) (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hseedMeas (hG.inter hH)
  have hHmass : (couplingMeasure (CubicEdge d)).real H = 1 := by
    change (couplingMeasure (CubicEdge d)).real
        (framedBoundaryClosedHistoryEvent cubicOrigin a (rootBranchTransverseFlip a)
          (cubicMetricBox d cubicOrigin m) n (fun _ ↦ 0)) = 1
    unfold framedBoundaryClosedHistoryEvent
    rw [couplingMeasure_real_framedTransportEvent]
    · simp [couplingMeasure_real_boundaryClosedHistoryEvent]
    · exact measurableSet_boundaryClosedHistoryEvent _ _
  have hseedInterH :
      (couplingMeasure (CubicEdge d)).real (seed ∩ H) =
        (couplingMeasure (CubicEdge d)).real seed := by
    have hmass := congrArg ENNReal.toReal hseedH.measure_inter_eq_mul
    have hmassReal :
        (couplingMeasure (CubicEdge d)).real (seed ∩ H) =
          (couplingMeasure (CubicEdge d)).real seed *
            (couplingMeasure (CubicEdge d)).real H := by
      simpa [Measure.real, ENNReal.toReal_mul] using hmass
    rw [hmassReal, hHmass, mul_one]
  have hstrict := mul_measureReal_inter_lt_inter_of_indepSet
    hseedH hseedGH (couplingMeasure_real_rootSeedLabelEvent_pos d m hp) hbranch
  rw [hseedInterH] at hstrict
  exact hstrict.trans_le <| measureReal_mono (by
    intro X hX
    exact ⟨hX.1, hX.2.1⟩)

/-- The positive initialization event: the central seed and every one of the `2d` simultaneous
root branches succeed. -/
def rootInitializationEvent
    (d m n : ℕ) (p : I) (delta : ℝ) : Set (CubicEdge d → ℝ) :=
  rootSeedLabelEvent d m p ∩ ⋂ a : CubicDirection d,
    rootBranchSuccessEvent d m n p delta a

theorem measurableSet_rootInitializationEvent
    (d m n : ℕ) (p : I) (delta : ℝ) :
    MeasurableSet (rootInitializationEvent d m n p delta) := by
  exact (measurableSet_rootSeedLabelEvent d m p).inter
    (MeasurableSet.iInter fun a ↦
      measurableSet_rootBranchSuccessEvent d m n p delta a)

/-- Equation (7.30), in ratio-free form.  The individual branch estimates may be proved by
Lemma 7.17 after factoring the central seed from the fresh restart coordinates. -/
theorem rootInitialization_probability_gt
    {d m n : ℕ} [NeZero d] (p : I) (delta epsilon : ℝ)
    (hrestart : ∀ a : CubicDirection d,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) <
        (couplingMeasure (CubicEdge d)).real
          (rootBranchSuccessEvent d m n p delta a ∩ rootSeedLabelEvent d m p)) :
    (1 - 2 * d * epsilon) *
        (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) <
      (couplingMeasure (CubicEdge d)).real
        (rootInitializationEvent d m n p delta) := by
  have h := allSuccess_inter_history_gt
    (fun a : CubicDirection d ↦ rootBranchSuccessEvent d m n p delta a)
    (rootSeedLabelEvent d m p)
    (fun a ↦ measurableSet_rootBranchSuccessEvent d m n p delta a)
    (measurableSet_rootSeedLabelEvent d m p) epsilon hrestart
  have hcard : Fintype.card (CubicDirection d) = 2 * d := by
    simp [CubicDirection, Fintype.card_prod, Nat.mul_comm]
  calc
    (1 - 2 * d * epsilon) *
        (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) =
      (1 - Fintype.card (CubicDirection d) * epsilon) *
        (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) := by
      rw [hcard]
      push_cast
      rfl
    _ < (couplingMeasure (CubicEdge d)).real
        ((⋂ a : CubicDirection d, rootBranchSuccessEvent d m n p delta a) ∩
          rootSeedLabelEvent d m p) := h
    _ = (couplingMeasure (CubicEdge d)).real
        (rootInitializationEvent d m n p delta) := by
      congr 1
      ext X
      simp [rootInitializationEvent, and_comm]

/-- The simultaneous root construction has positive mass whenever its source factor is positive.
This is the outer event consumed by `InitializedFinitePartitionedRestartProgram`. -/
theorem rootInitialization_probability_pos
    {d m n : ℕ} [NeZero d] {p : I} {delta epsilon : ℝ}
    (hp : 0 < (p : ℝ)) (hfactor : 2 * d * epsilon < 1)
    (hrestart : ∀ a : CubicDirection d,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real (rootSeedLabelEvent d m p) <
        (couplingMeasure (CubicEdge d)).real
          (rootBranchSuccessEvent d m n p delta a ∩ rootSeedLabelEvent d m p)) :
    0 < (couplingMeasure (CubicEdge d)).real
      (rootInitializationEvent d m n p delta) := by
  have hseed := couplingMeasure_real_rootSeedLabelEvent_pos d m hp
  have hlower := rootInitialization_probability_gt p delta epsilon hrestart
  have hfactorPos : 0 < 1 - 2 * d * epsilon := by linarith
  exact (mul_pos hfactorPos hseed).trans hlower

/-- The literal root initialization has positive probability from the framed Lemma 7.17
estimates themselves.  This version removes the intermediate seed-conditioned branch
hypothesis: freshness of the central seed is proved by
`rootBranchSuccess_inter_rootSeed_gt`. -/
theorem rootInitialization_probability_pos_of_branchBounds
    {d m n : ℕ} [NeZero d] (hmn : m ≤ n) {p : I} (hp : 0 < (p : ℝ))
    {delta epsilon : ℝ} (hfactor : 2 * d * epsilon < 1)
    (hbranch : ∀ a : CubicDirection d,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real
            ((rootBranchQuery d m a).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((rootBranchQuery d m a).successEvent m n p delta ∩
            (rootBranchQuery d m a).boundaryHistoryEvent n)) :
    0 < (couplingMeasure (CubicEdge d)).real
      (rootInitializationEvent d m n p delta) := by
  apply rootInitialization_probability_pos hp hfactor
  intro a
  exact rootBranchSuccess_inter_rootSeed_gt hmn hp delta epsilon a (hbranch a)

/-- The unframed coordinate estimates needed at the special root region.  Naming this predicate
keeps the very general Lemma 7.17 interface out of the final finite intersection proof. -/
def RootReferenceBranchBounds
    (d m n : ℕ) (p : I) (delta epsilon : ℝ) : Prop :=
  ∀ i : Fin d,
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d
              (cubicMetricBox d cubicOrigin m) n) (fun _ ↦ 0)) <
      (couplingMeasure (CubicEdge d)).real
        (sprinkledRestartEvent d i m n (cubicMetricBox d cubicOrigin m)
            p (fun _ ↦ 0) delta ∩
          boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d
              (cubicMetricBox d cubicOrigin m) n) (fun _ ↦ 0))

/-- Specialize the reusable all-region Lemma 7.17 payload to the central root box. -/
theorem rootReferenceBranchBounds_of_uniform
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (hmnBoundary : m + 1 < n)
    (hdelta1 : delta ≤ 1)
    (h : UniformRestartBounds d m n p delta epsilon) :
    RootReferenceBranchBounds d m n p delta epsilon := by
  intro i
  exact h i (cubicMetricBox d cubicOrigin m) (fun _ ↦ 0)
    (fun _ hx ↦ hx)
    (fun x hx ↦ mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans (by omega)))
    (regionAvoidsSeededBoundaryQuadrant_centralBox hmnBoundary i)
    (by intro e he; simpa using hdelta1)

/-- Uniform Lemma 7.17 specialized to the literal central root region. -/
theorem exists_rootReferenceBranchBounds
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {delta epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ m n : ℕ, 2 * m < n ∧ m + 1 < n ∧
      RootReferenceBranchBounds d m n p delta epsilon := by
  obtain ⟨m, n, hmn, hmnBoundary, hrestart⟩ :=
    exists_uniformRestartBounds
      d hd p htheta hp0 hp1 hepsilon hdelta hdelta1
  exact ⟨m, n, hmn, hmnBoundary,
    rootReferenceBranchBounds_of_uniform hmnBoundary hdelta1 hrestart⟩

/-- Signed-frame transport of the coordinate reference estimates. -/
theorem rootBranchBounds_of_reference
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (h : RootReferenceBranchBounds d m n p delta epsilon) :
    ∀ a : CubicDirection d,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real
            ((rootBranchQuery d m a).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((rootBranchQuery d m a).successEvent m n p delta ∩
            (rootBranchQuery d m a).boundaryHistoryEvent n) := by
  intro a
  have hframed := framedSprinkledRestart_inter_history_gt
    cubicOrigin a (rootBranchTransverseFlip a)
      (cubicMetricBox d cubicOrigin m) p (fun _ ↦ 0) delta epsilon (h a.1)
  change (1 - epsilon) *
      (couplingMeasure (CubicEdge d)).real
        (framedBoundaryClosedHistoryEvent cubicOrigin a (rootBranchTransverseFlip a)
          (cubicMetricBox d cubicOrigin m) n (fun _ ↦ 0)) <
    (couplingMeasure (CubicEdge d)).real
      (framedSprinkledRestartEvent cubicOrigin a (rootBranchTransverseFlip a)
          m n (cubicMetricBox d cubicOrigin m) p (fun _ ↦ 0) delta ∩
        framedBoundaryClosedHistoryEvent cubicOrigin a (rootBranchTransverseFlip a)
          (cubicMetricBox d cubicOrigin m) n (fun _ ↦ 0))
  exact hframed

/-- Source-faithful existence of a positive root block.  The coordinate-uniform form of
Lemma 7.17 chooses one pair `m,n`; the signed steering frame supplies all `2d` simultaneous
branches, and freshness factors them through the literal central seed. -/
theorem exists_rootInitialization_probability_pos
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {delta epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hfactor : 2 * d * epsilon < 1) :
    ∃ m n : ℕ, 2 * m < n ∧ m + 1 < n ∧
      0 < (couplingMeasure (CubicEdge d)).real
        (rootInitializationEvent d m n p delta) := by
  obtain ⟨m, n, hmn, hmnBoundary, hreference⟩ :=
    exists_rootReferenceBranchBounds
      d hd p htheta hp0 hp1 hepsilon hdelta hdelta1
  refine ⟨m, n, hmn, hmnBoundary, ?_⟩
  apply rootInitialization_probability_pos_of_branchBounds (by omega) hp0 hfactor
  exact rootBranchBounds_of_reference hreference

/-- One source-consistent choice of radii, uniform restart estimates for every later admissible
region, and the positive literal root event at those same radii. -/
structure DynamicBlockRestartPackage
    (d : ℕ) (p : I) (delta epsilon : ℝ) where
  m : ℕ
  n : ℕ
  two_mul_inner_lt_outer : 2 * m < n
  boundary_gap : m + 1 < n
  uniformBounds : UniformRestartBounds d m n p delta epsilon
  rootInitialization_pos :
    0 < (couplingMeasure (CubicEdge d)).real
      (rootInitializationEvent d m n p delta)

/-- Lemmas 7.9 and 7.17 produce a complete common-radius restart package, including the special
root construction. -/
theorem exists_dynamicBlockRestartPackage
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {delta epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hfactor : 2 * d * epsilon < 1) :
    Nonempty (DynamicBlockRestartPackage d p delta epsilon) := by
  obtain ⟨m, n, hmn, hmnBoundary, huniform⟩ :=
    exists_uniformRestartBounds d hd p htheta hp0 hp1 hepsilon hdelta hdelta1
  have hreference : RootReferenceBranchBounds d m n p delta epsilon :=
    rootReferenceBranchBounds_of_uniform hmnBoundary hdelta1 huniform
  have hroot : 0 < (couplingMeasure (CubicEdge d)).real
      (rootInitializationEvent d m n p delta) := by
    apply rootInitialization_probability_pos_of_branchBounds (by omega) hp0 hfactor
    exact rootBranchBounds_of_reference hreference
  exact ⟨{
    m := m
    n := n
    two_mul_inner_lt_outer := hmn
    boundary_gap := hmnBoundary
    uniformBounds := huniform
    rootInitialization_pos := hroot }⟩

end Percolation
