import Percolation.Bernoulli.CouplingSymmetry
import Percolation.Critical.RegionSymmetry

/-!
# Symmetries for oriented dynamic steering

The reference restart theorem exits through a positive coordinate face at the origin.  A sign
flip in the chosen coordinate followed by translation transports it to either signed face at an
arbitrary block center, while `CouplingSymmetry` preserves the common-uniform probability law.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Flip exactly the selected coordinate when the requested direction is negative. -/
def cubicDirectionOrientationFlip {d : ℕ} (a : CubicDirection d) : Fin d → Bool :=
  fun j ↦ decide (j = a.1 ∧ a.2 = false)

/-- Graph automorphism taking the origin to `center` and the reference positive `a.1` step to
the signed step `a` from `center`. -/
def cubicDirectionOrientationIso {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) :
    cubicGraph d ≃g cubicGraph d :=
  (cubicSignedCoordinateIso (cubicDirectionOrientationFlip a)).trans
    (cubicTranslationIso cubicOrigin center)

@[simp]
theorem cubicDirectionOrientationIso_apply
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (z : Cubic d) (j : Fin d) :
    cubicDirectionOrientationIso center a z j =
      (if cubicDirectionOrientationFlip a j then -z j else z j) + center j := by
  simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
    cubicSignedCoordinateEquiv, cubicTranslationIso_apply, cubicTranslate, cubicOrigin]

/-- The orientation automorphism is an exact coordinate-box isometry. -/
theorem cubicDirectionOrientationIso_mem_cubicMetricBox_iff
    {d n : ℕ} (center : Cubic d) (a : CubicDirection d) (x z : Cubic d) :
    cubicDirectionOrientationIso center a z ∈
        cubicMetricBox d (cubicDirectionOrientationIso center a x) n ↔
      z ∈ cubicMetricBox d x n := by
  rw [mem_cubicMetricBox, mem_cubicMetricBox]
  constructor <;> intro h j
  · have hj := h j
    by_cases hflip : cubicDirectionOrientationFlip a j <;>
      simp [cubicDirectionOrientationIso_apply, hflip] at hj ⊢ <;> omega
  · have hj := h j
    by_cases hflip : cubicDirectionOrientationFlip a j <;>
      simp [cubicDirectionOrientationIso_apply, hflip] at hj ⊢ <;> omega

theorem cubicDirectionOrientationIso_image_cubicMetricBox
    {d n : ℕ} (center : Cubic d) (a : CubicDirection d) (x : Cubic d) :
    cubicGraphIsoRegion (cubicDirectionOrientationIso center a)
        (cubicMetricBox d x n : Set (Cubic d)) =
      (cubicMetricBox d (cubicDirectionOrientationIso center a x) n :
        Set (Cubic d)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (cubicDirectionOrientationIso_mem_cubicMetricBox_iff center a x w).2 hw
  · intro hz
    let F := cubicDirectionOrientationIso center a
    obtain ⟨w, rfl⟩ := F.surjective z
    exact ⟨w,
      (cubicDirectionOrientationIso_mem_cubicMetricBox_iff center a x w).1 hz, rfl⟩

/-- The oriented automorphism maps the internal edge support of the origin box exactly onto the
same-radius box centered at its physical restart center. -/
theorem cubicDirectionOrientationIso_image_cubicBoxEdges_eq
    {d n : ℕ} (center : Cubic d) (a : CubicDirection d) :
    (cubicBoxEdges d cubicOrigin n).image
        (cubicDirectionOrientationIso center a).mapEdgeSet =
      cubicBoxEdges d center n := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    apply mem_cubicBoxEdges_of_endpoints
    intro z hz
    change z ∈ Sym2.map (cubicDirectionOrientationIso center a)
      (f : Sym2 (Cubic d)) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hf hw
    have himage :=
      (cubicDirectionOrientationIso_mem_cubicMetricBox_iff
        center a cubicOrigin w).2 hwBox
    simpa [cubicOrigin] using himage
  · rw [Finset.card_image_of_injective _
      (cubicDirectionOrientationIso center a).mapEdgeSet.injective]
    calc
      (cubicBoxEdges d center n).card =
          ((cubicBoxEdges d center n).image
            (cubicTranslationIso center cubicOrigin).mapEdgeSet).card := by
        rw [Finset.card_image_of_injective _
          (cubicTranslationIso center cubicOrigin).mapEdgeSet.injective]
      _ ≤ (cubicBoxEdges d cubicOrigin n).card := by
        apply Finset.card_le_card
        intro e he
        rw [Finset.mem_image] at he
        obtain ⟨f, hf, rfl⟩ := he
        exact cubicTranslation_mapEdgeSet_mem_cubicBoxEdges center cubicOrigin hf

@[simp]
theorem cubicDirectionOrientationIso_origin
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso center a cubicOrigin = center := by
  ext j
  simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
    cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
    cubicTranslate, cubicOrigin]

theorem cubicDirectionOrientationIso_positiveStep
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso center a
        (cubicStepFrom cubicOrigin (a.1, true)) =
      cubicStepFrom center a := by
  rcases a with ⟨i, positive⟩
  ext j
  by_cases hji : j = i
  · subst j
    cases positive <;>
      simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
        cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
        cubicTranslate, cubicOrigin, cubicStepFrom, cubicDirectionIncrement]
      <;> omega
  · simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
      cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
      cubicTranslate, cubicOrigin, cubicStepFrom, cubicDirectionIncrement, hji]

/-- The physical site center at a coarse vertex is the image of the reference origin. -/
theorem cubicDirectionOrientationIso_referenceSiteCenter
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso (grimmettMarstrandSiteCenter N x) a
        (grimmettMarstrandSiteCenter N cubicOrigin) =
      grimmettMarstrandSiteCenter N x := by
  rw [show grimmettMarstrandSiteCenter N cubicOrigin = cubicOrigin by
    ext j
    simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]]
  exact cubicDirectionOrientationIso_origin _ _

/-- The reference next site center `4Neᵢ` is carried to the site center indexed by the signed
coarse neighbor of `x`. -/
theorem cubicDirectionOrientationIso_referenceNextSiteCenter
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso (grimmettMarstrandSiteCenter N x) a
        (grimmettMarstrandSiteCenter N
          (cubicStepFrom cubicOrigin (a.1, true))) =
      grimmettMarstrandSiteCenter N (cubicStepFrom x a) := by
  rcases a with ⟨i, positive⟩
  ext j
  by_cases hji : j = i
  · subst j
    cases positive <;>
      simp [cubicDirectionOrientationIso_apply, cubicDirectionOrientationFlip,
        grimmettMarstrandSiteCenter, cubicScale, cubicOrigin, cubicStepFrom,
        cubicDirectionIncrement] <;> ring
  · simp [cubicDirectionOrientationIso_apply, cubicDirectionOrientationFlip,
      grimmettMarstrandSiteCenter, cubicScale, cubicOrigin, cubicStepFrom,
      cubicDirectionIncrement, hji]

/-- Oriented copy of the first-steering restart region at a coarse site `x`. -/
def orientedSteeredRestartRegion
    {d : ℕ} (N : ℕ) (x : Cubic d) (a : CubicDirection d)
    (m n : ℕ) (y : Cubic d) : Set (Cubic d) :=
  cubicGraphIsoRegion
    (cubicDirectionOrientationIso (grimmettMarstrandSiteCenter N x) a)
    (cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter a.1 m n y)
      (steeredPositiveRestartRegion d a.1 m n))

/-- Every oriented steering region is contained in the two endpoint site boxes. -/
theorem orientedSteeredRestartRegion_subset_endpointBoxes
    {d m n : ℕ} (x : Cubic d) (a : CubicDirection d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d a.1 n) :
    orientedSteeredRestartRegion (m + n + 1) x a m n y ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  rcases translated_steeredRestartRegion_subset_endpointBoxes a.1 hmn hy hw with hw | hw
  · left
    have hmem := (cubicDirectionOrientationIso_mem_cubicMetricBox_iff
      (grimmettMarstrandSiteCenter (m + n + 1) x) a
      (grimmettMarstrandSiteCenter (m + n + 1) cubicOrigin) w).2 hw
    simpa only [cubicDirectionOrientationIso_referenceSiteCenter] using hmem
  · right
    have hmem := (cubicDirectionOrientationIso_mem_cubicMetricBox_iff
      (grimmettMarstrandSiteCenter (m + n + 1) x) a
      (grimmettMarstrandSiteCenter (m + n + 1)
        (cubicStepFrom cubicOrigin (a.1, true))) w).2 hw
    simpa only [cubicDirectionOrientationIso_referenceNextSiteCenter] using hmem

/-- Transport a reference uniform-label event to a restart centered at `center` and oriented in
direction `a`. -/
def orientedCouplingTransportEvent {d : ℕ}
    (center : Cubic d) (a : CubicDirection d)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  cubicGraphIsoCouplingTransportEvent (cubicDirectionOrientationIso center a) A

theorem couplingMeasure_real_orientedTransportEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge d)).real
        (orientedCouplingTransportEvent center a A) =
      (couplingMeasure (CubicEdge d)).real A :=
  couplingMeasure_real_cubicGraphIsoTransportEvent
    (cubicDirectionOrientationIso center a) hA

theorem thresholdConfiguration_orientedCouplingReindex
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) (p : I)
    (X : CubicEdge d → ℝ) :
    thresholdConfiguration p
        (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X) =
      cubicGraphIsoConfigurationPullback (cubicDirectionOrientationIso center a)
        (thresholdConfiguration p X) :=
  thresholdConfiguration_cubicGraphIsoCouplingReindex _ p X

/-- A reference truncated connection witnessed after reindexing the uniform labels becomes the
corresponding oriented connection in the original labels. -/
theorem thresholdConfiguration_mem_orientedConnectionEventIn
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) (p : I)
    (X : CubicEdge d → ℝ) (E : Finset (CubicEdge d)) (u v : Cubic d)
    (h : thresholdConfiguration p
      (cubicGraphIsoCouplingReindex (cubicDirectionOrientationIso center a) X) ∈
        connectionEventIn d E u v) :
    thresholdConfiguration p X ∈
      connectionEventIn d
        (E.image (cubicDirectionOrientationIso center a).mapEdgeSet)
        (cubicDirectionOrientationIso center a u)
        (cubicDirectionOrientationIso center a v) := by
  rw [thresholdConfiguration_orientedCouplingReindex] at h
  exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
    (cubicDirectionOrientationIso center a) E (thresholdConfiguration p X) u v).1 h

/-- Oriented form of a concrete reference restart event. -/
def orientedSprinkledRestartEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    Set (CubicEdge d → ℝ) :=
  orientedCouplingTransportEvent center a
    (sprinkledRestartEvent d a.1 m n R p beta delta)

/-- Literal finite set of uniform-label coordinates read by an oriented restart. -/
noncomputable def orientedRestartSupport
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) (m n : ℕ)
    (R : Finset (Cubic d)) :
    Finset (CubicEdge d) :=
  (restartEventSupport d a.1 m n R).image
    (cubicDirectionOrientationIso center a).mapEdgeSet

theorem measurableSet_orientedSprinkledRestartEvent_coordSigma
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (m n : ℕ) (R : Finset (Cubic d))
    (p : I) (beta : CubicEdge d → I) (delta : ℝ) :
    MeasurableSet[coordSigma (CubicEdge d)
      (orientedRestartSupport center a m n R : Set (CubicEdge d))]
      (orientedSprinkledRestartEvent center a m n R p beta delta) := by
  apply measurableSet_cubicGraphIsoCouplingTransportEvent_coordSigma
    (cubicDirectionOrientationIso center a) (restartEventSupport d a.1 m n R)
    (measurableSet_sprinkledRestartEvent d a.1 m n R p beta delta)
  intro X Y hXY
  exact sprinkledRestartEvent_congr_of_eqOn_restartEventSupport
    (fun e he => hXY e he)

/-- Oriented copy of the corresponding reference closed-boundary history. -/
def orientedBoundaryClosedHistoryEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (n : ℕ) (beta : CubicEdge d → I) :
    Set (CubicEdge d → ℝ) :=
  orientedCouplingTransportEvent center a
    (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta)

/-- Coordinates of the transported boundary cell used by an oriented restart. -/
noncomputable def orientedBoundaryHistorySupport
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (n : ℕ) : Finset (CubicEdge d) :=
  (cubicRegionBoundaryEdgesWithinBox d R n).image
    (cubicDirectionOrientationIso center a).mapEdgeSet

theorem orientedBoundaryHistorySupport_subset_restartSupport
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) :
    orientedBoundaryHistorySupport center a R n ⊆
      orientedRestartSupport center a m n R := by
  intro e he
  rw [orientedBoundaryHistorySupport, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [orientedRestartSupport, Finset.mem_image]
  exact ⟨f,
    boundary_subset_restartEventSupport d a.1 m n R hf,
    rfl⟩

theorem measurableSet_orientedBoundaryClosedHistoryEvent_coordSigma
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (n : ℕ) (beta : CubicEdge d → I) :
    MeasurableSet[coordSigma (CubicEdge d)
      (orientedBoundaryHistorySupport center a R n : Set (CubicEdge d))]
      (orientedBoundaryClosedHistoryEvent center a R n beta) := by
  apply measurableSet_cubicGraphIsoCouplingTransportEvent_coordSigma
    (cubicDirectionOrientationIso center a)
    (cubicRegionBoundaryEdgesWithinBox d R n)
    (measurableSet_boundaryClosedHistoryEvent _ beta)
  intro X Y hXY
  exact boundaryClosedHistoryEvent_congr_of_eqOn (fun e he => hXY e he)

/-- Ratio-free restart bounds transport to every block center and signed inlet direction. -/
theorem orientedSprinkledRestart_inter_history_gt
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (p : I) (beta : CubicEdge d → I)
    (delta epsilon : ℝ)
    (h : (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta) <
      (couplingMeasure (CubicEdge d)).real
        (sprinkledRestartEvent d a.1 m n R p beta delta ∩
          boundaryClosedHistoryEvent
            (cubicRegionBoundaryEdgesWithinBox d R n) beta)) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (orientedBoundaryClosedHistoryEvent center a R n beta) <
      (couplingMeasure (CubicEdge d)).real
        (orientedSprinkledRestartEvent center a m n R p beta delta ∩
          orientedBoundaryClosedHistoryEvent center a R n beta) := by
  let G := sprinkledRestartEvent d a.1 m n R p beta delta
  let H := boundaryClosedHistoryEvent
    (cubicRegionBoundaryEdgesWithinBox d R n) beta
  have hG : MeasurableSet G :=
    measurableSet_sprinkledRestartEvent d a.1 m n R p beta delta
  have hH : MeasurableSet H :=
    measurableSet_boundaryClosedHistoryEvent _ beta
  rw [show orientedSprinkledRestartEvent center a m n R p beta delta =
      orientedCouplingTransportEvent center a G by rfl,
    show orientedBoundaryClosedHistoryEvent center a R n beta =
      orientedCouplingTransportEvent center a H by rfl]
  simp only [orientedCouplingTransportEvent]
  rw [← cubicGraphIsoCouplingTransportEvent_inter,
    couplingMeasure_real_cubicGraphIsoTransportEvent
      (cubicDirectionOrientationIso center a) hH,
    couplingMeasure_real_cubicGraphIsoTransportEvent
      (cubicDirectionOrientationIso center a) (hG.inter hH)]
  exact h

/-- A fresh oriented restart keeps its ratio-free lower bound after adjoining any earlier
history cell supported on disjoint uniform-label coordinates.  This is the exact form consumed
by an event-generated adaptive answer: the earlier cell may have zero mass. -/
theorem orientedSprinkledRestart_inter_past_history_ge
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (p : I) (beta : CubicEdge d → I)
    (delta epsilon : ℝ)
    (pastSupport : Finset (CubicEdge d)) (past : Set (CubicEdge d → ℝ))
    (hpast : MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport : Set (CubicEdge d))] past)
    (hfresh : Disjoint (pastSupport : Set (CubicEdge d))
      (orientedRestartSupport center a m n R : Set (CubicEdge d)))
    (h : (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (orientedBoundaryClosedHistoryEvent center a R n beta) <
      (couplingMeasure (CubicEdge d)).real
        (orientedSprinkledRestartEvent center a m n R p beta delta ∩
          orientedBoundaryClosedHistoryEvent center a R n beta)) :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          (past ∩ orientedBoundaryClosedHistoryEvent center a R n beta) ≤
      (couplingMeasure (CubicEdge d)).real
        (orientedSprinkledRestartEvent center a m n R p beta delta ∩
          (past ∩ orientedBoundaryClosedHistoryEvent center a R n beta)) := by
  let restartSupport := orientedRestartSupport center a m n R
  let G := orientedSprinkledRestartEvent center a m n R p beta delta
  let H := orientedBoundaryClosedHistoryEvent center a R n beta
  have hG : MeasurableSet[coordSigma (CubicEdge d)
      (restartSupport : Set (CubicEdge d))] G := by
    exact measurableSet_orientedSprinkledRestartEvent_coordSigma
      center a m n R p beta delta
  have hHsmall : MeasurableSet[coordSigma (CubicEdge d)
      (orientedBoundaryHistorySupport center a R n : Set (CubicEdge d))] H := by
    exact measurableSet_orientedBoundaryClosedHistoryEvent_coordSigma
      center a R n beta
  have hH : MeasurableSet[coordSigma (CubicEdge d)
      (restartSupport : Set (CubicEdge d))] H :=
    (coordSigma_mono fun e he =>
      orientedBoundaryHistorySupport_subset_restartSupport center a R he) H hHsmall
  have hpastH : IndepSet past H (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hpast hH
  have hpastGH : IndepSet past (G ∩ H) (couplingMeasure (CubicEdge d)) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hfresh hpast (hG.inter hH)
  exact mul_measureReal_inter_le_inter_of_indepSet hpastH hpastGH h.le

end Percolation
