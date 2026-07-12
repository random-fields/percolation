import Percolation.Bernoulli.CouplingSymmetry
import Percolation.Critical.RegionSymmetry

/-!
# Symmetries for oriented dynamic steering

The reference restart theorem exits through a positive coordinate face at the origin.  A sign
flip in the chosen coordinate followed by translation transports it to either signed face at an
arbitrary block center, while `CouplingSymmetry` preserves the common-uniform probability law.
-/

namespace Percolation

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

/-- Oriented copy of the corresponding reference closed-boundary history. -/
def orientedBoundaryClosedHistoryEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (R : Finset (Cubic d)) (n : ℕ) (beta : CubicEdge d → I) :
    Set (CubicEdge d → ℝ) :=
  orientedCouplingTransportEvent center a
    (boundaryClosedHistoryEvent (cubicRegionBoundaryEdgesWithinBox d R n) beta)

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

end Percolation
