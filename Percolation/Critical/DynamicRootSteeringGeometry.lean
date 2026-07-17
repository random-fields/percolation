import Percolation.Critical.DynamicRootRadialWitness
import Percolation.Critical.DynamicFramedStateStage
import Percolation.Critical.DynamicRootSourceState
import Percolation.Critical.DynamicSteering

/-!
# Steering geometry from the selected radial seeds

The second root phase must start from the actual seeds selected by the simultaneous radial
event.  This file proves that the opposite-quadrant restart from each such seed stays inside
the root site box and its corresponding half-way bond box.  No canonical replacement center
is introduced.
-/

namespace Percolation

open scoped unitInterval

/-- Reference positive restart region before the first transverse reversal. -/
def positiveSeededRestartRegion
    (d : ℕ) (i : Fin d) (m n : ℕ) : Set (Cubic d) :=
  (cubicMetricBox d cubicOrigin n : Set (Cubic d)) ∪
    seededBoundaryLayerRegion d i m n

/-- A reference restart reads only a uniformly bounded box.  The slightly generous radius is
useful for total-runtime displacement estimates; exact thickening containment uses the sharper
two-endpoint-box lemmas below. -/
theorem positiveSeededRestartRegion_subset_metricBox
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    positiveSeededRestartRegion d i m n ⊆
      (cubicMetricBox d cubicOrigin (n + 2 * m + 1) : Set (Cubic d)) := by
  intro z hz
  rcases hz with hz | hz
  · change z ∈ cubicMetricBox d cubicOrigin n at hz
    change z ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1)
    rw [mem_cubicMetricBox] at hz ⊢
    intro j
    have hj := hz j
    omega
  · obtain ⟨r, hr1, hr2, y, hy, rfl⟩ := hz
    change cubicTranslateAlongCoordinate y i r ∈
      cubicMetricBox d cubicOrigin (n + 2 * m + 1)
    rw [mem_cubicMetricBox]
    intro j
    have hyFace := mem_cubicBoxFace.mp
      (mem_seededBoundaryQuadrant_iff.mp hy).1
    by_cases hji : j = i
    · subst j
      have hyi := hyFace.1
      simp [cubicTranslateAlongCoordinate, cubicOrigin] at hyi ⊢
      omega
    · have hyj := hyFace.2 j hji
      simp [cubicTranslateAlongCoordinate_of_ne, hji, cubicOrigin] at hyj ⊢
      omega

/-- The convenient `2N` form, where `N=m+n+1`. -/
theorem positiveSeededRestartRegion_subset_doubleScaleBox
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    positiveSeededRestartRegion d i m n ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  have hz' := positiveSeededRestartRegion_subset_metricBox d i m n hz
  change z ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1) at hz'
  change z ∈ cubicMetricBox d cubicOrigin (2 * (m + n + 1))
  rw [mem_cubicMetricBox] at hz' ⊢
  intro j
  have hj := hz' j
  omega

/-- Every vertex incident to a coordinate read by the exact reference restart belongs to the
reference exploratory box or to its layered target. -/
theorem cubicEdgeEndpointVertices_restartEventSupport_subset_positiveSeededRestartRegion
    (d : ℕ) (i : Fin d) (m n : ℕ) (R : Finset (Cubic d)) :
    (cubicEdgeEndpointVertices (restartEventSupport d i m n R) : Set (Cubic d)) ⊆
      positiveSeededRestartRegion d i m n := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  simp only [restartEventSupport, Finset.mem_union] at he
  rcases he with (heBoundary | heExterior) | heTarget
  · left
    exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
      (mem_cubicRegionBoundaryEdgesWithinBox_iff.mp heBoundary).1 hze
  · left
    exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
      (mem_cubicRegionExteriorEdgesWithinBox_iff.mp heExterior).1 hze
  · obtain ⟨heSupport, heNotBox⟩ := Finset.mem_sdiff.mp heTarget
    rw [seedConnectionSupport] at heSupport
    simp only [Finset.mem_union] at heSupport
    rcases heSupport with (heBox | heStep) | heSeed
    · exact (heNotBox heBox).elim
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp heStep
      change z ∈ s(y, cubicStepFrom y (i, true)) at hze
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      · left
        have hyFace := mem_cubicBoxFace.mp
          (mem_seededBoundaryQuadrant_iff.mp hy).1
        have hyBox : z ∈ cubicMetricBox d cubicOrigin n := by
          rw [mem_cubicMetricBox]
          intro j
          by_cases hji : j = i
          · subst j
            simp [cubicOrigin, hyFace.1]
          · exact hyFace.2 j hji
        exact hyBox
      · right
        refine ⟨1, by omega, by omega, y, hy, ?_⟩
        ext j
        by_cases hji : j = i
        · subst j
          simp [cubicStepFrom, cubicDirectionIncrement,
            cubicTranslateAlongCoordinate]
        · simp [cubicStepFrom, cubicDirectionIncrement,
            cubicTranslateAlongCoordinate, hji]
    · rw [Finset.mem_biUnion] at heSeed
      obtain ⟨c, hc, heBox⟩ := heSeed
      right
      exact (mem_seededBoundaryAdmissibleCenters_iff.mp hc).2 z
        (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hze)

/-- Framing a reference restart transports its whole endpoint support into the framed copy of
the positive seeded restart region. -/
theorem cubicEdgeEndpointVertices_framedRestartSupport_subset_frameRegion
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) :
    (cubicEdgeEndpointVertices
        (framedRestartSupport center a transverseFlip m n R) : Set (Cubic d)) ⊆
      cubicGraphIsoRegion (cubicRestartFrameIso center a transverseFlip)
        (positiveSeededRestartRegion d a.1 m n) := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  rw [framedRestartSupport, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  change z ∈ Sym2.map (cubicRestartFrameIso center a transverseFlip)
    (f : Sym2 (Cubic d)) at hze
  rw [Sym2.mem_map] at hze
  obtain ⟨w, hw, rfl⟩ := hze
  exact ⟨w,
    cubicEdgeEndpointVertices_restartEventSupport_subset_positiveSeededRestartRegion
      d a.1 m n R (mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, hf, hw⟩), rfl⟩

/-- Every endpoint queried by a framed restart lies in the radius-`2(m+n+1)` box about its
physical frame center. -/
theorem cubicEdgeEndpointVertices_framedRestartSupport_subset_centeredBox
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) :
    (cubicEdgeEndpointVertices
        (framedRestartSupport center a transverseFlip m n R) : Set (Cubic d)) ⊆
      (cubicMetricBox d center (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ :=
    cubicEdgeEndpointVertices_framedRestartSupport_subset_frameRegion
      center a transverseFlip R hz
  have hwBox := positiveSeededRestartRegion_subset_doubleScaleBox d a.1 m n hw
  apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
    center a transverseFlip cubicOrigin w).2 at hwBox
  simpa only [cubicRestartFrameIso_origin] using hwBox

/-- Query-facing form of endpoint-support containment. -/
theorem FramedRestartQuery.endpointVertices_restartSupport_subset_frameRegion
    {d m n : ℕ} (Q : FramedRestartQuery d) :
    (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆
      cubicGraphIsoRegion
        (cubicRestartFrameIso Q.center Q.direction Q.transverseFlip)
        (positiveSeededRestartRegion d Q.direction.1 m n) := by
  exact cubicEdgeEndpointVertices_framedRestartSupport_subset_frameRegion
    Q.center Q.direction Q.transverseFlip Q.region

/-- Query-facing centered-box bound. -/
theorem FramedRestartQuery.endpointVertices_restartSupport_subset_centeredBox
    {d m n : ℕ} (Q : FramedRestartQuery d) :
    (cubicEdgeEndpointVertices (Q.restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d Q.center (2 * (m + n + 1)) : Set (Cubic d)) := by
  exact cubicEdgeEndpointVertices_framedRestartSupport_subset_centeredBox
    Q.center Q.direction Q.transverseFlip Q.region

/-- A restart whose physical center lies in a coarse half-way box reads vertices only in the
two radius-`2N` boxes at that bond's endpoints.  The proof uses the sharper transverse
radius-`n` support bound; the isotropic wide-box estimate alone would lose one block radius. -/
theorem cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_center_mem_halfwayBox
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) (x : Cubic d)
    (hcenter : center ∈ grimmettMarstrandHalfwayBox d (m + n + 1) x a) :
    (cubicEdgeEndpointVertices
        (framedRestartSupport center a transverseFlip m n R) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ :=
    cubicEdgeEndpointVertices_framedRestartSupport_subset_frameRegion
      center a transverseFlip R hz
  have hwWide := positiveSeededRestartRegion_subset_doubleScaleBox d a.1 m n hw
  rcases a with ⟨i, positive⟩
  let z := cubicRestartFrameIso center (i, positive) transverseFlip w
  by_cases hleft :
      -((2 * (m + n + 1) : ℕ) : ℤ) ≤
          z i - grimmettMarstrandSiteCenter (m + n + 1) x i ∧
        z i - grimmettMarstrandSiteCenter (m + n + 1) x i ≤
          ((2 * (m + n + 1) : ℕ) : ℤ)
  · left
    change z ∈ cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
      (2 * (m + n + 1))
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      omega
    · have hc := mem_cubicMetricBox.mp hcenter j
      have hwTrans : -(n : ℤ) ≤ w j ∧ w j ≤ (n : ℤ) := by
        rcases hw with hwBox | hwLayer
        · simpa [cubicOrigin] using mem_cubicMetricBox.mp hwBox j
        · exact seededBoundaryLayerRegion_transverse_bounds hji hwLayer
      cases positive <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
          grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
          cubicStepFrom, cubicDirectionIncrement, hji] at hc ⊢ <;>
        ring_nf at hc ⊢ <;> omega
  · right
    change z ∈ cubicMetricBox d
      (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x (i, positive)))
      (2 * (m + n + 1))
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      have hc := mem_cubicMetricBox.mp hcenter i
      have hwAxis :
          -((2 * (m + n + 1) : ℕ) : ℤ) ≤ w i ∧
            w i ≤ ((2 * (m + n + 1) : ℕ) : ℤ) := by
        simpa [cubicOrigin] using mem_cubicMetricBox.mp hwWide i
      cases positive <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
          grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
          cubicStepFrom, cubicDirectionIncrement, cubicOrigin] at hc hleft ⊢ <;>
        ring_nf at hc hleft ⊢ <;> omega
    · have hc := mem_cubicMetricBox.mp hcenter j
      have hwTrans : -(n : ℤ) ≤ w j ∧ w j ≤ (n : ℤ) := by
        rcases hw with hwBox | hwLayer
        · simpa [cubicOrigin] using mem_cubicMetricBox.mp hwBox j
        · exact seededBoundaryLayerRegion_transverse_bounds hji hwLayer
      cases positive <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
          grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
          cubicStepFrom, cubicDirectionIncrement, hji] at hc ⊢ <;>
        ring_nf at hc ⊢ <;> omega

/-- An anisotropic corridor is the exact geometric invariant needed by every non-root restart.
Along the requested signed direction the center may range from one site radius behind the
publishing center all the way to the neighboring site center; in transverse coordinates it
stays within one site radius.  The sharper reference bounds `[-n,n+2m+1]` axially and
`[-n,n]` transversely then keep the whole finite support inside the two endpoint `2N` boxes. -/
theorem cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_directionalBounds
    {d m n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d)) (x : Cubic d)
    (haxis : if a.2 then
        grimmettMarstrandSiteCenter (m + n + 1) x a.1 - (m + n + 1 : ℕ) ≤
            center a.1 ∧
          center a.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x a.1 +
              4 * (m + n + 1 : ℕ)
      else
        grimmettMarstrandSiteCenter (m + n + 1) x a.1 -
              4 * (m + n + 1 : ℕ) ≤ center a.1 ∧
          center a.1 ≤
            grimmettMarstrandSiteCenter (m + n + 1) x a.1 + (m + n + 1 : ℕ))
    (htrans : ∀ j, j ≠ a.1 →
      grimmettMarstrandSiteCenter (m + n + 1) x j - (m + n + 1 : ℕ) ≤ center j ∧
        center j ≤
          grimmettMarstrandSiteCenter (m + n + 1) x j + (m + n + 1 : ℕ)) :
    (cubicEdgeEndpointVertices
        (framedRestartSupport center a transverseFlip m n R) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ :=
    cubicEdgeEndpointVertices_framedRestartSupport_subset_frameRegion
      center a transverseFlip R hz
  rcases a with ⟨i, positive⟩
  let z := cubicRestartFrameIso center (i, positive) transverseFlip w
  have hwAxis : -(n : ℤ) ≤ w i ∧ w i ≤ (n + 2 * m + 1 : ℕ) := by
    rcases hw with hwBox | hwLayer
    · have hi := mem_cubicMetricBox.mp hwBox i
      simp [cubicOrigin] at hi ⊢
      omega
    · obtain ⟨r, hr1, hr2, y, hy, rfl⟩ := hwLayer
      have hyi := (mem_cubicBoxFace.mp
        (mem_seededBoundaryQuadrant_iff.mp hy).1).1
      simp [cubicTranslateAlongCoordinate_same, cubicOrigin] at hyi ⊢
      omega
  by_cases hleft :
      -((2 * (m + n + 1) : ℕ) : ℤ) ≤
          z i - grimmettMarstrandSiteCenter (m + n + 1) x i ∧
        z i - grimmettMarstrandSiteCenter (m + n + 1) x i ≤
          ((2 * (m + n + 1) : ℕ) : ℤ)
  · left
    change z ∈ cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
      (2 * (m + n + 1))
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      omega
    · have hc := htrans j hji
      have hwTrans : -(n : ℤ) ≤ w j ∧ w j ≤ (n : ℤ) := by
        rcases hw with hwBox | hwLayer
        · simpa [cubicOrigin] using mem_cubicMetricBox.mp hwBox j
        · exact seededBoundaryLayerRegion_transverse_bounds hji hwLayer
      by_cases hflip : transverseFlip j <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandSiteCenter, cubicScale, hji, hflip] at hc ⊢ <;>
        ring_nf at hc ⊢ <;> omega
  · right
    change z ∈ cubicMetricBox d
      (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x (i, positive)))
      (2 * (m + n + 1))
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      cases positive <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandSiteCenter, cubicScale, cubicStepFrom,
          cubicDirectionIncrement] at haxis hleft ⊢ <;>
        ring_nf at haxis hleft ⊢ <;> omega
    · have hc := htrans j hji
      have hwTrans : -(n : ℤ) ≤ w j ∧ w j ≤ (n : ℤ) := by
        rcases hw with hwBox | hwLayer
        · simpa [cubicOrigin] using mem_cubicMetricBox.mp hwBox j
        · exact seededBoundaryLayerRegion_transverse_bounds hji hwLayer
      cases positive <;> by_cases hflip : transverseFlip j <;>
        simp [z, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
          grimmettMarstrandSiteCenter, cubicScale, cubicStepFrom,
          cubicDirectionIncrement, hji, hflip] at hc ⊢ <;>
        ring_nf at hc ⊢ <;> omega

/-- A compensating restart begun anywhere in the publishing site's radius-`N` box satisfies
the directional corridor bounds automatically. -/
theorem cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_center_mem_siteBox
    {d m n : ℕ} (center x : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (R : Finset (Cubic d))
    (hcenter : center ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1)) :
    (cubicEdgeEndpointVertices
        (framedRestartSupport center a transverseFlip m n R) : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x)
          (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  apply cubicEdgeEndpointVertices_framedRestartSupport_subset_endpointBoxes_of_directionalBounds
    center a transverseFlip R x
  · rcases a with ⟨i, positive⟩
    have hi := mem_cubicMetricBox.mp hcenter i
    cases positive <;> simp at hi ⊢ <;> omega
  · intro j _hja
    exact mem_cubicMetricBox.mp hcenter j

/-- The local frame of the post-radial extension selected in signed direction `a`. -/
def RootRadialSeedProfile.postRadialFrame
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (a : CubicDirection d) :
    cubicGraph d ≃g cubicGraph d :=
  cubicRestartFrameIso (W.physicalCenter a) a
    (oppositeTransverseRestartFlip a)

/-- Physical region read by one post-radial extension. -/
def RootRadialSeedProfile.postRadialRestartRegion
    {d m n : ℕ} (W : RootRadialSeedProfile d m n) (a : CubicDirection d) :
    Set (Cubic d) :=
  cubicGraphIsoRegion (W.postRadialFrame a)
    (positiveSeededRestartRegion d a.1 m n)

/-- Composition identity behind the first steering move: applying the opposite transverse
frame at the selected physical seed is the same as reversing the reference transverse
coordinates, translating by the selected reference seed, and then applying the original
radial orientation. -/
theorem RootRadialSeedProfile.postRadialFrame_apply
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d) (z : Cubic d) :
    W.postRadialFrame a z =
      cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
        (cubicTranslate cubicOrigin (W a).seedCenter.1
          (cubicRestartFrameIso cubicOrigin (a.1, true)
            (oppositeTransverseRestartFlip (a.1, true)) z)) := by
  ext j
  by_cases hja : j = a.1
  · subst j
    cases ha : a.2
    · simp [RootRadialSeedProfile.postRadialFrame,
        RootRadialSeedProfile.physicalCenter, cubicRestartFrameIso_apply,
        cubicRestartFrameFlip, cubicTranslate, cubicOrigin, ha]
      ring
    · simp [RootRadialSeedProfile.postRadialFrame,
        RootRadialSeedProfile.physicalCenter, cubicRestartFrameIso_apply,
        cubicRestartFrameFlip, cubicTranslate, cubicOrigin, ha]
  · simp [RootRadialSeedProfile.postRadialFrame,
      RootRadialSeedProfile.physicalCenter, cubicRestartFrameIso_apply,
      cubicRestartFrameFlip, rootRadialTransverseFlip,
      oppositeTransverseRestartFlip, cubicTranslate, cubicOrigin, hja]

/-- Complete explored-edge certificate carried by a named mixed-threshold radial witness. -/
theorem rootRadialMixedWitness_exploredCertificate
    {d m n : ℕ} (hmn : m ≤ n) (a : CubicDirection d)
    (p incremented : I) {delta : ℝ} (hdelta : delta = (incremented : ℝ))
    (X : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hW : W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X)) :
    ∃ (e : CubicEdge d)
        (w : (cubicGraph d).Walk
          (cubicRegionBoundaryOutsideEndpoint
            (cubicMetricBox d cubicOrigin m) e) W.boundaryPoint.1),
      e ∈ cubicRegionBoundaryEdgesWithinBox d
          (cubicMetricBox d cubicOrigin m) n ∧
      walkEdgeFinset w ⊆ cubicRegionExteriorEdgesWithinBox d
        (cubicMetricBox d cubicOrigin m) n ∧
      (cubicRestartFrameIso cubicOrigin a
          (rootRadialTransverseFlip a)).mapEdgeSet e ∈
        rootRadialExploredEdges d m n p incremented X ∧
      (∀ f ∈ walkEdgeFinset w,
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExploredEdges d m n p incremented X ∧
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExteriorEdges d m n) ∧
      (cubicRestartFrameIso cubicOrigin a
          (rootRadialTransverseFlip a)).mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true)) ∈
        rootRadialExploredEdges d m n p incremented X ∧
      (cubicRestartFrameIso cubicOrigin a
          (rootRadialTransverseFlip a)).mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true)) ∈
        rootRadialExteriorEdges d m n ∧
      ∀ f ∈ cubicBoxEdges d W.seedCenter.1 m,
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExploredEdges d m n p incremented X ∧
        (cubicRestartFrameIso cubicOrigin a
            (rootRadialTransverseFlip a)).mapEdgeSet f ∈
          rootRadialExteriorEdges d m n := by
  classical
  let R := cubicMetricBox d cubicOrigin m
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  let Xref := cubicGraphIsoCouplingReindex F X
  let B := finiteEdgesBelow (rootInitialBoundaryEdges d m n) incremented X
  let A := B ∪ finiteEdgesBelow (rootRadialExteriorEdges d m n) p X
  let C := finiteEdgeReachableClosure A B
  change W.IsMixedRestartWitness R p (fun _ ↦ 0) delta Xref at hW
  rcases hW with ⟨hrealized, e, heBoundary, hconnection, heIncrement⟩
  rcases hrealized with ⟨hoCleared, hentryBox, hcLayer, hcSeed⟩
  rcases hconnection with ⟨w, hwOpen, hwExterior⟩
  have hePhysicalBoundary : F.mapEdgeSet e ∈ rootInitialBoundaryEdges d m n :=
    rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges a heBoundary
  have hePhysicalOpen : X (F.mapEdgeSet e) < (incremented : ℝ) := by
    change Xref e < (incremented : ℝ)
    simpa [hdelta] using heIncrement
  have heB : F.mapEdgeSet e ∈ B :=
    mem_finiteEdgesBelow_iff.mpr ⟨hePhysicalBoundary, hePhysicalOpen⟩
  have hBA : B ⊆ A := Finset.subset_union_left
  have heC : F.mapEdgeSet e ∈ C :=
    sources_subset_finiteEdgeReachableClosure (allowed := A) (sources := B) hBA heB
  have heExplored : F.mapEdgeSet e ∈
      rootRadialExploredEdges d m n p incremented X := by
    change F.mapEdgeSet e ∈ nextExploredEdgeSet (rootInitialExploredEdges d m) A B
    exact Finset.mem_union_right _ heC
  have referenceOpen_mem_A : ∀ {f : CubicEdge d},
      f ∈ restartEventSupport d a.1 m n R → f ∉ E → Xref f < (p : ℝ) →
        F.mapEdgeSet f ∈ A := by
    intro f hfSupport hfNotBoundary hfOpen
    apply Finset.mem_union_right
    rw [mem_finiteEdgesBelow_iff]
    refine ⟨rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
      hmn a hfSupport ?_, hfOpen⟩
    simpa [R, E] using hfNotBoundary
  let y : Cubic d := W.boundaryPoint.1
  let o : CubicEdge d := cubicStepEdge y (a.1, true)
  have hoTarget : o ∈ seededBoundaryTargetSupport d a.1 m n :=
    cubicStepEdge_mem_seededBoundaryTargetSupport W.boundaryPoint.2
  have hoSupport : o ∈ restartEventSupport d a.1 m n R :=
    target_subset_restartEventSupport d a.1 m n R hoTarget
  have hoOpen : Xref o < (p : ℝ) := hoCleared.1
  have hoNotBoundary : o ∉ E := hoCleared.2
  have hoA : F.mapEdgeSet o ∈ A :=
    referenceOpen_mem_A hoSupport hoNotBoundary hoOpen
  let step : (cubicGraph d).Walk y (cubicStepFrom y (a.1, true)) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom y (a.1, true)) SimpleGraph.Walk.nil
  let q : (cubicGraph d).Walk
      (cubicRegionBoundaryOutsideEndpoint R e) (cubicStepFrom y (a.1, true)) :=
    w.append step
  let qPhysical := q.map F.toHom
  have hqPhysicalAllowed : walkEdgeFinset qPhysical ⊆ A := by
    intro g hg
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map] at hg
    obtain ⟨fSym, hfq, hfg⟩ := List.mem_map.mp hg
    let f : CubicEdge d := ⟨fSym, q.edges_subset_edgeSet hfq⟩
    have hmap : F.mapEdgeSet f = g := by
      apply Subtype.ext
      exact hfg
    rw [← hmap]
    change fSym ∈ (w.append step).edges at hfq
    rw [SimpleGraph.Walk.edges_append] at hfq
    rcases List.mem_append.mp hfq with hfw | hfstep
    · have hfExterior : f ∈ cubicRegionExteriorEdgesWithinBox d R n :=
        hwExterior ((mem_walkEdgeFinset_iff w f).mpr hfw)
      have hfCleared := hwOpen f.1 hfw
      exact referenceOpen_mem_A
        (exterior_subset_restartEventSupport d a.1 m n R hfExterior)
        hfCleared.2 hfCleared.1
    · have hfo : f = o := by
        apply Subtype.ext
        simpa [step, o] using hfstep
      simpa [hfo] using hoA
  have heStart : F (cubicRegionBoundaryOutsideEndpoint R e) ∈
      (F.mapEdgeSet e : Sym2 (Cubic d)) := by
    change F (cubicRegionBoundaryOutsideEndpoint R e) ∈
      Sym2.map F (e : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    refine ⟨cubicRegionBoundaryOutsideEndpoint R e, ?_, rfl⟩
    rw [← cubicRegionBoundaryEndpoints_edge heBoundary]
    simp
  have hqClosure : walkEdgeFinset qPhysical ⊆ C :=
    walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
      qPhysical heC heStart hqPhysicalAllowed
  have hoPhysicalWalk : F.mapEdgeSet o ∈ walkEdgeFinset qPhysical := by
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
    apply List.mem_map.mpr
    refine ⟨(o : Sym2 (Cubic d)), ?_, rfl⟩
    change (o : Sym2 (Cubic d)) ∈ (w.append step).edges
    rw [SimpleGraph.Walk.edges_append]
    apply List.mem_append_right
    simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton]
    rfl
  have hoC : F.mapEdgeSet o ∈ C := hqClosure hoPhysicalWalk
  have hoExplored : F.mapEdgeSet o ∈
      rootRadialExploredEdges d m n p incremented X := by
    change F.mapEdgeSet o ∈ nextExploredEdgeSet (rootInitialExploredEdges d m) A B
    exact Finset.mem_union_right _ hoC
  have hoExterior : F.mapEdgeSet o ∈ rootRadialExteriorEdges d m n :=
    rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
      hmn a hoSupport (by simpa [R, E] using hoNotBoundary)
  have hseedAllowed : (cubicBoxEdges d W.seedCenter.1 m).image F.mapEdgeSet ⊆ A := by
    intro g hg
    obtain ⟨f, hfSeed, rfl⟩ := Finset.mem_image.mp hg
    have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
      W.boundaryPoint.2 hentryBox hcLayer hfSeed
    have hfCleared := hcSeed hfSeed
    exact referenceOpen_mem_A
      (target_subset_restartEventSupport d a.1 m n R hfTarget)
      hfCleared.2 hfCleared.1
  have hentry : F (cubicStepFrom y (a.1, true)) ∈
      (F.mapEdgeSet o : Sym2 (Cubic d)) := by
    change F (cubicStepFrom y (a.1, true)) ∈ Sym2.map F (o : Sym2 (Cubic d))
    apply Sym2.mem_map.mpr
    exact ⟨cubicStepFrom y (a.1, true), by simp [o, cubicStepEdge], rfl⟩
  have hentryPhysicalBox : F (cubicStepFrom y (a.1, true)) ∈
      cubicMetricBox d (F W.seedCenter.1) m :=
    (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) W.seedCenter.1
      (cubicStepFrom y (a.1, true))).2 hentryBox
  have hseedClosure : cubicBoxEdges d (F W.seedCenter.1) m ⊆ C := by
    apply cubicBoxEdges_subset_finiteEdgeReachableClosure_of_incident
      hoC hentry hentryPhysicalBox
    intro g hg
    obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective g
    apply hseedAllowed
    apply Finset.mem_image.mpr
    refine ⟨f, ?_, rfl⟩
    apply mem_cubicBoxEdges_of_endpoints
    intro z hz
    apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) W.seedCenter.1 z).1
    apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
    change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
    exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
  refine ⟨e, w, heBoundary, hwExterior, heExplored, ?_, hoExplored, hoExterior, ?_⟩
  · intro f hfw
    have hfPhysicalWalk : F.mapEdgeSet f ∈ walkEdgeFinset qPhysical := by
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map]
      apply List.mem_map.mpr
      refine ⟨(f : Sym2 (Cubic d)), ?_, rfl⟩
      change (f : Sym2 (Cubic d)) ∈ (w.append step).edges
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ ((mem_walkEdgeFinset_iff w f).mp hfw)
    have hfC := hqClosure hfPhysicalWalk
    refine ⟨?_, rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges a (hwExterior hfw)⟩
    change F.mapEdgeSet f ∈ nextExploredEdgeSet (rootInitialExploredEdges d m) A B
    exact Finset.mem_union_right _ hfC
  · intro f hfSeed
    have hfPhysicalBox : F.mapEdgeSet f ∈ cubicBoxEdges d (F W.seedCenter.1) m := by
      apply mem_cubicBoxEdges_of_endpoints
      intro z hz
      change z ∈ Sym2.map F (f : Sym2 (Cubic d)) at hz
      obtain ⟨u, huf, rfl⟩ := Sym2.mem_map.mp hz
      exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
        cubicOrigin a (rootRadialTransverseFlip a) W.seedCenter.1 u).2
          (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfSeed huf)
    refine ⟨?_, ?_⟩
    · change F.mapEdgeSet f ∈ nextExploredEdgeSet (rootInitialExploredEdges d m) A B
      exact Finset.mem_union_right _ (hseedClosure hfPhysicalBox)
    · have hfTarget := seedEdge_mem_seededBoundaryTargetSupport
        W.boundaryPoint.2 hentryBox hcLayer hfSeed
      exact rootBranch_mapEdgeSet_mem_rootRadialExteriorEdges_of_restartSupport
        hmn a (target_subset_restartEventSupport d a.1 m n R hfTarget)
        (by exact (hcSeed hfSeed).2)

/-- A seed named by the literal mixed-threshold radial witness is contained in the actual
source explored closure. -/
theorem rootRadialMixedWitness_seedBox_subset_explored
    {d m n : ℕ} (hmn : m ≤ n) (a : CubicDirection d)
    (p incremented : I) {delta : ℝ} (hdelta : delta = (incremented : ℝ))
    (X : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hW : W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X)) :
    cubicBoxEdges d
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
          W.seedCenter.1) m ⊆
      rootRadialExploredEdges d m n p incremented X := by
  classical
  obtain ⟨_e, _w, _he, _hw, _heExplored, _hwExplored,
      _hoExplored, _hoExterior, hseed⟩ :=
    rootRadialMixedWitness_exploredCertificate
      hmn a p incremented hdelta X W hW
  intro g hg
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  obtain ⟨f, rfl⟩ := F.mapEdgeSet.surjective g
  apply (hseed f ?_).1
  apply mem_cubicBoxEdges_of_endpoints
  intro z hz
  apply (cubicRestartFrameIso_mem_cubicMetricBox_iff
    cubicOrigin a (rootRadialTransverseFlip a) W.seedCenter.1 z).1
  apply endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hg
  change F z ∈ Sym2.map F (f : Sym2 (Cubic d))
  exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩

/-- The canonical post-radial query really starts from the seed selected by the preceding
mixed-threshold branch: its reference region contains the complete inlet box `B(m)`. -/
theorem RootRadialSeedProfile.cubicMetricBox_subset_postRadialQuery_region_of_mixedWitness
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) {delta : ℝ} (hdelta : delta = (incremented : ℝ))
    (X : CubicEdge d → ℝ)
    (hW : (W a).IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X)) :
    let S := rootPostRadialSourceEdgeState d m n p incremented X
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    cubicMetricBox d cubicOrigin m ⊆ Q.region := by
  classical
  let S := rootPostRadialSourceEdgeState d m n p incremented X
  let F := W.postRadialFrame a
  let Q := S.framedQuery (W.physicalCenter a) a
    (oppositeTransverseRestartFlip a)
  dsimp only
  intro z hz
  have hzEndpoint : z ∈ cubicEdgeEndpointVertices (cubicBoxEdges d cubicOrigin m) :=
    cubicMetricBox_subset_cubicEdgeEndpointVertices_cubicBoxEdges hm hz
  obtain ⟨f, hfBox, hzf⟩ := mem_cubicEdgeEndpointVertices_iff.mp hzEndpoint
  have hfPhysicalBox : F.mapEdgeSet f ∈
      cubicBoxEdges d (W.physicalCenter a) m := by
    have hfImage : F.mapEdgeSet f ∈
        (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet :=
      Finset.mem_image.mpr ⟨f, hfBox, rfl⟩
    rw [show (cubicBoxEdges d cubicOrigin m).image F.mapEdgeSet =
        cubicBoxEdges d (W.physicalCenter a) m by
      simpa [F, RootRadialSeedProfile.postRadialFrame] using
        cubicRestartFrameIso_image_cubicBoxEdges_eq
          (n := m) (W.physicalCenter a) a (oppositeTransverseRestartFlip a)] at hfImage
    exact hfImage
  have hfExplored : F.mapEdgeSet f ∈ S.explored := by
    change F.mapEdgeSet f ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).explored
    rw [rootPostRadialSourceEdgeState_explored hm hmn p incremented X]
    have hmn' : m ≤ n := by omega
    apply rootRadialMixedWitness_seedBox_subset_explored
      hmn' a p incremented hdelta X (W a) hW
    simpa [RootRadialSeedProfile.physicalCenter] using hfPhysicalBox
  have hfReference : f ∈ S.referenceExploredEdges F := by
    rw [SourceFiniteEdgeRevealState.referenceExploredEdges, Finset.mem_image]
    refine ⟨F.mapEdgeSet f, hfExplored, ?_⟩
    change F.mapEdgeSet.symm (F.mapEdgeSet f) = f
    exact F.mapEdgeSet.symm_apply_apply f
  change z ∈ cubicEdgeEndpointVertices (S.referenceExploredEdges F)
  exact mem_cubicEdgeEndpointVertices_iff.mpr ⟨f, hfReference, hzf⟩

/-- A named mixed-threshold radial witness is constant throughout its unchanged post-radial
accumulated-history cell. -/
theorem rootRadialMixedWitness_of_mem_rootPostRadialSourceHistoryProfile
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (a : CubicDirection d) (p incremented : I) {delta : ℝ}
    (hdelta : delta = (incremented : ℝ))
    (X Y : CubicEdge d → ℝ) (W : RestartSeedWitnessIndex d a.1 m n)
    (hW : W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) X))
    (hY : Y ∈
      (rootPostRadialSourceEdgeState d m n p incremented X).historyProfile.event) :
    W.IsMixedRestartWitness (cubicMetricBox d cubicOrigin m)
      p (fun _ ↦ 0) delta
      (cubicGraphIsoCouplingReindex
        (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)) Y) := by
  classical
  let R := cubicMetricBox d cubicOrigin m
  let E := cubicRegionBoundaryEdgesWithinBox d R n
  let F := cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
  let Yref := cubicGraphIsoCouplingReindex F Y
  have hmn' : m ≤ n := by omega
  obtain ⟨e, w, heBoundary, hwExterior, heExplored, hwCertificate,
      hoExplored, hoExterior, hseedCertificate⟩ :=
    rootRadialMixedWitness_exploredCertificate
      hmn' a p incremented hdelta X W hW
  have hrealizedX := hW.1
  rcases hrealizedX with ⟨hoCleared, hentryBox, hcLayer, hcSeed⟩
  change W.IsMixedRestartWitness R p (fun _ ↦ 0) delta Yref
  refine ⟨?_, e, heBoundary, ?_, ?_⟩
  · refine ⟨?_, hentryBox, hcLayer, ?_⟩
    · change Yref (cubicStepEdge W.boundaryPoint.1 (a.1, true)) < (p : ℝ) ∧
        cubicStepEdge W.boundaryPoint.1 (a.1, true) ∉ E
      constructor
      · change Y (F.mapEdgeSet
          (cubicStepEdge W.boundaryPoint.1 (a.1, true))) < (p : ℝ)
        exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
          hm hmn p incremented X Y hoExterior hoExplored hY
      · exact hoCleared.2
    · intro f hfSeed
      change Yref f < (p : ℝ) ∧ f ∉ E
      have hfCertificate := hseedCertificate f hfSeed
      constructor
      · change Y (F.mapEdgeSet f) < (p : ℝ)
        exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
          hm hmn p incremented X Y hfCertificate.2 hfCertificate.1 hY
      · exact (hcSeed hfSeed).2
  · refine ⟨w, ?_, hwExterior⟩
    intro fSym hfWalk
    let f : CubicEdge d := ⟨fSym, w.edges_subset_edgeSet hfWalk⟩
    have hfFinset : f ∈ walkEdgeFinset w :=
      (mem_walkEdgeFinset_iff w f).mpr hfWalk
    have hfCertificate := hwCertificate f hfFinset
    change Yref f < (p : ℝ) ∧ f ∉ E
    constructor
    · change Y (F.mapEdgeSet f) < (p : ℝ)
      exact label_lt_density_of_mem_rootPostRadialSourceHistoryProfile
        hm hmn p incremented X Y hfCertificate.2 hfCertificate.1 hY
    · intro hfBoundary
      exact Set.disjoint_left.mp
        (disjoint_cubicRegionExteriorEdgesWithinBox_boundary d R n)
        (hwExterior hfFinset) hfBoundary
  · change Yref e < ((fun _ : CubicEdge d ↦ (0 : I)) e : ℝ) + delta
    have hePhysicalBoundary :=
      rootBranch_mapEdgeSet_mem_rootInitialBoundaryEdges a heBoundary
    have heOpen := label_lt_incremented_of_mem_rootPostRadialSourceHistoryProfile
      hm hmn p incremented X Y hePhysicalBoundary heExplored hY
    simpa [Yref, F, hdelta] using heOpen

/-- The reference positive restart region becomes the literal opposite-quadrant region after
the transverse reversal. -/
theorem cubicRestartFrameIso_positiveSeededRestartRegion_subset_steered
    {d m n : ℕ} (i : Fin d) :
    cubicGraphIsoRegion
        (cubicRestartFrameIso cubicOrigin (i, true)
          (oppositeTransverseRestartFlip (i, true)))
        (positiveSeededRestartRegion d i m n) ⊆
      steeredPositiveRestartRegion d i m n := by
  rintro z ⟨w, hw, rfl⟩
  rcases hw with hw | hw
  · left
    have himage := (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin (i, true) (oppositeTransverseRestartFlip (i, true))
      cubicOrigin w).2 hw
    simpa only [cubicRestartFrameIso_origin] using himage
  · right
    exact cubicRestartFrameIso_seededBoundaryLayerRegion_subset_steered i
      ⟨w, hw, rfl⟩

/-- Geometry of the two restart applications assigned to one branch.  The first application
selects `c` in an arbitrary signed frame.  If the second application uses the selected seed's
physical displacement from `base`, its whole restart region stays in the two radius-`2N`
endpoint boxes of that same frame. -/
theorem pairedRestartRegion_subset_endpointBoxes_of_geometry
    {d m n : ℕ} (base c : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool)
    (hm : 1 ≤ m)
    (hgeom : SeedBoxWithinBoundaryLayer d a.1 m n c) :
    let target := cubicRestartFrameIso base a transverseFlip c
    cubicGraphIsoRegion
        (cubicRestartFrameIso target a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition base target)))
        (positiveSeededRestartRegion d a.1 m n) ⊆
      (cubicMetricBox d base (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (cubicRestartFrameIso base a transverseFlip
            (grimmettMarstrandSiteCenter (m + n + 1)
              (cubicStepFrom cubicOrigin (a.1, true))))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  dsimp only
  intro z hz
  rcases hz with ⟨q, hq, rfl⟩
  let G := cubicRestartFrameIso cubicOrigin (a.1, true)
    (oppositeTransverseRestartFlip (a.1, true))
  have hGq : G q ∈ steeredPositiveRestartRegion d a.1 m n :=
    cubicRestartFrameIso_positiveSeededRestartRegion_subset_steered a.1
      ⟨q, hq, rfl⟩
  have href :=
    translated_steeredRestartRegion_subset_endpointBoxes_of_boxWithinBoundaryLayer
      a.1 hgeom ⟨G q, hGq, rfl⟩
  have hpos : ∀ j, j ≠ a.1 → 0 < c j := by
    intro j hja
    have hc := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer a.1 hgeom hja
    omega
  rw [cubicRestartFrameIso_inletCompensating_comp _ _ _ _ hpos]
  rcases href with href | href
  · left
    have himage := (cubicRestartFrameIso_mem_cubicMetricBox_iff
      base a transverseFlip cubicOrigin
      (cubicTranslate cubicOrigin c (G q))).2 href
    simpa only [cubicRestartFrameIso_origin] using himage
  · right
    exact (cubicRestartFrameIso_mem_cubicMetricBox_iff
      base a transverseFlip
      (grimmettMarstrandSiteCenter (m + n + 1)
        (cubicStepFrom cubicOrigin (a.1, true)))
      (cubicTranslate cubicOrigin c (G q))).2 href

/-- The seed selected by the second member of a duplicate restart pair lies in the literal
half-way box of the corresponding reference bond.  The axial coordinates add to `2N`, while
the opposite transverse steering leaves only the difference of two coordinates in
`[m,n-m]`. -/
theorem translated_compensating_seedCenter_mem_referenceHalfwayBox
    {d m n : ℕ} (i : Fin d) {c q : Cubic d}
    (hc : SeedBoxWithinBoundaryLayer d i m n c)
    (hq : SeedBoxWithinBoundaryLayer d i m n q) :
    cubicTranslate cubicOrigin c
        (cubicRestartFrameIso cubicOrigin (i, true)
          (oppositeTransverseRestartFlip (i, true)) q) ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin (i, true) := by
  change cubicTranslate cubicOrigin c
      (cubicRestartFrameIso cubicOrigin (i, true)
        (oppositeTransverseRestartFlip (i, true)) q) ∈
    cubicMetricBox d
      (grimmettMarstrandBondCenter (m + n + 1) cubicOrigin
        (cubicStepFrom cubicOrigin (i, true))) (m + n + 1)
  rw [mem_cubicMetricBox]
  intro j
  by_cases hji : j = i
  · subst j
    have hcAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer i hc
    have hqAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer i hq
    simp [grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
      grimmettMarstrandBondCenter, cubicTranslate, cubicRestartFrameIso_apply,
      cubicRestartFrameFlip, cubicStepFrom, cubicDirectionIncrement, cubicOrigin,
      hcAxis, hqAxis]
    omega
  · have hcBounds := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer i hc hji
    have hqBounds := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer i hq hji
    simp [grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
      grimmettMarstrandBondCenter, cubicTranslate, cubicRestartFrameIso_apply,
      cubicRestartFrameFlip, oppositeTransverseRestartFlip, cubicStepFrom,
      cubicDirectionIncrement, cubicOrigin, hji]
    omega

/-- One compensating restart preserves the `N = m+n+1` transverse corridor about its
deterministic reference center.  This is the elementary invariant used separately at each
member of an inlet or outgoing restart pair; using the random first target as the second
reference would not have this property. -/
theorem inletCompensatingTarget_transverse_bounds_of_bounds
    {d m n : ℕ} {reference center c : Cubic d} {a : CubicDirection d}
    {j : Fin d}
    (hcenterj : reference j - (m + n + 1 : ℕ) ≤ center j ∧
      center j ≤ reference j + (m + n + 1 : ℕ))
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c)
    (hja : j ≠ a.1) :
    reference j - (m + n + 1 : ℕ) ≤
        cubicRestartFrameIso center a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition reference center)) c j ∧
      cubicRestartFrameIso center a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition reference center)) c j ≤
        reference j + (m + n + 1 : ℕ) := by
  have hcj := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer a.1 hc hja
  by_cases hpos : 0 < center j - reference j
  · have hlt : reference j < center j := by omega
    simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      inletCompensatingTransverseFlip, cubicRelativePosition, hja, hlt]
    constructor <;> omega
  · have hlt : ¬ reference j < center j := by omega
    simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      inletCompensatingTransverseFlip, cubicRelativePosition, hja, hlt]
    constructor <;> omega

/-- Box-facing wrapper for one compensating transverse step. -/
theorem inletCompensatingTarget_transverse_bounds
    {d m n : ℕ} {reference center c : Cubic d} {a : CubicDirection d}
    (hcenter : center ∈ cubicMetricBox d reference (m + n + 1))
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c)
    {j : Fin d} (hja : j ≠ a.1) :
    reference j - (m + n + 1 : ℕ) ≤
        cubicRestartFrameIso center a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition reference center)) c j ∧
      cubicRestartFrameIso center a
          (inletCompensatingTransverseFlip a
            (cubicRelativePosition reference center)) c j ≤
        reference j + (m + n + 1 : ℕ) := by
  exact inletCompensatingTarget_transverse_bounds_of_bounds
    (mem_cubicMetricBox.mp hcenter j) hc hja

/-- Coordinate form of the preceding invariant. -/
theorem inletCompensatingTarget_mem_transverseCorridor
    {d m n : ℕ} {reference center c : Cubic d} {a : CubicDirection d}
    (hcenter : center ∈ cubicMetricBox d reference (m + n + 1))
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c) :
    ∀ j : Fin d, j ≠ a.1 →
      reference j - (m + n + 1 : ℕ) ≤
          cubicRestartFrameIso center a
            (inletCompensatingTransverseFlip a
              (cubicRelativePosition reference center)) c j ∧
        cubicRestartFrameIso center a
            (inletCompensatingTransverseFlip a
              (cubicRelativePosition reference center)) c j ≤
          reference j + (m + n + 1 : ℕ) := by
  intro j hja
  exact inletCompensatingTarget_transverse_bounds hcenter hc hja

/-- Two successive restarts which both compensate against the deterministic publishing-site
center end in the literal half-way box of the chosen coarse bond. -/
theorem pairedInletCompensatingTarget_mem_halfwayBox
    {d m n : ℕ} {x center c q : Cubic d} {a : CubicDirection d}
    (hcenter : center ∈
      cubicMetricBox d (grimmettMarstrandSiteCenter (m + n + 1) x) (m + n + 1))
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c)
    (hq : SeedBoxWithinBoundaryLayer d a.1 m n q) :
    let reference := grimmettMarstrandSiteCenter (m + n + 1) x
    let first := cubicRestartFrameIso center a
      (inletCompensatingTransverseFlip a
        (cubicRelativePosition reference center)) c
    cubicRestartFrameIso first a
        (inletCompensatingTransverseFlip a
          (cubicRelativePosition reference first)) q ∈
      grimmettMarstrandHalfwayBox d (m + n + 1) x a := by
  dsimp only
  let reference := grimmettMarstrandSiteCenter (m + n + 1) x
  let first := cubicRestartFrameIso center a
    (inletCompensatingTransverseFlip a
      (cubicRelativePosition reference center)) c
  change cubicRestartFrameIso first a
      (inletCompensatingTransverseFlip a
        (cubicRelativePosition reference first)) q ∈
    cubicMetricBox d (grimmettMarstrandBondCenter (m + n + 1) x
      (cubicStepFrom x a)) (m + n + 1)
  rw [mem_cubicMetricBox]
  intro j
  by_cases hja : j = a.1
  · subst j
    have hcAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hc
    have hqAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hq
    have hcenterAxis := mem_cubicMetricBox.mp hcenter a.1
    rcases a with ⟨i, positive⟩
    cases positive <;>
      simp [first, reference, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
        cubicStepFrom, cubicDirectionIncrement, hcAxis, hqAxis] at hcenterAxis ⊢ <;>
      ring_nf at hcenterAxis ⊢ <;>
      constructor <;> omega
  · have hfirst := inletCompensatingTarget_transverse_bounds hcenter hc hja
    have hsecond := inletCompensatingTarget_transverse_bounds_of_bounds hfirst hq hja
    rcases a with ⟨i, positive⟩
    have hji : j ≠ i := hja
    simp [first, reference, grimmettMarstrandBondCenter,
      grimmettMarstrandSiteCenter, cubicScale, cubicStepFrom,
      cubicDirectionIncrement, hji] at hsecond ⊢
    ring_nf at hsecond ⊢
    exact hsecond

/-- Starting in the half-way box of a coarse bond, two compensating restarts aimed in that
bond direction recenter in the radius-`N` box of the destination coarse site. -/
theorem pairedInletCompensatingTarget_mem_destinationSiteBox
    {d m n : ℕ} {x inlet c q : Cubic d} {a : CubicDirection d}
    (hinlet : inlet ∈ grimmettMarstrandHalfwayBox d (m + n + 1) x a)
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c)
    (hq : SeedBoxWithinBoundaryLayer d a.1 m n q) :
    let destination := grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a)
    let first := cubicRestartFrameIso inlet a
      (inletCompensatingTransverseFlip a
        (cubicRelativePosition destination inlet)) c
    cubicRestartFrameIso first a
        (inletCompensatingTransverseFlip a
          (cubicRelativePosition destination first)) q ∈
      cubicMetricBox d destination (m + n + 1) := by
  dsimp only
  let destination := grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom x a)
  let first := cubicRestartFrameIso inlet a
    (inletCompensatingTransverseFlip a
      (cubicRelativePosition destination inlet)) c
  rw [mem_cubicMetricBox]
  intro j
  by_cases hja : j = a.1
  · subst j
    have hcAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hc
    have hqAxis := seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hq
    have hinletAxis := mem_cubicMetricBox.mp hinlet a.1
    rcases a with ⟨i, positive⟩
    cases positive <;>
      simp [first, destination, grimmettMarstrandHalfwayBox,
        grimmettMarstrandBondBox, grimmettMarstrandBondCenter,
        grimmettMarstrandSiteCenter, cubicScale, cubicRestartFrameIso_apply,
        cubicRestartFrameFlip, cubicStepFrom, cubicDirectionIncrement,
        hcAxis, hqAxis] at hinletAxis ⊢ <;>
      ring_nf at hinletAxis ⊢ <;>
      constructor <;> omega
  · have hinletTransverse : destination j - (m + n + 1 : ℕ) ≤ inlet j ∧
        inlet j ≤ destination j + (m + n + 1 : ℕ) := by
      have h := mem_cubicMetricBox.mp hinlet j
      rcases a with ⟨i, positive⟩
      have hji : j ≠ i := hja
      simp [destination, grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
        grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
        cubicStepFrom, cubicDirectionIncrement, hji] at h ⊢
      ring_nf at h ⊢
      exact h
    have hfirst := inletCompensatingTarget_transverse_bounds_of_bounds
      hinletTransverse hc hja
    have hsecond := inletCompensatingTarget_transverse_bounds_of_bounds hfirst hq hja
    simpa [first, destination] using hsecond

/-- A signed restart frame based at a coarse site carries the reference half-way center to the
literal bond center joining that coarse site to its signed neighbor. -/
theorem cubicRestartFrameIso_referenceHalfwayCenter
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) :
    cubicRestartFrameIso (grimmettMarstrandSiteCenter N x) a transverseFlip
        (grimmettMarstrandBondCenter N cubicOrigin
          (cubicStepFrom cubicOrigin (a.1, true))) =
      grimmettMarstrandBondCenter N x (cubicStepFrom x a) := by
  ext j
  rcases a with ⟨i, positive⟩
  by_cases hji : j = i
  · subst j
    cases positive <;>
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
        cubicStepFrom, cubicDirectionIncrement, cubicOrigin] <;>
      ring
  · simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
      cubicStepFrom, cubicDirectionIncrement, cubicOrigin, hji]
    ring

/-- Consequently the image of the reference half-way box is exactly contained in the literal
half-way box attached to the framed coarse site. -/
theorem cubicRestartFrameIso_referenceHalfwayBox_subset_halfwayBox
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) :
    cubicGraphIsoRegion
        (cubicRestartFrameIso (grimmettMarstrandSiteCenter N x) a transverseFlip)
        (grimmettMarstrandHalfwayBox d N cubicOrigin (a.1, true)) ⊆
      (grimmettMarstrandHalfwayBox d N x a : Set (Cubic d)) := by
  rintro z ⟨q, hq, rfl⟩
  have himage := (cubicRestartFrameIso_mem_cubicMetricBox_iff
    (grimmettMarstrandSiteCenter N x) a transverseFlip
    (grimmettMarstrandBondCenter N cubicOrigin
      (cubicStepFrom cubicOrigin (a.1, true))) q).2 hq
  simpa [grimmettMarstrandHalfwayBox, grimmettMarstrandBondBox,
    cubicRestartFrameIso_referenceHalfwayCenter] using himage

/-- Physical form of the preceding midpoint calculation.  A duplicate pair begun in an
arbitrary signed frame publishes a seed in the image of the reference half-way box. -/
theorem pairedRestartTarget_mem_framedHalfwayBox_of_geometry
    {d m n : ℕ} (base c q : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool)
    (hm : 1 ≤ m)
    (hc : SeedBoxWithinBoundaryLayer d a.1 m n c)
    (hq : SeedBoxWithinBoundaryLayer d a.1 m n q) :
    let firstTarget := cubicRestartFrameIso base a transverseFlip c
    cubicRestartFrameIso firstTarget a
        (inletCompensatingTransverseFlip a
          (cubicRelativePosition base firstTarget)) q ∈
      cubicGraphIsoRegion (cubicRestartFrameIso base a transverseFlip)
        (grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin (a.1, true)) := by
  dsimp only
  let G := cubicRestartFrameIso cubicOrigin (a.1, true)
    (oppositeTransverseRestartFlip (a.1, true))
  have hpos : ∀ j, j ≠ a.1 → 0 < c j := by
    intro j hja
    have hj := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer a.1 hc hja
    omega
  rw [cubicRestartFrameIso_inletCompensating_comp _ _ _ _ hpos]
  refine ⟨cubicTranslate cubicOrigin c (G q), ?_, rfl⟩
  exact translated_compensating_seedCenter_mem_referenceHalfwayBox a.1 hc hq

/-- A post-radial restart from a geometrically valid selected seed stays inside the two
endpoint site boxes required by the Grimmett--Marstrand construction.  Openness of the seed is
irrelevant to this containment; only the retained box-in-layer certificate is used. -/
theorem RootRadialSeedProfile.postRadialRestartRegion_subset_endpointBoxes_of_geometry
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d)
    (hgeom : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1) :
    W.postRadialRestartRegion a ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  rcases hz with ⟨q, hq, rfl⟩
  let G := cubicRestartFrameIso cubicOrigin (a.1, true)
    (oppositeTransverseRestartFlip (a.1, true))
  have hGq : G q ∈ steeredPositiveRestartRegion d a.1 m n :=
    cubicRestartFrameIso_positiveSeededRestartRegion_subset_steered a.1
      ⟨q, hq, rfl⟩
  have href :=
    translated_steeredRestartRegion_subset_endpointBoxes_of_boxWithinBoundaryLayer
      a.1 hgeom
        ⟨G q, hGq, rfl⟩
  rw [W.postRadialFrame_apply]
  rcases href with href | href
  · left
    have himage := (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a) cubicOrigin
      (cubicTranslate cubicOrigin (W a).seedCenter.1 (G q))).2 href
    simpa using himage
  · right
    have himage := (cubicRestartFrameIso_mem_cubicMetricBox_iff
      cubicOrigin a (rootRadialTransverseFlip a)
      (grimmettMarstrandSiteCenter (m + n + 1)
        (cubicStepFrom cubicOrigin (a.1, true)))
      (cubicTranslate cubicOrigin (W a).seedCenter.1 (G q))).2 href
    have hcenter :
        cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a)
            (grimmettMarstrandSiteCenter (m + n + 1)
              (cubicStepFrom cubicOrigin (a.1, true))) =
          grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin a) := by
      rw [show rootRadialTransverseFlip a = (fun _ ↦ false) by rfl,
        cubicRestartFrameIso_noTransverse_eq]
      have hzero : grimmettMarstrandSiteCenter (m + n + 1)
          (cubicOrigin : Cubic d) = cubicOrigin := by
        ext j
        simp [grimmettMarstrandSiteCenter, cubicScale, cubicOrigin]
      rw [← hzero]
      exact cubicDirectionOrientationIso_referenceNextSiteCenter
        (N := m + n + 1) cubicOrigin a
    simpa [hcenter] using himage

/-- Realization-facing wrapper for post-radial containment. -/
theorem RootRadialSeedProfile.postRadialRestartRegion_subset_endpointBoxes
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d) {omega : EdgeConfiguration d}
    (hW : (W a).IsRealized omega) :
    W.postRadialRestartRegion a ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin a))
          (2 * (m + n + 1)) : Set (Cubic d)) :=
  W.postRadialRestartRegion_subset_endpointBoxes_of_geometry a hW.2.2.1

/-- The literal finite support of a post-radial query is contained in its geometric restart
region and hence in the two endpoint site boxes. -/
theorem RootRadialSeedProfile.endpointVertices_postRadialQuery_subset_endpointBoxes
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d) (S : SourceFiniteEdgeRevealState d)
    {omega : EdgeConfiguration d} (hW : (W a).IsRealized omega) :
    (cubicEdgeEndpointVertices
        ((S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  apply W.postRadialRestartRegion_subset_endpointBoxes a hW
  simpa [RootRadialSeedProfile.postRadialRestartRegion,
    RootRadialSeedProfile.postRadialFrame, SourceFiniteEdgeRevealState.framedQuery] using
    (S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)).endpointVertices_restartSupport_subset_frameRegion hz

/-- Geometry-only form of the literal post-radial support containment. -/
theorem RootRadialSeedProfile.endpointVertices_postRadialQuery_subset_endpointBoxes_of_geometry
    {d m n : ℕ} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d) (S : SourceFiniteEdgeRevealState d)
    (hgeom : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1) :
    (cubicEdgeEndpointVertices
        ((S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)).restartSupport m n) : Set (Cubic d)) ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1)
            (cubicStepFrom cubicOrigin a))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  apply W.postRadialRestartRegion_subset_endpointBoxes_of_geometry a hgeom
  simpa [RootRadialSeedProfile.postRadialRestartRegion,
    RootRadialSeedProfile.postRadialFrame, SourceFiniteEdgeRevealState.framedQuery] using
    (S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)).endpointVertices_restartSupport_subset_frameRegion hz

/-- If the root and the coarse neighbor in direction `a` both belong to `F`, every endpoint
read by that root extension lies in the literal final thickening. -/
theorem RootRadialSeedProfile.endpointVertices_postRadialQuery_subset_thickening
    {d m n : ℕ} {F : Set (Cubic d)} (W : RootRadialSeedProfile d m n)
    (a : CubicDirection d) (S : SourceFiniteEdgeRevealState d)
    {omega : EdgeConfiguration d} (hW : (W a).IsRealized omega)
    (hrootF : cubicOrigin ∈ F) (hstepF : cubicStepFrom cubicOrigin a ∈ F) :
    (cubicEdgeEndpointVertices
        ((S.framedQuery (W.physicalCenter a) a
          (oppositeTransverseRestartFlip a)).restartSupport m n) : Set (Cubic d)) ⊆
      grimmettMarstrandThickening d F (m + n + 1) := by
  intro z hz
  rcases W.endpointVertices_postRadialQuery_subset_endpointBoxes a S hW hz with hz | hz
  · exact grimmettMarstrandCenteredBox_subset_thickening hrootF le_rfl hz
  · exact grimmettMarstrandCenteredBox_subset_thickening hstepF le_rfl hz

/-- The simultaneous radial support is already inside the root-centered part of the final
thickening. -/
theorem rootRadialEdgeSupport_endpointVertices_subset_thickening
    {d m n : ℕ} {F : Set (Cubic d)} (hrootF : cubicOrigin ∈ F) :
    (cubicEdgeEndpointVertices (rootRadialEdgeSupport d m n) : Set (Cubic d)) ⊆
      grimmettMarstrandThickening d F (m + n + 1) := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  have heWide := rootRadialEdgeSupport_subset_wideBox d m n he
  apply grimmettMarstrandCenteredBox_subset_thickening
    (N := m + n + 1) (R := n + 2 * m + 1) hrootF (by omega)
  exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heWide hze

/-- Reference-coordinate separation between two distinct post-radial root directions.  A
restart in direction `b` uses the wide radius only along `b`; in every transverse coordinate it
stays in the original radius-`n` strip.  After recentering at the selected seed in a distinct
direction `a`, every endpoint therefore lies strictly behind the new positive `n`-face. -/
theorem RootRadialSeedProfile.postRadial_referenceCoord_add_one_lt_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a)
    {R : Finset (Cubic d)} {f : CubicEdge d}
    (hf : f ∈ restartEventSupport d b.1 m n R)
    {w z : Cubic d} (hwf : w ∈ (f : Sym2 (Cubic d)))
    (hframes : W.postRadialFrame a z = W.postRadialFrame b w) :
    z a.1 + 1 < (n : ℤ) := by
  have hwWide : w ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1) :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
      (restartEventSupport_subset_cubicBoxEdges_wide d b.1 m n R hf) hwf
  rcases a with ⟨i, sa⟩
  rcases b with ⟨j, sb⟩
  have hai : (W (i, sa)).seedCenter.1 i = (n + m + 1 : ℕ) :=
    seedCenter_axis_eq_of_boxWithinBoundaryLayer i (hgeom (i, sa))
  have hbj : (W (j, sb)).seedCenter.1 j = (n + m + 1 : ℕ) :=
    seedCenter_axis_eq_of_boxWithinBoundaryLayer j (hgeom (j, sb))
  by_cases hij : i = j
  · subst j
    have hwBounds := (mem_cubicMetricBox.mp hwWide) i
    simp [cubicOrigin] at hwBounds
    cases sa <;> cases sb
    · exact (hab rfl).elim
    · have hcenterA : W.physicalCenter (i, false) i =
          -(n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hai, cubicOrigin]
      have hcenterB : W.physicalCenter (i, true) i =
          (n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hbj, cubicOrigin]
      have hAz : W.postRadialFrame (i, false) z i =
          -z i - (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterA]
        simp [cubicRestartFrameFlip] <;> ring
      have hBw : W.postRadialFrame (i, true) w i =
          w i + (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterB]
        simp [cubicRestartFrameFlip] <;> ring
      have hcoord : W.postRadialFrame (i, false) z i =
          W.postRadialFrame (i, true) w i := congrFun hframes i
      have hcoord' : -z i - (n + m + 1 : ℕ) =
          w i + (n + m + 1 : ℕ) :=
        hAz.symm.trans (hcoord.trans hBw)
      clear hcoord hAz hBw hframes hcenterA hcenterB hai hbj
      change z i + 1 < (n : ℤ)
      omega
    · have hcenterA : W.physicalCenter (i, true) i =
          (n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hai, cubicOrigin]
      have hcenterB : W.physicalCenter (i, false) i =
          -(n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hbj, cubicOrigin]
      have hAz : W.postRadialFrame (i, true) z i =
          z i + (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterA]
        simp [cubicRestartFrameFlip] <;> ring
      have hBw : W.postRadialFrame (i, false) w i =
          -w i - (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterB]
        simp [cubicRestartFrameFlip] <;> ring
      have hcoord : W.postRadialFrame (i, true) z i =
          W.postRadialFrame (i, false) w i := congrFun hframes i
      have hcoord' : z i + (n + m + 1 : ℕ) =
          -w i - (n + m + 1 : ℕ) :=
        hAz.symm.trans (hcoord.trans hBw)
      clear hcoord hAz hBw hframes hcenterA hcenterB hai hbj
      change z i + 1 < (n : ℤ)
      omega
    · exact (hab rfl).elim
  · have hwTrans := endpoint_mem_restartEventSupport_transverse_bounds
        (i := j) (j := i) hij hf hwf
    have hbi := seedCenter_transverse_bounds_of_boxWithinBoundaryLayer
      j (hgeom (j, sb)) hij
    have hcenterB : W.physicalCenter (j, sb) i = (W (j, sb)).seedCenter.1 i := by
      simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
        rootRadialTransverseFlip, cubicOrigin, hij]
    have hBw : W.postRadialFrame (j, sb) w i =
        -w i + (W (j, sb)).seedCenter.1 i := by
      simp only [RootRadialSeedProfile.postRadialFrame,
        cubicRestartFrameIso_apply]
      rw [hcenterB]
      simp [cubicRestartFrameFlip, oppositeTransverseRestartFlip, hij]
    cases sa
    · have hcenterA : W.physicalCenter (i, false) i =
          -(n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hai, cubicOrigin]
      have hAz : W.postRadialFrame (i, false) z i =
          -z i - (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterA]
        simp [cubicRestartFrameFlip] <;> ring
      have hcoord : W.postRadialFrame (i, false) z i =
          W.postRadialFrame (j, sb) w i := congrFun hframes i
      have hcoord' : -z i - (n + m + 1 : ℕ) =
          -w i + (W (j, sb)).seedCenter.1 i :=
        hAz.symm.trans (hcoord.trans hBw)
      change z i + 1 < (n : ℤ)
      omega
    · have hcenterA : W.physicalCenter (i, true) i =
          (n + m + 1 : ℕ) := by
        simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
          hai, cubicOrigin]
      have hAz : W.postRadialFrame (i, true) z i =
          z i + (n + m + 1 : ℕ) := by
        simp only [RootRadialSeedProfile.postRadialFrame,
          cubicRestartFrameIso_apply]
        rw [hcenterA]
        simp [cubicRestartFrameFlip] <;> ring
      have hcoord : W.postRadialFrame (i, true) z i =
          W.postRadialFrame (j, sb) w i := congrFun hframes i
      have hcoord' : z i + (n + m + 1 : ℕ) =
          -w i + (W (j, sb)).seedCenter.1 i :=
        hAz.symm.trans (hcoord.trans hBw)
      change z i + 1 < (n : ℤ)
      omega

/-- The weaker endpoint separation used by freshness follows from the one-layer estimate. -/
theorem RootRadialSeedProfile.postRadial_referenceCoord_lt_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a)
    {R : Finset (Cubic d)} {f : CubicEdge d}
    (hf : f ∈ restartEventSupport d b.1 m n R)
    {w z : Cubic d} (hwf : w ∈ (f : Sym2 (Cubic d)))
    (hframes : W.postRadialFrame a z = W.postRadialFrame b w) :
    z a.1 < (n : ℤ) := by
  have h := W.postRadial_referenceCoord_add_one_lt_of_ne
    hm hmn hgeom hab hf hwf hframes
  omega

/-- Pulling a distinct post-radial restart support into the current direction's reference frame
puts every endpoint strictly behind the current positive target face.  This is the support-level
form of `postRadial_referenceCoord_lt_of_ne` needed by the sequential root exploration. -/
theorem RootRadialSeedProfile.postRadialRestartSupport_endpoint_coord_add_one_lt_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a) {R : Finset (Cubic d)}
    {e : CubicEdge d}
    (he : e ∈ (framedRestartSupport (W.physicalCenter b) b
      (oppositeTransverseRestartFlip b) m n R).image
        (W.postRadialFrame a).symm.mapEdgeSet)
    {z : Cubic d} (hze : z ∈ (e : Sym2 (Cubic d))) :
    z a.1 + 1 < (n : ℤ) := by
  classical
  rw [Finset.mem_image] at he
  obtain ⟨ePhysical, hePhysical, rfl⟩ := he
  change z ∈ Sym2.map (W.postRadialFrame a).symm
    (ePhysical : Sym2 (Cubic d)) at hze
  rw [Sym2.mem_map] at hze
  obtain ⟨y, hye, rfl⟩ := hze
  rw [framedRestartSupport, Finset.mem_image] at hePhysical
  obtain ⟨f, hf, rfl⟩ := hePhysical
  change y ∈ Sym2.map (W.postRadialFrame b) (f : Sym2 (Cubic d)) at hye
  rw [Sym2.mem_map] at hye
  obtain ⟨w, hwf, rfl⟩ := hye
  apply W.postRadial_referenceCoord_add_one_lt_of_ne hm hmn hgeom hab hf hwf
  simp

/-- Weak endpoint separation retained for the existing target-freshness interface. -/
theorem RootRadialSeedProfile.postRadialRestartSupport_endpoint_coord_lt_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a) {R : Finset (Cubic d)}
    {e : CubicEdge d}
    (he : e ∈ (framedRestartSupport (W.physicalCenter b) b
      (oppositeTransverseRestartFlip b) m n R).image
        (W.postRadialFrame a).symm.mapEdgeSet)
    {z : Cubic d} (hze : z ∈ (e : Sym2 (Cubic d))) :
    z a.1 < (n : ℤ) := by
  have h := W.postRadialRestartSupport_endpoint_coord_add_one_lt_of_ne
    hm hmn hgeom hab he hze
  omega

/-- Endpoint freshness between two distinct root directions: after pulling the earlier
direction's restart support into the current frame, it is disjoint from the current seeded
target support. -/
theorem RootRadialSeedProfile.postRadialRestartSupport_targetEndpointFresh_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a) (R : Finset (Cubic d)) :
    Disjoint
      (cubicEdgeEndpointVertices
        ((framedRestartSupport (W.physicalCenter b) b
          (oppositeTransverseRestartFlip b) m n R).image
            (W.postRadialFrame a).symm.mapEdgeSet))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  apply disjoint_endpointVertices_seededBoundaryTargetSupport_of_coord_lt
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_cubicEdgeEndpointVertices_iff.mp hz
  exact W.postRadialRestartSupport_endpoint_coord_lt_of_ne
    hm hmn hgeom hab he hze

/-- A source update in a distinct root direction preserves the fact that all explored
endpoints lie behind the current direction's target face.  The old part follows from the
induction hypothesis, while every newly added edge lies in the distinct direction's framed
restart support and is handled by the pairwise steering geometry above. -/
theorem RootRadialSeedProfile.referenceEndpoint_coord_lt_next_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a)
    (S : SourceFiniteEdgeRevealState d) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hBehind : ∀ z ∈ cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)), z a.1 < (n : ℤ))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((S.next
        ((S.framedQuery (W.physicalCenter b) b
          (oppositeTransverseRestartFlip b)).restartSupport m n)
        p incremented X).referenceExploredEdges (W.postRadialFrame a))) :
    z a.1 < (n : ℤ) := by
  classical
  let Fa := W.postRadialFrame a
  let Qb := S.framedQuery (W.physicalCenter b) b
    (oppositeTransverseRestartFlip b)
  obtain ⟨e, heReference, hze⟩ :=
    mem_cubicEdgeEndpointVertices_iff.mp hz
  rw [SourceFiniteEdgeRevealState.referenceExploredEdges,
    Finset.mem_image] at heReference
  obtain ⟨f, hfNext, rfl⟩ := heReference
  have hfNext' : f ∈ S.nextExplored (Qb.restartSupport m n) p incremented X := by
    exact hfNext
  have hfAllowed := S.nextExplored_subset_explored_union_stageRegion
    (Qb.restartSupport m n) p incremented X hfNext'
  rw [Finset.mem_union] at hfAllowed
  rcases hfAllowed with hfOld | hfStage
  · apply hBehind z
    apply mem_cubicEdgeEndpointVertices_iff.mpr
    refine ⟨Fa.symm.mapEdgeSet f, ?_, hze⟩
    exact Finset.mem_image.mpr ⟨f, hfOld, rfl⟩
  · apply W.postRadialRestartSupport_endpoint_coord_lt_of_ne
      hm hmn hgeom hab (R := cubicEdgeEndpointVertices
        (S.referenceExploredEdges (W.postRadialFrame b)))
    · apply Finset.mem_image.mpr
      refine ⟨f, ?_, rfl⟩
      simpa [Qb, SourceFiniteEdgeRevealState.framedQuery,
        FramedRestartQuery.restartSupport,
        RootRadialSeedProfile.postRadialFrame] using hfStage
    · exact hze

/-- One source update in another direction preserves a full unused vertex layer before the
current target face.  This is the precise geometry required by Lemma 7.17, whose avoidance
hypothesis includes the vertex boundary of the explored region. -/
theorem RootRadialSeedProfile.referenceEndpoint_coord_add_one_lt_next_of_ne
    {d m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n)
    (hgeom : ∀ c : CubicDirection d,
      SeedBoxWithinBoundaryLayer d c.1 m n (W c).seedCenter.1)
    {a b : CubicDirection d} (hab : b ≠ a)
    (S : SourceFiniteEdgeRevealState d) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hBehind : ∀ z ∈ cubicEdgeEndpointVertices
      (S.referenceExploredEdges (W.postRadialFrame a)), z a.1 + 1 < (n : ℤ))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((S.next
        ((S.framedQuery (W.physicalCenter b) b
          (oppositeTransverseRestartFlip b)).restartSupport m n)
        p incremented X).referenceExploredEdges (W.postRadialFrame a))) :
    z a.1 + 1 < (n : ℤ) := by
  classical
  let Fa := W.postRadialFrame a
  let Qb := S.framedQuery (W.physicalCenter b) b
    (oppositeTransverseRestartFlip b)
  obtain ⟨e, heReference, hze⟩ :=
    mem_cubicEdgeEndpointVertices_iff.mp hz
  rw [SourceFiniteEdgeRevealState.referenceExploredEdges,
    Finset.mem_image] at heReference
  obtain ⟨f, hfNext, rfl⟩ := heReference
  have hfNext' : f ∈ S.nextExplored (Qb.restartSupport m n) p incremented X := hfNext
  have hfAllowed := S.nextExplored_subset_explored_union_stageRegion
    (Qb.restartSupport m n) p incremented X hfNext'
  rw [Finset.mem_union] at hfAllowed
  rcases hfAllowed with hfOld | hfStage
  · apply hBehind z
    apply mem_cubicEdgeEndpointVertices_iff.mpr
    refine ⟨Fa.symm.mapEdgeSet f, ?_, hze⟩
    exact Finset.mem_image.mpr ⟨f, hfOld, rfl⟩
  · apply W.postRadialRestartSupport_endpoint_coord_add_one_lt_of_ne
      hm hmn hgeom hab (R := cubicEdgeEndpointVertices
        (S.referenceExploredEdges (W.postRadialFrame b)))
    · apply Finset.mem_image.mpr
      refine ⟨f, ?_, rfl⟩
      simpa [Qb, SourceFiniteEdgeRevealState.framedQuery,
        FramedRestartQuery.restartSupport,
        RootRadialSeedProfile.postRadialFrame] using hfStage
    · exact hze

/-- Every endpoint examined by the simultaneous radial phase lies strictly behind the next
positive target face when pulled into the selected seed's post-radial frame. -/
theorem rootPostRadialSourceEdgeState_referenceEndpoint_coord_add_one_lt_of_geometry
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hgeom : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((rootPostRadialSourceEdgeState d m n p incremented X).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 + 1 < (n : ℤ) := by
  let F := W.postRadialFrame a
  obtain ⟨e, heReference, hze⟩ :=
    mem_cubicEdgeEndpointVertices_iff.mp hz
  rw [SourceFiniteEdgeRevealState.referenceExploredEdges,
    Finset.mem_image] at heReference
  obtain ⟨f, hfExplored, rfl⟩ := heReference
  change z ∈ Sym2.map F.symm (f : Sym2 (Cubic d)) at hze
  rw [Sym2.mem_map] at hze
  obtain ⟨w, hwf, hwz⟩ := hze
  have hwEq : w = F z := by
    apply F.injective
    simpa using congrArg F hwz
  subst w
  have hfRadial : f ∈ rootRadialExploredEdges d m n p incremented X := by
    rw [rootPostRadialSourceEdgeState_explored hm (Nat.le_of_lt hmn)
      p incremented X] at hfExplored
    exact hfExplored
  have hfWide : f ∈ cubicBoxEdges d cubicOrigin (n + 2 * m + 1) :=
    rootRadialEdgeSupport_subset_wideBox d m n
      (rootRadialExploredEdges_subset_support d m n p incremented X hfRadial)
  have hzPhysical : F z ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1) :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfWide hwf
  have hseedAxis : (W a).seedCenter.1 a.1 = (n + m + 1 : ℕ) :=
    seedCenter_axis_eq_of_boxWithinBoundaryLayer a.1 hgeom
  cases ha : a.2
  · have hphysicalAxis : W.physicalCenter a a.1 =
        -(n + m + 1 : ℕ) := by
      simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
        hseedAxis, cubicOrigin, ha]
    have hcoord := (mem_cubicMetricBox.mp hzPhysical) a.1
    simp [F, RootRadialSeedProfile.postRadialFrame, cubicRestartFrameFlip,
      hphysicalAxis, cubicOrigin, ha] at hcoord
    omega
  · have hphysicalAxis : W.physicalCenter a a.1 =
        (n + m + 1 : ℕ) := by
      simp [RootRadialSeedProfile.physicalCenter, cubicRestartFrameFlip,
        hseedAxis, cubicOrigin, ha]
    have hcoord := (mem_cubicMetricBox.mp hzPhysical) a.1
    simp [F, RootRadialSeedProfile.postRadialFrame, cubicRestartFrameFlip,
      hphysicalAxis, cubicOrigin, ha] at hcoord
    omega

/-- Weak post-radial endpoint separation retained for target-support freshness. -/
theorem rootPostRadialSourceEdgeState_referenceEndpoint_coord_lt_of_geometry
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hgeom : SeedBoxWithinBoundaryLayer d a.1 m n (W a).seedCenter.1)
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((rootPostRadialSourceEdgeState d m n p incremented X).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 < (n : ℤ) := by
  have h := rootPostRadialSourceEdgeState_referenceEndpoint_coord_add_one_lt_of_geometry
    hm hmn W a p incremented X hgeom hz
  omega

/-- Realization-facing one-layer post-radial endpoint bound. -/
theorem rootPostRadialSourceEdgeState_referenceEndpoint_coord_add_one_lt
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hW : (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((rootPostRadialSourceEdgeState d m n p incremented X).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 + 1 < (n : ℤ) :=
  rootPostRadialSourceEdgeState_referenceEndpoint_coord_add_one_lt_of_geometry
    hm hmn W a p incremented X hW.2.2.1 hz

/-- Realization-facing wrapper for the geometric post-radial endpoint bound. -/
theorem rootPostRadialSourceEdgeState_referenceEndpoint_coord_lt
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hW : (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X))
    {z : Cubic d}
    (hz : z ∈ cubicEdgeEndpointVertices
      ((rootPostRadialSourceEdgeState d m n p incremented X).referenceExploredEdges
        (W.postRadialFrame a))) :
    z a.1 < (n : ℤ) :=
  rootPostRadialSourceEdgeState_referenceEndpoint_coord_lt_of_geometry
    hm hmn W a p incremented X hW.2.2.1 hz

/-- The literal post-radial source state has not examined any endpoint of the next target from
the selected seed.  This is the concrete first instance of Grimmett's steering-freshness claim:
the simultaneous radial support lies in `B(n+2m+1)`, whereas the selected center is exactly
`n+m+1` units in direction `a`, so its pullback lies strictly behind the new `n`-face. -/
theorem rootPostRadialSourceEdgeState_targetEndpointFresh
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hW : (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X)) :
    let S := rootPostRadialSourceEdgeState d m n p incremented X
    let F := W.postRadialFrame a
    Disjoint (cubicEdgeEndpointVertices (S.referenceExploredEdges F))
      (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) := by
  dsimp only
  apply disjoint_endpointVertices_seededBoundaryTargetSupport_of_coord_lt
  intro z hz
  exact rootPostRadialSourceEdgeState_referenceEndpoint_coord_lt
    hm hmn W a p incremented X hW hz

/-- Consequently, the literal first post-radial query has exactly the source boundary
intersected with its reveal support; no extra target coordinate has been examined. -/
theorem rootPostRadial_framedQuery_boundarySupport_eq
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hW : (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X)) :
    let S := rootPostRadialSourceEdgeState d m n p incremented X
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    Q.boundarySupport n = S.boundary ∩ Q.restartSupport m n := by
  dsimp only
  apply SourceFiniteEdgeRevealState.framedQuery_boundarySupport_eq_boundary_inter_restartSupport_of_targetEndpointFresh
  simpa [RootRadialSeedProfile.postRadialFrame] using
    rootPostRadialSourceEdgeState_targetEndpointFresh hm hmn W a p incremented X hW

/-- The literal first post-radial query is also disjoint from the edge set already explored by
the simultaneous radial phase. -/
theorem rootPostRadial_framedQuery_explored_disjoint_restartSupport
    {d m n : ℕ} [NeZero d] (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (a : CubicDirection d)
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hW : (W a).IsRealized
      (framedReferenceThresholdConfiguration cubicOrigin a
        (rootRadialTransverseFlip a) p X)) :
    let S := rootPostRadialSourceEdgeState d m n p incremented X
    let Q := S.framedQuery (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a)
    Disjoint (S.explored : Set (CubicEdge d))
      (Q.restartSupport m n : Set (CubicEdge d)) := by
  dsimp only
  apply SourceFiniteEdgeRevealState.framedQuery_explored_disjoint_restartSupport_of_targetEndpointFresh
  simpa [RootRadialSeedProfile.postRadialFrame] using
    rootPostRadialSourceEdgeState_targetEndpointFresh hm hmn W a p incremented X hW

/-- The radial root event simultaneously supplies all concrete seed centers, their final-density
connections to the central seed, and the endpoint-box steering certificate needed for the
second root phase. -/
theorem exists_rootRadialSeedProfile_with_steering_of_mem
    {d m n : ℕ} (hmn : m + 1 < n) {X : CubicEdge d → ℝ}
    {p pFinal : I} {delta : ℝ}
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hdeltaFinal : delta ≤ (pFinal : ℝ))
    (hroot : X ∈ rootRadialEvent d m n p delta) :
    ∃ W : RootRadialSeedProfile d m n,
      ∀ a : CubicDirection d,
        rootRadialSelectedSeed d m n pFinal a X = some (W a) ∧
        (W a).IsRealized
          (framedReferenceThresholdConfiguration cubicOrigin a
            (rootRadialTransverseFlip a) pFinal X) ∧
        (∃ z ∈ cubicMetricBox d cubicOrigin m,
          thresholdConfiguration pFinal X ∈
            connectionEventIn d (cubicBoxEdges d cubicOrigin n)
              (cubicRestartFrameIso cubicOrigin a (rootRadialTransverseFlip a) z)
              (W.physicalBoundaryPoint a)) ∧
        W.postRadialRestartRegion a ⊆
          (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
            (cubicMetricBox d
              (grimmettMarstrandSiteCenter (m + n + 1)
                (cubicStepFrom cubicOrigin a))
              (2 * (m + n + 1)) : Set (Cubic d)) := by
  obtain ⟨W, hW⟩ := exists_rootRadialSeedProfile_of_mem
    hmn hpFinal hdeltaFinal hroot
  refine ⟨W, fun a ↦ ?_⟩
  have ha := hW a
  refine ⟨ha.1, ha.2.1, ha.2.2, ?_⟩
  exact W.postRadialRestartRegion_subset_endpointBoxes a ha.2.1

end Percolation
