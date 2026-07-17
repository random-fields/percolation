import Percolation.Critical.DynamicRestartCertificate

/-!
# Full signed steering frames

The exit direction alone does not determine a Grimmett--Marstrand steering move.  On pp. 159--
162 the transverse quadrant is chosen from the location of the inlet seed; in the first move all
transverse signs are reversed to turn `T(n)` into `T*(n)`.  This file therefore extends the older
axis-only orientation by an explicit transverse sign mask.  Keeping that mask in the public data
prevents a formally valid but geometrically unfaithful block program.
-/

namespace Percolation

/-- Physical displacement of `target` from `base`, expressed in the fixed cubic coordinates.
Compensating steering depends on this signed displacement after all preceding frame flips. -/
def cubicRelativePosition {d : ℕ} (base target : Cubic d) : Cubic d :=
  fun j ↦ target j - base j

@[simp]
theorem cubicRelativePosition_apply {d : ℕ} (base target : Cubic d) (j : Fin d) :
    cubicRelativePosition base target j = target j - base j :=
  rfl

@[simp]
theorem cubicRelativePosition_self {d : ℕ} (base : Cubic d) :
    cubicRelativePosition base base = cubicOrigin := by
  ext j
  simp [cubicRelativePosition, cubicOrigin]

/-- Coordinate flips for a restart frame.  The exit coordinate is fixed by the signed direction;
all other coordinates are controlled independently by `transverseFlip`. -/
def cubicRestartFrameFlip {d : ℕ}
    (a : CubicDirection d) (transverseFlip : Fin d → Bool) : Fin d → Bool :=
  fun j ↦ if j = a.1 then decide (a.2 = false) else transverseFlip j

/-- Full signed-coordinate restart frame followed by translation to the physical center. -/
def cubicRestartFrameIso {d : ℕ}
    (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) : cubicGraph d ≃g cubicGraph d :=
  (cubicSignedCoordinateIso (cubicRestartFrameFlip a transverseFlip)).trans
    (cubicTranslationIso cubicOrigin center)

@[simp]
theorem cubicRestartFrameIso_apply
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (z : Cubic d) (j : Fin d) :
    cubicRestartFrameIso center a transverseFlip z j =
      (if cubicRestartFrameFlip a transverseFlip j then -z j else z j) + center j := by
  simp [cubicRestartFrameIso, cubicSignedCoordinateIso, cubicSignedCoordinateEquiv,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin]

@[simp]
theorem cubicRestartFrameIso_origin
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) :
    cubicRestartFrameIso center a transverseFlip cubicOrigin = center := by
  ext j
  simp [cubicOrigin]

/-- The reference positive exit step is sent to the requested signed physical step, regardless
of the transverse steering mask. -/
theorem cubicRestartFrameIso_positiveStep
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) :
    cubicRestartFrameIso center a transverseFlip
        (cubicStepFrom cubicOrigin (a.1, true)) =
      cubicStepFrom center a := by
  rcases a with ⟨i, positive⟩
  ext j
  by_cases hji : j = i
  · subst j
    cases positive <;>
      simp [cubicRestartFrameFlip, cubicStepFrom, cubicDirectionIncrement, cubicOrigin] <;>
      ring
  · simp [cubicRestartFrameFlip, cubicStepFrom, cubicDirectionIncrement,
      cubicOrigin, hji]

/-- Every full restart frame is an exact coordinate-box isometry. -/
theorem cubicRestartFrameIso_mem_cubicMetricBox_iff
    {d n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) (x z : Cubic d) :
    cubicRestartFrameIso center a transverseFlip z ∈
        cubicMetricBox d (cubicRestartFrameIso center a transverseFlip x) n ↔
      z ∈ cubicMetricBox d x n := by
  rw [mem_cubicMetricBox, mem_cubicMetricBox]
  constructor <;> intro h j
  · have hj := h j
    by_cases hflip : cubicRestartFrameFlip a transverseFlip j <;>
      simp [cubicRestartFrameIso_apply, hflip] at hj ⊢ <;> omega
  · have hj := h j
    by_cases hflip : cubicRestartFrameFlip a transverseFlip j <;>
      simp [cubicRestartFrameIso_apply, hflip] at hj ⊢ <;> omega

/-- The reference box-edge support is carried exactly to the physical centered box for every
choice of transverse steering signs. -/
theorem cubicRestartFrameIso_image_cubicBoxEdges_eq
    {d n : ℕ} (center : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool) :
    (cubicBoxEdges d cubicOrigin n).image
        (cubicRestartFrameIso center a transverseFlip).mapEdgeSet =
      cubicBoxEdges d center n := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    apply mem_cubicBoxEdges_of_endpoints
    intro z hz
    change z ∈ Sym2.map (cubicRestartFrameIso center a transverseFlip)
      (f : Sym2 (Cubic d)) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hf hw
    have himage :=
      (cubicRestartFrameIso_mem_cubicMetricBox_iff
        center a transverseFlip cubicOrigin w).2 hwBox
    simpa [cubicOrigin] using himage
  · rw [Finset.card_image_of_injective _
      (cubicRestartFrameIso center a transverseFlip).mapEdgeSet.injective]
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

/-- Axis-only orientation is the special frame with no transverse flips. -/
theorem cubicRestartFrameIso_noTransverse_eq
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) :
    cubicRestartFrameIso center a (fun _ ↦ false) =
      cubicDirectionOrientationIso center a := by
  ext z j
  by_cases hja : j = a.1
  · subst j
    cases ha : a.2 <;>
      simp [cubicRestartFrameIso_apply, cubicDirectionOrientationIso_apply,
        cubicRestartFrameFlip, cubicDirectionOrientationFlip, ha]
  · simp [cubicRestartFrameIso_apply, cubicDirectionOrientationIso_apply,
      cubicRestartFrameFlip, cubicDirectionOrientationFlip, hja]

/-- Mask used by the first steering move: reverse every transverse coordinate while preserving
the exit-coordinate sign selected by `a`. -/
def oppositeTransverseRestartFlip {d : ℕ} (a : CubicDirection d) : Fin d → Bool :=
  fun j ↦ decide (j ≠ a.1)

/-- Reversing all transverse signs carries the standard positive seed quadrant exactly to the
steered quadrant `T*(n)` used in the first Grimmett--Marstrand move.  This is an equality of the
actual finite target sets, rather than only a bounding-box inclusion. -/
theorem cubicRestartFrameIso_mem_steeredPositiveBoundaryQuadrant_iff
    {d n : ℕ} (i : Fin d) (z : Cubic d) :
    cubicRestartFrameIso cubicOrigin (i, true)
        (oppositeTransverseRestartFlip (i, true)) z ∈
        steeredPositiveBoundaryQuadrant d i n ↔
      z ∈ seededBoundaryQuadrant d i n := by
  rw [mem_steeredPositiveBoundaryQuadrant_iff,
    mem_seededBoundaryQuadrant_iff]
  constructor
  · rintro ⟨hface, htransverse⟩
    rw [mem_cubicBoxFace] at hface ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin] using hface.1
    · intro j hji
      have hjBounds := hface.2 j hji
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin, hji] at hjBounds
      simp [cubicOrigin]
      constructor <;> omega
    · intro j hji
      have hjNonpos := htransverse j hji
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin, hji] at hjNonpos
      omega
  · rintro ⟨hface, htransverse⟩
    rw [mem_cubicBoxFace] at hface ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin] using hface.1
    · intro j hji
      have hjBounds := hface.2 j hji
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin, hji] at hjBounds ⊢
      constructor <;> omega
    · intro j hji
      have hjNonneg := htransverse j hji
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        oppositeTransverseRestartFlip, cubicOrigin, hji]
      omega

theorem cubicRestartFrameIso_image_seededBoundaryQuadrant_eq_steered
    {d n : ℕ} (i : Fin d) :
    (seededBoundaryQuadrant d i n).image
        (cubicRestartFrameIso cubicOrigin (i, true)
          (oppositeTransverseRestartFlip (i, true))) =
      steeredPositiveBoundaryQuadrant d i n := by
  classical
  ext z
  constructor
  · rw [Finset.mem_image]
    rintro ⟨w, hw, rfl⟩
    exact (cubicRestartFrameIso_mem_steeredPositiveBoundaryQuadrant_iff i w).2 hw
  · intro hz
    let F := cubicRestartFrameIso cubicOrigin (i, true)
      (oppositeTransverseRestartFlip (i, true))
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [Finset.mem_image]
    exact ⟨w,
      (cubicRestartFrameIso_mem_steeredPositiveBoundaryQuadrant_iff i w).1 hz,
      rfl⟩

/-- Reversing all transverse coordinates carries the whole layered target `T(m,n)` into the
opposite layered target `T*(m,n)`, not only its boundary face. -/
theorem cubicRestartFrameIso_seededBoundaryLayerRegion_subset_steered
    {d m n : ℕ} (i : Fin d) :
    cubicGraphIsoRegion
        (cubicRestartFrameIso cubicOrigin (i, true)
          (oppositeTransverseRestartFlip (i, true)))
        (seededBoundaryLayerRegion d i m n) ⊆
      steeredPositiveBoundaryLayerRegion d i m n := by
  rintro z ⟨w, ⟨r, hr1, hr2, y, hy, rfl⟩, rfl⟩
  let F := cubicRestartFrameIso cubicOrigin (i, true)
    (oppositeTransverseRestartFlip (i, true))
  refine ⟨r, hr1, hr2, F y,
    (cubicRestartFrameIso_mem_steeredPositiveBoundaryQuadrant_iff i y).2 hy, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp [F, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      cubicOrigin, cubicTranslateAlongCoordinate]
  · simp [F, cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      oppositeTransverseRestartFlip, cubicOrigin, hji,
      cubicTranslateAlongCoordinate_of_ne]

/-- Transverse sign mask from p. 161: if the inlet seed is displaced positively in coordinate
`j`, reverse the reference quadrant in that coordinate; otherwise retain its positive side. -/
def inletCompensatingTransverseFlip {d : ℕ}
    (a : CubicDirection d) (inletCenter : Cubic d) : Fin d → Bool :=
  fun j ↦ decide (j ≠ a.1 ∧ 0 < inletCenter j)

/-- The inlet compensation mask only reads coordinates transverse to the steering axis. -/
theorem inletCompensatingTransverseFlip_eq_of_eq_off_axis
    {d : ℕ} (a : CubicDirection d) (u v : Cubic d)
    (h : ∀ j, j ≠ a.1 → u j = v j) :
    inletCompensatingTransverseFlip a u =
      inletCompensatingTransverseFlip a v := by
  funext j
  by_cases hja : j = a.1
  · simp [inletCompensatingTransverseFlip, hja]
  · simp [inletCompensatingTransverseFlip, hja, h j hja]

/-- Changing the reference origin only along the steering axis does not change the transverse
compensation computed from a fixed physical inlet. -/
theorem inletCompensatingTransverseFlip_relative_eq_of_eq_off_axis
    {d : ℕ} (a : CubicDirection d) (reference₁ reference₂ inlet : Cubic d)
    (h : ∀ j, j ≠ a.1 → reference₁ j = reference₂ j) :
    inletCompensatingTransverseFlip a
        (cubicRelativePosition reference₁ inlet) =
      inletCompensatingTransverseFlip a
        (cubicRelativePosition reference₂ inlet) := by
  apply inletCompensatingTransverseFlip_eq_of_eq_off_axis
  intro j hja
  simp [cubicRelativePosition, h j hja]

/-- The corresponding source region `T_a(n)`.  When an inlet coordinate is zero the source
inequality imposes no sign condition; our oriented image chooses its nonnegative half, which is
a subset and hence retains the required steering containment. -/
noncomputable def inletCompensatingBoundaryRegion
    (d : ℕ) (i : Fin d) (inletCenter : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  (cubicBoxFace d cubicOrigin n i true).filter fun x ↦
    ∀ j : Fin d, j ≠ i → x j * inletCenter j ≤ 0

@[simp]
theorem mem_inletCompensatingBoundaryRegion_iff
    {d n : ℕ} {i : Fin d} {inletCenter x : Cubic d} :
    x ∈ inletCompensatingBoundaryRegion d i inletCenter n ↔
      x ∈ cubicBoxFace d cubicOrigin n i true ∧
        ∀ j : Fin d, j ≠ i → x j * inletCenter j ≤ 0 := by
  classical
  simp [inletCompensatingBoundaryRegion]

/-- The full-frame image of the reference quadrant obeys Grimmett's compensating sign
inequality in every transverse coordinate, including the zero-coordinate endpoint. -/
theorem cubicRestartFrameIso_mem_inletCompensatingBoundaryRegion
    {d n : ℕ} (i : Fin d) (inletCenter : Cubic d)
    {z : Cubic d} (hz : z ∈ seededBoundaryQuadrant d i n) :
    cubicRestartFrameIso cubicOrigin (i, true)
        (inletCompensatingTransverseFlip (i, true) inletCenter) z ∈
      inletCompensatingBoundaryRegion d i inletCenter n := by
  rw [mem_inletCompensatingBoundaryRegion_iff, mem_cubicBoxFace]
  have hzData := mem_seededBoundaryQuadrant_iff.mp hz
  have hzFace := mem_cubicBoxFace.mp hzData.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
      inletCompensatingTransverseFlip, cubicOrigin] using hzFace.1
  · intro j hji
    have hjBounds := hzFace.2 j hji
    by_cases hpos : 0 < inletCenter j
    · simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        inletCompensatingTransverseFlip, cubicOrigin, hji, hpos]
      simp [cubicOrigin] at hjBounds
      constructor <;> omega
    · simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        inletCompensatingTransverseFlip, cubicOrigin, hji, hpos]
      simpa [cubicOrigin] using hjBounds
  · intro j hji
    have hzNonneg := hzData.2 j hji
    by_cases hpos : 0 < inletCenter j
    · simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        inletCompensatingTransverseFlip, cubicOrigin, hji, hpos]
      exact hzNonneg
    · simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        inletCompensatingTransverseFlip, cubicOrigin, hji, hpos]
      exact mul_nonpos_of_nonneg_of_nonpos hzNonneg (le_of_not_gt hpos)

/-- A second restart using the signed displacement selected by the first restart exactly
implements Grimmett's transverse reversal in the first frame's reference coordinates.  This
identity is the algebraic reason the two applications assigned to one outgoing branch do not
drift in a flipped transverse direction. -/
theorem cubicRestartFrameIso_inletCompensating_comp
    {d : ℕ} (center c : Cubic d) (a : CubicDirection d)
    (transverseFlip : Fin d → Bool)
    (hpos : ∀ j, j ≠ a.1 → 0 < c j) (z : Cubic d) :
    let target := cubicRestartFrameIso center a transverseFlip c
    cubicRestartFrameIso target a
        (inletCompensatingTransverseFlip a
          (cubicRelativePosition center target)) z =
      cubicRestartFrameIso center a transverseFlip
        (cubicTranslate cubicOrigin c
          (cubicRestartFrameIso cubicOrigin (a.1, true)
            (oppositeTransverseRestartFlip (a.1, true)) z)) := by
  dsimp only
  ext j
  by_cases hja : j = a.1
  · subst j
    rcases a with ⟨i, positive⟩
    cases positive <;>
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        cubicRelativePosition, inletCompensatingTransverseFlip,
        oppositeTransverseRestartFlip, cubicTranslate, cubicOrigin] <;>
      ring
  · have hc : 0 < c j := hpos j hja
    have hcneg : ¬c j < 0 := by omega
    have hnegc : ¬0 < -c j := by omega
    by_cases hflip : transverseFlip j
    · have hrelative : cubicRelativePosition center
          (cubicRestartFrameIso center a transverseFlip c) j = -c j := by
        simp [cubicRelativePosition, cubicRestartFrameIso_apply,
          cubicRestartFrameFlip, hja, hflip]
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        cubicRelativePosition, inletCompensatingTransverseFlip,
        oppositeTransverseRestartFlip, cubicTranslate, cubicOrigin,
        hja, hflip, hrelative, hc, hcneg, hnegc]
      ring
    · have hrelative : cubicRelativePosition center
          (cubicRestartFrameIso center a transverseFlip c) j = c j := by
        simp [cubicRelativePosition, cubicRestartFrameIso_apply,
          cubicRestartFrameFlip, hja, hflip]
      simp [cubicRestartFrameIso_apply, cubicRestartFrameFlip,
        cubicRelativePosition, inletCompensatingTransverseFlip,
        oppositeTransverseRestartFlip, cubicTranslate, cubicOrigin,
        hja, hflip, hrelative, hc, hcneg, hnegc]
      ring

end Percolation
