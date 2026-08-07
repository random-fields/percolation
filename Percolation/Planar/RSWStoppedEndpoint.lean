import Percolation.Planar.RSWStoppedContact

/-!
# The endpoint-split square crossing in stopped-interface coordinates

The final square-root factor in Grimmett's Lemma 11.73 is most naturally used after a
quarter-turn and an upward translation.  In these coordinates it is a bottom--top crossing of
`[0,2n] × [0,2n]` whose bottom endpoint lies in the right half.  The witness extractor below
also trims repeated visits to the bottom and top sides, so later incidence arguments may use the
literal cyclic order of the two bottom endpoints.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Quarter-turn the centered square and translate it to `[0,2n] × [0,2n]`. -/
def rswStoppedQuarterTurnIso (n : ℕ) : squareGraph ≃g squareGraph :=
  (brSquareQuarterTurnIso n).trans (rswStoppedSquareTranslationIso n)

@[simp]
theorem rswStoppedQuarterTurnIso_zero (n : ℕ) (x : SquareVertex) :
    rswStoppedQuarterTurnIso n x 0 = x 1 + (n : ℤ) := by
  simp [rswStoppedQuarterTurnIso]

@[simp]
theorem rswStoppedQuarterTurnIso_one (n : ℕ) (x : SquareVertex) :
    rswStoppedQuarterTurnIso n x 1 = x 0 := by
  simp [rswStoppedQuarterTurnIso]

/-- The clean upper-half-start RSW event in stopped-interface coordinates. -/
def rswStoppedRightBottomVerticalCrossingEvent (n : ℕ) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (rswStoppedQuarterTurnIso n)
    (rswSquareCleanUpperStartCrossingEvent n)

theorem measurableSet_rswStoppedRightBottomVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (rswStoppedRightBottomVerticalCrossingEvent n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_rswSquareCleanUpperStartCrossingEvent n)

theorem isIncreasingEvent_rswStoppedRightBottomVerticalCrossingEvent (n : ℕ) :
    IsIncreasingEvent (rswStoppedRightBottomVerticalCrossingEvent n) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_rswSquareCleanUpperStartCrossingEvent n)

theorem bernoulliBondMeasure_real_rswStoppedRightBottomVerticalCrossingEvent
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real
      (rswStoppedRightBottomVerticalCrossingEvent n) =
      (bernoulliBondMeasure 2 p).real
        (rswSquareCleanUpperStartCrossingEvent n) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_rswSquareCleanUpperStartCrossingEvent n)

theorem one_sub_sqrt_rswSquare_le_stoppedRightBottomVerticalProbability
    (p : I) (n : ℕ) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (rswStoppedRightBottomVerticalCrossingEvent n) := by
  rw [bernoulliBondMeasure_real_rswStoppedRightBottomVerticalCrossingEvent]
  exact one_sub_sqrt_rswSquare_le_cleanUpperStartCrossingProbability p n

private theorem walkEdgeFinset_map_subset_rswStoppedSquareEdges_quarterTurn
    {n : ℕ} {u v : SquareVertex}
    (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ squareBoundaryFreeRectangleEdges (2 * n) n) :
    walkEdgeFinset (w.map (rswStoppedQuarterTurnIso n).toHom) ⊆
      rswStoppedSquareEdges n := by
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map, List.mem_map] at he
  rcases he with ⟨f, hf, hfe⟩
  let fe : SquareEdge := ⟨f, w.edges_subset_edgeSet hf⟩
  have hfeAllowed : fe ∈ squareBoundaryFreeRectangleEdges (2 * n) n :=
    hw ((mem_walkEdgeFinset_iff w fe).mpr hf)
  have hquarter : (brSquareQuarterTurnIso n).mapEdgeSet fe ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    rw [← brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges n]
    exact Finset.mem_image.mpr ⟨fe, hfeAllowed, rfl⟩
  rw [rswStoppedSquareEdges, Finset.mem_image]
  refine ⟨(brSquareQuarterTurnIso n).mapEdgeSet fe, hquarter, ?_⟩
  apply Subtype.ext
  change Sym2.map (rswStoppedSquareTranslationIso n)
      (Sym2.map (brSquareQuarterTurnIso n) f) = (e : Sym2 SquareVertex)
  rw [Sym2.map_map]
  simpa [rswStoppedQuarterTurnIso, Function.comp_def] using hfe

/-- A member of the placed half-start event has a simple open bottom--top witness.  Its only
visits to the bottom and top boundary lines are its displayed endpoints, and its bottom endpoint
lies in the right half. -/
theorem exists_normalized_rswStoppedRightBottomVerticalPath_of_mem
    {n : ℕ} {omega : EdgeConfiguration 2}
    (homega : omega ∈ rswStoppedRightBottomVerticalCrossingEvent n) :
    ∃ b t : SquareVertex, ∃ q : squareGraph.Walk b t,
      (n : ℤ) ≤ b 0 ∧ b 0 ≤ 2 * (n : ℤ) ∧ b 1 = 0 ∧
      0 ≤ t 0 ∧ t 0 ≤ 2 * (n : ℤ) ∧ t 1 = 2 * (n : ℤ) ∧
      walkIsOpen omega q ∧ q.IsPath ∧
      walkEdgeFinset q ⊆ rswStoppedSquareEdges n ∧
      (∀ z ∈ q.support, z 1 = 0 → z = b) ∧
      (∀ z ∈ q.support, z 1 = 2 * (n : ℤ) → z = t) ∧
      ∀ z ∈ q.support, z ≠ b → z ≠ t →
        0 < z 1 ∧ z 1 < 2 * (n : ℤ) := by
  classical
  change cubicGraphIsoConfigurationPullback (rswStoppedQuarterTurnIso n) omega ∈
    rswSquareCleanUpperStartCrossingEvent n at homega
  simp only [rswSquareCleanUpperStartCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := homega
  let F := rswStoppedQuarterTurnIso n
  let W := w.map F.toHom
  have hWOpen : walkIsOpen omega W :=
    walkIsOpen_map_cubicGraphIso F w hwOpen
  have hWEdges : walkEdgeFinset W ⊆ rswStoppedSquareEdges n := by
    simpa [W, F] using
      walkEdgeFinset_map_subset_rswStoppedSquareEdges_quarterTurn w
        (fun e he ↦ (Finset.mem_filter.mp (hwEdges he)).1)
  have hx' := mem_rswSquareUpperLeftSide_iff.mp hx
  have hy' := mem_squareRectangleRight_iff.mp hy
  have hstart : F x 1 = 0 := by
    simp [F, hx'.1]
  have hend : 2 * (n : ℤ) ≤ F y 1 := by
    simp [F, hy'.1]
  obtain ⟨b, t, q, hbLevel, htLevel, hqOpen, hqPath,
      hqEdgesOriginal, hqSupport, hbUnique, htUnique⟩ :=
    exists_open_cubicPath_between_levels_normalized W hWOpen
      (1 : Fin 2) 0 (2 * (n : ℤ)) (by omega) hstart.le hend
  have hqEdges : walkEdgeFinset q ⊆ rswStoppedSquareEdges n := by
    intro e he
    exact hWEdges ((mem_walkEdgeFinset_iff W e).mpr
      (hqEdgesOriginal ((mem_walkEdgeFinset_iff q e).mp he)))
  have hWCoords : ∀ z ∈ W.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    simp only [W, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨a, ha, rfl⟩
    have haRect : a ∈ squareRectangleVertices (2 * n) n := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at ha
      rcases ha with rfl | ⟨e, he, hae⟩
      · exact (Finset.mem_filter.mp hy).1
      · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
        have heBoundaryFree : ee ∈
            squareBoundaryFreeRectangleEdges (2 * n) n :=
          (Finset.mem_filter.mp
            (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))).1
        exact endpoint_mem_squareRectangle_of_edge_mem
          (Finset.mem_filter.mp heBoundaryFree).1 hae
    have ha' := mem_squareRectangleVertices_iff.mp haRect
    change 0 ≤ F a 0 ∧ F a 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ F a 1 ∧ F a 1 ≤ 2 * (n : ℤ)
    simp only [F, rswStoppedQuarterTurnIso_zero,
      rswStoppedQuarterTurnIso_one]
    omega
  have hbW := hqSupport b q.start_mem_support
  have htW := hqSupport t q.end_mem_support
  have hbCoords := hWCoords b hbW.2.2
  have htCoords := hWCoords t htW.2.2
  have hwLeftUnique : ∀ a ∈ w.support, a 0 = 0 → a = x := by
    intro a ha ha0
    by_cases hn0 : n = 0
    · have haRect : a ∈ squareRectangleVertices (2 * n) n := by
        rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at ha
        rcases ha with rfl | ⟨e, he, hae⟩
        · exact (Finset.mem_filter.mp hy).1
        · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
          have heBoundaryFree : ee ∈
              squareBoundaryFreeRectangleEdges (2 * n) n :=
            (Finset.mem_filter.mp
              (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))).1
          exact endpoint_mem_squareRectangle_of_edge_mem
            (Finset.mem_filter.mp heBoundaryFree).1 hae
      have haCoords := mem_squareRectangleVertices_iff.mp haRect
      subst n
      ext i
      fin_cases i <;> norm_num at haCoords hx' ⊢ <;> omega
    · rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at ha
      rcases ha with rfl | ⟨e, he, hae⟩
      · have hy0 := hy'.1
        omega
      · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
        have heClean := Finset.mem_filter.mp
          (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he))
        exact heClean.2 a hae ha0
  have hWBottomUnique : ∀ z ∈ W.support, z 1 = 0 → z = F x := by
    intro z hz hz0
    simp only [W, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have ha0 : a 0 = 0 := by
      change rswStoppedQuarterTurnIso n a 1 = 0 at hz0
      simpa only [rswStoppedQuarterTurnIso_one] using hz0
    exact congrArg F (hwLeftUnique a ha ha0)
  refine ⟨b, t, q, ?_, ?_, hbLevel, ?_, ?_, htLevel,
    hqOpen, hqPath, ?_, hbUnique, htUnique, ?_⟩
  · have hbxSource : (n : ℤ) ≤ F x 0 := by
      simp only [F, rswStoppedQuarterTurnIso_zero]
      omega
    have hbPrefix := hbW.1
    -- Normalization retains a subpath of `W`; its bottom endpoint is the unique bottom visit
    -- of the original placed crossing, namely `F x`.
    have hbEq : b = F x := by
      exact hWBottomUnique b hbW.2.2 hbLevel
    simpa [hbEq] using hbxSource
  · exact hbCoords.2.1
  · exact htCoords.1
  · exact htCoords.2.1
  · intro e he
    exact hqEdges he
  · intro z hz hzb hzt
    have hzBounds := hqSupport z hz
    have hzNeLower : z 1 ≠ 0 := by
      intro hz0
      exact hzb (hbUnique z hz hz0)
    have hzNeUpper : z 1 ≠ 2 * (n : ℤ) := by
      intro hzTop
      exact hzt (htUnique z hz hzTop)
    omega

end

end Percolation
