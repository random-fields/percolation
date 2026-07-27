import Percolation.Bernoulli.Inhomogeneous
import Percolation.Planar.BondCrossingInterface
import Percolation.Planar.RSWPlacements
import Percolation.Planar.SquareCritical

/-!
# Finite bond-crossing duality

For the centered self-dual rectangle `[0,2n+1] × [-n,n]`, failure of a primal open
left--right crossing creates a shifted-dual open bottom--top interface.  A quarter-turn and
translation sends that interface back to a left--right crossing of the same rectangle.  At
density `1/2`, complementation, dual-edge reindexing, and this lattice automorphism all preserve
the Bernoulli law.  This gives a uniform half-density crossing lower bound without an external
planar-topology axiom.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval Sym2

/-- The quarter-turn which sends the shifted-dual rectangle
`[-1,2n+1] × [-n-1,n]` to the primal coordinate frame. -/
def centeredRectangleDualityIso (n : ℕ) : squareGraph ≃g squareGraph :=
  squareCrossingQuarterTurnIso
    (squareVertex (n : ℤ) (-(n : ℤ) - 1)) cubicOrigin

@[simp]
theorem centeredRectangleDualityIso_apply_zero (n : ℕ) (z : SquareVertex) :
    centeredRectangleDualityIso n z 0 = z 1 + (n : ℤ) + 1 := by
  simp [centeredRectangleDualityIso, squareCrossingQuarterTurnIso,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex,
    cubicOrigin]
  ring

@[simp]
theorem centeredRectangleDualityIso_apply_one (n : ℕ) (z : SquareVertex) :
    centeredRectangleDualityIso n z 1 = z 0 - (n : ℤ) := by
  simp [centeredRectangleDualityIso, squareCrossingQuarterTurnIso,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex,
    cubicOrigin]
  ring

/-- Complement primal bonds, pass to the shifted dual, and rotate back to the primal frame. -/
noncomputable def rotatedDualSquareConfiguration
    (n : ℕ) (ω : EdgeConfiguration 2) : EdgeConfiguration 2 :=
  cubicGraphIsoConfigurationPullback (centeredRectangleDualityIso n).symm
    (dualSquareConfiguration ω)

private theorem interfaceDualGraphWalk_support_bounds
    {n : ℕ} (hn : 0 < n) {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent (2 * n + 1) n)
    {b t : DualSquareVertex}
    (hb : b ∈ siteRectangleBottomInterfaceDualVertices (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω))
    (ht : t ∈ siteRectangleTopInterfaceDualVertices (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω))
    (w : (siteRectangleInterfaceDualGraph (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω)).Walk b t)
    {z : DualSquareVertex} (hz : z ∈ w.support) :
    0 ≤ z 0 ∧ z 0 < (2 * n + 1 : ℕ) ∧ -(n : ℤ) - 1 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have hbData := mem_siteRectangleBottomInterfaceDualVertices_iff.mp hb
  have htData := mem_siteRectangleTopInterfaceDualVertices_iff.mp ht
  have hbt : b ≠ t := by
    intro h
    subst t
    omega
  have hwNotNil : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne hbt
  rcases (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hwNotNil).mp hz with
    ⟨e, he, hze⟩
  have heGraph : e ∈
      (siteRectangleInterfaceDualGraph (2 * n + 1) n
        (bondRectangleLeftReachableSet (2 * n + 1) n ω)).edgeSet :=
    w.edges_subset_edgeSet he
  rw [mem_siteRectangleInterfaceDualGraph_edgeSet_iff] at heGraph
  rcases heGraph with ⟨heDual, heInterface⟩
  rw [mem_siteRectangleInterfaceDualEdges_iff] at heInterface
  rcases heInterface with ⟨a, ha, hae⟩
  have hza : z ∈
      (squarePositiveEdgeDualCrossingEmbedding a : Sym2 DualSquareVertex) := by
    have hval := congrArg Subtype.val hae
    rw [hval]
    exact hze
  exact interfaceDualVertex_bounds_of_bond_not_crossing hno ha hza

private theorem mapped_interfaceDualGraphWalk_support_mem_rectangle
    {n : ℕ} (hn : 0 < n) {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent (2 * n + 1) n)
    {b t : DualSquareVertex}
    (hb : b ∈ siteRectangleBottomInterfaceDualVertices (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω))
    (ht : t ∈ siteRectangleTopInterfaceDualVertices (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω))
    (w : (siteRectangleInterfaceDualGraph (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω)).Walk b t)
    {z : SquareVertex}
    (hz : z ∈ ((bondRectangleInterfaceDualGraphWalk w).map
      (centeredRectangleDualityIso n).toHom).support) :
    z ∈ squareRectangleVertices (2 * n + 1) n := by
  rw [SimpleGraph.Walk.support_map] at hz
  rcases List.mem_map.mp hz with ⟨z', hz', rfl⟩
  let F := SimpleGraph.Hom.ofLE
    (siteRectangleInterfaceDualGraph_le_dualSquareGraph (2 * n + 1) n
      (bondRectangleLeftReachableSet (2 * n + 1) n ω))
  change z' ∈ (w.map F).support at hz'
  rw [SimpleGraph.Walk.support_map] at hz'
  rcases List.mem_map.mp hz' with ⟨u, hu, huz⟩
  have huz' : u = z' := by
    simpa [F] using huz
  subst z'
  have huBounds := interfaceDualGraphWalk_support_bounds hn hno hb ht w hu
  have hFu : F u = u := by
    simp [F]
  rw [hFu]
  rw [mem_squareRectangleVertices_iff]
  change 0 ≤ centeredRectangleDualityIso n u 0 ∧
    centeredRectangleDualityIso n u 0 ≤ (2 * n + 1 : ℕ) ∧
      -(n : ℤ) ≤ centeredRectangleDualityIso n u 1 ∧
        centeredRectangleDualityIso n u 1 ≤ (n : ℤ)
  rw [centeredRectangleDualityIso_apply_zero,
    centeredRectangleDualityIso_apply_one]
  push_cast
  omega

/-- The rotated dual of every noncrossing configuration crosses the same centered self-dual
rectangle from left to right. -/
theorem rotatedDualSquareConfiguration_mem_crossing_of_not_crossing
    {n : ℕ} (hn : 0 < n) {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent (2 * n + 1) n) :
    rotatedDualSquareConfiguration n ω ∈
      squareRectangleCrossingEvent (2 * n + 1) n := by
  rcases exists_interfaceDual_reachable_bottom_top
      (m := 2 * n + 1) (n := n)
      (eta := bondRectangleLeftReachableSet (2 * n + 1) n ω) hn with
    ⟨b, hb, t, ht, hbt⟩
  let w₀ := Classical.choice hbt
  let w := bondRectangleInterfaceDualGraphWalk w₀
  have hwOpen : dualWalkIsOpen ω w :=
    dualWalkIsOpen_bondRectangleInterfaceDualGraphWalk_of_not_crossing hno w₀
  let q := w.map (centeredRectangleDualityIso n).toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback (centeredRectangleDualityIso n)
        (rotatedDualSquareConfiguration n ω)) w := by
    have hpull :
        cubicGraphIsoConfigurationPullback (centeredRectangleDualityIso n)
            (cubicGraphIsoConfigurationPullback (centeredRectangleDualityIso n).symm
              (dualSquareConfiguration ω)) =
          dualSquareConfiguration ω := by
      simpa using cubicGraphIsoConfigurationPullback_symm
        (centeredRectangleDualityIso n).symm (dualSquareConfiguration ω)
    rw [rotatedDualSquareConfiguration, hpull]
    exact hwOpen
  have hqOpen : walkIsOpen (rotatedDualSquareConfiguration n ω) q :=
    walkIsOpen_map_cubicGraphIso (centeredRectangleDualityIso n) w hsource
  have hqSupport : ∀ z ∈ q.support, z ∈ squareRectangleVertices (2 * n + 1) n := by
    intro z hz
    simpa [q, w] using
      mapped_interfaceDualGraphWalk_support_mem_rectangle hn hno hb ht w₀ hz
  have hqEdges : walkEdgeFinset q ⊆ squareRectangleEdges (2 * n + 1) n :=
    walkEdgeFinset_subset_squareRectangleEdges_of_support q hqSupport
  have hbData := mem_siteRectangleBottomInterfaceDualVertices_iff.mp hb
  have htData := mem_siteRectangleTopInterfaceDualVertices_iff.mp ht
  have hleft : centeredRectangleDualityIso n b ∈
      squareRectangleLeft (2 * n + 1) n := by
    rw [mem_squareRectangleLeft_iff]
    have hbRect := hqSupport _ q.start_mem_support
    have hbBounds := mem_squareRectangleVertices_iff.mp hbRect
    refine ⟨?_, hbBounds.2.2.1, hbBounds.2.2.2⟩
    rw [centeredRectangleDualityIso_apply_zero, hbData.2.2.1]
    ring
  have hright : centeredRectangleDualityIso n t ∈
      squareRectangleRight (2 * n + 1) n := by
    rw [mem_squareRectangleRight_iff]
    have htRect := hqSupport _ q.end_mem_support
    have htBounds := mem_squareRectangleVertices_iff.mp htRect
    refine ⟨?_, htBounds.2.2.1, htBounds.2.2.2⟩
    simp [htData.2.2.1]
    omega
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
  exact ⟨centeredRectangleDualityIso n b, hleft,
    centeredRectangleDualityIso n t, hright, q, hqOpen, hqEdges⟩

/-! ### Bernoulli-law invariance -/

/-- The shifted-dual complementation map is measurable. -/
theorem measurable_dualSquareConfiguration :
    Measurable (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2) := by
  let f := squareEdgeDualCrossingEquiv.symm.toEmbedding
  have hfun : (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2) =
      (fun ω : EdgeConfiguration 2 ↦ f ⁻¹' ωᶜ) := by
    funext ω
    ext e
    rfl
  rw [hfun]
  exact (measurable_preimage_embedding f).comp measurable_compl

/-- Dual complementation sends density `p` to complementary density `1-p`. -/
theorem bernoulliBondMeasure_map_dualSquareConfiguration (p : I) :
    (bernoulliBondMeasure 2 p).map dualSquareConfiguration =
      bernoulliBondMeasure 2 (σ p) := by
  let f := squareEdgeDualCrossingEquiv.symm.toEmbedding
  let C : EdgeConfiguration 2 → EdgeConfiguration 2 := fun ω ↦ ωᶜ
  let R : EdgeConfiguration 2 → EdgeConfiguration 2 := fun ω ↦ f ⁻¹' ω
  have hfun : (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2) =
      R ∘ C := by
    funext ω
    ext e
    rfl
  calc
    (bernoulliBondMeasure 2 p).map dualSquareConfiguration =
        (bernoulliBondMeasure 2 p).map (R ∘ C) := by rw [hfun]
    _ = ((bernoulliBondMeasure 2 p).map C).map R := by
      simpa [C, R] using
        (Measure.map_map (measurable_preimage_embedding f) measurable_compl
          (μ := bernoulliBondMeasure 2 p)).symm
    _ = (bernoulliBondMeasure 2 (σ p)).map R := by
      rw [bernoulliBondMeasure, bernoulliBondMeasure,
        show C = (fun ω : EdgeConfiguration 2 ↦ ωᶜ) by rfl,
        setBernoulli_map_compl_univ]
    _ = bernoulliBondMeasure 2 (σ p) := by
      simpa [bernoulliBondMeasure, R] using
        setBernoulli_map_preimage_univ f (σ p)

/-- At the self-dual density, the rotated-dual transformation preserves the Bernoulli law. -/
theorem bernoulliBondMeasure_map_rotatedDualSquareConfiguration_half (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).map
        (rotatedDualSquareConfiguration n) =
      bernoulliBondMeasure 2 squareHalfDensity := by
  let F := centeredRectangleDualityIso n
  let D := (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2)
  let R := cubicGraphIsoConfigurationPullback F.symm
  have hfun : rotatedDualSquareConfiguration n = R ∘ D := by
    rfl
  calc
    (bernoulliBondMeasure 2 squareHalfDensity).map
        (rotatedDualSquareConfiguration n) =
        (bernoulliBondMeasure 2 squareHalfDensity).map (R ∘ D) := by rw [hfun]
    _ = ((bernoulliBondMeasure 2 squareHalfDensity).map D).map R := by
      simpa [D, R] using
        (Measure.map_map (measurable_cubicGraphIsoConfigurationPullback F.symm)
          measurable_dualSquareConfiguration
          (μ := bernoulliBondMeasure 2 squareHalfDensity)).symm
    _ = (bernoulliBondMeasure 2 squareHalfDensity).map R := by
      have hsigma : σ squareHalfDensity = squareHalfDensity := by
        ext
        norm_num [squareHalfDensity]
      rw [bernoulliBondMeasure_map_dualSquareConfiguration]
      rw [hsigma]
    _ = bernoulliBondMeasure 2 squareHalfDensity := by
      exact bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback
        squareHalfDensity F.symm

theorem measurable_rotatedDualSquareConfiguration (n : ℕ) :
    Measurable (rotatedDualSquareConfiguration n) :=
  (measurable_cubicGraphIsoConfigurationPullback
    (centeredRectangleDualityIso n).symm).comp measurable_dualSquareConfiguration

/-- The centered self-dual rectangle has crossing probability at least `1/2` at density
`1/2`. -/
theorem half_le_squareRectangleCrossingProbability_centered (n : ℕ) (hn : 0 < n) :
    1 / 2 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (squareRectangleCrossingEvent (2 * n + 1) n) := by
  let μ := bernoulliBondMeasure 2 squareHalfDensity
  let A := squareRectangleCrossingEvent (2 * n + 1) n
  let T := rotatedDualSquareConfiguration n
  have hA : MeasurableSet A := measurableSet_squareRectangleCrossingEvent _ _
  have hsubset : Aᶜ ⊆ T ⁻¹' A := by
    intro ω hω
    exact rotatedDualSquareConfiguration_mem_crossing_of_not_crossing hn hω
  have hmono : μ.real Aᶜ ≤ μ.real (T ⁻¹' A) :=
    measureReal_mono hsubset (measure_ne_top _ _)
  have hmap := congrArg (fun ν : Measure (EdgeConfiguration 2) ↦ ν.real A)
    (bernoulliBondMeasure_map_rotatedDualSquareConfiguration_half n)
  change (Measure.map T μ).real A = μ.real A at hmap
  rw [map_measureReal_apply (measurable_rotatedDualSquareConfiguration n) hA] at hmap
  have hcomp : μ.real Aᶜ ≤ μ.real A := hmono.trans_eq hmap
  have hsum := measureReal_add_measureReal_compl (μ := μ) hA
  rw [probReal_univ] at hsum
  linarith

/-! ### Transfer to Grimmett's one-bond-wider rectangle -/

/-- Translate the centered rectangle `[0,2n+1] × [-n,n]` to
`[0,2n+1] × [0,2n]`. -/
def centeredToGrimmettRectangleIso (n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex 0 (-(n : ℤ))) cubicOrigin

@[simp]
theorem centeredToGrimmettRectangleIso_apply_zero (n : ℕ) (z : SquareVertex) :
    centeredToGrimmettRectangleIso n z 0 = z 0 := by
  simp [centeredToGrimmettRectangleIso, cubicTranslationIso_apply, cubicTranslate,
    squareVertex, cubicOrigin]

@[simp]
theorem centeredToGrimmettRectangleIso_apply_one (n : ℕ) (z : SquareVertex) :
    centeredToGrimmettRectangleIso n z 1 = z 1 + n := by
  simp [centeredToGrimmettRectangleIso, cubicTranslationIso_apply, cubicTranslate,
    squareVertex, cubicOrigin]

/-- Translating a centered crossing gives a crossing of Grimmett's rectangle with even
height parameter. -/
theorem centeredCrossingPlacement_subset_grimmettRectangleCrossingEvent
    (n : ℕ) :
    cubicGraphIsoEvent (centeredToGrimmettRectangleIso n)
        (squareRectangleCrossingEvent (2 * n + 1) n) ⊆
      grimmettRectangleCrossingEvent (2 * n) := by
  intro ω hω
  let F := centeredToGrimmettRectangleIso n
  change cubicGraphIsoConfigurationPullback F ω ∈
    squareRectangleCrossingEvent (2 * n + 1) n at hω
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hω
  rcases hω with ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩
  let q := w.map F.toHom
  have hqOpen : walkIsOpen ω q :=
    walkIsOpen_map_cubicGraphIso F w hwOpen
  have hwSupport : ∀ z ∈ w.support, z ∈ squareRectangleVertices (2 * n + 1) n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact (Finset.mem_filter.mp hy).1
    · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
      exact endpoint_mem_squareRectangle_of_edge_mem
        (hwEdges ((mem_walkEdgeFinset_iff w ee).mpr he)) hze
  have hqSupport : ∀ z ∈ q.support, z ∈ grimmettRectangleVertices (2 * n) := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨u, hu, rfl⟩
    have huBounds := mem_squareRectangleVertices_iff.mp (hwSupport u hu)
    rw [mem_grimmettRectangleVertices_iff]
    simp [F]
    omega
  have hqBox : walkEdgeFinset q ⊆ cubicBoxEdges 2 cubicOrigin (2 * n + 1) :=
    walkEdgeFinset_subset_cubicBoxEdges_of_support q fun z hz ↦ by
      rw [mem_cubicMetricBox]
      have hzBounds := mem_grimmettRectangleVertices_iff.mp (hqSupport z hz)
      intro i
      fin_cases i <;> simp [cubicOrigin] <;> omega
  have hqEdges : walkEdgeFinset q ⊆ grimmettRectangleEdges (2 * n) := by
    intro e he
    rw [grimmettRectangleEdges, Finset.mem_filter]
    refine ⟨hqBox he, ?_, ?_⟩
    · apply hqSupport e.1.out.1
      apply q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff q e).mp he)
      exact Sym2.out_fst_mem e.1
    · apply hqSupport e.1.out.2
      apply q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff q e).mp he)
      exact Sym2.out_snd_mem e.1
  have hx' : F x ∈ grimmettRectangleLeft (2 * n) := by
    rw [mem_grimmettRectangleLeft_iff]
    have hxBounds := mem_squareRectangleLeft_iff.mp hx
    simp [F]
    omega
  have hy' : F y ∈ grimmettRectangleRight (2 * n) := by
    rw [mem_grimmettRectangleRight_iff]
    have hyBounds := mem_squareRectangleRight_iff.mp hy
    simp [F]
    omega
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion]
  exact ⟨F x, hx', F y, hy', q, hqOpen, hqEdges⟩

/-- The axiom-free self-duality argument gives the half-density lower bound for every even
member of Grimmett's rectangle family. -/
theorem half_le_grimmettRectangleCrossingProbability_even
    (n : ℕ) (hn : 0 < n) :
    1 / 2 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (grimmettRectangleCrossingEvent (2 * n)) := by
  let F := centeredToGrimmettRectangleIso n
  let A := squareRectangleCrossingEvent (2 * n + 1) n
  calc
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real A :=
      half_le_squareRectangleCrossingProbability_centered n hn
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real (cubicGraphIsoEvent F A) := by
      symm
      exact bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity F
        (measurableSet_squareRectangleCrossingEvent _ _)
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent (2 * n)) :=
      measureReal_mono
        (centeredCrossingPlacement_subset_grimmettRectangleCrossingEvent n)
        (measure_ne_top _ _)

/-! ### Consequence for the square-lattice critical probability -/

theorem card_squareRectangleLeft (m n : ℕ) :
    (squareRectangleLeft m n).card = 2 * n + 1 := by
  classical
  let f : ℤ ↪ SquareVertex :=
    ⟨fun y ↦ squareVertex 0 y, fun _ _ h ↦ congrFun h 1⟩
  have heq : squareRectangleLeft m n =
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).map f := by
    ext x
    rw [mem_squareRectangleLeft_iff, Finset.mem_map]
    constructor
    · rintro ⟨hx0, hxLower, hxUpper⟩
      refine ⟨x 1, Finset.mem_Icc.mpr ⟨hxLower, hxUpper⟩, ?_⟩
      ext i
      fin_cases i
      · simpa [f, squareVertex] using hx0.symm
      · simp [f, squareVertex]
    · rintro ⟨y, hy, hyx⟩
      have hyBounds := Finset.mem_Icc.mp hy
      subst x
      simpa [f, squareVertex] using hyBounds
  rw [heq, Finset.card_map, Int.card_Icc]
  omega

theorem squareRectangleCrossingEvent_centered_subset_radiusConnectionEvents (n : ℕ) :
    squareRectangleCrossingEvent (2 * n + 1) n ⊆
      ⋃ x ∈ squareRectangleLeft (2 * n + 1) n,
        radiusConnectionEvent 2 x (2 * n + 1) := by
  intro ω hω
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hω
  rcases hω with ⟨x, hx, y, hy, hxy⟩
  refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
  rcases hxy with ⟨w, hwOpen, _hwEdges⟩
  have hx0 := (mem_squareRectangleLeft_iff.mp hx).1
  have hy0 := (mem_squareRectangleRight_iff.mp hy).1
  have hcoord : 2 * n + 1 ≤ cubicL1Dist x y := by
    have hle := cubicL1Dist_coord_le x y (0 : Fin 2)
    rw [hx0, hy0] at hle
    simpa using hle
  exact exists_open_walk_to_cubicMetricSphere_in_ball w hwOpen hcoord

theorem squareRectangleCrossingProbability_centered_le (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real
        (squareRectangleCrossingEvent (2 * n + 1) n) ≤
      (2 * n + 1 : ℕ) * radiusTail 2 p (2 * n + 1) := by
  let μ := bernoulliBondMeasure 2 p
  have hcover := squareRectangleCrossingEvent_centered_subset_radiusConnectionEvents n
  calc
    μ.real (squareRectangleCrossingEvent (2 * n + 1) n) ≤
        μ.real (⋃ x ∈ squareRectangleLeft (2 * n + 1) n,
          radiusConnectionEvent 2 x (2 * n + 1)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ x ∈ squareRectangleLeft (2 * n + 1) n,
        μ.real (radiusConnectionEvent 2 x (2 * n + 1)) :=
      measureReal_biUnion_finset_le _ _
    _ = (2 * n + 1 : ℕ) * radiusTail 2 p (2 * n + 1) := by
      dsimp [μ]
      simp_rw [bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail]
      simp [card_squareRectangleLeft]

private theorem tendsto_two_mul_add_one_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) *
      Real.exp (-c * ((2 * n + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hcastReal : Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n ↦ by
        show (n : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ)
        exact_mod_cast (show n ≤ 2 * n + 1 by omega))
      tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ ↦ c * ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
    hcastReal.const_mul_atTop hc
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hmul : Tendsto
      (fun n : ℕ ↦ c⁻¹ *
        ((c * ((2 * n + 1 : ℕ) : ℝ)) ^ 1 *
          Real.exp (-(c * ((2 * n + 1 : ℕ) : ℝ)))))
      atTop (nhds (c⁻¹ * 0)) :=
    tendsto_const_nhds.mul hbase
  convert hmul using 1
  · funext n
    field_simp [hc.ne']
  · simp

/-- The axiom-free finite duality lower bound implies `p_c(ℤ²) ≤ 1/2`. -/
theorem cubicCriticalProbability_two_le_half_via_bond_interface :
    cubicCriticalProbability 2 ≤ 1 / 2 := by
  by_contra hpc
  have hhalfpc : (squareHalfDensity : ℝ) < cubicCriticalProbability 2 := by
    rw [coe_squareHalfDensity]
    exact lt_of_not_ge hpc
  obtain ⟨c, hc, hdecay⟩ :=
    radiusTail_exponential_decay_of_lt_critical 2 (by omega) squareHalfDensity hhalfpc
  have hlim := tendsto_two_mul_add_one_mul_exp_neg_mul c hc
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((2 * n + 1 : ℕ) : ℝ) *
        Real.exp (-c * ((2 * n + 1 : ℕ) : ℝ)) < 1 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let n := max 1 N
  have hn : 0 < n := by simp [n]
  have hnN : N ≤ n := Nat.le_max_right _ _
  have hsmall := hN n hnN
  have htail := hdecay (2 * n + 1)
  have htail' :
      radiusTail 2 squareHalfDensity (2 * n + 1) ≤
        Real.exp (-c * ((2 * n + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using htail
  have hcontra : (1 / 2 : ℝ) < 1 / 2 := by
    calc
      (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (squareRectangleCrossingEvent (2 * n + 1) n) :=
        half_le_squareRectangleCrossingProbability_centered n hn
      _ ≤ (2 * n + 1 : ℕ) * radiusTail 2 squareHalfDensity (2 * n + 1) :=
        squareRectangleCrossingProbability_centered_le squareHalfDensity n
      _ ≤ ((2 * n + 1 : ℕ) : ℝ) *
          Real.exp (-c * ((2 * n + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left htail' (by positivity)
      _ < 1 / 2 := hsmall
  exact (lt_irrefl _ hcontra)

end Percolation
