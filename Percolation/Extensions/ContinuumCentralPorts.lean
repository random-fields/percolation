import Percolation.Extensions.ContinuumSubcritical
import Percolation.Critical.RootedSitePercolation

/-!
# Central ports from site percolation to the Boolean model

A unit cube is called port-good when one of its active Poisson marks lies in a small central
subcube.  Representatives of port-good nearest-neighbor cubes are at Euclidean distance less
than two, uniformly in the dimension.  Thus an infinite cubic site cluster of port-good cubes
embeds into the literal marked Boolean graph.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped BigOperators NNReal unitInterval

/-- Half-width of the central port in each coordinate. -/
noncomputable def continuumCentralPortRadius (d : ℕ) : ℝ :=
  1 / (8 * (d + 1))

theorem continuumCentralPortRadius_pos (d : ℕ) :
    0 < continuumCentralPortRadius d := by
  unfold continuumCentralPortRadius
  positivity

/-- Left endpoint of the positive central port. -/
noncomputable def continuumCentralPortLower : I :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Right endpoint of the positive central port. -/
noncomputable def continuumCentralPortUpper (d : ℕ) : I :=
  ⟨1 / 2 + continuumCentralPortRadius d, by
    constructor
    · exact add_nonneg (by norm_num) (continuumCentralPortRadius_pos d).le
    · unfold continuumCentralPortRadius
      have hden : (0 : ℝ) < 8 * ((d : ℝ) + 1) := by positivity
      have hd0 : (0 : ℝ) ≤ d := by positivity
      have hrle : (1 : ℝ) / (8 * ((d : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hden]
        nlinarith
      linarith⟩

@[simp]
theorem coe_continuumCentralPortLower :
    (continuumCentralPortLower : ℝ) = 1 / 2 := rfl

@[simp]
theorem coe_continuumCentralPortUpper (d : ℕ) :
    (continuumCentralPortUpper d : ℝ) =
      1 / 2 + continuumCentralPortRadius d := rfl

/-- A mark lies in the positive, dimension-dependent central port.  A one-sided port has the
same geometric purpose as a symmetric one and gives a literal coordinate rectangle. -/
def continuumMarkIsCentral (d : ℕ) (a : ContinuumUnitMark d) : Prop :=
  ∀ i, a i ∈ Set.Icc continuumCentralPortLower (continuumCentralPortUpper d)

theorem measurableSet_continuumMarkIsCentral (d : ℕ) :
    MeasurableSet {a : ContinuumUnitMark d | continuumMarkIsCentral d a} := by
  rw [show {a : ContinuumUnitMark d | continuumMarkIsCentral d a} =
      ⋂ i : Fin d,
        {a | a i ∈ Set.Icc continuumCentralPortLower (continuumCentralPortUpper d)} by
    ext a
    simp [continuumMarkIsCentral]]
  exact MeasurableSet.iInter fun i : Fin d ↦
    measurableSet_Icc.preimage (measurable_pi_apply i)

/-- A cube sample contains at least one active point in its central port. -/
def continuumCubeHasCentralPoint (d : ℕ) : Set (ContinuumCubeSample d) :=
  {sample | ∃ k, k < sample.1 ∧ continuumMarkIsCentral d (sample.2 k)}

theorem measurableSet_continuumCubeHasCentralPoint (d : ℕ) :
    MeasurableSet (continuumCubeHasCentralPoint d) := by
  rw [show continuumCubeHasCentralPoint d = ⋃ k : ℕ,
      {sample | k < sample.1} ∩
        {sample | continuumMarkIsCentral d (sample.2 k)} by
    ext sample
    simp [continuumCubeHasCentralPoint]]
  exact MeasurableSet.iUnion fun k =>
    ((measurable_fst (measurableSet_Ioi : MeasurableSet (Set.Ioi k))).inter
      ((measurableSet_continuumMarkIsCentral d).preimage
        (measurable_pi_apply k |>.comp measurable_snd)))

/-- Site field of cubes containing a central active point. -/
def continuumCentralCubes {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : Set (Cubic d) :=
  {x | Xi x ∈ continuumCubeHasCentralPoint d}

theorem measurable_continuumCentralCubes {d : ℕ} :
    Measurable (continuumCentralCubes :
      ContinuumPoissonConfiguration d → Set (Cubic d)) := by
  change Measurable ((fun P : Cubic d → Prop ↦ {x | P x}) ∘
    fun (Xi : ContinuumPoissonConfiguration d) (x : Cubic d) ↦
      Xi x ∈ continuumCubeHasCentralPoint d)
  apply Measurable.comp (by fun_prop)
  exact measurable_pi_lambda _ fun x ↦
    ((measurableSet_continuumCubeHasCentralPoint d).preimage
      (measurable_pi_apply x)).mem

private theorem continuumCentralCube_exists_index {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d}
    (x : continuumCentralCubes Xi) :
    ∃ k, k < (Xi x.1).1 ∧ continuumMarkIsCentral d ((Xi x.1).2 k) :=
  x.2

/-- A canonically chosen active central mark in a port-good cube. -/
noncomputable def continuumCentralPointIndex {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d}
    (x : continuumCentralCubes Xi) : Cubic d × ℕ :=
  (x.1, Classical.choose (continuumCentralCube_exists_index x))

theorem continuumCentralPointIndex_active {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d}
    (x : continuumCentralCubes Xi) :
    continuumPoissonPointActive Xi (continuumCentralPointIndex x) :=
  (Classical.choose_spec (continuumCentralCube_exists_index x)).1

theorem continuumCentralPointIndex_mark_central {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d}
    (x : continuumCentralCubes Xi) :
    continuumMarkIsCentral d
      ((Xi x.1).2 (continuumCentralPointIndex x).2) :=
  (Classical.choose_spec (continuumCentralCube_exists_index x)).2

theorem continuumCentralPointIndex_injective {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d} :
    Function.Injective (continuumCentralPointIndex
      (Xi := Xi)) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg Prod.fst hxy

private theorem abs_continuumPoissonPoint_sub_cubeIndex_le
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (x : continuumCentralCubes Xi) (i : Fin d) :
    |continuumPoissonPoint Xi (continuumCentralPointIndex x) i - (x.1 i : ℝ)| ≤
      continuumCentralPortRadius d := by
  change |(x.1 i : ℝ) + continuumCenteredUnitMark
      ((Xi x.1).2 (continuumCentralPointIndex x).2 i) - (x.1 i : ℝ)| ≤ _
  let a : I := (Xi x.1).2 (continuumCentralPointIndex x).2 i
  have ha := continuumCentralPointIndex_mark_central x i
  change continuumCentralPortLower ≤ a ∧ a ≤ continuumCentralPortUpper d at ha
  have hrlt : continuumCentralPortRadius d < (1 / 2 : ℝ) := by
    unfold continuumCentralPortRadius
    have hden : (0 : ℝ) < 8 * ((d : ℝ) + 1) := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  have ha1 : (a : ℝ) ≠ 1 := by
    intro haeq
    have hau : (a : ℝ) ≤ 1 / 2 + continuumCentralPortRadius d := by
      exact Subtype.coe_le_coe.mpr ha.2
    rw [haeq] at hau
    linarith
  unfold continuumCenteredUnitMark
  rw [if_neg ha1]
  have habs : |(a : ℝ) - 1 / 2| ≤ continuumCentralPortRadius d := by
    rw [abs_le]
    constructor
    · have hal : (1 / 2 : ℝ) ≤ a := Subtype.coe_le_coe.mpr ha.1
      have hrpos := continuumCentralPortRadius_pos d
      linarith
    · have hau : (a : ℝ) ≤ 1 / 2 + continuumCentralPortRadius d := by
        exact Subtype.coe_le_coe.mpr ha.2
      linarith
  simpa only [a, add_sub_cancel_left] using habs

/-- Central representatives of nearest-neighbor cubes lie within the Boolean connection
radius. -/
theorem continuumCentralPoint_dist_lt_two_of_cubicAdj
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    {x y : continuumCentralCubes Xi} (hxy : (cubicGraph d).Adj x.1 y.1) :
    coordinateEuclideanDist
        (continuumPoissonPoint Xi (continuumCentralPointIndex x))
        (continuumPoissonPoint Xi (continuumCentralPointIndex y)) < 2 := by
  refine (coordinateEuclideanDist_le_sum_abs _ _).trans_lt ?_
  have hcoord (i : Fin d) :
      |continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
          continuumPoissonPoint Xi (continuumCentralPointIndex y) i| ≤
        |((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)| +
          2 * continuumCentralPortRadius d := by
    have hx := abs_continuumPoissonPoint_sub_cubeIndex_le x i
    have hy := abs_continuumPoissonPoint_sub_cubeIndex_le y i
    calc
      |continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
          continuumPoissonPoint Xi (continuumCentralPointIndex y) i| =
          |(((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)) +
            ((continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
                (x.1 i : ℝ)) -
              (continuumPoissonPoint Xi (continuumCentralPointIndex y) i -
                (y.1 i : ℝ)))| := by ring_nf
      _ ≤ |((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)| +
          |(continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
                (x.1 i : ℝ)) -
            (continuumPoissonPoint Xi (continuumCentralPointIndex y) i -
                (y.1 i : ℝ))| := abs_add_le _ _
      _ ≤ |((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)| +
          (|continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
                (x.1 i : ℝ)| +
            |continuumPoissonPoint Xi (continuumCentralPointIndex y) i -
                (y.1 i : ℝ)|) := by gcongr; exact abs_sub _ _
      _ ≤ |((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)| +
          2 * continuumCentralPortRadius d := by linarith
  calc
    (∑ i : Fin d, |continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
        continuumPoissonPoint Xi (continuumCentralPointIndex y) i|) ≤
        ∑ i : Fin d, (|((x.1 i : ℤ) : ℝ) - ((y.1 i : ℤ) : ℝ)| +
          2 * continuumCentralPortRadius d) :=
      Finset.sum_le_sum fun i _hi => hcoord i
    _ = (cubicL1Dist x.1 y.1 : ℝ) +
        d * (2 * continuumCentralPortRadius d) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [cubicL1Dist, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, abs_sub_comm]
      · simp
    _ = 1 + d * (2 * continuumCentralPortRadius d) := by
      congr 1
      exact_mod_cast (cubicGraph_dist_eq_l1Dist d x.1 y.1).symm.trans
        (SimpleGraph.dist_eq_one_iff_adj.mpr hxy)
    _ < 2 := by
      unfold continuumCentralPortRadius
      have hd : (d : ℝ) < 4 * ((d : ℝ) + 1) := by linarith
      have hden : (0 : ℝ) < 4 * ((d : ℝ) + 1) := by positivity
      rw [show (d : ℝ) * (2 * (1 / (8 * ((d : ℝ) + 1)))) =
          (d : ℝ) / (4 * ((d : ℝ) + 1)) by field_simp <;> ring]
      linarith [div_lt_one hden |>.2 hd]

/-- Graph homomorphism from the port-good site graph to the fixed-index Boolean graph. -/
noncomputable def continuumCentralSiteToPoissonHom {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :
    (cubicGraph d).induce (continuumCentralCubes Xi) →g
      continuumPoissonAmbientGraph Xi where
  toFun := continuumCentralPointIndex
  map_rel' := by
    intro x y hxy
    refine continuumPoissonAmbientGraph_adj.mpr ⟨?_,
      continuumCentralPointIndex_active x,
      continuumCentralPointIndex_active y, ?_⟩
    · exact (continuumCentralPointIndex_injective (Xi := Xi)).ne hxy.ne
    · exact (continuumCentralPoint_dist_lt_two_of_cubicAdj
        (SimpleGraph.induce_adj.mp hxy)).le

/-- The selected representative in the origin cube lies inside the unit ball centred at the
spatial origin. -/
theorem continuumCentralPointIndex_origin_coversOrigin
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (h0 : cubicOrigin ∈ continuumCentralCubes Xi) :
    continuumPoissonPointCoversOrigin Xi
      (continuumCentralPointIndex
        (⟨cubicOrigin, h0⟩ : continuumCentralCubes Xi)) := by
  let x : continuumCentralCubes Xi := ⟨cubicOrigin, h0⟩
  refine ⟨continuumCentralPointIndex_active x, ?_⟩
  calc
    coordinateEuclideanDist
        (continuumPoissonPoint Xi (continuumCentralPointIndex x))
        (continuumSpatialOrigin d) ≤
        ∑ i : Fin d,
          |continuumPoissonPoint Xi (continuumCentralPointIndex x) i -
            continuumSpatialOrigin d i| :=
      coordinateEuclideanDist_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, continuumCentralPortRadius d := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa [x, continuumSpatialOrigin, cubicOrigin] using
        abs_continuumPoissonPoint_sub_cubeIndex_le x i
    _ = d * continuumCentralPortRadius d := by simp
    _ ≤ 1 := by
      unfold continuumCentralPortRadius
      have hden : (0 : ℝ) < 8 * ((d : ℝ) + 1) := by positivity
      rw [show (d : ℝ) * (1 / (8 * ((d : ℝ) + 1))) =
          (d : ℝ) / (8 * ((d : ℝ) + 1)) by field_simp <;> ring]
      rw [div_le_one hden]
      nlinarith [show (0 : ℝ) ≤ d by positivity]

/-- An infinite central-cube cluster rooted at the origin gives the literal source event
`|W(0)| = ∞`. -/
theorem continuumOriginPercolates_of_infiniteCentralOriginCluster
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (hinf : (siteOpenCluster (cubicGraph d) (continuumCentralCubes Xi)
      cubicOrigin).Infinite) :
    Xi ∈ continuumOriginPercolatesEvent d := by
  have h0 : cubicOrigin ∈ continuumCentralCubes Xi := by
    obtain ⟨y, hy⟩ := hinf.nonempty
    obtain ⟨w, hw⟩ := hy
    exact hw cubicOrigin (by simp)
  let xI : continuumCentralCubes Xi := ⟨cubicOrigin, h0⟩
  let C := siteOpenCluster (cubicGraph d) (continuumCentralCubes Xi) cubicOrigin
  let lift : C → continuumCentralCubes Xi := fun y ↦
    ⟨y.1, siteOpenCluster_subset (cubicGraph d) (continuumCentralCubes Xi)
      cubicOrigin y.2⟩
  let f : C → Cubic d × ℕ := fun y ↦ continuumCentralPointIndex (lift y)
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun q : Cubic d × ℕ ↦ q.1) hyz
  haveI : Infinite C := Set.infinite_coe_iff.mpr hinf
  have himage : (f '' (Set.univ : Set C)).Infinite :=
    Set.infinite_univ.image hf.injOn
  have h00 : cubicOrigin ∈ C := by
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    simpa using h0
  let xC : C := ⟨cubicOrigin, h00⟩
  let a : Cubic d × ℕ := continuumCentralPointIndex xI
  refine ⟨a, continuumCentralPointIndex_origin_coversOrigin h0,
    continuumCentralPointIndex_active xI, himage.mono ?_⟩
  rintro z ⟨y, _hy, rfl⟩
  obtain ⟨w, hw⟩ := y.2
  have hreach : ((cubicGraph d).induce (continuumCentralCubes Xi)).Reachable
      xI (lift y) := by
    refine ⟨?_⟩
    simpa [xI, lift] using w.induce (continuumCentralCubes Xi) hw
  simpa [a, f, xC, xI, lift] using
    hreach.map (continuumCentralSiteToPoissonHom Xi)

/-- Deterministic port comparison: an infinite cubic cluster of good cubes forces an infinite
component in the marked Boolean graph. -/
theorem continuumPoissonPercolates_of_hasInfiniteCentralCubeCluster
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (hinf : hasInfiniteSiteCluster (cubicGraph d) (continuumCentralCubes Xi)) :
    continuumPoissonPercolates Xi := by
  obtain ⟨x, hxinf⟩ := hinf
  have hx : x ∈ continuumCentralCubes Xi := by
    by_contra hx
    apply hxinf
    rw [siteOpenCluster_eq_reachable]
    simp [hx]
  let xI : continuumCentralCubes Xi := ⟨x, hx⟩
  let C := siteOpenCluster (cubicGraph d) (continuumCentralCubes Xi) x
  let lift : C → continuumCentralCubes Xi := fun y ↦
    ⟨y.1, siteOpenCluster_subset (cubicGraph d) (continuumCentralCubes Xi) x y.2⟩
  let f : C → Cubic d × ℕ := fun y ↦ continuumCentralPointIndex (lift y)
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun q : Cubic d × ℕ ↦ q.1) hyz
  haveI : Infinite C := Set.infinite_coe_iff.mpr hxinf
  have himage : (f '' (Set.univ : Set C)).Infinite :=
    Set.infinite_univ.image hf.injOn
  have hxx : x ∈ C := by
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    simpa using hx
  let xC : C := ⟨x, hxx⟩
  refine ⟨f xC, himage.mono ?_⟩
  rintro z ⟨y, _hy, rfl⟩
  obtain ⟨w, hw⟩ := y.2
  have hreach : ((cubicGraph d).induce (continuumCentralCubes Xi)).Reachable
      xI (lift y) := by
    refine ⟨?_⟩
    simpa [xI, lift] using w.induce (continuumCentralCubes Xi) hw
  simpa [f, xC, xI, lift] using
    hreach.map (continuumCentralSiteToPoissonHom Xi)

end Percolation
