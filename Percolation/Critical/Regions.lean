import Percolation.Bernoulli.FKGInfinite
import Percolation.Critical.BoxRadius

/-!
# Percolation in induced cubic regions and site percolation

This file introduces the region and site-percolation vocabulary used by Grimmett's Chapter 7.
Region connections are represented by ambient cubic walks whose entire support lies in the
region.  This keeps them compatible with the repository's existing bond configurations.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The cubic graph induced by a set of lattice vertices. -/
def cubicRegionGraph (d : ℕ) (A : Set (Cubic d)) : SimpleGraph A :=
  (cubicGraph d).induce A

/-- The event that `x` and `y` are joined by an open walk supported entirely in `A`. -/
def connectionEventWithinVertices (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ w : (cubicGraph d).Walk x y,
    walkIsOpen ω w ∧ ∀ z ∈ w.support, z ∈ A}

theorem connectionEventWithinVertices_subset_connectionEvent
    (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    connectionEventWithinVertices d A x y ⊆ connectionEvent d x y := by
  rintro ω ⟨w, hw, _hA⟩
  exact ⟨w, hw⟩

theorem connectionEventWithinVertices_mono {d : ℕ} {A B : Set (Cubic d)}
    (hAB : A ⊆ B) (x y : Cubic d) :
    connectionEventWithinVertices d A x y ⊆ connectionEventWithinVertices d B x y := by
  rintro ω ⟨w, hw, hA⟩
  exact ⟨w, hw, fun z hz ↦ hAB (hA z hz)⟩

theorem isIncreasingEvent_connectionEventWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    IsIncreasingEvent (connectionEventWithinVertices d A x y) := by
  rintro ω η hωη ⟨w, hw, hA⟩
  exact ⟨w, fun e he ↦ hωη (hw e he), hA⟩

theorem measurableSet_connectionEventWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    MeasurableSet (connectionEventWithinVertices d A x y) := by
  have hrepr : connectionEventWithinVertices d A x y =
      ⋃ (steps : List (CubicDirection d))
        (hend : cubicEndpointFrom x steps = y)
        (_hA : ∀ z ∈ (cubicWalkFrom x steps).support, z ∈ A),
        {ω : EdgeConfiguration d |
          walkIsOpen ω ((cubicWalkFrom x steps).copy rfl hend)} := by
    ext ω
    simp only [connectionEventWithinVertices, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hA⟩
      obtain ⟨steps, hend, hcopy, -⟩ := exists_cubicWalkFrom_copy_eq w
      have hsupport : ∀ z ∈ (cubicWalkFrom x steps).support, z ∈ A := by
        intro z hz
        apply hA z
        have hz' : z ∈ ((cubicWalkFrom x steps).copy rfl hend).support := by
          simpa using hz
        exact hcopy ▸ hz'
      refine ⟨steps, hend, hsupport, ?_⟩
      have : walkIsOpen ω ((cubicWalkFrom x steps).copy rfl hend) := hcopy ▸ hw
      exact this
    · rintro ⟨steps, hend, hA, hw⟩
      refine ⟨(cubicWalkFrom x steps).copy rfl hend, hw, ?_⟩
      intro z hz
      apply hA z
      simpa using hz
  rw [hrepr]
  exact MeasurableSet.iUnion fun steps ↦ MeasurableSet.iUnion fun hend ↦
    MeasurableSet.iUnion fun _hA ↦ measurableSet_walkIsOpen _

@[simp]
theorem connectionEventWithinVertices_univ (d : ℕ) (x y : Cubic d) :
    connectionEventWithinVertices d Set.univ x y = connectionEvent d x y := by
  apply Set.Subset.antisymm
  · exact connectionEventWithinVertices_subset_connectionEvent d Set.univ x y
  · rintro ω ⟨w, hw⟩
    exact ⟨w, hw, by simp⟩

/-! ### Coordinate-convex walks -/

/-- A vertex lies coordinatewise between two endpoints. -/
def CubicCoordinateBetween {d : ℕ} (x y z : Cubic d) : Prop :=
  ∀ i : Fin d, (x i ≤ z i ∧ z i ≤ y i) ∨ (y i ≤ z i ∧ z i ≤ x i)

theorem cubicCoordinateBetween_left {d : ℕ} (x y : Cubic d) :
    CubicCoordinateBetween x y x := by
  intro i
  by_cases h : x i ≤ y i
  · exact Or.inl ⟨le_rfl, h⟩
  · exact Or.inr ⟨le_of_not_ge h, le_rfl⟩

theorem CubicCoordinateBetween.trans_right {d : ℕ} {x y z w : Cubic d}
    (hz : CubicCoordinateBetween x y z) (hw : CubicCoordinateBetween z y w) :
    CubicCoordinateBetween x y w := by
  intro i
  rcases hz i with hz | hz <;> rcases hw i with hw | hw <;> omega

/-- Coordinate-by-coordinate motion can be chosen so every intermediate vertex remains in the
coordinate rectangle spanned by the endpoints. -/
theorem exists_cubicWalk_support_between (d : ℕ) (x y : Cubic d) :
    ∃ w : (cubicGraph d).Walk x y,
      ∀ z ∈ w.support, CubicCoordinateBetween x y z := by
  classical
  suffices h : ∀ (n : ℕ) (x : Cubic d), cubicL1Dist x y = n →
      ∃ w : (cubicGraph d).Walk x y,
        ∀ z ∈ w.support, CubicCoordinateBetween x y z by
    exact h (cubicL1Dist x y) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases hxy : x = y
    · subst y
      exact ⟨SimpleGraph.Walk.nil, by
        intro z hz
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        subst z
        exact cubicCoordinateBetween_left x x⟩
    · have hne : ∃ i, x i ≠ y i := by
        by_contra hall
        exact hxy (funext fun i ↦ not_ne_iff.mp (not_exists.mp hall i))
      obtain ⟨i, hi⟩ := hne
      let a : CubicDirection d := (i, decide (x i < y i))
      let x' := cubicStepFrom x a
      have hstep_i : x' i = if x i < y i then x i + 1 else x i - 1 := by
        simp only [x', a, cubicStepFrom]
        by_cases hlt : x i < y i
        · simp [cubicDirectionIncrement, hlt]
        · simp [cubicDirectionIncrement, hlt, sub_eq_neg_add, add_comm]
      have hstep_ne : ∀ j, j ≠ i → x' j = x j := by
        intro j hji
        simp [x', a, cubicStepFrom, hji]
      have hdrop : (y i - x' i).natAbs + 1 = (y i - x i).natAbs := by
        rw [hstep_i]
        by_cases hlt : x i < y i
        · simp only [hlt, if_true]
          omega
        · simp only [hlt, if_false]
          have : y i < x i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hi)
          omega
      have hsum : cubicL1Dist x' y + 1 = n := by
        rw [← hx]
        simp only [cubicL1Dist]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
          ← Finset.sum_erase_add _ (fun j ↦ (y j - x j).natAbs) (Finset.mem_univ i)]
        have herase : ∑ j ∈ Finset.univ.erase i, (y j - x' j).natAbs =
            ∑ j ∈ Finset.univ.erase i, (y j - x j).natAbs :=
          Finset.sum_congr rfl fun j hj ↦ by
            rw [hstep_ne j (Finset.mem_erase.mp hj).1]
        omega
      have hstepBetween : CubicCoordinateBetween x y x' := by
        intro j
        by_cases hji : j = i
        · subst j
          rw [hstep_i]
          by_cases hlt : x i < y i
          · simp only [hlt, if_true]
            exact Or.inl ⟨by omega, by omega⟩
          · simp only [hlt, if_false]
            have : y i < x i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hi)
            exact Or.inr ⟨by omega, by omega⟩
        · rw [hstep_ne j hji]
          exact cubicCoordinateBetween_left x y j
      obtain ⟨w, hw⟩ := ih (cubicL1Dist x' y) (by omega) x' rfl
      refine ⟨SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x a) w, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact cubicCoordinateBetween_left _ _
      · exact hstepBetween.trans_right (hw z hz)

/-- Coordinate-convex subsets induce connected subgraphs of the cubic lattice. -/
theorem cubicRegionGraph_connected_of_coordinateConvex {d : ℕ} {A : Set (Cubic d)}
    (hA : A.Nonempty)
    (hconvex : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A →
      ∀ ⦃z⦄, CubicCoordinateBetween x y z → z ∈ A) :
    (cubicRegionGraph d A).Connected := by
  letI : Nonempty A := Set.nonempty_coe_sort.mpr hA
  refine ⟨?_⟩
  intro x y
  obtain ⟨w, hw⟩ := exists_cubicWalk_support_between d x.1 y.1
  have hsupport : ∀ z ∈ w.support, z ∈ A := fun z hz ↦
    hconvex x.2 y.2 (hw z hz)
  let q := w.induce A hsupport
  exact ⟨by simpa [q] using q⟩

theorem cubicRegionGraph_univ_connected (d : ℕ) :
    (cubicRegionGraph d Set.univ).Connected :=
  cubicRegionGraph_connected_of_coordinateConvex Set.univ_nonempty
    (fun {_x} _hx {_y} _hy {z} _hz ↦ Set.mem_univ z)

/-- The open cluster of `x` when all paths are constrained to the region `A`. -/
def cubicOpenClusterWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (ω : EdgeConfiguration d) (x : Cubic d) : Set (Cubic d) :=
  {y | y ∈ A ∧ ω ∈ connectionEventWithinVertices d A x y}

@[simp]
theorem cubicOpenClusterWithinVertices_univ
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) :
    cubicOpenClusterWithinVertices d Set.univ ω x = cubicOpenClusterFrom d ω x := by
  ext y
  simp [cubicOpenClusterWithinVertices, cubicOpenClusterFrom,
    connectionEventWithinVertices_univ, connectionEvent]

theorem cubicOpenClusterWithinVertices_mono {d : ℕ} {A B : Set (Cubic d)}
    (hAB : A ⊆ B) (ω : EdgeConfiguration d) (x : Cubic d) :
    cubicOpenClusterWithinVertices d A ω x ⊆
      cubicOpenClusterWithinVertices d B ω x := by
  rintro y ⟨hyA, hy⟩
  exact ⟨hAB hyA, connectionEventWithinVertices_mono hAB x y hy⟩

/-- There is a self-avoiding open path of length at least `n`, starting at `x` and supported in
`A`. -/
def hasOpenPathOfLengthAtLeastWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) : Prop :=
  ∃ y, ∃ w : (cubicGraph d).Walk x y,
    w.IsPath ∧ n ≤ w.length ∧ walkIsOpen ω w ∧ ∀ z ∈ w.support, z ∈ A

/-- Arbitrarily long self-avoiding open paths constrained to `A`. -/
def hasArbitrarilyLongOpenPathsWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (ω : EdgeConfiguration d) (x : Cubic d) : Prop :=
  ∀ n, hasOpenPathOfLengthAtLeastWithinVertices d A ω x n

theorem measurableSet_hasOpenPathOfLengthAtLeastWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (x : Cubic d) (n : ℕ) :
    MeasurableSet {ω | hasOpenPathOfLengthAtLeastWithinVertices d A ω x n} := by
  have hrepr : {ω | hasOpenPathOfLengthAtLeastWithinVertices d A ω x n} =
      ⋃ (steps : List (CubicDirection d))
        (_hpath : (cubicWalkFrom x steps).IsPath)
        (_hlen : n ≤ steps.length)
        (_hA : ∀ z ∈ (cubicWalkFrom x steps).support, z ∈ A),
        {ω : EdgeConfiguration d | walkIsOpen ω (cubicWalkFrom x steps)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, w, hwpath, hwlen, hwopen, hwA⟩
      obtain ⟨steps, hend, hcopy, hlen⟩ := exists_cubicWalkFrom_copy_eq w
      have hpath : (cubicWalkFrom x steps).IsPath := by
        have : ((cubicWalkFrom x steps).copy rfl hend).IsPath := hcopy ▸ hwpath
        simpa using this
      have hA : ∀ z ∈ (cubicWalkFrom x steps).support, z ∈ A := by
        intro z hz
        apply hwA z
        have hz' : z ∈ ((cubicWalkFrom x steps).copy rfl hend).support := by simpa using hz
        exact hcopy ▸ hz'
      refine ⟨steps, hpath, ?_, hA, ?_⟩
      · simpa [hlen] using hwlen
      · have : walkIsOpen ω ((cubicWalkFrom x steps).copy rfl hend) := hcopy ▸ hwopen
        exact (walkIsOpen_copy (cubicWalkFrom x steps) rfl hend).mp this
    · rintro ⟨steps, hpath, hlen, hA, hopen⟩
      exact ⟨cubicEndpointFrom x steps, cubicWalkFrom x steps, hpath,
        by simpa [cubicWalkFrom_length] using hlen, hopen, hA⟩
  rw [hrepr]
  exact MeasurableSet.iUnion fun steps ↦ MeasurableSet.iUnion fun _hpath ↦
    MeasurableSet.iUnion fun _hlen ↦ MeasurableSet.iUnion fun _hA ↦
      measurableSet_walkIsOpen _

private theorem mem_cubicOpenClusterWithinVertices_of_mem_support
    {d : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d}
    {x y z : Cubic d} {w : (cubicGraph d).Walk x y}
    (hopen : walkIsOpen ω w) (hA : ∀ q ∈ w.support, q ∈ A)
    (hz : z ∈ w.support) : z ∈ cubicOpenClusterWithinVertices d A ω x := by
  constructor
  · exact hA z hz
  · induction w with
    | nil =>
        rw [SimpleGraph.Walk.mem_support_nil_iff] at hz
        subst z
        exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simp [hA]⟩
    | @cons u v y huv p ih =>
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simp [hA]⟩
        · have hopenTail : walkIsOpen ω p := by
            intro e he
            exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
          have hATail : ∀ q ∈ p.support, q ∈ A := by
            intro q hq
            exact hA q (by simp [hq])
          rcases ih hopenTail hATail hz with ⟨q, hqopen, hqA⟩
          refine ⟨SimpleGraph.Walk.cons huv q, ?_, ?_⟩
          · intro e he
            simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
            rcases he with he | he
            · subst e
              exact hopen _ (by simp [SimpleGraph.Walk.edges_cons])
            · exact hqopen e he
          · intro q' hq'
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hq'
            rcases hq' with rfl | hq'
            · exact hA _ (by simp)
            · exact hqA q' hq'

private theorem cubicOpenClusterWithinVertices_finite_of_not_hasOpenPath
    {d n : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d} {x : Cubic d}
    (hno : ¬ hasOpenPathOfLengthAtLeastWithinVertices d A ω x n) :
    (cubicOpenClusterWithinVertices d A ω x).Finite := by
  apply (cubicEndpointsOfLengthLT_finite d x n).subset
  intro y hy
  rcases hy.2 with ⟨w, hwopen, hwA⟩
  let q : (cubicGraph d).Walk x y := w.toPath
  have hqpath : q.IsPath := w.toPath.property
  have hqopen : walkIsOpen ω q := walkIsOpen_toPath w hwopen
  have hqA : ∀ z ∈ q.support, z ∈ A := by
    intro z hz
    exact hwA z (w.support_toPath_subset hz)
  have hlen : q.length < n := by
    by_contra hn
    exact hno ⟨y, q, hqpath, le_of_not_gt hn, hqopen, hqA⟩
  rcases exists_cubicWalkFrom_copy_eq q with ⟨steps, hend, _hcopy, hsteps⟩
  exact ⟨⟨q.length, hlen⟩, ⟨steps, hsteps⟩, hend.symm⟩

theorem cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong
    {d : ℕ} {A : Set (Cubic d)} {ω : EdgeConfiguration d} {x : Cubic d} :
    (cubicOpenClusterWithinVertices d A ω x).Infinite ↔
      hasArbitrarilyLongOpenPathsWithinVertices d A ω x := by
  constructor
  · intro hinf n
    by_contra hno
    exact hinf (cubicOpenClusterWithinVertices_finite_of_not_hasOpenPath hno)
  · intro hpaths
    rw [← Set.not_finite]
    intro hfinite
    let n := (cubicOpenClusterWithinVertices d A ω x).ncard
    rcases hpaths n with ⟨y, w, hwpath, hwlen, hwopen, hwA⟩
    let supportSet : Set (Cubic d) := {z | z ∈ w.support}
    have hsfinite : supportSet.Finite := by
      classical
      exact w.support.finite_toSet
    have hsub : supportSet ⊆ cubicOpenClusterWithinVertices d A ω x := by
      intro z hz
      exact mem_cubicOpenClusterWithinVertices_of_mem_support hwopen hwA hz
    have hcard := Set.ncard_le_ncard hsub hfinite
    have hsCard : supportSet.ncard = w.length + 1 := by
      classical
      rw [Set.ncard_eq_toFinset_card supportSet hsfinite]
      have heq : hsfinite.toFinset = w.support.toFinset := by ext z; simp [supportSet]
      rw [heq, List.toFinset_card_of_nodup hwpath.support_nodup,
        SimpleGraph.Walk.length_support]
    have : w.length + 1 ≤ n := by simpa [n, hsCard] using hcard
    omega

/-- There is an infinite open component in the graph induced by `A`. -/
def hasInfiniteOpenClusterInVertices
    (d : ℕ) (A : Set (Cubic d)) (ω : EdgeConfiguration d) : Prop :=
  ∃ x ∈ A, (cubicOpenClusterWithinVertices d A ω x).Infinite

theorem measurableSet_hasInfiniteOpenClusterInVertices (d : ℕ) (A : Set (Cubic d)) :
    MeasurableSet {ω | hasInfiniteOpenClusterInVertices d A ω} := by
  have hrepr : {ω | hasInfiniteOpenClusterInVertices d A ω} =
      ⋃ (x : Cubic d) (_hx : x ∈ A),
        ⋂ n : ℕ, {ω | hasOpenPathOfLengthAtLeastWithinVertices d A ω x n} := by
    ext ω
    simp only [Set.mem_setOf_eq, hasInfiniteOpenClusterInVertices, Set.mem_iUnion,
      Set.mem_iInter]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, hx, cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mp hinf⟩
    · rintro ⟨x, hx, hpaths⟩
      exact ⟨x, hx, cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong.mpr hpaths⟩
  rw [hrepr]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun _hx ↦
    MeasurableSet.iInter fun n ↦
      measurableSet_hasOpenPathOfLengthAtLeastWithinVertices d A x n

theorem measurableSet_cubicOpenClusterWithinVertices_infinite
    (d : ℕ) (A : Set (Cubic d)) (x : Cubic d) :
    MeasurableSet {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} := by
  have hrepr : {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} =
      ⋂ n : ℕ, {ω | hasOpenPathOfLengthAtLeastWithinVertices d A ω x n} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact cubicOpenClusterWithinVertices_infinite_iff_arbitrarilyLong
  rw [hrepr]
  exact MeasurableSet.iInter fun n ↦
      measurableSet_hasOpenPathOfLengthAtLeastWithinVertices d A x n

theorem isIncreasingEvent_cubicOpenClusterWithinVertices_infinite
    (d : ℕ) (A : Set (Cubic d)) (x : Cubic d) :
    IsIncreasingEvent {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} := by
  rintro ω η hωη hxinf
  refine hxinf.mono ?_
  rintro y ⟨hyA, w, hwopen, hwA⟩
  exact ⟨hyA, w, fun e he ↦ hωη (hwopen e he), hwA⟩

theorem hasInfiniteOpenClusterInVertices_mono_region {d : ℕ} {A B : Set (Cubic d)}
    (hAB : A ⊆ B) :
    {ω | hasInfiniteOpenClusterInVertices d A ω} ⊆
      {ω | hasInfiniteOpenClusterInVertices d B ω} := by
  rintro ω ⟨x, hxA, hxinf⟩
  exact ⟨x, hAB hxA,
    hxinf.mono (cubicOpenClusterWithinVertices_mono hAB ω x)⟩

theorem isIncreasingEvent_hasInfiniteOpenClusterInVertices
    (d : ℕ) (A : Set (Cubic d)) :
    IsIncreasingEvent {ω | hasInfiniteOpenClusterInVertices d A ω} := by
  rintro ω η hωη ⟨x, hxA, hxinf⟩
  refine ⟨x, hxA, hxinf.mono ?_⟩
  rintro y ⟨hyA, w, hwopen, hwA⟩
  exact ⟨hyA, w, fun e he ↦ hωη (hwopen e he), hwA⟩

/-- Percolation probability from a specified vertex in the subgraph induced by `A`. -/
noncomputable def regionThetaFrom
    (d : ℕ) (A : Set (Cubic d)) (p : I) (x : Cubic d) : ℝ :=
  (bernoulliBondMeasure d p).real
    {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite}

@[simp]
theorem regionThetaFrom_univ (d : ℕ) (p : I) (x : Cubic d) :
    regionThetaFrom d Set.univ p x = thetaFrom d p x := by
  simp [regionThetaFrom, thetaFrom, hasInfiniteOpenClusterFrom]

theorem connectionWithin_inter_infiniteCluster_subset
    (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    connectionEventWithinVertices d A y x ∩
        {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} ⊆
      {ω | (cubicOpenClusterWithinVertices d A ω y).Infinite} := by
  rintro ω ⟨⟨w, hwopen, hwA⟩, hxinf⟩
  refine hxinf.mono ?_
  rintro z ⟨hzA, wz, hwzopen, hwzA⟩
  exact ⟨hzA, w.append wz, walkIsOpen_append hwopen hwzopen, by
    intro q hq
    rw [SimpleGraph.Walk.support_append] at hq
    exact List.mem_append.mp hq |>.elim (hwA q)
      (fun h ↦ hwzA q (List.mem_of_mem_tail h))⟩

theorem bernoulliBondMeasure_real_connectionWithin_mul_regionThetaFrom_le
    (d : ℕ) (A : Set (Cubic d)) (p : I) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (connectionEventWithinVertices d A y x) *
        regionThetaFrom d A p x ≤ regionThetaFrom d A p y := by
  have hfkg := setBernoulli_real_fkg p
    (isIncreasingEvent_connectionEventWithinVertices d A y x)
    (isIncreasingEvent_cubicOpenClusterWithinVertices_infinite d A x)
    (measurableSet_connectionEventWithinVertices d A y x)
    (measurableSet_cubicOpenClusterWithinVertices_infinite d A x)
  exact hfkg.trans (measureReal_mono
    (connectionWithin_inter_infiniteCluster_subset d A x y))

theorem bernoulliBondMeasure_real_connectionWithin_pos_of_connected
    {d : ℕ} {A : Set (Cubic d)} (hAconn : (cubicRegionGraph d A).Connected)
    (p : I) (hp : 0 < (p : ℝ)) {x y : Cubic d} (hx : x ∈ A) (hy : y ∈ A) :
    0 < (bernoulliBondMeasure d p).real (connectionEventWithinVertices d A x y) := by
  obtain ⟨wA, _hwApath⟩ := hAconn.exists_isPath (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)
  let emb := SimpleGraph.Embedding.induce (G := cubicGraph d) A
  let w : (cubicGraph d).Walk x y := wA.map emb.toHom
  let q : (cubicGraph d).Walk x y := w.toPath
  have hsub : {ω : EdgeConfiguration d | walkIsOpen ω q} ⊆
      connectionEventWithinVertices d A x y := by
    intro ω hω
    refine ⟨q, hω, ?_⟩
    intro z hz
    have hz' : z ∈ w.support := w.support_toPath_subset hz
    change z ∈ (wA.map emb.toHom).support at hz'
    rw [SimpleGraph.Walk.support_map] at hz'
    obtain ⟨zA, _hzA, hzAeq⟩ := List.mem_map.mp hz'
    simpa [emb] using hzAeq ▸ zA.property
  have hqtrail : q.IsTrail := by simp [q]
  exact (bernoulliBondMeasure_real_walkIsOpen_pos p q hqtrail hp).trans_le
    (measureReal_mono hsub)

theorem regionThetaFrom_eq_zero_iff_of_connected
    {d : ℕ} {A : Set (Cubic d)} (hAconn : (cubicRegionGraph d A).Connected)
    (p : I) {x y : Cubic d} (hx : x ∈ A) (hy : y ∈ A) :
    regionThetaFrom d A p x = 0 ↔ regionThetaFrom d A p y = 0 := by
  by_cases hp : (p : ℝ) = 0
  · have hroot (z : Cubic d) : regionThetaFrom d A p z = 0 := by
      apply le_antisymm
      · have hsub : {ω | (cubicOpenClusterWithinVertices d A ω z).Infinite} ⊆
            {ω | hasInfiniteOpenClusterFrom d ω z} := by
          intro ω hzinf
          exact hzinf.mono fun u hu ↦
            connectionEventWithinVertices_subset_connectionEvent d A z u hu.2
        exact (measureReal_mono hsub).trans_eq
          (thetaFrom_eq_zero_of_coe_eq_zero d hp z)
      · exact measureReal_nonneg
    simp [hroot]
  · have hp' : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp)
    have key : ∀ {u v : Cubic d}, u ∈ A → v ∈ A →
        regionThetaFrom d A p u = 0 → regionThetaFrom d A p v = 0 := by
      intro u v hu hv hu0
      have hle := bernoulliBondMeasure_real_connectionWithin_mul_regionThetaFrom_le
        d A p v u
      rw [hu0] at hle
      have hpos := bernoulliBondMeasure_real_connectionWithin_pos_of_connected
        hAconn p hp' hu hv
      apply le_antisymm
      · by_contra hnot
        have hvpos : 0 < regionThetaFrom d A p v :=
          lt_of_not_ge hnot
        exact (not_le_of_gt (mul_pos hpos hvpos)) hle
      · exact measureReal_nonneg
    exact ⟨key hx hy, key hy hx⟩

/-- Origin-rooted percolation probability in the subgraph induced by `A`. -/
noncomputable def regionTheta (d : ℕ) (A : Set (Cubic d)) (p : I) : ℝ :=
  regionThetaFrom d A p cubicOrigin

/-- Probability that the region contains some infinite open component.  This root-free quantity
is used to define the critical probability of regions not containing the origin. -/
noncomputable def regionHasInfiniteClusterProbability
    (d : ℕ) (A : Set (Cubic d)) (p : I) : ℝ :=
  (bernoulliBondMeasure d p).real {ω | hasInfiniteOpenClusterInVertices d A ω}

theorem regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected
    {d : ℕ} {A : Set (Cubic d)} (hAconn : (cubicRegionGraph d A).Connected)
    (p : I) {x : Cubic d} (hx : x ∈ A) :
    regionHasInfiniteClusterProbability d A p = 0 ↔ regionThetaFrom d A p x = 0 := by
  let μ := bernoulliBondMeasure d p
  constructor
  · intro hglobal
    apply le_antisymm
    · have hsub : {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} ⊆
          {ω | hasInfiniteOpenClusterInVertices d A ω} :=
        fun _ω hω ↦ ⟨x, hx, hω⟩
      exact (measureReal_mono hsub).trans_eq hglobal
    · exact measureReal_nonneg
  · intro hxzero
    have hyzero : ∀ (y : Cubic d), y ∈ A → regionThetaFrom d A p y = 0 := by
      intro y hy
      exact (regionThetaFrom_eq_zero_iff_of_connected hAconn p hx hy).mp hxzero
    have hevent : {ω | hasInfiniteOpenClusterInVertices d A ω} =
        ⋃ y : A, {ω | (cubicOpenClusterWithinVertices d A ω y.1).Infinite} := by
      ext ω
      simp [hasInfiniteOpenClusterInVertices]
    have hymeasure : ∀ y : A,
        μ {ω | (cubicOpenClusterWithinVertices d A ω y.1).Infinite} = 0 := by
      intro y
      apply (measureReal_eq_zero_iff (μ := μ)).mp
      simpa [μ, regionThetaFrom] using hyzero y.1 y.2
    have hunion : μ (⋃ y : A,
        {ω | (cubicOpenClusterWithinVertices d A ω y.1).Infinite}) = 0 := by
      apply le_antisymm
      · refine (measure_iUnion_le (μ := μ) (fun y : A ↦
          {ω | (cubicOpenClusterWithinVertices d A ω y.1).Infinite})).trans_eq ?_
        simp_rw [hymeasure]
        exact tsum_zero
      · exact bot_le
    apply (measureReal_eq_zero_iff (μ := μ)).mpr
    rw [hevent]
    exact hunion

theorem regionHasInfiniteClusterProbability_mono_region {d : ℕ} {A B : Set (Cubic d)}
    (hAB : A ⊆ B) (p : I) :
    regionHasInfiniteClusterProbability d A p ≤
      regionHasInfiniteClusterProbability d B p := by
  exact measureReal_mono
    (hasInfiniteOpenClusterInVertices_mono_region hAB)

theorem regionHasInfiniteClusterProbability_mono_density
    (d : ℕ) (A : Set (Cubic d)) :
    Monotone (regionHasInfiniteClusterProbability d A) := by
  intro p q hpq
  exact (isIncreasingEvent_hasInfiniteOpenClusterInVertices d A).setBernoulli_real_mono
    (measurableSet_hasInfiniteOpenClusterInVertices d A) hpq

theorem regionHasInfiniteClusterProbability_zero_density
    (d : ℕ) (A : Set (Cubic d)) :
    regionHasInfiniteClusterProbability d A (⟨0, by simp⟩ : I) = 0 := by
  let p0 : I := ⟨0, by simp⟩
  let μ := bernoulliBondMeasure d p0
  have hsub : {ω | hasInfiniteOpenClusterInVertices d A ω} ⊆
      ⋃ x : Cubic d, {ω | hasInfiniteOpenClusterFrom d ω x} := by
    rintro ω ⟨x, _hxA, hxinf⟩
    refine Set.mem_iUnion.mpr ⟨x, hxinf.mono ?_⟩
    rintro y ⟨_hyA, hy⟩
    exact connectionEventWithinVertices_subset_connectionEvent d A x y hy
  have hxzero : ∀ x : Cubic d, μ {ω | hasInfiniteOpenClusterFrom d ω x} = 0 := by
    intro x
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    simpa [μ, p0, thetaFrom] using
      (thetaFrom_eq_zero_of_coe_eq_zero d (p := p0) (by simp [p0]) x)
  have hunion : μ (⋃ x : Cubic d, {ω | hasInfiniteOpenClusterFrom d ω x}) = 0 := by
    apply le_antisymm
    · exact (measure_iUnion_le _).trans_eq (by simp [hxzero])
    · exact bot_le
  apply (measureReal_eq_zero_iff (μ := μ)).mpr
  exact measure_mono_null hsub hunion

private theorem regionCriticalZeroSet_nonempty (d : ℕ) (A : Set (Cubic d)) :
    (((fun p : I ↦ (p : ℝ)) ''
      {p : I | regionHasInfiniteClusterProbability d A p = 0}) : Set ℝ).Nonempty := by
  exact ⟨0, ⟨(⟨0, by simp⟩ : I), regionHasInfiniteClusterProbability_zero_density d A, rfl⟩⟩

private theorem regionCriticalZeroSet_bddAbove (d : ℕ) (A : Set (Cubic d)) :
    BddAbove (((fun p : I ↦ (p : ℝ)) ''
      {p : I | regionHasInfiniteClusterProbability d A p = 0}) : Set ℝ) := by
  refine ⟨1, ?_⟩
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

/-- Bond critical probability of the cubic subgraph induced by `A`. -/
noncomputable def regionCriticalProbability (d : ℕ) (A : Set (Cubic d)) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) ''
    {p : I | regionHasInfiniteClusterProbability d A p = 0}) : Set ℝ)

theorem regionCriticalProbability_nonneg (d : ℕ) (A : Set (Cubic d)) :
    0 ≤ regionCriticalProbability d A := by
  rw [regionCriticalProbability]
  exact le_csSup (regionCriticalZeroSet_bddAbove d A)
    ⟨(⟨0, by simp⟩ : I), regionHasInfiniteClusterProbability_zero_density d A, rfl⟩

theorem regionCriticalProbability_le_one (d : ℕ) (A : Set (Cubic d)) :
    regionCriticalProbability d A ≤ 1 := by
  rw [regionCriticalProbability]
  apply csSup_le (regionCriticalZeroSet_nonempty d A)
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

theorem regionCriticalProbability_anti {d : ℕ} {A B : Set (Cubic d)}
    (hAB : A ⊆ B) :
    regionCriticalProbability d B ≤ regionCriticalProbability d A := by
  rw [regionCriticalProbability, regionCriticalProbability]
  apply csSup_le (regionCriticalZeroSet_nonempty d B)
  rintro q ⟨p, hpB, rfl⟩
  apply le_csSup (regionCriticalZeroSet_bddAbove d A)
  refine ⟨p, ?_, rfl⟩
  apply le_antisymm
  · exact (regionHasInfiniteClusterProbability_mono_region hAB p).trans_eq hpB
  · exact measureReal_nonneg

theorem regionHasInfiniteClusterProbability_eq_zero_of_lt_critical
    {d : ℕ} {A : Set (Cubic d)} {p : I}
    (hp : (p : ℝ) < regionCriticalProbability d A) :
    regionHasInfiniteClusterProbability d A p = 0 := by
  rw [regionCriticalProbability] at hp
  obtain ⟨q, ⟨qI, hqzero, rfl⟩, hpq⟩ :=
    exists_lt_of_lt_csSup (regionCriticalZeroSet_nonempty d A) hp
  apply le_antisymm
  · exact (regionHasInfiniteClusterProbability_mono_density d A
      (show p ≤ qI by exact_mod_cast hpq.le)).trans_eq hqzero
  · exact measureReal_nonneg

theorem regionHasInfiniteClusterProbability_pos_of_critical_lt
    {d : ℕ} {A : Set (Cubic d)} {p : I}
    (hp : regionCriticalProbability d A < (p : ℝ)) :
    0 < regionHasInfiniteClusterProbability d A p := by
  apply lt_of_le_of_ne measureReal_nonneg
  intro hzero
  have hmem : (p : ℝ) ∈ (((fun q : I ↦ (q : ℝ)) ''
      {q : I | regionHasInfiniteClusterProbability d A q = 0}) : Set ℝ) :=
    ⟨p, hzero.symm, rfl⟩
  have hle : (p : ℝ) ≤ regionCriticalProbability d A := by
    rw [regionCriticalProbability]
    exact le_csSup (regionCriticalZeroSet_bddAbove d A) hmem
  exact (not_le_of_gt hp) hle

theorem regionCriticalProbability_univ (d : ℕ) :
    regionCriticalProbability d Set.univ = cubicCriticalProbability d := by
  have hsets : (((fun p : I ↦ (p : ℝ)) ''
      {p : I | regionHasInfiniteClusterProbability d Set.univ p = 0}) : Set ℝ) =
      (((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0}) : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨q, hqzero, rfl⟩
      refine ⟨q, ?_, rfl⟩
      have hroot :=
        (regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected
          (cubicRegionGraph_univ_connected d) q
          (by simp : cubicOrigin ∈ (Set.univ : Set (Cubic d)))).mp hqzero
      simpa using hroot
    · rintro ⟨q, hqzero, rfl⟩
      refine ⟨q, ?_, rfl⟩
      apply
        (regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected
          (cubicRegionGraph_univ_connected d) q
          (by simp : cubicOrigin ∈ (Set.univ : Set (Cubic d)))).mpr
      simpa using hqzero
  rw [regionCriticalProbability, cubicCriticalProbability, hsets]

/-! ### Site percolation on a graph -/

/-- The graph containing exactly those edges whose endpoints are both open sites. -/
def siteOpenGraph {V : Type*} (G : SimpleGraph V) (η : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ η ∧ y ∈ η
  symm := by
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := ⟨by
    intro x hx
    exact G.loopless.irrefl x hx.1⟩

@[simp]
theorem siteOpenGraph_adj {V : Type*} {G : SimpleGraph V} {η : Set V} {x y : V} :
    (siteOpenGraph G η).Adj x y ↔ G.Adj x y ∧ x ∈ η ∧ y ∈ η :=
  Iff.rfl

/-- The site-connection event between two vertices, expressed using a walk in the fixed graph.
This witness formulation makes measurability transparent on countable graphs. -/
def siteConnectionEvent {V : Type*} (G : SimpleGraph V) (x y : V) : Set (Set V) :=
  {η | ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ η}

/-- A site-open connection constrained to a finite vertex set. -/
def siteConnectionEventIn {V : Type*} (G : SimpleGraph V) (R : Finset V)
    (x y : V) : Set (Set V) :=
  {η | ∃ w : G.Walk x y,
    (∀ z ∈ w.support, z ∈ R) ∧ ∀ z ∈ w.support, z ∈ η}

theorem dependsOn_siteConnectionEventIn {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (x y : V) :
    DependsOn R (siteConnectionEventIn G R x y) := by
  intro η ξ hagree
  constructor
  · rintro ⟨w, hwR, hwη⟩
    exact ⟨w, hwR, fun z hz ↦ (hagree z (hwR z hz)).mp (hwη z hz)⟩
  · rintro ⟨w, hwR, hwξ⟩
    exact ⟨w, hwR, fun z hz ↦ (hagree z (hwR z hz)).mpr (hwξ z hz)⟩

theorem measurableSet_siteConnectionEventIn {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (x y : V) :
    MeasurableSet (siteConnectionEventIn G R x y) :=
  (dependsOn_siteConnectionEventIn G R x y).measurableSet

theorem isIncreasingEvent_siteConnectionEventIn {V : Type*} (G : SimpleGraph V)
    (R : Finset V) (x y : V) :
    IsIncreasingEvent (siteConnectionEventIn G R x y) := by
  intro η ξ hηξ
  rintro ⟨w, hwR, hwη⟩
  exact ⟨w, hwR, fun z hz ↦ hηξ (hwη z hz)⟩

/-- The site-open cluster of a vertex. -/
def siteOpenCluster {V : Type*} (G : SimpleGraph V) (η : Set V) (x : V) : Set V :=
  {y | η ∈ siteConnectionEvent G x y}

theorem siteOpenCluster_eq_reachable {V : Type*} (G : SimpleGraph V) (η : Set V) (x : V) :
    siteOpenCluster G η x = {y | x ∈ η ∧ (siteOpenGraph G η).Reachable x y} := by
  ext y
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨hw x (by simp), ?_⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.rfl
    | @cons u v y huv q ih =>
        apply SimpleGraph.Reachable.trans
          (SimpleGraph.Adj.reachable (siteOpenGraph_adj.mpr
            ⟨huv, hw u (by simp), hw v (by simp)⟩))
        exact ih fun z hz ↦ hw z (by simp [hz])
  · rintro ⟨hx, ⟨w⟩⟩
    let f : siteOpenGraph G η →g G :=
      { toFun := id
        map_rel' := fun h ↦ (siteOpenGraph_adj.mp h).1 }
    let q : G.Walk x y := w.map f
    refine ⟨q, ?_⟩
    intro z hz
    have hzMap : z ∈ w.support.map f := by
      change z ∈ (w.map f).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      exact hz
    obtain ⟨z', hz', hz'eq⟩ := List.mem_map.mp hzMap
    have hz'eq' : z' = z := by simpa [f] using hz'eq
    have hopenSupport : ∀ {a b : V} (r : (siteOpenGraph G η).Walk a b),
        a ∈ η → ∀ z ∈ r.support, z ∈ η := by
      intro a b r
      induction r with
      | nil =>
          intro ha z hz
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          subst z
          exact ha
      | @cons a b c hab r ih =>
          intro ha z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact ha
          · exact ih (siteOpenGraph_adj.mp hab).2.2 z hz
    exact hz'eq' ▸ hopenSupport w hx z' hz'

theorem siteOpenCluster_subset {V : Type*} (G : SimpleGraph V) (η : Set V) (x : V) :
    siteOpenCluster G η x ⊆ η := by
  intro y hy
  obtain ⟨w, hw⟩ := hy
  exact hw y (by simp)

theorem measurableSet_siteConnectionEvent {V : Type*} [Countable V]
    (G : SimpleGraph V) (x y : V) : MeasurableSet (siteConnectionEvent G x y) := by
  classical
  have hrepr : siteConnectionEvent G x y =
      ⋃ l : List V, ⋃ (_hl : ∃ w : G.Walk x y, w.support = l),
        ⋂ z ∈ l.toFinset, {η : Set V | z ∈ η} := by
    ext η
    constructor
    · rintro ⟨w, hw⟩
      refine Set.mem_iUnion.mpr ⟨w.support, Set.mem_iUnion.mpr ⟨⟨w, rfl⟩, ?_⟩⟩
      simp only [Set.mem_iInter]
      intro z
      simp only [List.mem_toFinset, Set.mem_setOf_eq]
      intro hz
      exact hw z hz
    · intro hη
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hη
      obtain ⟨⟨w, rfl⟩, hw⟩ := Set.mem_iUnion.mp hl
      refine ⟨w, fun z hz ↦ ?_⟩
      have hz' := Set.mem_iInter.mp hw z
      exact Set.mem_iInter.mp hz' (by simpa using hz)
  rw [hrepr]
  exact MeasurableSet.iUnion fun l ↦ MeasurableSet.iUnion fun _hl ↦
    l.toFinset.measurableSet_biInter fun z _hz ↦ measurableSet_mem z

/-- A site configuration has an infinite open component. -/
def hasInfiniteSiteCluster {V : Type*} (G : SimpleGraph V) (η : Set V) : Prop :=
  ∃ x, (siteOpenCluster G η x).Infinite

theorem Set.Infinite.of_hasInfiniteSiteCluster {V : Type*} {G : SimpleGraph V}
    {η : Set V} (hη : hasInfiniteSiteCluster G η) : η.Infinite := by
  obtain ⟨x, hx⟩ := hη
  exact hx.mono (siteOpenCluster_subset G η x)

theorem measurableSet_hasInfiniteSiteCluster {V : Type*} [Countable V]
    (G : SimpleGraph V) : MeasurableSet {η : Set V | hasInfiniteSiteCluster G η} := by
  classical
  have hrepr : {η : Set V | hasInfiniteSiteCluster G η} =
      ⋃ x : V, ⋂ s : Finset V, ⋃ y : V, ⋃ (_hy : y ∉ s), siteConnectionEvent G x y := by
    ext η
    simp only [Set.mem_setOf_eq, hasInfiniteSiteCluster, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, fun s ↦ ?_⟩
      obtain ⟨y, hy, hys⟩ := hx.exists_notMem_finset s
      exact ⟨y, hys, hy⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨y, hys, hy⟩ := hx hfinite.toFinset
      exact hys (hfinite.mem_toFinset.mpr hy)
  rw [hrepr]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iInter fun s ↦
    MeasurableSet.iUnion fun y ↦ MeasurableSet.iUnion fun _hy ↦
      measurableSet_siteConnectionEvent G x y

theorem isIncreasingEvent_siteConnectionEvent {V : Type*}
    (G : SimpleGraph V) (x y : V) : IsIncreasingEvent (siteConnectionEvent G x y) := by
  rintro η ξ hηξ ⟨w, hw⟩
  exact ⟨w, fun z hz ↦ hηξ (hw z hz)⟩

theorem isIncreasingEvent_hasInfiniteSiteCluster {V : Type*} (G : SimpleGraph V) :
    IsIncreasingEvent {η : Set V | hasInfiniteSiteCluster G η} := by
  rintro η ξ hηξ ⟨x, hxinf⟩
  refine ⟨x, hxinf.mono ?_⟩
  intro y hy
  exact isIncreasingEvent_siteConnectionEvent G x y hηξ hy

/-- Site-percolation probability on a countable graph. -/
noncomputable def siteTheta {V : Type*} [Countable V]
    (G : SimpleGraph V) (p : I) : ℝ :=
  setBer((Set.univ : Set V), p).real {η | hasInfiniteSiteCluster G η}

theorem siteTheta_mono {V : Type*} [Countable V] (G : SimpleGraph V) :
    Monotone (siteTheta G) := by
  intro p q hpq
  exact (isIncreasingEvent_hasInfiniteSiteCluster G).setBernoulli_real_mono
    (measurableSet_hasInfiniteSiteCluster G) hpq

@[simp]
theorem siteTheta_zero {V : Type*} [Countable V] (G : SimpleGraph V) :
    siteTheta G (0 : I) = 0 := by
  rw [siteTheta, setBernoulli_zero]
  have hempty : ¬ hasInfiniteSiteCluster G (∅ : Set V) := by
    rintro ⟨x, hxinf⟩
    apply hxinf
    have hsub : siteOpenCluster G ∅ x ⊆ {x} := by
      rintro y ⟨w, hw⟩
      have := hw x (by simp)
      simp at this
    exact Set.Finite.subset (Set.finite_singleton x) hsub
  rw [measureReal_def, Measure.dirac_apply' _
    (measurableSet_hasInfiniteSiteCluster G)]
  simp [hempty]

/-- Critical site density on a countable graph. -/
noncomputable def siteCriticalProbability {V : Type*} [Countable V]
    (G : SimpleGraph V) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | siteTheta G p = 0}) : Set ℝ)

private theorem siteCriticalZeroSet_nonempty {V : Type*} [Countable V]
    (G : SimpleGraph V) :
    (((fun p : I ↦ (p : ℝ)) '' {p : I | siteTheta G p = 0}) : Set ℝ).Nonempty := by
  exact ⟨0, ⟨(0 : I), siteTheta_zero G, rfl⟩⟩

private theorem siteCriticalZeroSet_bddAbove {V : Type*} [Countable V]
    (G : SimpleGraph V) :
    BddAbove (((fun p : I ↦ (p : ℝ)) '' {p : I | siteTheta G p = 0}) : Set ℝ) := by
  refine ⟨1, ?_⟩
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

theorem siteCriticalProbability_nonneg {V : Type*} [Countable V]
    (G : SimpleGraph V) : 0 ≤ siteCriticalProbability G := by
  rw [siteCriticalProbability]
  exact le_csSup (siteCriticalZeroSet_bddAbove G) ⟨(0 : I), siteTheta_zero G, rfl⟩

theorem siteCriticalProbability_le_one {V : Type*} [Countable V]
    (G : SimpleGraph V) : siteCriticalProbability G ≤ 1 := by
  rw [siteCriticalProbability]
  apply csSup_le (siteCriticalZeroSet_nonempty G)
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

theorem siteTheta_eq_zero_of_lt_criticalProbability {V : Type*} [Countable V]
    {G : SimpleGraph V} {p : I} (hp : (p : ℝ) < siteCriticalProbability G) :
    siteTheta G p = 0 := by
  rw [siteCriticalProbability] at hp
  obtain ⟨q, ⟨qI, hqzero, rfl⟩, hpq⟩ :=
    exists_lt_of_lt_csSup (siteCriticalZeroSet_nonempty G) hp
  apply le_antisymm
  · exact (siteTheta_mono G (show p ≤ qI by exact_mod_cast hpq.le)).trans_eq hqzero
  · exact measureReal_nonneg

theorem siteTheta_pos_of_criticalProbability_lt {V : Type*} [Countable V]
    {G : SimpleGraph V} {p : I} (hp : siteCriticalProbability G < (p : ℝ)) :
    0 < siteTheta G p := by
  apply lt_of_le_of_ne measureReal_nonneg
  intro hzero
  have hmem : (p : ℝ) ∈
      (((fun q : I ↦ (q : ℝ)) '' {q : I | siteTheta G q = 0}) : Set ℝ) :=
    ⟨p, hzero.symm, rfl⟩
  have hle : (p : ℝ) ≤ siteCriticalProbability G := by
    rw [siteCriticalProbability]
    exact le_csSup (siteCriticalZeroSet_bddAbove G) hmem
  exact (not_le_of_gt hp) hle

/-! ### Slabs, half-spaces, and thickened regions -/

/-- Grimmett's slab `ℤ² × [0,k]^(d-2)`. -/
def cubicSlab (d k : ℕ) : Set (Cubic d) :=
  {x | ∀ i : Fin d, 2 ≤ i.val → 0 ≤ x i ∧ x i ≤ (k : ℤ)}

@[simp]
theorem cubicSlab_two (k : ℕ) : cubicSlab 2 k = Set.univ := by
  ext x
  simp only [cubicSlab, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i hi
  omega

theorem cubicSlab_nonempty (d k : ℕ) : (cubicSlab d k).Nonempty := by
  refine ⟨cubicOrigin, ?_⟩
  intro i _hi
  simp [cubicOrigin]

theorem cubicSlab_coordinateConvex (d k : ℕ) {x y z : Cubic d}
    (hx : x ∈ cubicSlab d k) (hy : y ∈ cubicSlab d k)
    (hz : CubicCoordinateBetween x y z) : z ∈ cubicSlab d k := by
  intro i hi
  have hxi := hx i hi
  have hyi := hy i hi
  rcases hz i with hzi | hzi <;> omega

theorem cubicRegionGraph_cubicSlab_connected (d k : ℕ) :
    (cubicRegionGraph d (cubicSlab d k)).Connected :=
  cubicRegionGraph_connected_of_coordinateConvex (cubicSlab_nonempty d k)
    (fun {x} hx {y} hy {z} hz ↦
      cubicSlab_coordinateConvex d k (x := x) (y := y) (z := z) hx hy hz)

/-- The coordinate half-space `ℤ^(d-1) × ℤ₊`.  The quantified definition is also total in
dimension zero, where it gives the whole singleton lattice. -/
def cubicHalfSpace (d : ℕ) : Set (Cubic d) :=
  {x | ∀ i : Fin d, i.val + 1 = d → 0 ≤ x i}

@[simp]
theorem cubicHalfSpace_zero : cubicHalfSpace 0 = Set.univ := by
  ext x
  simp [cubicHalfSpace]

theorem cubicHalfSpace_nonempty (d : ℕ) : (cubicHalfSpace d).Nonempty := by
  refine ⟨cubicOrigin, ?_⟩
  intro i _hi
  simp [cubicOrigin]

theorem cubicHalfSpace_coordinateConvex (d : ℕ) {x y z : Cubic d}
    (hx : x ∈ cubicHalfSpace d) (hy : y ∈ cubicHalfSpace d)
    (hz : CubicCoordinateBetween x y z) : z ∈ cubicHalfSpace d := by
  intro i hi
  have hxi := hx i hi
  have hyi := hy i hi
  rcases hz i with hzi | hzi <;> omega

theorem cubicRegionGraph_cubicHalfSpace_connected (d : ℕ) :
    (cubicRegionGraph d (cubicHalfSpace d)).Connected :=
  cubicRegionGraph_connected_of_coordinateConvex (cubicHalfSpace_nonempty d)
    (fun {x} hx {y} hy {z} hz ↦
      cubicHalfSpace_coordinateConvex d (x := x) (y := y) (z := z) hx hy hz)

/-- Coordinatewise integer dilation of a cubic-lattice vertex. -/
def cubicScale {d : ℕ} (a : ℤ) (x : Cubic d) : Cubic d :=
  fun i ↦ a * x i

/-- The literal thickening `2k F + B(k)` from Theorem 7.2. -/
def cubicDilatedThickening (d : ℕ) (F : Set (Cubic d)) (k : ℕ) : Set (Cubic d) :=
  {y | ∃ x ∈ F, y ∈ cubicMetricBox d (cubicScale (2 * (k : ℤ)) x) k}

/-- Literal Minkowski-sum presentation `2kF + B(k)`. -/
def cubicDilatedMinkowskiSum (d : ℕ) (F : Set (Cubic d)) (k : ℕ) : Set (Cubic d) :=
  {y | ∃ x ∈ F, ∃ b ∈ cubicMetricBox d cubicOrigin k,
    y = cubicTranslate cubicOrigin (cubicScale (2 * (k : ℤ)) x) b}

theorem cubicDilatedThickening_eq_minkowskiSum
    (d : ℕ) (F : Set (Cubic d)) (k : ℕ) :
    cubicDilatedThickening d F k = cubicDilatedMinkowskiSum d F k := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    let c := cubicScale (2 * (k : ℤ)) x
    let b := cubicTranslate c cubicOrigin y
    have hb : b ∈ cubicMetricBox d cubicOrigin k := by
      apply mem_cubicMetricBox_iff_lInfDist_le.mpr
      have hdist : cubicLInfDist cubicOrigin b = cubicLInfDist c y := by
        simpa [b, c] using cubicLInfDist_translate c cubicOrigin c y
      rw [hdist]
      exact mem_cubicMetricBox_iff_lInfDist_le.mp hy
    refine ⟨x, hx, b, hb, ?_⟩
    funext i
    simp [b, c, cubicTranslate, cubicOrigin]
  · rintro ⟨x, hx, b, hb, rfl⟩
    refine ⟨x, hx, ?_⟩
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    have hdist := cubicLInfDist_translate cubicOrigin
      (cubicScale (2 * (k : ℤ)) x) cubicOrigin b
    simpa [cubicOrigin] using
      hdist.trans_le (mem_cubicMetricBox_iff_lInfDist_le.mp hb)

/-- Critical probability of the width-`k` slab. -/
noncomputable def slabCriticalProbability (d k : ℕ) : ℝ :=
  regionCriticalProbability d (cubicSlab d k)

/-- Half-space percolation probability. -/
noncomputable def halfSpaceTheta (d : ℕ) (p : I) : ℝ :=
  regionTheta d (cubicHalfSpace d) p

theorem cubicOrigin_mem_cubicHalfSpace (d : ℕ) : cubicOrigin ∈ cubicHalfSpace d := by
  intro i _hi
  simp [cubicOrigin]

theorem cubicCriticalProbability_le_halfSpaceRegionCritical (d : ℕ) :
    cubicCriticalProbability d ≤ regionCriticalProbability d (cubicHalfSpace d) := by
  rw [← regionCriticalProbability_univ d]
  exact regionCriticalProbability_anti (Set.subset_univ (cubicHalfSpace d))

theorem regionHasInfiniteClusterProbability_eq_zero_iff_halfSpaceTheta_eq_zero
    (d : ℕ) (p : I) :
    regionHasInfiniteClusterProbability d (cubicHalfSpace d) p = 0 ↔
      halfSpaceTheta d p = 0 := by
  simpa [halfSpaceTheta, regionTheta] using
    (regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected
      (cubicRegionGraph_cubicHalfSpace_connected d) p (cubicOrigin_mem_cubicHalfSpace d))

theorem halfSpaceTheta_eq_zero_of_lt_critical {d : ℕ} {p : I}
    (hp : (p : ℝ) < regionCriticalProbability d (cubicHalfSpace d)) :
    halfSpaceTheta d p = 0 :=
  (regionHasInfiniteClusterProbability_eq_zero_iff_halfSpaceTheta_eq_zero d p).mp
    (regionHasInfiniteClusterProbability_eq_zero_of_lt_critical hp)

theorem halfSpaceTheta_pos_of_critical_lt {d : ℕ} {p : I}
    (hp : regionCriticalProbability d (cubicHalfSpace d) < (p : ℝ)) :
    0 < halfSpaceTheta d p := by
  have hglobal := regionHasInfiniteClusterProbability_pos_of_critical_lt hp
  apply lt_of_le_of_ne measureReal_nonneg
  intro hzero
  have := (regionHasInfiniteClusterProbability_eq_zero_iff_halfSpaceTheta_eq_zero d p).mpr
    hzero.symm
  exact hglobal.ne this.symm

end Percolation
