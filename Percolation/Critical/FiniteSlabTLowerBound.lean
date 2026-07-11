import Percolation.Critical.FiniteSlabLowerBound
import Percolation.Critical.TwoPoint

/-!
# Uniform connection bounds in `T_n(L)`

This file formalizes equations (7.87)--(7.88), transporting the `S_n(L)` estimate through
coordinate slices of `T_n(L)` and combining the consecutive connections by finite FKG.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ### Generic finite connection chains -/

/-- A list of consecutive vertices whose constrained connection probabilities are all at
least `δ`.  The first vertex is supplied separately so the empty tail represents a reflexive
connection. -/
def ConnectionLowerBoundChain
    {d : ℕ} (p : I) (A : Set (Cubic d)) (δ : ℝ) :
    Cubic d → List (Cubic d) → Prop
  | _, [] => True
  | x, y :: ys =>
      y ∈ A ∧
      δ ≤ (bernoulliBondMeasure d p).real
        (connectionEventWithinVertices d A x y) ∧
      ConnectionLowerBoundChain p A δ y ys

theorem connectionLowerBoundChain_append
    {d : ℕ} {p : I} {A : Set (Cubic d)} {δ : ℝ}
    {x y : Cubic d} {ys : List (Cubic d)}
    (hy : y ∈ A)
    (hxy : δ ≤ (bernoulliBondMeasure d p).real
      (connectionEventWithinVertices d A x y))
    (hys : ConnectionLowerBoundChain p A δ y ys) :
    ConnectionLowerBoundChain p A δ x (y :: ys) :=
  ⟨hy, hxy, hys⟩

/-- Finite FKG chain lemma: `r` uniformly positive consecutive connections give a connection
between the endpoints with lower bound `δ^r`. -/
theorem pow_length_le_connectionEventWithinVertices_of_lowerBoundChain
    {d : ℕ} (p : I) (A : Set (Cubic d)) {x : Cubic d}
    (ys : List (Cubic d)) (hxA : x ∈ A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hchain : ConnectionLowerBoundChain p A δ x ys) :
    δ ^ ys.length ≤ (bernoulliBondMeasure d p).real
      (connectionEventWithinVertices d A x (ys.getLastD x)) := by
  induction ys generalizing x with
  | nil =>
      simp only [List.length_nil, pow_zero, List.getLastD_nil]
      have hself : connectionEventWithinVertices d A x x = Set.univ := by
        ext ω
        constructor
        · exact fun _ ↦ Set.mem_univ ω
        · intro _
          exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using hxA⟩
      rw [hself, probReal_univ]
  | cons y ys ih =>
      rcases hchain with ⟨hyA, hxy, htail⟩
      have htailBound := ih hyA htail
      have hend : (y :: ys).getLastD x = ys.getLastD y := by
        cases ys with
        | nil => simp
        | cons z zs => simp only [List.getLastD_cons]
      have hsub : connectionEventWithinVertices d A x y ∩
          connectionEventWithinVertices d A y (ys.getLastD y) ⊆
        connectionEventWithinVertices d A x ((y :: ys).getLastD x) := by
        rintro ω ⟨⟨q, hqOpen, hqA⟩, ⟨r, hrOpen, hrA⟩⟩
        rw [hend]
        refine ⟨q.append r, walkIsOpen_append hqOpen hrOpen, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.mem_support_append_iff] at hz
        exact hz.elim (hqA z) (hrA z)
      calc
        δ ^ (y :: ys).length = δ * δ ^ ys.length := by
          simp only [List.length_cons, pow_succ]
          ring
        _ ≤ (bernoulliBondMeasure d p).real
              (connectionEventWithinVertices d A x y) *
            (bernoulliBondMeasure d p).real
              (connectionEventWithinVertices d A y (ys.getLastD y)) :=
          mul_le_mul hxy htailBound (pow_nonneg hδ _) measureReal_nonneg
        _ ≤ (bernoulliBondMeasure d p).real
            (connectionEventWithinVertices d A x y ∩
              connectionEventWithinVertices d A y (ys.getLastD y)) :=
          bernoulliBondMeasure_real_fkg p
            (isIncreasingEvent_connectionEventWithinVertices d A x y)
            (isIncreasingEvent_connectionEventWithinVertices d A y (ys.getLastD y))
            (measurableSet_connectionEventWithinVertices d A x y)
            (measurableSet_connectionEventWithinVertices d A y (ys.getLastD y))
        _ ≤ (bernoulliBondMeasure d p).real
            (connectionEventWithinVertices d A x ((y :: ys).getLastD x)) :=
          measureReal_mono hsub (measure_ne_top _ _)

/-! ### Transporting an `S_n(L)` connection -/

/-- A constrained `S_n(L)` connection pulled through a cubic graph automorphism. -/
def transportedFiniteThickSlabSConnectionEvent
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (n L : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  cubicGraphIsoConfigurationPullback F ⁻¹'
    finiteThickSlabSConnectionEvent d n L x y

theorem transportedFiniteThickSlabSConnectionEvent_probability
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (p : I) (n L : ℕ) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real
        (transportedFiniteThickSlabSConnectionEvent F n L x y) =
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ.real (finiteThickSlabSConnectionEvent d n L x y))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      (finiteThickSlabSConnectionEvent d n L x y) =
    (bernoulliBondMeasure d p).real
      (finiteThickSlabSConnectionEvent d n L x y) at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_finiteThickSlabSConnectionEvent d n L x y)] at hmap
  exact hmap

theorem transportedFiniteThickSlabSConnectionEvent_subset_connectionWithin
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (n L : ℕ)
    (x y : Cubic d) {B : Set (Cubic d)}
    (hregion : cubicGraphIsoRegion F
      (finiteThickSlabSVertices d n L : Set (Cubic d)) ⊆ B) :
    transportedFiniteThickSlabSConnectionEvent F n L x y ⊆
      connectionEventWithinVertices d B (F x) (F y) := by
  intro ω hω
  have hmapped :=
    (cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_iff
      F (finiteThickSlabSVertices d n L : Set (Cubic d)) ω x y).1 hω
  exact connectionEventWithinVertices_mono hregion (F x) (F y) hmapped

/-- Concrete data exhibiting two `T_n(L)` vertices in a common transported `S_n(L)` slice. -/
structure FiniteThickSlabSSlicePlacement
    (d n L : ℕ) (u v : Cubic d) where
  iso : cubicGraph d ≃g cubicGraph d
  source : Cubic d
  target : Cubic d
  source_mem : source ∈ finiteThickSlabSVertices d n L
  target_mem : target ∈ finiteThickSlabSVertices d n L
  map_source : iso source = u
  map_target : iso target = v
  image_subset : cubicGraphIsoRegion iso
    (finiteThickSlabSVertices d n L : Set (Cubic d)) ⊆
      (finiteThickSlabTVertices d n L : Set (Cubic d))

/-- Any transported `S_n(L)` slice placement inherits the uniform (7.79) lower bound. -/
theorem connectionT_lowerBound_of_sSlicePlacement
    {d n L : ℕ} (p : I) {u v : Cubic d}
    (P : FiniteThickSlabSSlicePlacement d n L u v)
    {δ : ℝ}
    (hS : ∀ x ∈ finiteThickSlabSVertices d n L,
      ∀ y ∈ finiteThickSlabSVertices d n L,
        δ ≤ (bernoulliBondMeasure d p).real
          (finiteThickSlabSConnectionEvent d n L x y)) :
    δ ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L u v) := by
  calc
    δ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L P.source P.target) :=
      hS P.source P.source_mem P.target P.target_mem
    _ = (bernoulliBondMeasure d p).real
        (transportedFiniteThickSlabSConnectionEvent
          P.iso n L P.source P.target) :=
      (transportedFiniteThickSlabSConnectionEvent_probability
        P.iso p n L P.source P.target).symm
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabTConnectionEvent d n L u v) := by
      have hmono : (bernoulliBondMeasure d p).real
          (transportedFiniteThickSlabSConnectionEvent
            P.iso n L P.source P.target) ≤
          (bernoulliBondMeasure d p).real
            (connectionEventWithinVertices d
              (finiteThickSlabTVertices d n L : Set (Cubic d))
              (P.iso P.source) (P.iso P.target)) := measureReal_mono
        (transportedFiniteThickSlabSConnectionEvent_subset_connectionWithin
          P.iso n L P.source P.target P.image_subset)
        (measure_ne_top _ _)
      simpa only [finiteThickSlabTConnectionEvent, P.map_source, P.map_target] using hmono

/-! ### The coordinate chain in (7.87) -/

/-- Inclusion of a horizontal coordinate index into the full cubic coordinate type. -/
def tSlabHorizontalIndex {d : ℕ} (j : Fin (d - 1)) : Fin d :=
  Fin.castLE (Nat.sub_le d 1) j

@[simp]
theorem tSlabHorizontalIndex_val {d : ℕ} (j : Fin (d - 1)) :
    (tSlabHorizontalIndex j).val = j.val := rfl

theorem tSlabHorizontalIndex_lt_last {d : ℕ} (j : Fin (d - 1)) :
    (tSlabHorizontalIndex j).val + 1 < d := by
  change j.val + 1 < d
  omega

/-- Chain vertex `s(j)`: the first `j` horizontal coordinates have been set to zero; the last
bounded coordinate is also set to zero after the first step. -/
def tSlabChainVertex {d : ℕ} (x : Cubic d) (j : ℕ) : Cubic d :=
  fun i ↦
    if i.val + 1 = d then
      if j = 0 then x i else 0
    else if i.val < j then 0 else x i

@[simp]
theorem tSlabChainVertex_zero {d : ℕ} (x : Cubic d) :
    tSlabChainVertex x 0 = x := by
  ext i
  simp [tSlabChainVertex]

@[simp]
theorem tSlabChainVertex_last {d : ℕ} (hd : 2 ≤ d) (x : Cubic d) :
    tSlabChainVertex x (d - 1) = cubicOrigin := by
  ext i
  by_cases hi : i.val + 1 = d
  · simp [tSlabChainVertex, hi, cubicOrigin]
    omega
  · have hilt : i.val < d - 1 := by omega
    simp [tSlabChainVertex, hi, hilt, cubicOrigin]

theorem tSlabChainVertex_mem_T
    {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L) (j : ℕ) :
    tSlabChainVertex x j ∈ finiteThickSlabTVertices d n L := by
  rw [mem_finiteThickSlabTVertices_iff] at hx ⊢
  intro i
  by_cases hiLast : i.val + 1 = d
  · have hxi := hx i
    simp [tSlabChainVertex, hiLast] at hxi ⊢
    by_cases hj : j = 0 <;> simp [hj, hxi]
  · have hxi := hx i
    rw [if_neg hiLast] at hxi ⊢
    by_cases hij : i.val < j
    · simp [tSlabChainVertex, hiLast, hij]
    · simpa [tSlabChainVertex, hiLast, hij] using hxi

/-- Consecutive chain vertices agree away from the coordinate currently being zeroed and,
at the first step, the final bounded coordinate. -/
theorem tSlabChainVertex_succ_eq_of_ne
    {d : ℕ} (x : Cubic d) (j : Fin (d - 1)) (i : Fin d)
    (hij : i ≠ tSlabHorizontalIndex j)
    (hLast : j.val ≠ 0 ∨ i.val + 1 ≠ d) :
    tSlabChainVertex x j.val i = tSlabChainVertex x (j.val + 1) i := by
  simp only [tSlabChainVertex]
  by_cases hiLast : i.val + 1 = d
  · rw [if_pos hiLast, if_pos hiLast]
    rcases hLast with hj | hcontra
    · simp [hj]
    · exact (hcontra hiLast).elim
  · rw [if_neg hiLast, if_neg hiLast]
    have hval : i.val ≠ j.val := by
      intro h
      apply hij
      exact Fin.ext h
    by_cases hijlt : i.val < j.val
    · simp [hijlt, Nat.lt_add_right 1 hijlt]
    · have hsucc : ¬ i.val < j.val + 1 := by omega
      simp [hijlt, hsucc]

/-- Coordinate permutation for the `j`-th slice: for `j≥2`, it sends the second unbounded
coordinate of `S_n(L)` to horizontal coordinate `j`; for `j=0,1` it is the identity. -/
def tSlabSlicePermutation {d : ℕ} (hd : 3 ≤ d) (j : Fin (d - 1)) : Fin d ≃ Fin d :=
  if hj : j.val < 2 then Equiv.refl _
  else Equiv.swap ⟨1, by omega⟩ (tSlabHorizontalIndex j)

/-- Translation offset for the `j`-th slice.  Bounded horizontal coordinates are translated
from `[0,L]` toward zero, while the two unbounded coordinates and the final bounded coordinate
have zero offset. -/
def tSlabSliceOffset {d : ℕ} (hd : 3 ≤ d) (x : Cubic d)
    (j : Fin (d - 1)) : Cubic d :=
  fun i ↦
    if ((tSlabSlicePermutation hd j).symm i).val < 2 then 0
    else if i.val + 1 = d then 0
    else tSlabChainVertex x j.val i

/-- The graph isomorphism placing the `j`-th copy of `S_n(L)` inside `T_n(L)`. -/
def tSlabSliceIso {d : ℕ} (hd : 3 ≤ d) (x : Cubic d)
    (j : Fin (d - 1)) : cubicGraph d ≃g cubicGraph d :=
  RelIso.trans (cubicCoordinatePermutationIso (tSlabSlicePermutation hd j))
    (cubicTranslationIso cubicOrigin (tSlabSliceOffset hd x j))

@[simp]
theorem tSlabSliceIso_apply
    {d : ℕ} (hd : 3 ≤ d) (x z : Cubic d) (j : Fin (d - 1)) (i : Fin d) :
    tSlabSliceIso hd x j z i =
      z ((tSlabSlicePermutation hd j).symm i) + tSlabSliceOffset hd x j i := by
  simp [tSlabSliceIso, cubicTranslate, cubicOrigin,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]

@[simp]
theorem tSlabSlicePermutation_last
    {d : ℕ} (hd : 3 ≤ d) (j : Fin (d - 1)) :
    tSlabSlicePermutation hd j ⟨d - 1, by omega⟩ = ⟨d - 1, by omega⟩ := by
  by_cases hj : j.val < 2
  · simp [tSlabSlicePermutation, hj]
  · have hlastOne : (⟨d - 1, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hlastJ : (⟨d - 1, by omega⟩ : Fin d) ≠ tSlabHorizontalIndex j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      exact (Nat.ne_of_lt (tSlabHorizontalIndex_lt_last j)) (by omega)
    simp [tSlabSlicePermutation, hj,
      Equiv.swap_apply_of_ne_of_ne hlastOne hlastJ]

@[simp]
theorem tSlabSlicePermutation_symm_last
    {d : ℕ} (hd : 3 ≤ d) (j : Fin (d - 1)) :
    (tSlabSlicePermutation hd j).symm ⟨d - 1, by omega⟩ =
      ⟨d - 1, by omega⟩ := by
  apply (tSlabSlicePermutation hd j).injective
  simp

theorem tSlabSlicePermutation_apply_ne_last_of_val_lt_two
    {d : ℕ} (hd : 3 ≤ d) (j : Fin (d - 1)) (i : Fin d)
    (hi : i.val < 2) :
    tSlabSlicePermutation hd j i ≠ ⟨d - 1, by omega⟩ := by
  intro h
  have h' := congrArg (tSlabSlicePermutation hd j).symm h
  simp at h'
  have := congrArg Fin.val h'
  simp at this
  omega

theorem tSlabChainVertex_horizontal_bounds
    {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    (j : ℕ) (i : Fin d) (hiLast : i.val + 1 ≠ d) :
    -((n : ℕ) : ℤ) ≤ tSlabChainVertex x j i ∧
      tSlabChainVertex x j i ≤ 0 := by
  have hxi := mem_finiteThickSlabTVertices_iff.mp hx i
  rw [if_neg hiLast] at hxi
  have habs : |x i| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact Int.ofNat_le.mpr hxi
  have hxBounds := abs_le.mp habs
  by_cases hij : i.val < j
  · simp [tSlabChainVertex, hiLast, hij]
  · simpa [tSlabChainVertex, hiLast, hij] using
      And.intro hxBounds.1 (hxNonpos i hiLast)

theorem cubicGraphIsoRegion_tSlabSlice_subset_T
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n)
    {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    (j : Fin (d - 1)) :
    cubicGraphIsoRegion (tSlabSliceIso hd x j)
        (finiteThickSlabSVertices d n L : Set (Cubic d)) ⊆
      (finiteThickSlabTVertices d n L : Set (Cubic d)) := by
  rintro _ ⟨z, hz, rfl⟩
  change tSlabSliceIso hd x j z ∈ finiteThickSlabTVertices d n L
  rw [mem_finiteThickSlabTVertices_iff]
  have hzS := mem_finiteThickSlabSVertices_iff.mp hz
  intro i
  let k := (tSlabSlicePermutation hd j).symm i
  by_cases hk : k.val < 2
  · have hiLast : i.val + 1 ≠ d := by
      intro hi
      have hiEq : i = ⟨d - 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      have hkEq : k = ⟨d - 1, by omega⟩ := by
        simp [k, hiEq]
      rw [hkEq] at hk
      omega
    rw [if_neg hiLast]
    have hzk := hzS k
    rw [if_pos hk] at hzk
    have hzero : tSlabSliceOffset hd x j i = 0 := by
      simp [tSlabSliceOffset, k, hk]
    rw [tSlabSliceIso_apply, hzero, add_zero]
    change (z k).natAbs ≤ n
    exact hzk
  · have hk2 : 2 ≤ k.val := by omega
    have hzk := hzS k
    rw [if_neg hk] at hzk
    by_cases hiLast : i.val + 1 = d
    · rw [if_pos hiLast]
      have hzero : tSlabSliceOffset hd x j i = 0 := by
        simp [tSlabSliceOffset, k, hk, hiLast]
      rw [tSlabSliceIso_apply, hzero, add_zero]
      change 0 ≤ z k ∧ z k ≤ L
      exact hzk
    · rw [if_neg hiLast]
      have hc := tSlabChainVertex_horizontal_bounds hx hxNonpos j.val i hiLast
      have hoffset : tSlabSliceOffset hd x j i = tSlabChainVertex x j.val i := by
        simp [tSlabSliceOffset, k, hk, hiLast]
      rw [tSlabSliceIso_apply, hoffset]
      change (z k + tSlabChainVertex x j.val i).natAbs ≤ n
      apply Int.ofNat_le.mp
      rw [Int.natCast_natAbs, abs_le]
      constructor
      · omega
      · have hLcast : (L : ℤ) ≤ n := by exact_mod_cast hnL
        omega

theorem tSlabChainVertex_succ_eq_of_bounded_slice_coordinate
    {d : ℕ} (hd : 3 ≤ d) (x : Cubic d) (j : Fin (d - 1)) (i : Fin d)
    (hk : ¬ ((tSlabSlicePermutation hd j).symm i).val < 2)
    (hiLast : i.val + 1 ≠ d) :
    tSlabChainVertex x j.val i = tSlabChainVertex x (j.val + 1) i := by
  have hij : i ≠ tSlabHorizontalIndex j := by
    intro hijEq
    by_cases hj : j.val < 2
    · have hiVal : i.val = j.val := by simp [hijEq]
      have hperm : tSlabSlicePermutation hd j = Equiv.refl _ := by
        simp [tSlabSlicePermutation, hj]
      rw [hperm] at hk
      simp at hk
      omega
    · have hpre : (tSlabSlicePermutation hd j).symm i = ⟨1, by omega⟩ := by
        rw [hijEq]
        simp [tSlabSlicePermutation, hj]
      rw [hpre] at hk
      exact hk (by simp)
  exact tSlabChainVertex_succ_eq_of_ne x j i hij (Or.inr hiLast)

theorem tSlabSliceIso_symm_chainVertex_mem_S
    {d n L : ℕ} (hd : 3 ≤ d) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (j : Fin (d - 1)) :
    (tSlabSliceIso hd x j).symm (tSlabChainVertex x j.val) ∈
      finiteThickSlabSVertices d n L := by
  let F := tSlabSliceIso hd x j
  let e := tSlabSlicePermutation hd j
  let u := tSlabChainVertex x j.val
  let s := F.symm u
  have huT : u ∈ finiteThickSlabTVertices d n L :=
    tSlabChainVertex_mem_T hx j.val
  have hsmap : F s = u := F.apply_symm_apply u
  change s ∈ finiteThickSlabSVertices d n L
  rw [mem_finiteThickSlabSVertices_iff]
  intro l
  let i := e l
  have hcoord := congrFun hsmap i
  have hei : e.symm i = l := e.symm_apply_apply l
  have hcoord' : s l + tSlabSliceOffset hd x j i = u i := by
    simpa [F, e, i, tSlabSliceIso_apply, hei] using hcoord
  by_cases hl : l.val < 2
  · rw [if_pos hl]
    have hiLast : i.val + 1 ≠ d := by
      intro hiLast
      apply tSlabSlicePermutation_apply_ne_last_of_val_lt_two hd j l hl
      apply Fin.ext
      change (e l).val + 1 = d at hiLast
      change (e l).val = (d - 1)
      omega
    have huBound := mem_finiteThickSlabTVertices_iff.mp huT i
    rw [if_neg hiLast] at huBound
    have hoffset : tSlabSliceOffset hd x j i = 0 := by
      simp [tSlabSliceOffset, e, i, hei, hl]
    rw [hoffset, add_zero] at hcoord'
    simpa [hcoord'] using huBound
  · rw [if_neg hl]
    by_cases hiLast : i.val + 1 = d
    · have huBound := mem_finiteThickSlabTVertices_iff.mp huT i
      rw [if_pos hiLast] at huBound
      have hoffset : tSlabSliceOffset hd x j i = 0 := by
        simp [tSlabSliceOffset, e, i, hei, hl, hiLast]
      rw [hoffset, add_zero] at hcoord'
      simpa [hcoord'] using huBound
    · have hoffset : tSlabSliceOffset hd x j i = u i := by
        simp [tSlabSliceOffset, e, i, hei, hl, hiLast, u]
      rw [hoffset] at hcoord'
      have hs0 : s l = 0 := by omega
      simp [hs0]

theorem tSlabSliceIso_symm_succChainVertex_mem_S
    {d n L : ℕ} (hd : 3 ≤ d) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (j : Fin (d - 1)) :
    (tSlabSliceIso hd x j).symm (tSlabChainVertex x (j.val + 1)) ∈
      finiteThickSlabSVertices d n L := by
  let F := tSlabSliceIso hd x j
  let e := tSlabSlicePermutation hd j
  let u := tSlabChainVertex x j.val
  let v := tSlabChainVertex x (j.val + 1)
  let s := F.symm v
  have hvT : v ∈ finiteThickSlabTVertices d n L :=
    tSlabChainVertex_mem_T hx (j.val + 1)
  have hsmap : F s = v := F.apply_symm_apply v
  change s ∈ finiteThickSlabSVertices d n L
  rw [mem_finiteThickSlabSVertices_iff]
  intro l
  let i := e l
  have hcoord := congrFun hsmap i
  have hei : e.symm i = l := e.symm_apply_apply l
  have hcoord' : s l + tSlabSliceOffset hd x j i = v i := by
    simpa [F, e, i, tSlabSliceIso_apply, hei] using hcoord
  by_cases hl : l.val < 2
  · rw [if_pos hl]
    have hiLast : i.val + 1 ≠ d := by
      intro hiLast
      apply tSlabSlicePermutation_apply_ne_last_of_val_lt_two hd j l hl
      apply Fin.ext
      change (e l).val + 1 = d at hiLast
      change (e l).val = (d - 1)
      omega
    have hvBound := mem_finiteThickSlabTVertices_iff.mp hvT i
    rw [if_neg hiLast] at hvBound
    have hoffset : tSlabSliceOffset hd x j i = 0 := by
      simp [tSlabSliceOffset, e, i, hei, hl]
    rw [hoffset, add_zero] at hcoord'
    simpa [hcoord'] using hvBound
  · rw [if_neg hl]
    by_cases hiLast : i.val + 1 = d
    · have hvBound := mem_finiteThickSlabTVertices_iff.mp hvT i
      rw [if_pos hiLast] at hvBound
      have hoffset : tSlabSliceOffset hd x j i = 0 := by
        simp [tSlabSliceOffset, e, i, hei, hl, hiLast]
      rw [hoffset, add_zero] at hcoord'
      simpa [hcoord'] using hvBound
    · have hoffset : tSlabSliceOffset hd x j i = u i := by
        simp [tSlabSliceOffset, e, i, hei, hl, hiLast, u]
      have huv : u i = v i := by
        exact tSlabChainVertex_succ_eq_of_bounded_slice_coordinate hd x j i
          (by simpa [e, i, hei] using hl) hiLast
      rw [hoffset, ← huv] at hcoord'
      have hs0 : s l = 0 := by omega
      simp [hs0]

/-- The consecutive vertices of the coordinate-zeroing chain lie in one transported copy of
`S_n(L)` contained in `T_n(L)`. -/
def tSlabStepSlicePlacement
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    (j : Fin (d - 1)) :
    FiniteThickSlabSSlicePlacement d n L
      (tSlabChainVertex x j.val) (tSlabChainVertex x (j.val + 1)) where
  iso := tSlabSliceIso hd x j
  source := (tSlabSliceIso hd x j).symm (tSlabChainVertex x j.val)
  target := (tSlabSliceIso hd x j).symm (tSlabChainVertex x (j.val + 1))
  source_mem := tSlabSliceIso_symm_chainVertex_mem_S hd hx j
  target_mem := tSlabSliceIso_symm_succChainVertex_mem_S hd hx j
  map_source := (tSlabSliceIso hd x j).apply_symm_apply _
  map_target := (tSlabSliceIso hd x j).apply_symm_apply _
  image_subset := cubicGraphIsoRegion_tSlabSlice_subset_T hd hnL hx hxNonpos j

/-- Equation (7.87), one step of the coordinate-zeroing chain. -/
theorem tSlabChainStep_connection_lowerBound
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n)
    (p : I) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    (j : Fin (d - 1)) {delta : ℝ}
    (hS : ∀ u ∈ finiteThickSlabSVertices d n L,
      ∀ v ∈ finiteThickSlabSVertices d n L,
        delta ≤ (bernoulliBondMeasure d p).real
          (finiteThickSlabSConnectionEvent d n L u v)) :
    delta ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L
        (tSlabChainVertex x j.val) (tSlabChainVertex x (j.val + 1))) :=
  connectionT_lowerBound_of_sSlicePlacement p
    (tSlabStepSlicePlacement hd hnL hx hxNonpos j) hS

/-- The remaining vertices in a consecutive portion of the coordinate-zeroing chain. -/
def tSlabChainTail {d : ℕ} (x : Cubic d) (start count : ℕ) : List (Cubic d) :=
  List.ofFn fun i : Fin count ↦ tSlabChainVertex x (start + i.val + 1)

@[simp]
theorem tSlabChainTail_length {d : ℕ} (x : Cubic d) (start count : ℕ) :
    (tSlabChainTail x start count).length = count := by
  simp [tSlabChainTail]

theorem tSlabChainTail_lowerBound
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n)
    (p : I) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    {delta : ℝ}
    (hS : ∀ u ∈ finiteThickSlabSVertices d n L,
      ∀ v ∈ finiteThickSlabSVertices d n L,
        delta ≤ (bernoulliBondMeasure d p).real
          (finiteThickSlabSConnectionEvent d n L u v))
    (start count : ℕ) (hcount : start + count ≤ d - 1) :
    ConnectionLowerBoundChain p
      (finiteThickSlabTVertices d n L : Set (Cubic d)) delta
      (tSlabChainVertex x start) (tSlabChainTail x start count) := by
  induction count generalizing start with
  | zero => simp [tSlabChainTail, ConnectionLowerBoundChain]
  | succ count ih =>
      let j : Fin (d - 1) := ⟨start, by omega⟩
      rw [tSlabChainTail, List.ofFn_succ]
      refine ⟨tSlabChainVertex_mem_T hx (start + 1), ?_, ?_⟩
      · have hstep := tSlabChainStep_connection_lowerBound hd hnL p hx hxNonpos j hS
        simpa only [finiteThickSlabTConnectionEvent, j] using hstep
      · have htail := ih (start + 1) (by omega)
        have htailEq :
            List.ofFn (fun i : Fin count ↦
              tSlabChainVertex x (start + i.succ.val + 1)) =
              tSlabChainTail x (start + 1) count := by
          rw [tSlabChainTail]
          congr 1
          funext i
          congr 1
          rw [Fin.val_succ]
          omega
        rw [htailEq]
        simpa using htail

@[simp]
theorem tSlabChainTail_getLastD_succ
    {d : ℕ} (x fallback : Cubic d) (start count : ℕ) :
    (tSlabChainTail x start (count + 1)).getLastD fallback =
      tSlabChainVertex x (start + count + 1) := by
  rw [tSlabChainTail, List.ofFn_succ']
  rw [List.concat_eq_append, List.getLastD_concat]
  congr 1

theorem tSlabChainTail_getLastD_origin
    {d : ℕ} (hd : 3 ≤ d) (x : Cubic d) :
    (tSlabChainTail x 0 (d - 1)).getLastD x = cubicOrigin := by
  have hdsub : d - 1 = (d - 2) + 1 := by omega
  rw [hdsub, tSlabChainTail_getLastD_succ]
  convert tSlabChainVertex_last (by omega) x using 1
  congr 1
  omega

/-- Equation (7.88) for a point in the nonpositive horizontal orthant. -/
theorem finiteThickSlabTConnection_origin_lowerBound_of_nonpos
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n)
    (p : I) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hxNonpos : ∀ i : Fin d, i.val + 1 ≠ d → x i ≤ 0)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hS : ∀ u ∈ finiteThickSlabSVertices d n L,
      ∀ v ∈ finiteThickSlabSVertices d n L,
        delta ≤ (bernoulliBondMeasure d p).real
          (finiteThickSlabSConnectionEvent d n L u v)) :
    delta ^ (d - 1) ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L x cubicOrigin) := by
  have hchain := tSlabChainTail_lowerBound hd hnL p hx hxNonpos hS
    0 (d - 1) (by omega)
  have hchain' : ConnectionLowerBoundChain p
      (finiteThickSlabTVertices d n L : Set (Cubic d)) delta x
      (tSlabChainTail x 0 (d - 1)) := by
    simpa only [tSlabChainVertex_zero] using hchain
  have hbound := pow_length_le_connectionEventWithinVertices_of_lowerBoundChain
    p (finiteThickSlabTVertices d n L : Set (Cubic d))
      (tSlabChainTail x 0 (d - 1)) hx hdelta hchain'
  simpa only [tSlabChainTail_length, tSlabChainVertex_zero,
    tSlabChainTail_getLastD_origin hd x, finiteThickSlabTConnectionEvent] using hbound

/-! ### Simultaneous sign normalization -/

theorem cubicSignedCoordinateIso_mem_finiteThickSlabT_iff
    {d n L : ℕ} (hd : 0 < d) (flip : Fin d → Bool)
    (hLast : flip ⟨d - 1, by omega⟩ = false) (x : Cubic d) :
    cubicSignedCoordinateIso flip x ∈ finiteThickSlabTVertices d n L ↔
      x ∈ finiteThickSlabTVertices d n L := by
  rw [mem_finiteThickSlabTVertices_iff, mem_finiteThickSlabTVertices_iff]
  constructor <;> intro hx i
  · have hi := hx i
    by_cases hiLast : i.val + 1 = d
    · have hiEq : i = ⟨d - 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hiEq] at hi ⊢
      simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hLast] using hi
    · rw [if_neg hiLast] at hi ⊢
      by_cases hf : flip i
      · simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hf,
          Int.natAbs_neg] using hi
      · simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hf] using hi
  · by_cases hiLast : i.val + 1 = d
    · have hiEq : i = ⟨d - 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hiEq]
      simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hLast] using hx ⟨d - 1, by omega⟩
    · rw [if_neg hiLast] at ⊢
      have hi := hx i
      rw [if_neg hiLast] at hi
      by_cases hf : flip i
      · simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hf,
          Int.natAbs_neg] using hi
      · simpa [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, hf] using hi

theorem cubicGraphIsoRegion_signedCoordinate_finiteThickSlabT
    {d n L : ℕ} (hd : 0 < d) (flip : Fin d → Bool)
    (hLast : flip ⟨d - 1, by omega⟩ = false) :
    cubicGraphIsoRegion (cubicSignedCoordinateIso flip)
        (finiteThickSlabTVertices d n L : Set (Cubic d)) =
      (finiteThickSlabTVertices d n L : Set (Cubic d)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (cubicSignedCoordinateIso_mem_finiteThickSlabT_iff hd flip hLast y).2 hy
  · intro hx
    refine ⟨cubicSignedCoordinateIso flip x, ?_, ?_⟩
    · exact (cubicSignedCoordinateIso_mem_finiteThickSlabT_iff hd flip hLast _).2 hx
    · exact cubicSignedCoordinateEquiv_apply_self flip x

/-- Reflect exactly the positive horizontal coordinates; the bounded final coordinate is fixed. -/
def tSlabNonpositiveFlip {d : ℕ} (x : Cubic d) (i : Fin d) : Bool :=
  decide (i.val + 1 ≠ d ∧ 0 < x i)

@[simp]
theorem tSlabNonpositiveFlip_last
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    tSlabNonpositiveFlip x ⟨d - 1, by omega⟩ = false := by
  simp [tSlabNonpositiveFlip]
  omega

theorem cubicSignedCoordinateIso_tSlabNonpositiveFlip_nonpos
    {d : ℕ} (x : Cubic d) (i : Fin d) (hiLast : i.val + 1 ≠ d) :
    cubicSignedCoordinateIso (tSlabNonpositiveFlip x) x i ≤ 0 := by
  by_cases hi : 0 < x i
  · simp [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv,
      tSlabNonpositiveFlip, hiLast, hi]
    omega
  · simp [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv,
      tSlabNonpositiveFlip, hiLast, hi, le_of_not_gt hi]

@[simp]
theorem cubicSignedCoordinateIso_origin
    {d : ℕ} (flip : Fin d → Bool) :
    cubicSignedCoordinateIso flip cubicOrigin = cubicOrigin := by
  ext i
  by_cases hf : flip i <;>
    simp [cubicSignedCoordinateIso, cubicSignedCoordinateEquiv, cubicOrigin, hf]

/-- Equation (7.88) for an arbitrary point of `T_n(L)`. -/
theorem finiteThickSlabTConnection_origin_lowerBound
    {d n L : ℕ} (hd : 3 ≤ d) (hnL : L ≤ n)
    (p : I) {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hS : ∀ u ∈ finiteThickSlabSVertices d n L,
      ∀ v ∈ finiteThickSlabSVertices d n L,
        delta ≤ (bernoulliBondMeasure d p).real
          (finiteThickSlabSConnectionEvent d n L u v)) :
    delta ^ (d - 1) ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L x cubicOrigin) := by
  let flip := tSlabNonpositiveFlip x
  let F := cubicSignedCoordinateIso flip
  let x' := F x
  have hLast : flip ⟨d - 1, by omega⟩ = false := by
    simpa only [flip] using tSlabNonpositiveFlip_last (by omega) x
  have hx' : x' ∈ finiteThickSlabTVertices d n L :=
    (cubicSignedCoordinateIso_mem_finiteThickSlabT_iff (by omega) flip hLast x).2 hx
  have hx'Nonpos : ∀ i : Fin d, i.val + 1 ≠ d → x' i ≤ 0 := by
    intro i hi
    exact cubicSignedCoordinateIso_tSlabNonpositiveFlip_nonpos x i hi
  have hnormalized := finiteThickSlabTConnection_origin_lowerBound_of_nonpos
    hd hnL p hx' hx'Nonpos hdelta hS
  have hprob := bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso
    F (finiteThickSlabTVertices d n L : Set (Cubic d)) p x cubicOrigin
  rw [cubicGraphIsoRegion_signedCoordinate_finiteThickSlabT
    (by omega) flip hLast, cubicSignedCoordinateIso_origin] at hprob
  exact hnormalized.trans_eq hprob.symm

/-- Two root connections are glued by FKG to connect arbitrary points of `T_n(L)`. -/
theorem sq_originConnectionLowerBound_le_finiteThickSlabTConnection
    {d n L : ℕ} (p : I) {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hroot : ∀ z ∈ finiteThickSlabTVertices d n L,
      epsilon ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabTConnectionEvent d n L z cubicOrigin)) :
    epsilon ^ 2 ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L x y) := by
  let A := finiteThickSlabTConnectionEvent d n L x cubicOrigin
  let B := finiteThickSlabTConnectionEvent d n L y cubicOrigin
  have hsub : A ∩ B ⊆ finiteThickSlabTConnectionEvent d n L x y := by
    rintro omega ⟨⟨q, hqOpen, hqT⟩, ⟨r, hrOpen, hrT⟩⟩
    refine ⟨q.append r.reverse,
      walkIsOpen_append hqOpen (walkIsOpen_reverse hrOpen), ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    exact hz.elim (hqT z) (fun hzr ↦ hrT z (by simpa using hzr))
  calc
    epsilon ^ 2 = epsilon * epsilon := by ring
    _ ≤ (bernoulliBondMeasure d p).real A *
        (bernoulliBondMeasure d p).real B :=
      mul_le_mul (hroot x hx) (hroot y hy) hepsilon measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) :=
      bernoulliBondMeasure_real_fkg p
        (isIncreasingEvent_finiteThickSlabTConnectionEvent d n L x cubicOrigin)
        (isIncreasingEvent_finiteThickSlabTConnectionEvent d n L y cubicOrigin)
        (measurableSet_finiteThickSlabTConnectionEvent d n L x cubicOrigin)
        (measurableSet_finiteThickSlabTConnectionEvent d n L y cubicOrigin)
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabTConnectionEvent d n L x y) :=
      measureReal_mono hsub (measure_ne_top _ _)

/-- Equations (7.87)--(7.88): the `S_n(L)` constant yields a uniform pairwise bound in
`T_n(L)` whenever the horizontal radius is at least the slab thickness. -/
theorem finiteThickSlabSConnectionLowerBound_pow_le_connectionT_of_L_le_n
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} (hnL : L ≤ n) {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    (finiteThickSlabSConnectionLowerBound d L p₁ p₂ ^ (d - 1)) ^ 2 ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabTConnectionEvent d n L x y) := by
  have hdelta : 0 ≤ finiteThickSlabSConnectionLowerBound d L p₁ p₂ := by
    exact le_trans (by positivity : 0 ≤
      ((p₂ : ℝ) ^ ((d - 2) * L) *
        (slabCornerAllConnectionLowerBound d L p₁ p₂) ^ 2) ^ 2) le_rfl
  apply sq_originConnectionLowerBound_le_finiteThickSlabTConnection
    p₂ hx hy (pow_nonneg hdelta _)
  intro z hz
  exact finiteThickSlabTConnection_origin_lowerBound hd hnL p₂ hz hdelta
    (fun u hu v hv ↦ finiteThickSlabSConnectionLowerBound_le
      d (by omega) L h12 hu hv)

/-! ### Uniform treatment of the finitely many radii below `L` -/

theorem cubicL1Dist_le_d_mul_two_n_add_L_of_mem_finiteThickSlabT
    {d n L : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    cubicL1Dist x y ≤ d * (2 * n + L) := by
  classical
  rw [cubicL1Dist]
  calc
    (∑ i : Fin d, (y i - x i).natAbs) ≤
        ∑ _i : Fin d, (2 * n + L) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hxi := mem_finiteThickSlabTVertices_iff.mp hx i
      have hyi := mem_finiteThickSlabTVertices_iff.mp hy i
      by_cases hiLast : i.val + 1 = d
      · rw [if_pos hiLast] at hxi hyi
        apply Int.ofNat_le.mp
        rw [Int.natCast_natAbs, abs_le]
        constructor <;> omega
      · rw [if_neg hiLast] at hxi hyi
        have hxabs : |x i| ≤ (n : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact Int.ofNat_le.mpr hxi
        have hyabs : |y i| ≤ (n : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact Int.ofNat_le.mpr hyi
        have hxbounds := abs_le.mp hxabs
        have hybounds := abs_le.mp hyabs
        apply Int.ofNat_le.mp
        rw [Int.natCast_natAbs, abs_le]
        constructor <;> omega
    _ = d * (2 * n + L) := by simp

/-- Coordinate-convexity of `T_n(L)`: the standard Manhattan walk stays in the region. -/
theorem exists_cubicPath_in_finiteThickSlabT
    {d n L : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    ∃ w : (cubicGraph d).Walk x y,
      w.IsPath ∧ w.length ≤ d * (2 * n + L) ∧
        ∀ z ∈ w.support, z ∈ finiteThickSlabTVertices d n L := by
  obtain ⟨w, hwlen, hwbetween⟩ :=
    exists_cubicWalk_length_eq_l1Dist_support_between d x y
  let q : (cubicGraph d).Walk x y := w.toPath
  have hqlen : q.length ≤ w.length := by
    simpa [q, SimpleGraph.Walk.toPath] using SimpleGraph.Walk.length_bypass_le w
  refine ⟨q, by simp [q], hqlen.trans (hwlen.trans_le
    (cubicL1Dist_le_d_mul_two_n_add_L_of_mem_finiteThickSlabT hx hy)), ?_⟩
  intro z hz
  have hzbetween := hwbetween z (w.support_toPath_subset hz)
  rw [mem_finiteThickSlabTVertices_iff]
  intro i
  have hxi := mem_finiteThickSlabTVertices_iff.mp hx i
  have hyi := mem_finiteThickSlabTVertices_iff.mp hy i
  by_cases hiLast : i.val + 1 = d
  · rw [if_pos hiLast] at hxi hyi ⊢
    rcases hzbetween i with hzxy | hzyx <;> omega
  · rw [if_neg hiLast] at hxi hyi ⊢
    have hxabs : |x i| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact Int.ofNat_le.mpr hxi
    have hyabs : |y i| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact Int.ofNat_le.mpr hyi
    have hxbounds := abs_le.mp hxabs
    have hybounds := abs_le.mp hyabs
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, abs_le]
    rcases hzbetween i with hzxy | hzyx <;> omega

/-- For `n<L`, opening one deterministic path gives a lower bound independent of `n`. -/
theorem pow_d_mul_three_L_le_connectionT_of_n_lt_L
    {d n L : ℕ} (p : I) (hnL : n < L) {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    (p : ℝ) ^ (d * (3 * L)) ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabTConnectionEvent d n L x y) := by
  obtain ⟨w, hwPath, hwLength, hwT⟩ :=
    exists_cubicPath_in_finiteThickSlabT hx hy
  let W : Set (EdgeConfiguration d) := {omega | walkIsOpen omega w}
  have hlength : w.length ≤ d * (3 * L) := by
    apply hwLength.trans
    gcongr
    omega
  have hWprob : (p : ℝ) ^ (d * (3 * L)) ≤
      (bernoulliBondMeasure d p).real W := by
    rw [show (bernoulliBondMeasure d p).real W = (p : ℝ) ^ w.length by
      exact bernoulliBondMeasure_real_walkIsOpen p w hwPath.isTrail]
    exact pow_le_pow_of_le_one p.2.1 p.2.2 hlength
  exact hWprob.trans (measureReal_mono (by
    intro omega homega
    exact ⟨w, homega, hwT⟩) (measure_ne_top _ _))

/-- Explicit uniform constant for the `T_n(L)` half of Lemma 7.78. -/
noncomputable def finiteThickSlabTConnectionLowerBound
    (d L : ℕ) (p₁ p₂ : I) : ℝ :=
  min ((finiteThickSlabSConnectionLowerBound d L p₁ p₂ ^ (d - 1)) ^ 2)
    ((p₂ : ℝ) ^ (d * (3 * L)))

theorem finiteThickSlabTConnectionLowerBound_pos
    (d L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    0 < finiteThickSlabTConnectionLowerBound d L p₁ p₂ := by
  have hS := finiteThickSlabSConnectionLowerBound_pos d L hcrit h12
  have hp₂ : 0 < (p₂ : ℝ) := lt_of_le_of_lt p₁.2.1 h12
  exact lt_min (pow_pos (pow_pos hS _) _) (pow_pos hp₂ _)

/-- Exact uniform (7.80) package, valid for every radius `n`. -/
theorem finiteThickSlabTConnectionLowerBound_le
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L)
    (hy : y ∈ finiteThickSlabTVertices d n L) :
    finiteThickSlabTConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabTConnectionEvent d n L x y) := by
  by_cases hnL : L ≤ n
  · exact (min_le_left _ _).trans
      (finiteThickSlabSConnectionLowerBound_pow_le_connectionT_of_L_le_n
        d hd L h12 hnL hx hy)
  · exact (min_le_right _ _).trans
      (pow_d_mul_three_L_le_connectionT_of_n_lt_L p₂ (by omega) hx hy)

/-! ### The joint finite-slab package -/

/-- One constant serving both conclusions (7.79) and (7.80). -/
noncomputable def finiteThickSlabConnectionLowerBound
    (d L : ℕ) (p₁ p₂ : I) : ℝ :=
  min (finiteThickSlabSConnectionLowerBound d L p₁ p₂)
    (finiteThickSlabTConnectionLowerBound d L p₁ p₂)

theorem finiteThickSlabConnectionLowerBound_pos
    (d L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    0 < finiteThickSlabConnectionLowerBound d L p₁ p₂ :=
  lt_min (finiteThickSlabSConnectionLowerBound_pos d L hcrit h12)
    (finiteThickSlabTConnectionLowerBound_pos d L hcrit h12)

/-- Lemma 7.78 after the intermediate quarter-slab choice (7.81) has been made. -/
theorem uniformFiniteSlabConnectionLowerBound_of_quarterSlabCritical_lt
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) :
    UniformFiniteSlabConnectionLowerBound d p₂ L
      (finiteThickSlabConnectionLowerBound d L p₁ p₂) := by
  constructor
  · intro n _hn x hx y hy
    exact (min_le_left _ _).trans
      (finiteThickSlabSConnectionLowerBound_le d (by omega) L h12 hx hy)
  · intro n _hn x hx y hy
    exact (min_le_right _ _).trans
      (finiteThickSlabTConnectionLowerBound_le d hd L h12 hx hy)

/-- Existential form of Lemma 7.78 conditional only on a strict quarter-slab critical-point
comparison.  Theorem 7.2 supplies that comparison in the final source-facing theorem. -/
theorem exists_uniformFiniteSlabConnectionLowerBound_of_quarterSlabCritical_lt
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    ∃ delta : ℝ, 0 < delta ∧
      UniformFiniteSlabConnectionLowerBound d p₂ L delta := by
  exact ⟨finiteThickSlabConnectionLowerBound d L p₁ p₂,
    finiteThickSlabConnectionLowerBound_pos d L hcrit h12,
    uniformFiniteSlabConnectionLowerBound_of_quarterSlabCritical_lt d hd L h12⟩

/-- The exact Lemma 7.78 conclusion once the chosen quarter slab is supercritical at `p`.
The auxiliary density in (7.81) is selected internally as the midpoint. -/
theorem exists_uniformFiniteSlabConnectionLowerBound_of_critical_lt
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) (p : I)
    (hp : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ delta : ℝ, 0 < delta ∧
      UniformFiniteSlabConnectionLowerBound d p L delta := by
  let q := regionCriticalProbability d (cubicQuarterSlab d L)
  let p₁ : I := ⟨(q + (p : ℝ)) / 2, by
    constructor
    · exact div_nonneg (add_nonneg (regionCriticalProbability_nonneg d _) p.2.1) zero_le_two
    · have hq1 := regionCriticalProbability_le_one d (cubicQuarterSlab d L)
      linarith [p.2.2]⟩
  have hcrit : q < (p₁ : ℝ) := by
    change q < (q + (p : ℝ)) / 2
    linarith
  have h1p : (p₁ : ℝ) < p := by
    change (q + (p : ℝ)) / 2 < (p : ℝ)
    linarith
  exact exists_uniformFiniteSlabConnectionLowerBound_of_quarterSlabCritical_lt
    d hd L hcrit h1p

theorem exists_unit_uniformFiniteSlabConnectionLowerBound_of_critical_lt
    (d : ℕ) (hd : 3 ≤ d) (L : ℕ) (p : I)
    (hp : regionCriticalProbability d (cubicQuarterSlab d L) < (p : ℝ)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      UniformFiniteSlabConnectionLowerBound d p L delta := by
  obtain ⟨delta, hdelta, hslab⟩ :=
    exists_uniformFiniteSlabConnectionLowerBound_of_critical_lt d hd L p hp
  have horigin : cubicOrigin ∈ finiteThickSlabSVertices d 1 L := by
    rw [mem_finiteThickSlabSVertices_iff]
    intro i
    by_cases hi : i.val < 2
    · simp [hi, cubicOrigin]
    · simp [hi, cubicOrigin]
  have hdeltaOne := hslab.1 1 le_rfl cubicOrigin horigin cubicOrigin horigin
  rw [finiteThickSlabSConnectionEvent_self horigin, probReal_univ] at hdeltaOne
  exact ⟨delta, hdelta, hdeltaOne, hslab⟩

end Percolation
