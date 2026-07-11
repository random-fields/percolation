import Percolation.Critical.StaticSecondCluster
import Percolation.Critical.ConcreteAnimals

/-!
# Annular shell geometry for Grimmett Lemma 7.89

The shell between two peeled coordinate boxes is covered by signed slabs.  Each slab is a
translated/reflected copy of `T_n(L)`.  This file packages that geometry separately from the
ratio-free recursion in `StaticCoalescence.lean`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Outer radius reached by one shifted shell of thickness `L`. -/
def boxShellOuterRadius (r L : ℕ) : ℕ := r + L + 1

/-- A signed shell slice.  Its thickness coordinate contains `L+1` vertices, beginning one
step outside `B(r)`; all other coordinates range over the full outer box. -/
noncomputable def boxShellSliceVertices
    (d r L : ℕ) (i : Fin d) (positive : Bool) : Finset (Cubic d) :=
  if positive then
    coordinateClosedStripVertices d (boxShellOuterRadius r L) i
      (r + 1) (boxShellOuterRadius r L)
  else
    coordinateClosedStripVertices d (boxShellOuterRadius r L) i
      (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ))

@[simp]
theorem mem_boxShellSliceVertices_iff
    {d r L : ℕ} {i : Fin d} {positive : Bool} {x : Cubic d} :
    x ∈ boxShellSliceVertices d r L i positive ↔
      x ∈ cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) ∧
        if positive then (r + 1 : ℤ) ≤ x i ∧ x i ≤ boxShellOuterRadius r L
        else -(boxShellOuterRadius r L : ℤ) ≤ x i ∧ x i ≤ -(r + 1 : ℤ) := by
  cases positive <;> simp [boxShellSliceVertices]

/-- The canonical chain of `d+1` outer-box corners used in (7.95): at corner `j`, the first
`j` coordinates are positive and the rest are negative. -/
def boxShellChainCorner (d R : ℕ) (j : Fin (d + 1)) : Cubic d :=
  fun i ↦ if i.val < j.val then R else -(R : ℤ)

theorem boxShellChainCorner_mem_cubicMetricBox
    (d R : ℕ) (j : Fin (d + 1)) :
    boxShellChainCorner d R j ∈ cubicMetricBox d cubicOrigin R := by
  rw [mem_cubicMetricBox]
  intro i
  simp only [cubicOrigin, zero_sub, zero_add, boxShellChainCorner]
  split_ifs <;> omega

/-- A deterministic coordinate distinct from `i`, available in dimensions at least two. -/
def boxShellOtherCoord {d : ℕ} (hd : 2 ≤ d) (i : Fin d) : Fin d :=
  if i.val = 0 then ⟨1, hd⟩ else ⟨0, by omega⟩

theorem boxShellOtherCoord_ne {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    boxShellOtherCoord hd i ≠ i := by
  intro h
  apply_fun Fin.val at h
  by_cases hi : i.val = 0
  · simp [boxShellOtherCoord, hi] at h
  · simp [boxShellOtherCoord, hi] at h
    exact hi h.symm

/-- Consecutive canonical corners agree in every coordinate except the coordinate being
flipped. -/
theorem boxShellChainCorner_succ_apply_of_ne
    {d R : ℕ} (j : Fin d) {i : Fin d} (hij : i ≠ j) :
    boxShellChainCorner d R j.castSucc i =
      boxShellChainCorner d R j.succ i := by
  have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  simp only [boxShellChainCorner, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- Every consecutive corner pair lies in one common signed shell slice. -/
theorem exists_boxShellSlice_pair_chainCorners
    {d r L : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    ∃ i : Fin d, ∃ positive : Bool,
      boxShellChainCorner d (boxShellOuterRadius r L) j.castSucc ∈
          boxShellSliceVertices d r L i positive ∧
        boxShellChainCorner d (boxShellOuterRadius r L) j.succ ∈
          boxShellSliceVertices d r L i positive := by
  let i := boxShellOtherCoord hd j
  have hij : i ≠ j := boxShellOtherCoord_ne hd j
  let positive : Bool := decide (i.val < j.val)
  refine ⟨i, positive, ?_, ?_⟩
  · rw [mem_boxShellSliceVertices_iff]
    refine ⟨boxShellChainCorner_mem_cubicMetricBox _ _ _, ?_⟩
    by_cases hlt : i.val < j.val
    · simp [positive, hlt, boxShellChainCorner, boxShellOuterRadius]
    · simp [positive, hlt, boxShellChainCorner, boxShellOuterRadius]
      omega
  · have heq := boxShellChainCorner_succ_apply_of_ne
      (R := boxShellOuterRadius r L) j hij
    rw [mem_boxShellSliceVertices_iff]
    refine ⟨boxShellChainCorner_mem_cubicMetricBox _ _ _, ?_⟩
    rw [← heq]
    by_cases hlt : i.val < j.val
    · simp [positive, hlt, boxShellChainCorner, boxShellOuterRadius]
    · simp [positive, hlt, boxShellChainCorner, boxShellOuterRadius]
      omega

/-- Chosen slice coordinate for the `j`th consecutive corner pair. -/
noncomputable def boxShellChainSliceCoord
    {d r L : ℕ} (hd : 2 ≤ d) (j : Fin d) : Fin d :=
  (exists_boxShellSlice_pair_chainCorners (r := r) (L := L) hd j).choose

/-- Chosen sign for the `j`th consecutive corner pair. -/
noncomputable def boxShellChainSlicePositive
    {d r L : ℕ} (hd : 2 ≤ d) (j : Fin d) : Bool :=
  (exists_boxShellSlice_pair_chainCorners (r := r) (L := L) hd j).choose_spec.choose

theorem boxShellChainCorners_mem_chosenSlice
    {d r L : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    boxShellChainCorner d (boxShellOuterRadius r L) j.castSucc ∈
        boxShellSliceVertices d r L (boxShellChainSliceCoord (r := r) (L := L) hd j)
          (boxShellChainSlicePositive (r := r) (L := L) hd j) ∧
      boxShellChainCorner d (boxShellOuterRadius r L) j.succ ∈
        boxShellSliceVertices d r L (boxShellChainSliceCoord (r := r) (L := L) hd j)
          (boxShellChainSlicePositive (r := r) (L := L) hd j) := by
  simpa [boxShellChainSliceCoord, boxShellChainSlicePositive] using
    (exists_boxShellSlice_pair_chainCorners (r := r) (L := L) hd j).choose_spec.choose_spec

/-- Every signed shell slice inherits the uniform `T_n(L)` connection lower bound. -/
theorem boxShellSlice_connection_probability_ge_of_uniformFiniteSlab
    {d r L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ}
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (i : Fin d) (positive : Bool) {u v : Cubic d}
    (hu : u ∈ boxShellSliceVertices d r L i positive)
    (hv : v ∈ boxShellSliceVertices d r L i positive) :
    δ ≤ (bernoulliBondMeasure d p).real
      (connectionEventWithinVertices d
        (boxShellSliceVertices d r L i positive : Set (Cubic d)) u v) := by
  have hn : 1 ≤ boxShellOuterRadius r L := by simp [boxShellOuterRadius]
  cases positive with
  | false =>
      have htop : -(boxShellOuterRadius r L : ℤ) + L = -(r + 1 : ℤ) := by
        simp [boxShellOuterRadius]
        ring
      have hu' : u ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ)) := by
        simpa [boxShellSliceVertices] using hu
      have hv' : v ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ)) := by
        simpa [boxShellSliceVertices] using hv
      rw [← htop] at hu' hv'
      have h := coordinateClosedStrip_connection_probability_ge_of_uniformFiniteSlab
        hd p hslab hn i (-(boxShellOuterRadius r L : ℤ))
        (by simp [boxShellOuterRadius]) (by simp [boxShellOuterRadius]; omega) hu' hv'
      simpa only [boxShellSliceVertices, Bool.false_eq_true, if_false, htop] using h
  | true =>
      have htop : (r + 1 : ℤ) + L = boxShellOuterRadius r L := by
        simp [boxShellOuterRadius]
        ring
      have hu' : u ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (r + 1) (boxShellOuterRadius r L) := by
        simpa [boxShellSliceVertices] using hu
      have hv' : v ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (r + 1) (boxShellOuterRadius r L) := by
        simpa [boxShellSliceVertices] using hv
      rw [← htop] at hu' hv'
      have h := coordinateClosedStrip_connection_probability_ge_of_uniformFiniteSlab
        hd p hslab hn i (r + 1)
        (by simp [boxShellOuterRadius]; omega) htop.le hu' hv'
      simpa only [boxShellSliceVertices, if_true, htop] using h

/-! ### Surface entrances -/

/-- One signed coordinate step. -/
def coordinateSignedStep {d : ℕ} (i : Fin d) (positive : Bool) (x : Cubic d) : Cubic d :=
  cubicStepFrom x (i, positive)

/-- Its cubic edge. -/
def coordinateSignedStepEdge {d : ℕ} (i : Fin d) (positive : Bool)
    (x : Cubic d) : CubicEdge d :=
  cubicStepEdge x (i, positive)

@[simp]
theorem coordinateSignedStep_apply_self
    {d : ℕ} (i : Fin d) (positive : Bool) (x : Cubic d) :
    coordinateSignedStep i positive x i = if positive then x i + 1 else x i - 1 := by
  cases positive with
  | false =>
      simp [coordinateSignedStep, cubicStepFrom, cubicDirectionIncrement]
      ring
  | true => simp [coordinateSignedStep, cubicStepFrom, cubicDirectionIncrement]

theorem coordinateSignedStep_apply_of_ne
    {d : ℕ} {i j : Fin d} (hji : j ≠ i) (positive : Bool) (x : Cubic d) :
    coordinateSignedStep i positive x j = x j := by
  simp [coordinateSignedStep, cubicStepFrom, hji]

/-- A point of a nontrivial box surface lies on a signed coordinate face. -/
theorem exists_signed_coord_of_mem_cubicBoxSurface
    {d r : ℕ} (hd : 1 ≤ d) {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin r) :
    ∃ i : Fin d, ∃ positive : Bool,
      if positive then x i = r else x i = -(r : ℤ) := by
  have hdist := mem_cubicBoxSurface.mp hx
  obtain ⟨i, hi⟩ := exists_coord_natAbs_eq_cubicLInfDist hd cubicOrigin x
  simp only [cubicOrigin, sub_zero] at hi
  rw [hdist] at hi
  by_cases hnonneg : 0 ≤ x i
  · refine ⟨i, true, ?_⟩
    simp only [if_true]
    have hcast : ((x i).natAbs : ℤ) = r := by exact_mod_cast hi
    rwa [Int.natAbs_of_nonneg hnonneg] at hcast
  · refine ⟨i, false, ?_⟩
    have hnonpos : x i ≤ 0 := le_of_not_ge hnonneg
    have hcast : ((x i).natAbs : ℤ) = r := by exact_mod_cast hi
    rw [Int.ofNat_natAbs_of_nonpos hnonpos] at hcast
    have hneg := congrArg Neg.neg hcast
    simpa using hneg

/-- Stepping outward from a signed point of `∂B(r)` enters the corresponding shell slice. -/
theorem coordinateSignedStep_mem_boxShellSlice
    {d r L : ℕ} {i : Fin d} {positive : Bool} {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin r)
    (hface : if positive then x i = r else x i = -(r : ℤ)) :
    coordinateSignedStep i positive x ∈ boxShellSliceVertices d r L i positive := by
  rw [mem_boxShellSliceVertices_iff]
  have hxBox : x ∈ cubicMetricBox d cubicOrigin r :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr (mem_cubicBoxSurface.mp hx).le
  have hstepBox : coordinateSignedStep i positive x ∈
      cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) := by
    rw [mem_cubicMetricBox]
    intro j
    have hxj := mem_cubicMetricBox.mp hxBox j
    simp only [cubicOrigin, zero_sub, zero_add] at hxj ⊢
    by_cases hji : j = i
    · subst j
      rw [coordinateSignedStep_apply_self]
      cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hface ⊢ <;>
        simp [boxShellOuterRadius] <;> omega
    · rw [coordinateSignedStep_apply_of_ne hji]
      constructor <;> simp [boxShellOuterRadius] <;> omega
  refine ⟨hstepBox, ?_⟩
  cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hface ⊢ <;>
    rw [coordinateSignedStep_apply_self] <;> simp [boxShellOuterRadius] <;> omega

/-- Canonical outer corner on the selected signed face. -/
def boxShellFaceCornerIndex {d : ℕ} (i : Fin d) (positive : Bool) : Fin (d + 1) :=
  if positive then i.succ else i.castSucc

theorem boxShellFaceCorner_mem_slice
    {d r L : ℕ} (i : Fin d) (positive : Bool) :
    boxShellChainCorner d (boxShellOuterRadius r L)
        (boxShellFaceCornerIndex i positive) ∈
      boxShellSliceVertices d r L i positive := by
  rw [mem_boxShellSliceVertices_iff]
  refine ⟨boxShellChainCorner_mem_cubicMetricBox _ _ _, ?_⟩
  cases positive with
  | false =>
      simp [boxShellFaceCornerIndex, boxShellChainCorner, boxShellOuterRadius]
      omega
  | true =>
      simp [boxShellFaceCornerIndex, boxShellChainCorner, boxShellOuterRadius]

/-- A surface vertex has an outward step and a canonical outer corner in one common shell
slice. -/
theorem exists_boxShellSlice_step_and_faceCorner
    {d r L : ℕ} (hd : 1 ≤ d) {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin r) :
    ∃ i : Fin d, ∃ positive : Bool,
      coordinateSignedStep i positive x ∈ boxShellSliceVertices d r L i positive ∧
        boxShellChainCorner d (boxShellOuterRadius r L)
            (boxShellFaceCornerIndex i positive) ∈
          boxShellSliceVertices d r L i positive := by
  obtain ⟨i, positive, hface⟩ := exists_signed_coord_of_mem_cubicBoxSurface hd hx
  exact ⟨i, positive, coordinateSignedStep_mem_boxShellSlice hx hface,
    boxShellFaceCorner_mem_slice i positive⟩

/-! ### Corner-chain events and probability -/

/-- Connection event for one consecutive pair in the canonical corner chain. -/
noncomputable def boxShellChainConnectionEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) (j : Fin d) : Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d
    (boxShellSliceVertices d r L
      (boxShellChainSliceCoord (r := r) (L := L) hd j)
      (boxShellChainSlicePositive (r := r) (L := L) hd j) : Set (Cubic d))
    (boxShellChainCorner d (boxShellOuterRadius r L) j.castSucc)
    (boxShellChainCorner d (boxShellOuterRadius r L) j.succ)

/-- All `d` consecutive corner connections occur. -/
noncomputable def allBoxShellChainConnectionsEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ j : Fin d, boxShellChainConnectionEvent hd r L j

theorem measurableSet_boxShellChainConnectionEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) (j : Fin d) :
    MeasurableSet (boxShellChainConnectionEvent hd r L j) :=
  measurableSet_connectionEventWithinVertices d _ _ _

theorem isIncreasingEvent_boxShellChainConnectionEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) (j : Fin d) :
    IsIncreasingEvent (boxShellChainConnectionEvent hd r L j) :=
  isIncreasingEvent_connectionEventWithinVertices d _ _ _

theorem boxShellChainConnection_probability_ge_of_uniformFiniteSlab
    {d r L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ}
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) (j : Fin d) :
    δ ≤ (bernoulliBondMeasure d p).real (boxShellChainConnectionEvent hd r L j) := by
  have hj := boxShellChainCorners_mem_chosenSlice (r := r) (L := L) hd j
  exact boxShellSlice_connection_probability_ge_of_uniformFiniteSlab
    (by omega) p hslab _ _ hj.1 hj.2

theorem pow_card_le_allBoxShellChainConnections_probability
    {d r L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    δ ^ d ≤ (bernoulliBondMeasure d p).real
      (allBoxShellChainConnectionsEvent hd r L) := by
  have hfkg := bernoulliBondMeasure_prod_le_real_biInter_fkg'
    (d := d) (κ := Fin d) p (J := Finset.univ)
    (A := boxShellChainConnectionEvent hd r L)
    (fun j _hj ↦ isIncreasingEvent_boxShellChainConnectionEvent hd r L j)
    (fun j _hj ↦ measurableSet_boxShellChainConnectionEvent hd r L j)
  calc
    δ ^ d = ∏ j : Fin d, δ := by simp
    _ ≤ ∏ j : Fin d, (bernoulliBondMeasure d p).real
        (boxShellChainConnectionEvent hd r L j) := by
      exact Finset.prod_le_prod (fun _ _ ↦ hδ0) fun j _ ↦
        boxShellChainConnection_probability_ge_of_uniformFiniteSlab hd p hslab j
    _ ≤ (bernoulliBondMeasure d p).real
        (allBoxShellChainConnectionsEvent hd r L) := by
      simpa [allBoxShellChainConnectionsEvent] using hfkg

/-- If every consecutive corner connection occurs, every canonical corner is connected to the
first corner inside the outer box. -/
theorem mem_connectionWithin_outerBox_from_first_chainCorner
    {d r L : ℕ} (hd : 2 ≤ d) {ω : EdgeConfiguration d}
    (hω : ω ∈ allBoxShellChainConnectionsEvent hd r L) (j : Fin (d + 1)) :
    ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
      (boxShellChainCorner d (boxShellOuterRadius r L) ⟨0, by omega⟩)
      (boxShellChainCorner d (boxShellOuterRadius r L) j) := by
  have hstep : ∀ k : Fin d,
      ω ∈ connectionEventWithinVertices d
        (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
        (boxShellChainCorner d (boxShellOuterRadius r L) k.castSucc)
        (boxShellChainCorner d (boxShellOuterRadius r L) k.succ) := by
    intro k
    have hk : ω ∈ boxShellChainConnectionEvent hd r L k := by
      exact Set.mem_iInter.mp hω k
    apply connectionEventWithinVertices_mono _ _ _ hk
    intro x hx
    exact Finset.mem_coe.mpr
      (mem_boxShellSliceVertices_iff.mp (Finset.mem_coe.mp hx)).1
  have hprefix : ∀ k : ℕ, ∀ hk : k ≤ d,
      ω ∈ connectionEventWithinVertices d
        (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
        (boxShellChainCorner d (boxShellOuterRadius r L) ⟨0, by omega⟩)
        (boxShellChainCorner d (boxShellOuterRadius r L) ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
        intro _hk
        refine ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact Finset.mem_coe.mpr (boxShellChainCorner_mem_cubicMetricBox _ _ _)
    | succ k ih =>
        intro hk
        have hklt : k < d := by omega
        let kFin : Fin d := ⟨k, hklt⟩
        have hprev := ih (by omega)
        have hnext := hstep kFin
        have hnext' : ω ∈ connectionEventWithinVertices d
            (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
            (boxShellChainCorner d (boxShellOuterRadius r L) ⟨k, by omega⟩)
            (boxShellChainCorner d (boxShellOuterRadius r L) ⟨k + 1, by omega⟩) := by
          simpa [kFin] using hnext
        exact connectionEventWithinVertices_trans_mem hprev hnext'
  have hjle : j.val ≤ d := by omega
  have hj := hprefix j.val hjle
  simpa using hj

/-- From an outward step to its selected outer corner inside one shell slice. -/
def boxShellEntranceConnectionEvent
    {d : ℕ} (r L : ℕ) (i : Fin d) (positive : Bool) (x : Cubic d) :
    Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d (boxShellSliceVertices d r L i positive : Set (Cubic d))
    (coordinateSignedStep i positive x)
    (boxShellChainCorner d (boxShellOuterRadius r L)
      (boxShellFaceCornerIndex i positive))

theorem boxShellEntranceConnection_probability_ge_of_uniformFiniteSlab
    {d r L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ}
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {i : Fin d} {positive : Bool} {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin r)
    (hface : if positive then x i = r else x i = -(r : ℤ)) :
    δ ≤ (bernoulliBondMeasure d p).real
      (boxShellEntranceConnectionEvent r L i positive x) :=
  boxShellSlice_connection_probability_ge_of_uniformFiniteSlab hd p hslab i positive
    (coordinateSignedStep_mem_boxShellSlice hx hface)
    (boxShellFaceCorner_mem_slice i positive)

/-- The complete fresh shell bridge: two outward edges, two entrance-to-corner connections,
and the canonical chain of consecutive outer corners. -/
noncomputable def boxShellBridgeEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ)
    (iu : Fin d) (su : Bool) (u : Cubic d)
    (iv : Fin d) (sv : Bool) (v : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | coordinateSignedStepEdge iu su u ∈ ω} ∩
    {ω | coordinateSignedStepEdge iv sv v ∈ ω} ∩
      boxShellEntranceConnectionEvent r L iu su u ∩
        boxShellEntranceConnectionEvent r L iv sv v ∩
          allBoxShellChainConnectionsEvent hd r L

theorem measurableSet_allBoxShellChainConnectionsEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) :
    MeasurableSet (allBoxShellChainConnectionsEvent hd r L) :=
  MeasurableSet.iInter fun j ↦ measurableSet_boxShellChainConnectionEvent hd r L j

theorem isIncreasingEvent_allBoxShellChainConnectionsEvent
    {d : ℕ} (hd : 2 ≤ d) (r L : ℕ) :
    IsIncreasingEvent (allBoxShellChainConnectionsEvent hd r L) :=
  isIncreasingEvent_iInter fun j ↦ isIncreasingEvent_boxShellChainConnectionEvent hd r L j

theorem mem_connectionEventWithinVertices_coordinateSignedStep
    {d : ℕ} {ω : EdgeConfiguration d} {i : Fin d} {positive : Bool}
    {x : Cubic d} {A : Set (Cubic d)}
    (hx : x ∈ A) (hstep : coordinateSignedStep i positive x ∈ A)
    (hopen : coordinateSignedStepEdge i positive x ∈ ω) :
    ω ∈ connectionEventWithinVertices d A x (coordinateSignedStep i positive x) := by
  let w : (cubicGraph d).Walk x (coordinateSignedStep i positive x) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x (i, positive)) SimpleGraph.Walk.nil
  refine ⟨w, ?_, ?_⟩
  · intro e he
    have hew := he
    have he' : e = s(x, coordinateSignedStep i positive x) := by
      simpa [w, coordinateSignedStep] using he
    have heq : (⟨e, w.edges_subset_edgeSet hew⟩ : CubicEdge d) =
        coordinateSignedStepEdge i positive x := by
      apply Subtype.ext
      simpa [coordinateSignedStepEdge, cubicStepEdge] using he'
    simpa [heq] using hopen
  · intro z hz
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · change z ∈ [coordinateSignedStep i positive x] at hz
      have : z = coordinateSignedStep i positive x := by simpa using hz
      subst z
      exact hstep

/-- Every configuration in the fresh bridge event connects the two old frontier vertices inside
the enlarged outer box. -/
theorem boxShellBridgeEvent_subset_connectionWithin_outerBox
    {d r L : ℕ} (hd : 2 ≤ d)
    {iu iv : Fin d} {su sv : Bool} {u v : Cubic d}
    (hu : u ∈ cubicBoxSurface d cubicOrigin r)
    (hv : v ∈ cubicBoxSurface d cubicOrigin r)
    (huface : if su then u iu = r else u iu = -(r : ℤ))
    (hvface : if sv then v iv = r else v iv = -(r : ℤ)) :
    boxShellBridgeEvent hd r L iu su u iv sv v ⊆
      connectionEventWithinVertices d
        (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d)) u v := by
  intro ω hω
  rcases hω with ⟨⟨⟨⟨huEdge, hvEdge⟩, huEntrance⟩, hvEntrance⟩, hchain⟩
  let zu := boxShellChainCorner d (boxShellOuterRadius r L)
    (boxShellFaceCornerIndex iu su)
  let zv := boxShellChainCorner d (boxShellOuterRadius r L)
    (boxShellFaceCornerIndex iv sv)
  let z0 := boxShellChainCorner d (boxShellOuterRadius r L) ⟨0, by omega⟩
  have huDist : cubicLInfDist cubicOrigin u ≤ boxShellOuterRadius r L := by
    rw [mem_cubicBoxSurface.mp hu]
    simp [boxShellOuterRadius]
    omega
  have hvDist : cubicLInfDist cubicOrigin v ≤ boxShellOuterRadius r L := by
    rw [mem_cubicBoxSurface.mp hv]
    simp [boxShellOuterRadius]
    omega
  have huBox : u ∈ cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) :=
    Finset.mem_coe.mpr <| mem_cubicMetricBox_iff_lInfDist_le.mpr huDist
  have hvBox : v ∈ cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) :=
    Finset.mem_coe.mpr <| mem_cubicMetricBox_iff_lInfDist_le.mpr hvDist
  have huStepBox : coordinateSignedStep iu su u ∈
      (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d)) :=
    Finset.mem_coe.mpr <| (mem_boxShellSliceVertices_iff.mp
      (coordinateSignedStep_mem_boxShellSlice hu huface)).1
  have hvStepBox : coordinateSignedStep iv sv v ∈
      (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d)) :=
    Finset.mem_coe.mpr <| (mem_boxShellSliceVertices_iff.mp
      (coordinateSignedStep_mem_boxShellSlice hv hvface)).1
  have huStep := mem_connectionEventWithinVertices_coordinateSignedStep
    huBox huStepBox huEdge
  have hvStep := mem_connectionEventWithinVertices_coordinateSignedStep
    hvBox hvStepBox hvEdge
  have huCorner : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
      (coordinateSignedStep iu su u) zu := by
    apply connectionEventWithinVertices_mono _ _ _ huEntrance
    intro x hx
    exact Finset.mem_coe.mpr
      (mem_boxShellSliceVertices_iff.mp (Finset.mem_coe.mp hx)).1
  have hvCorner : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) : Set (Cubic d))
      (coordinateSignedStep iv sv v) zv := by
    apply connectionEventWithinVertices_mono _ _ _ hvEntrance
    intro x hx
    exact Finset.mem_coe.mpr
      (mem_boxShellSliceVertices_iff.mp (Finset.mem_coe.mp hx)).1
  have hz0u := mem_connectionWithin_outerBox_from_first_chainCorner hd hchain
    (boxShellFaceCornerIndex iu su)
  have hz0v := mem_connectionWithin_outerBox_from_first_chainCorner hd hchain
    (boxShellFaceCornerIndex iv sv)
  exact connectionEventWithinVertices_trans_mem huStep <|
    connectionEventWithinVertices_trans_mem huCorner <|
      connectionEventWithinVertices_trans_mem
        (connectionEventWithinVertices_symm_mem hz0u) <|
        connectionEventWithinVertices_trans_mem hz0v <|
          connectionEventWithinVertices_trans_mem
            (connectionEventWithinVertices_symm_mem hvCorner)
            (connectionEventWithinVertices_symm_mem hvStep)

/-- The bridge event has the source-order lower bound `p² δ^(d+2)`: two fresh outward edges,
two entrance connections, and `d` consecutive corner connections. -/
theorem boxShellBridge_probability_ge_of_uniformFiniteSlab
    {d r L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    {iu iv : Fin d} {su sv : Bool} {u v : Cubic d}
    (hu : u ∈ cubicBoxSurface d cubicOrigin r)
    (hv : v ∈ cubicBoxSurface d cubicOrigin r)
    (huface : if su then u iu = r else u iu = -(r : ℤ))
    (hvface : if sv then v iv = r else v iv = -(r : ℤ)) :
    (p : ℝ) ^ 2 * δ ^ (d + 2) ≤ (bernoulliBondMeasure d p).real
      (boxShellBridgeEvent hd r L iu su u iv sv v) := by
  let EU : Set (EdgeConfiguration d) := {ω | coordinateSignedStepEdge iu su u ∈ ω}
  let EV : Set (EdgeConfiguration d) := {ω | coordinateSignedStepEdge iv sv v ∈ ω}
  let U := boxShellEntranceConnectionEvent r L iu su u
  let V := boxShellEntranceConnectionEvent r L iv sv v
  let C := allBoxShellChainConnectionsEvent hd r L
  have hEUm : MeasurableSet EU := (dependsOn_edgeOpenEvent _).measurableSet
  have hEVm : MeasurableSet EV := (dependsOn_edgeOpenEvent _).measurableSet
  have hUm : MeasurableSet U := measurableSet_connectionEventWithinVertices d _ _ _
  have hVm : MeasurableSet V := measurableSet_connectionEventWithinVertices d _ _ _
  have hCm : MeasurableSet C := measurableSet_allBoxShellChainConnectionsEvent hd r L
  have hEUinc : IsIncreasingEvent EU := by
    intro ω η hωη hω
    exact hωη hω
  have hEVinc : IsIncreasingEvent EV := by
    intro ω η hωη hω
    exact hωη hω
  have hUinc : IsIncreasingEvent U := isIncreasingEvent_connectionEventWithinVertices d _ _ _
  have hVinc : IsIncreasingEvent V := isIncreasingEvent_connectionEventWithinVertices d _ _ _
  have hCinc : IsIncreasingEvent C := isIncreasingEvent_allBoxShellChainConnectionsEvent hd r L
  have hEUprob : (bernoulliBondMeasure d p).real EU = (p : ℝ) := by
    have h := bernoulliBondMeasure_real_openEdgeSetEvent d p
      ({coordinateSignedStepEdge iu su u} : Finset (CubicEdge d))
    simpa [EU, openEdgeSetEvent] using h
  have hEVprob : (bernoulliBondMeasure d p).real EV = (p : ℝ) := by
    have h := bernoulliBondMeasure_real_openEdgeSetEvent d p
      ({coordinateSignedStepEdge iv sv v} : Finset (CubicEdge d))
    simpa [EV, openEdgeSetEvent] using h
  have hUlower : δ ≤ (bernoulliBondMeasure d p).real U :=
    boxShellEntranceConnection_probability_ge_of_uniformFiniteSlab
      (by omega) p hslab hu huface
  have hVlower : δ ≤ (bernoulliBondMeasure d p).real V :=
    boxShellEntranceConnection_probability_ge_of_uniformFiniteSlab
      (by omega) p hslab hv hvface
  have hClower : δ ^ d ≤ (bernoulliBondMeasure d p).real C :=
    pow_card_le_allBoxShellChainConnections_probability hd p hδ0 hslab
  have h12 := bernoulliBondMeasure_real_fkg p hEUinc hEVinc hEUm hEVm
  have h123 := bernoulliBondMeasure_real_fkg p (hEUinc.inter hEVinc) hUinc
    (hEUm.inter hEVm) hUm
  have h1234 := bernoulliBondMeasure_real_fkg p
    ((hEUinc.inter hEVinc).inter hUinc) hVinc ((hEUm.inter hEVm).inter hUm) hVm
  have h12345 := bernoulliBondMeasure_real_fkg p
    (((hEUinc.inter hEVinc).inter hUinc).inter hVinc) hCinc
    (((hEUm.inter hEVm).inter hUm).inter hVm) hCm
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  calc
    (p : ℝ) ^ 2 * δ ^ (d + 2) =
        ((((p : ℝ) * p) * δ) * δ) * δ ^ d := by ring
    _ ≤ ((((bernoulliBondMeasure d p).real (EU ∩ EV)) * δ) * δ) * δ ^ d := by
      gcongr
      simpa [hEUprob, hEVprob, pow_two] using h12
    _ ≤ (((bernoulliBondMeasure d p).real ((EU ∩ EV) ∩ U)) * δ) * δ ^ d := by
      gcongr
      calc
        (bernoulliBondMeasure d p).real (EU ∩ EV) * δ ≤
            (bernoulliBondMeasure d p).real (EU ∩ EV) *
              (bernoulliBondMeasure d p).real U :=
          mul_le_mul_of_nonneg_left hUlower measureReal_nonneg
        _ ≤ (bernoulliBondMeasure d p).real ((EU ∩ EV) ∩ U) := h123
    _ ≤ ((bernoulliBondMeasure d p).real (((EU ∩ EV) ∩ U) ∩ V)) * δ ^ d := by
      gcongr
      calc
        (bernoulliBondMeasure d p).real ((EU ∩ EV) ∩ U) * δ ≤
            (bernoulliBondMeasure d p).real ((EU ∩ EV) ∩ U) *
              (bernoulliBondMeasure d p).real V :=
          mul_le_mul_of_nonneg_left hVlower measureReal_nonneg
        _ ≤ (bernoulliBondMeasure d p).real (((EU ∩ EV) ∩ U) ∩ V) := h1234
    _ ≤ (bernoulliBondMeasure d p).real ((((EU ∩ EV) ∩ U) ∩ V) ∩ C) := by
      calc
        (bernoulliBondMeasure d p).real (((EU ∩ EV) ∩ U) ∩ V) * δ ^ d ≤
            (bernoulliBondMeasure d p).real (((EU ∩ EV) ∩ U) ∩ V) *
              (bernoulliBondMeasure d p).real C :=
          mul_le_mul_of_nonneg_left hClower measureReal_nonneg
        _ ≤ (bernoulliBondMeasure d p).real ((((EU ∩ EV) ∩ U) ∩ V) ∩ C) := h12345
    _ = (bernoulliBondMeasure d p).real
        (boxShellBridgeEvent hd r L iu su u iv sv v) := rfl

/-! ### Fresh shell support -/

/-- All outer-box edges not already internal to the old box. -/
noncomputable def boxShellFreshEdges (d r L : ℕ) : Finset (CubicEdge d) :=
  cubicBoxEdges d cubicOrigin (boxShellOuterRadius r L) \
    cubicBoxEdges d cubicOrigin r

theorem cubicBoxEdges_disjoint_boxShellFreshEdges (d r L : ℕ) :
    Disjoint (cubicBoxEdges d cubicOrigin r) (boxShellFreshEdges d r L) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOld heFresh
  exact (Finset.mem_sdiff.mp heFresh).2 heOld

/-- Internal edge support of one signed shell slice. -/
noncomputable def boxShellSliceEdges
    (d r L : ℕ) (i : Fin d) (positive : Bool) : Finset (CubicEdge d) :=
  if positive then
    coordinateClosedBandEdges d (boxShellOuterRadius r L) i
      (r + 1) (boxShellOuterRadius r L)
  else
    coordinateClosedBandEdges d (boxShellOuterRadius r L) i
      (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ))

theorem boxShellSliceEdges_subset_fresh
    {d r L : ℕ} (i : Fin d) (positive : Bool) :
    boxShellSliceEdges d r L i positive ⊆ boxShellFreshEdges d r L := by
  classical
  intro e he
  rw [boxShellFreshEdges, Finset.mem_sdiff]
  cases positive with
  | false =>
      have heData : e ∈ coordinateClosedBandEdges d (boxShellOuterRadius r L) i
          (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ)) := by
        simpa [boxShellSliceEdges] using he
      have heBand := mem_coordinateClosedBandEdges_iff.mp heData
      refine ⟨heBand.1, ?_⟩
      intro heOld
      let z := e.1.out.1
      have hzmem : z ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem e.1
      have hzOld := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heOld hzmem
      have hzBound := mem_cubicMetricBox.mp hzOld i
      have hzBand := heBand.2 z hzmem
      simp [cubicOrigin] at hzBound
      omega
  | true =>
      have heData : e ∈ coordinateClosedBandEdges d (boxShellOuterRadius r L) i
          (r + 1) (boxShellOuterRadius r L) := by
        simpa [boxShellSliceEdges] using he
      have heBand := mem_coordinateClosedBandEdges_iff.mp heData
      refine ⟨heBand.1, ?_⟩
      intro heOld
      let z := e.1.out.1
      have hzmem : z ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem e.1
      have hzOld := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heOld hzmem
      have hzBound := mem_cubicMetricBox.mp hzOld i
      have hzBand := heBand.2 z hzmem
      simp [cubicOrigin] at hzBound
      omega

theorem coordinateSignedStepEdge_mem_boxShellFreshEdges
    {d r L : ℕ} {i : Fin d} {positive : Bool} {x : Cubic d}
    (hx : x ∈ cubicBoxSurface d cubicOrigin r)
    (hface : if positive then x i = r else x i = -(r : ℤ)) :
    coordinateSignedStepEdge i positive x ∈ boxShellFreshEdges d r L := by
  classical
  rw [boxShellFreshEdges, Finset.mem_sdiff]
  have hxBox : x ∈ cubicMetricBox d cubicOrigin (boxShellOuterRadius r L) :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr <| by
      rw [mem_cubicBoxSurface.mp hx]
      simp [boxShellOuterRadius]
      omega
  have hstepSlice := coordinateSignedStep_mem_boxShellSlice (L := L) hx hface
  have hstepBox := (mem_boxShellSliceVertices_iff.mp hstepSlice).1
  refine ⟨?_, ?_⟩
  · exact cubicStepEdge_mem_cubicBoxEdges hxBox (by
      simpa [coordinateSignedStep, coordinateSignedStepEdge] using hstepBox)
  · intro heOld
    have hstepOld := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heOld
      (show coordinateSignedStep i positive x ∈
          (coordinateSignedStepEdge i positive x : Sym2 (Cubic d)) by
        simp [coordinateSignedStep, coordinateSignedStepEdge, cubicStepEdge])
    have hbound := mem_cubicMetricBox.mp hstepOld i
    simp [cubicOrigin] at hbound
    cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hface hbound <;>
      simp [hface] at hbound

/-- A connection inside a signed slice depends only on fresh shell edges. -/
theorem dependsOn_connectionWithin_boxShellSlice
    {d r L : ℕ} {i : Fin d} {positive : Bool} {x y : Cubic d}
    (hx : x ∈ boxShellSliceVertices d r L i positive) :
    DependsOn (boxShellFreshEdges d r L)
      (connectionEventWithinVertices d
        (boxShellSliceVertices d r L i positive : Set (Cubic d)) x y) := by
  cases positive with
  | false =>
      have hx' : x ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (-(boxShellOuterRadius r L : ℤ)) (-(r + 1 : ℤ)) := by
        simpa [boxShellSliceVertices] using hx
      exact (dependsOn_connectionEventWithinVertices_closedBand hx').mono
        (boxShellSliceEdges_subset_fresh i false)
  | true =>
      have hx' : x ∈ coordinateClosedStripVertices d (boxShellOuterRadius r L) i
          (r + 1) (boxShellOuterRadius r L) := by
        simpa [boxShellSliceVertices] using hx
      exact (dependsOn_connectionEventWithinVertices_closedBand hx').mono
        (boxShellSliceEdges_subset_fresh i true)

theorem dependsOn_allBoxShellChainConnectionsEvent
    {d r L : ℕ} (hd : 2 ≤ d) :
    DependsOn (boxShellFreshEdges d r L)
      (allBoxShellChainConnectionsEvent hd r L) := by
  intro ω η hagree
  simp only [allBoxShellChainConnectionsEvent, Set.mem_iInter]
  apply forall_congr'
  intro j
  have hj := boxShellChainCorners_mem_chosenSlice (r := r) (L := L) hd j
  exact dependsOn_connectionWithin_boxShellSlice hj.1 hagree

theorem dependsOn_boxShellBridgeEvent
    {d r L : ℕ} (hd : 2 ≤ d)
    {iu iv : Fin d} {su sv : Bool} {u v : Cubic d}
    (hu : u ∈ cubicBoxSurface d cubicOrigin r)
    (hv : v ∈ cubicBoxSurface d cubicOrigin r)
    (huface : if su then u iu = r else u iu = -(r : ℤ))
    (hvface : if sv then v iv = r else v iv = -(r : ℤ)) :
    DependsOn (boxShellFreshEdges d r L)
      (boxShellBridgeEvent hd r L iu su u iv sv v) := by
  have hEU := (dependsOn_edgeOpenEvent (coordinateSignedStepEdge iu su u)).mono
    (Finset.singleton_subset_iff.mpr
      (coordinateSignedStepEdge_mem_boxShellFreshEdges (L := L) hu huface))
  have hEV := (dependsOn_edgeOpenEvent (coordinateSignedStepEdge iv sv v)).mono
    (Finset.singleton_subset_iff.mpr
      (coordinateSignedStepEdge_mem_boxShellFreshEdges (L := L) hv hvface))
  have hU : DependsOn (boxShellFreshEdges d r L)
      (boxShellEntranceConnectionEvent r L iu su u) := by
    exact dependsOn_connectionWithin_boxShellSlice
      (L := L) (coordinateSignedStep_mem_boxShellSlice (L := L) hu huface)
  have hV : DependsOn (boxShellFreshEdges d r L)
      (boxShellEntranceConnectionEvent r L iv sv v) := by
    exact dependsOn_connectionWithin_boxShellSlice
      (L := L) (coordinateSignedStep_mem_boxShellSlice (L := L) hv hvface)
  exact ((((hEU.inter hEV).inter hU).inter hV).inter
    (dependsOn_allBoxShellChainConnectionsEvent hd))

/-! ### Annular frontier conditioning -/

theorem dependsOn_connectionToBoxSurfaceEvent
    {d R : ℕ} (x : Cubic d) :
    DependsOn (cubicBoxEdges d cubicOrigin R) (connectionToBoxSurfaceEvent d R x) := by
  intro ω η hagree
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, hxu⟩
    exact ⟨u, hu, (dependsOn_connectionEventIn d _ x u hagree).mp hxu⟩
  · rintro ⟨u, hu, hxu⟩
    exact ⟨u, hu, (dependsOn_connectionEventIn d _ x u hagree).mpr hxu⟩

theorem dependsOn_annularPeelingSeparationEvent
    {d n M k : ℕ} (x y : Cubic d) :
    DependsOn (cubicBoxEdges d cubicOrigin (annularPeelingRadius n M k))
      (annularPeelingSeparationEvent d n M k x y) := by
  unfold annularPeelingSeparationEvent
  split_ifs
  · exact (((dependsOn_connectionToBoxSurfaceEvent x).inter
      (dependsOn_connectionToBoxSurfaceEvent y)).inter
        (dependsOn_connectionEventIn d _ x y).compl)
  · exact dependsOn_empty_event _

/-- Reachable vertices on the current peeled surface. -/
noncomputable def annularFrontierVertices
    (d R : ℕ) (x : Cubic d) (ω : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (cubicBoxSurface d cubicOrigin R).filter fun u ↦
    ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin R) x u

@[simp]
theorem mem_annularFrontierVertices_iff
    {d R : ℕ} {x u : Cubic d} {ω : EdgeConfiguration d} :
    u ∈ annularFrontierVertices d R x ω ↔
      u ∈ cubicBoxSurface d cubicOrigin R ∧
        ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin R) x u := by
  classical
  simp [annularFrontierVertices]

theorem annularFrontierVertices_nonempty_of_mem_peeling
    {d n M k : ℕ} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ annularPeelingSeparationEvent d n M k x y) :
    (annularFrontierVertices d (annularPeelingRadius n M k) x ω).Nonempty ∧
      (annularFrontierVertices d (annularPeelingRadius n M k) y ω).Nonempty := by
  unfold annularPeelingSeparationEvent at hω
  by_cases hxy : x ∈ cubicMetricBox d cubicOrigin n ∧
      y ∈ cubicMetricBox d cubicOrigin n
  · rw [if_pos hxy] at hω
    simp only [Set.mem_inter_iff, connectionToBoxSurfaceEvent, Set.mem_iUnion] at hω
    obtain ⟨u, hu, hxu⟩ := hω.1.1
    obtain ⟨v, hv, hyv⟩ := hω.1.2
    exact ⟨⟨u, mem_annularFrontierVertices_iff.mpr ⟨hu, hxu⟩⟩,
      ⟨v, mem_annularFrontierVertices_iff.mpr ⟨hv, hyv⟩⟩⟩
  · rw [if_neg hxy] at hω
    exact hω.elim

theorem annularFrontierVertices_disjoint_of_mem_peeling
    {d n M k : ℕ} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ annularPeelingSeparationEvent d n M k x y) :
    Disjoint (annularFrontierVertices d (annularPeelingRadius n M k) x ω)
      (annularFrontierVertices d (annularPeelingRadius n M k) y ω) := by
  have hnot : ω ∉ connectionEventIn d
      (cubicBoxEdges d cubicOrigin (annularPeelingRadius n M k)) x y := by
    unfold annularPeelingSeparationEvent at hω
    by_cases hxy : x ∈ cubicMetricBox d cubicOrigin n ∧
        y ∈ cubicMetricBox d cubicOrigin n
    · rw [if_pos hxy] at hω
      exact hω.2
    · rw [if_neg hxy] at hω
      exact hω.elim
  rw [Finset.disjoint_left]
  intro u hux huy
  have hux' := (mem_annularFrontierVertices_iff.mp hux).2
  have huy' := (mem_annularFrontierVertices_iff.mp huy).2
  obtain ⟨px, hpxOpen, hpxEdges⟩ := hux'
  obtain ⟨py, hpyOpen, hpyEdges⟩ := huy'
  have hxy : ω ∈ connectionEventIn d
      (cubicBoxEdges d cubicOrigin (annularPeelingRadius n M k)) x y := by
    refine ⟨px.append py.reverse,
      walkIsOpen_append hpxOpen (walkIsOpen_reverse hpyOpen), ?_⟩
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact hpxEdges ((mem_walkEdgeFinset_iff px _).mpr he)
    · have he' : (e : Sym2 (Cubic d)) ∈ py.edges := by simpa using he
      exact hpyEdges ((mem_walkEdgeFinset_iff py _).mpr he')
  exact hnot hxy

theorem annularFrontierVertices_eq_of_agree
    {d R : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hagree : ∀ e ∈ cubicBoxEdges d cubicOrigin R, (e ∈ ω ↔ e ∈ η)) :
    annularFrontierVertices d R x ω = annularFrontierVertices d R x η := by
  ext u
  simp only [mem_annularFrontierVertices_iff]
  constructor
  · rintro ⟨hu, hconn⟩
    exact ⟨hu, (dependsOn_connectionEventIn d _ x u hagree).mp hconn⟩
  · rintro ⟨hu, hconn⟩
    exact ⟨hu, (dependsOn_connectionEventIn d _ x u hagree).mpr hconn⟩

/-- Symmetry and transitivity for connections constrained by a finite edge support. -/
theorem connectionEventIn_symm_mem
    {d : ℕ} {E : Finset (CubicEdge d)} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventIn d E x y) :
    ω ∈ connectionEventIn d E y x := by
  obtain ⟨w, hwopen, hwedges⟩ := hxy
  refine ⟨w.reverse, walkIsOpen_reverse hwopen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  have he' : (e : Sym2 (Cubic d)) ∈ w.edges := by simpa using he
  exact hwedges ((mem_walkEdgeFinset_iff w e).mpr he')

theorem connectionEventIn_trans_mem
    {d : ℕ} {E : Finset (CubicEdge d)} {x y z : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventIn d E x y)
    (hyz : ω ∈ connectionEventIn d E y z) :
    ω ∈ connectionEventIn d E x z := by
  obtain ⟨p, hpopen, hpedges⟩ := hxy
  obtain ⟨q, hqopen, hqedges⟩ := hyz
  refine ⟨p.append q, walkIsOpen_append hpopen hqopen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · exact hpedges ((mem_walkEdgeFinset_iff p e).mpr he)
  · exact hqedges ((mem_walkEdgeFinset_iff q e).mpr he)

/-- A fresh shell bridge between two old frontier vertices makes the next peeling event
impossible. -/
theorem not_mem_next_annularPeeling_of_shellBridge
    {d n k L : ℕ} (hd : 2 ≤ d) {x y u v : Cubic d}
    {iu iv : Fin d} {su sv : Bool}
    (huface : if su then u iu = annularPeelingRadius n (L + 1) k
      else u iu = -(annularPeelingRadius n (L + 1) k : ℤ))
    (hvface : if sv then v iv = annularPeelingRadius n (L + 1) k
      else v iv = -(annularPeelingRadius n (L + 1) k : ℤ))
    {ω : EdgeConfiguration d}
    (hu : u ∈ annularFrontierVertices d (annularPeelingRadius n (L + 1) k) x ω)
    (hv : v ∈ annularFrontierVertices d (annularPeelingRadius n (L + 1) k) y ω)
    (hbridge : ω ∈ boxShellBridgeEvent hd (annularPeelingRadius n (L + 1) k) L
      iu su u iv sv v) :
    ω ∉ annularPeelingSeparationEvent d n (L + 1) (k + 1) x y := by
  intro hnext
  let R := annularPeelingRadius n (L + 1) k
  let S := annularPeelingRadius n (L + 1) (k + 1)
  have hRS : boxShellOuterRadius R L = S := by
    simp [R, S, annularPeelingRadius, boxShellOuterRadius]
    ring
  have huPlane := (mem_annularFrontierVertices_iff.mp hu).1
  have hvPlane := (mem_annularFrontierVertices_iff.mp hv).1
  have hbridgeConn := boxShellBridgeEvent_subset_connectionWithin_outerBox hd
    huPlane hvPlane huface hvface hbridge
  have hbridgeIn : ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin S) u v := by
    obtain ⟨w, hwopen, hwsupport⟩ := hbridgeConn
    refine ⟨w, hwopen, ?_⟩
    rw [← hRS]
    exact walkEdgeFinset_subset_cubicBoxEdges_of_support w fun z hz ↦
      Finset.mem_coe.mp (hwsupport z hz)
  have hRleS : R ≤ S := by
    rw [← hRS]
    simp [boxShellOuterRadius]
    omega
  have hxu : ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin S) x u :=
    connectionEventIn_mono (cubicBoxEdges_mono_radius hRleS) x u
      (mem_annularFrontierVertices_iff.mp hu).2
  have hyv : ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin S) y v :=
    connectionEventIn_mono (cubicBoxEdges_mono_radius hRleS) y v
      (mem_annularFrontierVertices_iff.mp hv).2
  have hxy := connectionEventIn_trans_mem hxu <|
    connectionEventIn_trans_mem hbridgeIn (connectionEventIn_symm_mem hyv)
  have hnotNext : ω ∉ connectionEventIn d (cubicBoxEdges d cubicOrigin S) x y := by
    unfold annularPeelingSeparationEvent at hnext
    by_cases hguard : x ∈ cubicMetricBox d cubicOrigin n ∧
        y ∈ cubicMetricBox d cubicOrigin n
    · rw [if_pos hguard] at hnext
      exact hnext.2
    · rw [if_neg hguard] at hnext
      exact hnext.elim
  exact hnotNext hxy

/-- The uniform finite-slab conclusion of Lemma 7.78 gives the source one-shell contraction
(7.94), with an explicit success factor `p² δ^(d+2)`. -/
theorem annularPeeling_probability_block_step_of_uniformFiniteSlab
    {d n k L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (x y : Cubic d) :
    (bernoulliBondMeasure d p).real
        (annularPeelingSeparationEvent d n (L + 1) (k + 1) x y) ≤
      (1 - (p : ℝ) ^ 2 * δ ^ (d + 2)) *
        (bernoulliBondMeasure d p).real
          (annularPeelingSeparationEvent d n (L + 1) k x y) := by
  let R := annularPeelingRadius n (L + 1) k
  let E := cubicBoxEdges d cubicOrigin R
  let A := annularPeelingSeparationEvent d n (L + 1) k x y
  let B := annularPeelingSeparationEvent d n (L + 1) (k + 1) x y
  have hAdep : DependsOn E A := dependsOn_annularPeelingSeparationEvent x y
  have hBA : B ⊆ A := annularPeelingSeparationEvent_anti (by omega)
  apply setBernoulli_real_le_mul_of_sliceProbability_le E p
    (measurableSet_annularPeelingSeparationEvent d n (L + 1) k x y)
    (measurableSet_annularPeelingSeparationEvent d n (L + 1) (k + 1) x y)
  intro ω
  have hsliceA := hAdep.sliceProbability_eq_indicator subset_rfl p ω
  by_cases hωA : ω ∈ A
  · obtain ⟨huNonempty, hvNonempty⟩ :=
      annularFrontierVertices_nonempty_of_mem_peeling hωA
    obtain ⟨u, huFront⟩ := huNonempty
    obtain ⟨v, hvFront⟩ := hvNonempty
    have huPlane := (mem_annularFrontierVertices_iff.mp huFront).1
    have hvPlane := (mem_annularFrontierVertices_iff.mp hvFront).1
    obtain ⟨iu, su, huface⟩ := exists_signed_coord_of_mem_cubicBoxSurface (by omega) huPlane
    obtain ⟨iv, sv, hvface⟩ := exists_signed_coord_of_mem_cubicBoxSurface (by omega) hvPlane
    let F := boxShellBridgeEvent hd R L iu su u iv sv v
    let EF := boxShellFreshEdges d R L
    have hFdep : DependsOn EF F :=
      dependsOn_boxShellBridgeEvent hd huPlane hvPlane huface hvface
    have hdisj : Disjoint (E : Set (CubicEdge d)) (EF : Set (CubicEdge d)) := by
      exact_mod_cast cubicBoxEdges_disjoint_boxShellFreshEdges d R L
    have hpre : (fun η => spliceOn E (restrictTo E ω) η) ⁻¹' B ⊆ Fᶜ := by
      intro η hηB
      simp only [Set.mem_preimage] at hηB
      intro hηF
      let ζ := spliceOn E (restrictTo E ω) η
      have hagree : ∀ e ∈ cubicBoxEdges d cubicOrigin R, (e ∈ ω ↔ e ∈ ζ) := by
        intro e he
        have heE : e ∈ E := by simpa [E] using he
        change e ∈ ω ↔ e ∈ spliceOn E (restrictTo E ω) η
        rw [mem_spliceOn_of_mem heE, mem_restrictTo]
        simp [heE]
      have huζ : u ∈ annularFrontierVertices d R x ζ := by
        rw [← annularFrontierVertices_eq_of_agree hagree]
        simpa [R] using huFront
      have hvζ : v ∈ annularFrontierVertices d R y ζ := by
        rw [← annularFrontierVertices_eq_of_agree hagree]
        simpa [R] using hvFront
      have hζF : ζ ∈ F :=
        (hFdep.spliceOn_mem_iff_of_disjoint (restrictTo_subset E ω) hdisj η).mpr hηF
      exact (not_mem_next_annularPeeling_of_shellBridge hd huface hvface huζ hvζ hζF) hηB
    have hFm : MeasurableSet F := hFdep.measurableSet
    have hδF : (p : ℝ) ^ 2 * δ ^ (d + 2) ≤
        (bernoulliBondMeasure d p).real F :=
      boxShellBridge_probability_ge_of_uniformFiniteSlab hd p hδ0 hslab
        huPlane hvPlane huface hvface
    have hsliceB : sliceProbability E p B ω ≤ 1 - (p : ℝ) ^ 2 * δ ^ (d + 2) := by
      calc
        sliceProbability E p B ω = (bernoulliBondMeasure d p).real
            ((fun η => spliceOn E (restrictTo E ω) η) ⁻¹' B) := rfl
        _ ≤ (bernoulliBondMeasure d p).real Fᶜ := measureReal_mono hpre
        _ = 1 - (bernoulliBondMeasure d p).real F := by
          rw [measureReal_compl hFm, probReal_univ]
        _ ≤ 1 - (p : ℝ) ^ 2 * δ ^ (d + 2) := by linarith
    rw [hsliceA, Set.indicator_of_mem hωA]
    simpa using hsliceB
  · have hsliceB_le_A : sliceProbability E p B ω ≤ sliceProbability E p A ω :=
      measureReal_mono (Set.preimage_mono hBA)
    rw [hsliceA, Set.indicator_of_notMem hωA] at hsliceB_le_A ⊢
    simpa [B] using hsliceB_le_A

/-! ### Iteration and the geometric form of Lemma 7.89 -/

/-- The finite star of every cubic edge incident to one vertex. -/
noncomputable def cubicVertexIncidentEdges (d : ℕ) (x : Cubic d) :
    Finset (CubicEdge d) :=
  cubicIncidentEdges d {x}

/-- The local cylinder on which a prescribed vertex is isolated. -/
def cubicVertexIsolatedEvent (d : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  closedEdgeSetEvent d (cubicVertexIncidentEdges d x)

/-- If the root is strictly inside the target surface, isolating it rules out an arm to that
surface.  This supplies the uniform small-annulus estimate omitted in the printed peeling
argument after (7.94). -/
theorem disjoint_cubicVertexIsolatedEvent_connectionToBoxSurfaceEvent
    {d n N : ℕ} {x : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n) (hnN : n < N) :
    Disjoint (cubicVertexIsolatedEvent d x) (connectionToBoxSurfaceEvent d N x) := by
  classical
  rw [Set.disjoint_left]
  intro ω hωisolated hωarm
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion] at hωarm
  obtain ⟨z, hzSurface, w, hwopen, _hwEdges⟩ := hωarm
  have hxz : x ≠ z := by
    intro hxz
    subst z
    have hxDist := mem_cubicMetricBox_iff_lInfDist_le.mp hx
    have hzDist := mem_cubicBoxSurface.mp hzSurface
    omega
  cases w with
  | nil => exact hxz rfl
  | @cons _ z _ hadj wtail =>
      let e : CubicEdge d :=
        ⟨s(x, z), (cubicGraph d).mem_edgeSet.mpr hadj⟩
      have heOpen : e ∈ ω := by
        have hfirst := hwopen s(x, z) (by simp)
        simpa [e, edgeOpen] using hfirst
      have heIncident : e ∈ cubicVertexIncidentEdges d x := by
        unfold cubicVertexIncidentEdges
        apply mem_cubicIncidentEdges_of_endpoint (V := {x}) (x := x) (e := e) (by simp)
        simp [e]
      exact (Set.disjoint_left.mp hωisolated) heIncident heOpen

/-- The isolation cylinder has the expected Bernoulli probability. -/
theorem bernoulliBondMeasure_real_cubicVertexIsolatedEvent
    (d : ℕ) (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (cubicVertexIsolatedEvent d x) =
      (1 - (p : ℝ)) ^ (cubicVertexIncidentEdges d x).card := by
  exact bernoulliBondMeasure_real_closedEdgeSetEvent d p (cubicVertexIncidentEdges d x)

/-- A cubic vertex has at most `2d` incident edge coordinates. -/
theorem cubicVertexIncidentEdges_card_le (d : ℕ) (x : Cubic d) :
    (cubicVertexIncidentEdges d x).card ≤ 2 * d := by
  simpa [cubicVertexIncidentEdges] using cubicIncidentEdges_card_le d ({x} : Finset (Cubic d))

/-- For a proper density, every nontrivial annular arm event has a uniform probability gap
below one.  Closing the finite star at `x` is a subset of the complementary event. -/
theorem twoArmSeparation_probability_le_one_sub_isolation
    {d n N : ℕ} (p : I) {x y : Cubic d} (hnN : n < N) :
    (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
      1 - (1 - (p : ℝ)) ^ (2 * d) := by
  by_cases hx : x ∈ cubicMetricBox d cubicOrigin n
  · have hdisj := disjoint_cubicVertexIsolatedEvent_connectionToBoxSurfaceEvent hx hnN
    have hsub : twoArmSeparationEvent d n N x y ⊆ (cubicVertexIsolatedEvent d x)ᶜ := by
      intro ω hω
      have hωarm : ω ∈ connectionToBoxSurfaceEvent d N x := by
        unfold twoArmSeparationEvent at hω
        split at hω
        · exact hω.1.1
        · exact hω.elim
      exact fun hωiso ↦ (Set.disjoint_left.mp hdisj) hωiso hωarm
    have hmeasure :
        (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
          (bernoulliBondMeasure d p).real (cubicVertexIsolatedEvent d x)ᶜ :=
      measureReal_mono hsub (measure_ne_top _ _)
    have hisolatedMeasurable : MeasurableSet (cubicVertexIsolatedEvent d x) :=
      measurableSet_closedEdgeSetEvent d _
    rw [measureReal_compl hisolatedMeasurable, probReal_univ,
      bernoulliBondMeasure_real_cubicVertexIsolatedEvent] at hmeasure
    have hbase0 : 0 ≤ 1 - (p : ℝ) := by exact sub_nonneg.mpr p.2.2
    have hbase1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
    have hpow : (1 - (p : ℝ)) ^ (2 * d) ≤
        (1 - (p : ℝ)) ^ (cubicVertexIncidentEdges d x).card :=
      pow_le_pow_of_le_one hbase0 hbase1 (cubicVertexIncidentEdges_card_le d x)
    linarith
  · have hbase0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
    have hbase1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
    rw [twoArmSeparationEvent, if_neg (not_and_of_not_left _ hx), measureReal_empty]
    have hpow : (1 - (p : ℝ)) ^ (2 * d) ≤ (1 : ℝ) ^ (2 * d) :=
      pow_le_pow_left₀ hbase0 hbase1 (2 * d)
    simpa using hpow

/-- Iterating the concrete shell estimate gives Grimmett's geometric bound immediately.  The
success factor is kept exact here; later exponential corollaries may decrease it in order to
stay uniformly away from the endpoint `q = 0`. -/
theorem twoArmSeparation_probability_le_pow_of_uniformFiniteSlab
    {d n N L : ℕ} (hd : 2 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hnN : n ≤ N) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
      (1 - (p : ℝ) ^ 2 * δ ^ (d + 2)) ^ ((N - n) / (L + 1)) := by
  have hδ1 : δ ≤ 1 := by
    have horigin : cubicOrigin ∈ finiteThickSlabSVertices d 1 L := by
      rw [mem_finiteThickSlabSVertices_iff]
      intro i
      simp [cubicOrigin]
    exact (hslab.1 1 le_rfl cubicOrigin horigin cubicOrigin horigin).trans
      measureReal_le_one
  have hpSqLe : (p : ℝ) ^ 2 ≤ 1 := by
    nlinarith [p.2.1, p.2.2, sq_nonneg (p : ℝ), sq_nonneg (1 - (p : ℝ))]
  have hδpowLe : δ ^ (d + 2) ≤ 1 := by
    simpa using pow_le_pow_left₀ hδ0 hδ1 (d + 2)
  have hsuccessLe : (p : ℝ) ^ 2 * δ ^ (d + 2) ≤ 1 := by
    nlinarith [pow_nonneg hδ0 (d + 2)]
  apply twoArmSeparation_probability_le_pow_of_annular_block_step p hnN
    (sub_nonneg.mpr hsuccessLe)
  intro k
  exact annularPeeling_probability_block_step_of_uniformFiniteSlab
    hd p hδ0 hslab x y

/-- Exponential rate that simultaneously absorbs quotient rounding for full shells and the
uniform isolation estimate for annuli thinner than one shell. -/
noncomputable def annularPeelingExponentialRate (q q₀ : ℝ) (M : ℕ) : ℝ :=
  min (secondClusterPeelingRate q M) (-Real.log q₀ / M)

theorem annularPeelingExponentialRate_pos
    {q q₀ : ℝ} {M : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq₀0 : 0 < q₀) (hq₀1 : q₀ < 1) (hM : 1 ≤ M) :
    0 < annularPeelingExponentialRate q q₀ M := by
  rw [annularPeelingExponentialRate, lt_min_iff]
  exact ⟨secondClusterPeelingRate_pos hq0 hq1 hM,
    div_pos (neg_pos.mpr (Real.log_neg hq₀0 hq₀1)) (by positivity)⟩

/-- Full-shell geometric decay is bounded by the common exponential rate. -/
theorem pow_natDiv_le_exp_neg_annularPeelingExponentialRate
    {q q₀ : ℝ} {m M : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hM : 1 ≤ M) (hm : M ≤ m) :
    q ^ (m / M) ≤ Real.exp (-(annularPeelingExponentialRate q q₀ M) * m) := by
  refine (pow_natDiv_le_exp_neg_secondClusterPeelingRate hq0 hq1 hM hm).trans ?_
  apply Real.exp_le_exp.mpr
  have hrate : annularPeelingExponentialRate q q₀ M ≤
      secondClusterPeelingRate q M := min_le_left _ _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- In an annulus thinner than one shell, the isolation gap is absorbed by the same rate. -/
theorem one_sub_pow_le_exp_neg_annularPeelingExponentialRate
    {q q₀ : ℝ} {m M : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq₀0 : 0 < q₀) (hq₀1 : q₀ < 1) (hM : 1 ≤ M) (hm : m < M) :
    q₀ ≤ Real.exp (-(annularPeelingExponentialRate q q₀ M) * m) := by
  have hrate : annularPeelingExponentialRate q q₀ M ≤ -Real.log q₀ / M :=
    min_le_right _ _
  have hrate0 : 0 ≤ annularPeelingExponentialRate q q₀ M :=
    (annularPeelingExponentialRate_pos hq0 hq1 hq₀0 hq₀1 hM).le
  have hM0 : (0 : ℝ) < M := by positivity
  have hmCast : (m : ℝ) ≤ M := by exact_mod_cast hm.le
  have hmul : annularPeelingExponentialRate q q₀ M * m ≤ -Real.log q₀ := by
    calc
      annularPeelingExponentialRate q q₀ M * m ≤
          (-Real.log q₀ / M) * m :=
        mul_le_mul_of_nonneg_right hrate (by positivity)
      _ ≤ (-Real.log q₀ / M) * M := by
        exact mul_le_mul_of_nonneg_left hmCast
          (div_nonneg (neg_nonneg.mpr (Real.log_nonpos hq₀0.le hq₀1.le)) hM0.le)
      _ = -Real.log q₀ := by field_simp
  calc
    q₀ = Real.exp (Real.log q₀) := (Real.exp_log hq₀0).symm
    _ ≤ Real.exp (-(annularPeelingExponentialRate q q₀ M) * m) :=
      Real.exp_le_exp.mpr (by linarith)

/-- Integer-radius form of Grimmett's Lemma 7.89 from the exact finite-slab conclusion of
Lemma 7.78.  Unlike the raw `q^⌊(N-n)/M⌋` estimate, this theorem also handles every positive
gap smaller than one shell, using the explicit isolated-root cylinder. -/
theorem exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n N : ℕ, n < N → ∀ x y : Cubic d,
      (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤
        Real.exp (-ξ * ((N - n : ℕ) : ℝ)) := by
  let ε : ℝ := (p : ℝ) ^ 2 * δ ^ (d + 2) / 2
  let q : ℝ := 1 - ε
  let q₀ : ℝ := 1 - (1 - (p : ℝ)) ^ (2 * d)
  let M : ℕ := L + 1
  let ξ : ℝ := annularPeelingExponentialRate q q₀ M
  have hpSq0 : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hp0
  have hpSqLe : (p : ℝ) ^ 2 ≤ 1 := by
    nlinarith [p.2.1, p.2.2, sq_nonneg (p : ℝ), sq_nonneg (1 - (p : ℝ))]
  have hδpow0 : 0 < δ ^ (d + 2) := pow_pos hδ0 _
  have hδpowLe : δ ^ (d + 2) ≤ 1 := by
    simpa using pow_le_pow_left₀ hδ0.le hδ1 (d + 2)
  have hsuccess0 : 0 < (p : ℝ) ^ 2 * δ ^ (d + 2) := mul_pos hpSq0 hδpow0
  have hsuccessLe : (p : ℝ) ^ 2 * δ ^ (d + 2) ≤ 1 := by
    nlinarith [pow_nonneg hδ0.le (d + 2)]
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεLeHalf : ε ≤ 1 / 2 := by dsimp [ε]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hbase0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hbase1 : 1 - (p : ℝ) < 1 := by linarith
  have hpowBase0 : 0 < (1 - (p : ℝ)) ^ (2 * d) := pow_pos hbase0 _
  have hpowBase1 : (1 - (p : ℝ)) ^ (2 * d) < 1 := by
    apply pow_lt_one₀ hbase0.le hbase1
    omega
  have hq₀0 : 0 < q₀ := by dsimp [q₀]; linarith
  have hq₀1 : q₀ < 1 := by dsimp [q₀]; linarith
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hξ0 : 0 < ξ := annularPeelingExponentialRate_pos hq0 hq1 hq₀0 hq₀1 hM
  refine ⟨ξ, hξ0, ?_⟩
  intro n N hnN x y
  let m := N - n
  by_cases hmM : M ≤ m
  · have hgeom : (bernoulliBondMeasure d p).real
        (twoArmSeparationEvent d n N x y) ≤ q ^ (m / M) := by
      apply twoArmSeparation_probability_le_pow_of_annular_block_step p hnN.le
        hq0.le
      intro k
      have hraw := annularPeeling_probability_block_step_of_uniformFiniteSlab
        hd p hδ0.le hslab x y (n := n) (k := k) (L := L)
      have hcoef : 1 - (p : ℝ) ^ 2 * δ ^ (d + 2) ≤ q := by
        dsimp [q, ε]
        linarith
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoef measureReal_nonneg)
    exact hgeom.trans
      (pow_natDiv_le_exp_neg_annularPeelingExponentialRate
        hq0 hq1 hM hmM)
  · have hsmall := twoArmSeparation_probability_le_one_sub_isolation
      p (x := x) (y := y) hnN
    exact hsmall.trans
      (one_sub_pow_le_exp_neg_annularPeelingExponentialRate
        hq0 hq1 hq₀0 hq₀1 hM (Nat.lt_of_not_ge hmM))

/-- Source-facing scaled-radius version of Lemma 7.89.  The explicit ceiling in
`scaledBoxRadius` resolves Grimmett's convention of using real radii where integers are
required, while the exponent retains the exact real quantity `n(a-1)`. -/
theorem exists_scaledTwoArmSeparation_probability_le_exp_of_uniformFiniteSlab
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ℝ, 1 < a →
      ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n,
        (bernoulliBondMeasure d p).real
            (twoArmSeparationEvent d n (scaledBoxRadius a n) x y) ≤
          Real.exp (-(n : ℝ) * (a - 1) * ξ) := by
  obtain ⟨ξ, hξ0, hξ⟩ :=
    exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
      hd p hp0 hp1 hδ0 hδ1 hslab
  refine ⟨ξ, hξ0, ?_⟩
  intro n hn a ha x hx y hy
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOuter : n < scaledBoxRadius a n := by
    rw [scaledBoxRadius, Nat.lt_ceil]
    nlinarith
  have hraw := hξ n (scaledBoxRadius a n) hnOuter x y
  refine hraw.trans (Real.exp_le_exp.mpr ?_)
  have hceil : a * (n : ℝ) ≤ (scaledBoxRadius a n : ℕ) := by
    exact Nat.le_ceil (a * (n : ℝ))
  have hcastSub : (((scaledBoxRadius a n - n : ℕ) : ℝ)) =
      (scaledBoxRadius a n : ℕ) - (n : ℝ) := by
    rw [Nat.cast_sub hnOuter.le]
  rw [hcastSub]
  nlinarith

/-! ### Coalescence consequence -/

/-- The polynomial pair-count correction is negligible compared with any positive linear
annular decay rate. -/
theorem tendsto_cubicMetricBox_card_sq_mul_exp_neg_nat
    (d : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 *
        Real.exp (-ξ * n))
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (2 * d) * Real.exp (-ξ * n))
      Filter.atTop (nhds 0) :=
    (Real.summable_pow_mul_exp_neg_nat_mul (2 * d) hξ).tendsto_atTop_zero
  have hscaled : Filter.Tendsto
      (fun n : ℕ ↦ (3 : ℝ) ^ (2 * d) *
        ((n : ℝ) ^ (2 * d) * Real.exp (-ξ * n)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (3 : ℝ) ^ (2 * d))).mul hbase
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)
    (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩) hscaled
  rw [cubicMetricBox_card]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlin : (2 * n + 1 : ℝ) ≤ 3 * n := by exact_mod_cast (show 2 * n + 1 ≤ 3 * n by omega)
  have hpow : (2 * n + 1 : ℝ) ^ (2 * d) ≤ (3 * n : ℝ) ^ (2 * d) := by
    exact pow_le_pow_left₀ (by positivity) hlin (2 * d)
  calc
    ((((2 * n + 1) ^ d : ℕ) : ℝ) ^ 2) * Real.exp (-ξ * n) =
        (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-ξ * n) := by
      norm_num [← pow_mul, Nat.mul_comm, mul_comm]
    _ ≤ (3 * n : ℝ) ^ (2 * d) * Real.exp (-ξ * n) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (3 : ℝ) ^ (2 * d) *
        ((n : ℝ) ^ (2 * d) * Real.exp (-ξ * n)) := by
      rw [mul_pow]
      ring

/-- Lemma 7.89 implies that all infinite-cluster vertices in `B(n)` coalesce inside `B(2n)`
with probability tending to one.  This is the concrete bridge consumed by the existing
probability assembly for Lemma 7.97. -/
theorem infiniteClusterCoalescenceEvent_probability_tendsto_one_of_uniformFiniteSlab
    {d L : ℕ} (hd : 2 ≤ d) (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterCoalescenceEvent d n (2 * n)))
      Filter.atTop (nhds 1) := by
  obtain ⟨ξ, hξ0, hξ⟩ :=
    exists_twoArmSeparation_probability_le_exp_of_uniformFiniteSlab
      hd p hp0 hp1 hδ0 hδ1 hslab
  apply infiniteClusterCoalescenceEvent_probability_tendsto_one_of_twoArm_bound
    p id (fun n ↦ 2 * n) (fun n ↦ Real.exp (-ξ * n))
  · intro n
    dsimp
    omega
  · intro n x hx y hy
    by_cases hn : n = 0
    · subst n
      simpa using (measureReal_le_one (μ := bernoulliBondMeasure d p)
        (s := twoArmSeparationEvent d 0 0 x y))
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hbound := hξ n (2 * n) (by omega) x y
      have hsub : 2 * n - n = n := by omega
      simpa [hsub] using hbound
  · exact tendsto_cubicMetricBox_card_sq_mul_exp_neg_nat d hξ0

end Percolation
