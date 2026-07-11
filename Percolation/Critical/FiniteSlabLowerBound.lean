import Percolation.Critical.SlabConnectivity
import Percolation.Critical.RegionSymmetry

/-!
# Uniform finite-slab connection lower bounds

This file formalizes the probabilistic and geometric steps (7.81)--(7.88) in the proof of
Grimmett's Lemma 7.78.  The first stage extracts uniform corner-to-face estimates from
percolation in the quarter-slab `ℤ₊² × [0,L]^(d-2)`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The coordinate permutation interchanging the first two coordinates. -/
def cubicFirstTwoSwapEquiv (d : ℕ) (hd : 2 ≤ d) : Fin d ≃ Fin d :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, hd⟩

@[simp]
theorem cubicFirstTwoSwapEquiv_zero (d : ℕ) (hd : 2 ≤ d) :
    cubicFirstTwoSwapEquiv d hd ⟨0, by omega⟩ = ⟨1, hd⟩ := by
  simp [cubicFirstTwoSwapEquiv]

@[simp]
theorem cubicFirstTwoSwapEquiv_one (d : ℕ) (hd : 2 ≤ d) :
    cubicFirstTwoSwapEquiv d hd ⟨1, hd⟩ = ⟨0, by omega⟩ := by
  simp [cubicFirstTwoSwapEquiv]

/-- The cubic-graph automorphism interchanging the first two coordinates. -/
def cubicFirstTwoSwapIso (d : ℕ) (hd : 2 ≤ d) :
    cubicGraph d ≃g cubicGraph d :=
  cubicCoordinatePermutationIso (cubicFirstTwoSwapEquiv d hd)

@[simp]
theorem cubicFirstTwoSwapIso_apply_zero
    (d : ℕ) (hd : 2 ≤ d) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd x ⟨0, by omega⟩ = x ⟨1, hd⟩ := by
  simp [cubicFirstTwoSwapIso, cubicFirstTwoSwapEquiv,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]

@[simp]
theorem cubicFirstTwoSwapIso_apply_one
    (d : ℕ) (hd : 2 ≤ d) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd x ⟨1, hd⟩ = x ⟨0, by omega⟩ := by
  simp [cubicFirstTwoSwapIso, cubicFirstTwoSwapEquiv,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]

theorem cubicFirstTwoSwapIso_apply_of_two_le
    (d : ℕ) (hd : 2 ≤ d) (x : Cubic d) (i : Fin d) (hi : 2 ≤ i.val) :
    cubicFirstTwoSwapIso d hd x i = x i := by
  have hi0 : i ≠ ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hi1 : i ≠ ⟨1, hd⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [cubicFirstTwoSwapIso, cubicFirstTwoSwapEquiv,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv,
    Equiv.swap_apply_of_ne_of_ne hi0 hi1]

@[simp]
theorem cubicFirstTwoSwapIso_origin (d : ℕ) (hd : 2 ≤ d) :
    cubicFirstTwoSwapIso d hd cubicOrigin = cubicOrigin := by
  ext i
  by_cases hi : i.val < 2
  · interval_cases hval : i.val
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
      rw [hi0]
      simp [cubicOrigin]
    · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
      rw [hi1]
      simp [cubicOrigin]
  · rw [cubicFirstTwoSwapIso_apply_of_two_le d hd cubicOrigin i (by omega)]

@[simp]
theorem cubicFirstTwoSwapIso_involutive
    (d : ℕ) (hd : 2 ≤ d) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd (cubicFirstTwoSwapIso d hd x) = x := by
  ext i
  by_cases hi : i.val < 2
  · interval_cases hval : i.val
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
      rw [hi0]
      simp
    · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
      rw [hi1]
      simp
  · rw [cubicFirstTwoSwapIso_apply_of_two_le d hd _ i (by omega),
      cubicFirstTwoSwapIso_apply_of_two_le d hd x i (by omega)]

theorem cubicFirstTwoSwapIso_mem_slabCornerBoxVertices_iff
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd x ∈ slabCornerBoxVertices d m L ↔
      x ∈ slabCornerBoxVertices d m L := by
  rw [mem_slabCornerBoxVertices_iff, mem_slabCornerBoxVertices_iff]
  constructor <;> intro h i
  · by_cases hi : i.val < 2
    · interval_cases hval : i.val
      · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
        rw [hi0]
        simpa using h ⟨1, hd⟩
      · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
        rw [hi1]
        simpa using h ⟨0, by omega⟩
    · have hi2 : 2 ≤ i.val := by omega
      simpa [hi, cubicFirstTwoSwapIso_apply_of_two_le d hd x i hi2] using h i
  · by_cases hi : i.val < 2
    · interval_cases hval : i.val
      · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
        rw [hi0]
        simpa using h ⟨1, hd⟩
      · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
        rw [hi1]
        simpa using h ⟨0, by omega⟩
    · have hi2 : 2 ≤ i.val := by omega
      simpa [hi, cubicFirstTwoSwapIso_apply_of_two_le d hd x i hi2] using h i

theorem cubicGraphIsoRegion_firstTwoSwap_slabCornerBox
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    cubicGraphIsoRegion (cubicFirstTwoSwapIso d hd)
        (slabCornerBoxVertices d m L : Set (Cubic d)) =
      (slabCornerBoxVertices d m L : Set (Cubic d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicFirstTwoSwapIso_mem_slabCornerBoxVertices_iff d hd m L x).2 hx
  · intro x hx
    refine ⟨cubicFirstTwoSwapIso d hd x, ?_, ?_⟩
    · exact (cubicFirstTwoSwapIso_mem_slabCornerBoxVertices_iff d hd m L x).2 hx
    · exact cubicFirstTwoSwapIso_involutive d hd x

theorem cubicFirstTwoSwapIso_mem_rightFace_iff
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd x ∈
        slabCornerTargetFace d hd m L ⟨1, by decide⟩ ↔
      x ∈ slabCornerTargetFace d hd m L ⟨0, by decide⟩ := by
  simp only [slabCornerTargetFace, Finset.mem_filter]
  rw [cubicFirstTwoSwapIso_mem_slabCornerBoxVertices_iff]
  simp

theorem cubicGraphIsoRegion_firstTwoSwap_rightFace
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    cubicGraphIsoRegion (cubicFirstTwoSwapIso d hd)
        (slabCornerTargetFace d hd m L ⟨0, by decide⟩ : Set (Cubic d)) =
      (slabCornerTargetFace d hd m L ⟨1, by decide⟩ : Set (Cubic d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicFirstTwoSwapIso_mem_rightFace_iff d hd m L x).2 hx
  · intro x hx
    refine ⟨cubicFirstTwoSwapIso d hd x, ?_, ?_⟩
    · apply (cubicFirstTwoSwapIso_mem_rightFace_iff d hd m L
          (cubicFirstTwoSwapIso d hd x)).1
      simpa using hx
    · exact cubicFirstTwoSwapIso_involutive d hd x

theorem slabCornerConnectionEvent_zero_eq_toSet
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    slabCornerConnectionEvent d hd m L ⟨0, by decide⟩ =
      connectionEventWithinVerticesToSet d
        (slabCornerBoxVertices d m L : Set (Cubic d)) cubicOrigin
        (slabCornerTargetFace d hd m L ⟨0, by decide⟩ : Set (Cubic d)) := by
  have hstart : slabCornerVertex d m ⟨0, by decide⟩ = cubicOrigin := by
    ext i
    simp [slabCornerVertex, cubicOrigin]
  rw [slabCornerConnectionEvent, connectionEventWithinVerticesToSet, hstart]
  ext ω
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨y, hy, hconn⟩ <;> exact ⟨y, hy, hconn⟩

/-- The companion origin-to-top event in the union used immediately before (7.82). -/
def slabCornerOriginTopConnectionEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) : Set (EdgeConfiguration d) :=
  connectionEventWithinVerticesToSet d
    (slabCornerBoxVertices d m L : Set (Cubic d)) cubicOrigin
    (slabCornerTargetFace d hd m L ⟨1, by decide⟩ : Set (Cubic d))

theorem slabCornerConnectionEvent_zero_probability_eq_originTop
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) :
    (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) =
      (bernoulliBondMeasure d p).real
        (slabCornerOriginTopConnectionEvent d hd m L) := by
  rw [slabCornerConnectionEvent_zero_eq_toSet]
  have h := bernoulliBondMeasure_real_connectionEventWithinVerticesToSet_graphIso
    (cubicFirstTwoSwapIso d hd)
    (slabCornerBoxVertices d m L : Set (Cubic d))
    (slabCornerTargetFace d hd m L ⟨0, by decide⟩ : Set (Cubic d))
    p cubicOrigin
  rw [cubicGraphIsoRegion_firstTwoSwap_slabCornerBox,
    cubicFirstTwoSwapIso_origin,
    cubicGraphIsoRegion_firstTwoSwap_rightFace] at h
  exact h

theorem slabCornerBoxVertices_subset_cubicQuarterSlab
    (d m L : ℕ) :
    (slabCornerBoxVertices d m L : Set (Cubic d)) ⊆ cubicQuarterSlab d L := by
  intro x hx i
  have hxi := mem_slabCornerBoxVertices_iff.mp hx i
  by_cases hi : i.val < 2
  · exact ⟨(if_pos hi ▸ hxi).1, fun hi2 ↦ (not_lt_of_ge hi2 hi).elim⟩
  · have hi2 : 2 ≤ i.val := by omega
    exact ⟨(if_neg hi ▸ hxi).1, fun _ ↦ (if_neg hi ▸ hxi).2⟩

/-- A finite walk which starts in a vertex set and ends outside it has a prefix ending at the
last inside vertex before its first exit. -/
theorem exists_walk_prefix_to_boundary
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (w : G.Walk u v) (hu : P u) (hv : ¬ P v) :
    ∃ x z, ∃ q : G.Walk u x,
      P x ∧ ¬ P z ∧ G.Adj x z ∧
        (∀ y ∈ q.support, P y) ∧ q.edges <+: w.edges ∧ z ∈ w.support := by
  induction w with
  | nil => exact (hv hu).elim
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hu₁ : P u₁
      · obtain ⟨x, z, q, hx, hz, hxz, hqP, hqPrefix, hzSupport⟩ := ih hu₁ hv
        refine ⟨x, z, q.cons hu₀u₁, hx, hz, hxz, ?_, ?_, ?_⟩
        · intro y hy
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
          exact hy.elim (fun h ↦ h ▸ hu) (hqP y)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩
        · exact by simp [hzSupport]
      · refine ⟨u₀, u₁, .nil, hu, hu₁, hu₀u₁, ?_, List.nil_prefix, ?_⟩
        · simpa using hu
        · simp

/-- The union of the origin-to-right and origin-to-top events preceding (7.82). -/
def slabCornerOriginExitEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) : Set (EdgeConfiguration d) :=
  slabCornerConnectionEvent d hd m L ⟨0, by decide⟩ ∪
    slabCornerOriginTopConnectionEvent d hd m L

/-- An infinite quarter-slab cluster from the origin must leave every finite corner box through
its right or top face. -/
theorem infiniteQuarterSlabCluster_subset_slabCornerOriginExitEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    {ω | (cubicOpenClusterWithinVertices d (cubicQuarterSlab d L) ω
      cubicOrigin).Infinite} ⊆ slabCornerOriginExitEvent d hd m L := by
  intro ω hω
  have hexists : ∃ y ∈ cubicOpenClusterWithinVertices d (cubicQuarterSlab d L) ω
      cubicOrigin, y ∉ slabCornerBoxVertices d m L := by
    by_contra hnot
    push Not at hnot
    apply hω
    exact (slabCornerBoxVertices d m L).finite_toSet.subset fun y hy ↦ hnot y hy
  obtain ⟨y, hyCluster, hyOutside⟩ := hexists
  rcases hyCluster.2 with ⟨w, hwOpen, hwQuarter⟩
  have horigin : cubicOrigin ∈ slabCornerBoxVertices d m L := by
    rw [mem_slabCornerBoxVertices_iff]
    intro i
    simp [cubicOrigin]
  obtain ⟨x, z, q, hxBox, hzOutside, hxz, hqBox, hqPrefix, hzSupport⟩ :=
    exists_walk_prefix_to_boundary w horigin hyOutside
  have hqOpen : walkIsOpen ω q :=
    walkIsOpen_of_edges_subset hwOpen hqPrefix.subset
  have hzQuarter : z ∈ cubicQuarterSlab d L := hwQuarter z hzSupport
  have hxBounds := mem_slabCornerBoxVertices_iff.mp hxBox
  rw [mem_slabCornerBoxVertices_iff] at hzOutside
  push Not at hzOutside
  obtain ⟨i, hiOutside⟩ := hzOutside
  have hi : i.val < 2 := by
    by_contra hnot
    have hi2 : 2 ≤ i.val := by omega
    have hzi := hzQuarter i
    exact hiOutside (by simpa [show ¬ i.val < 2 by omega] using ⟨hzi.1, hzi.2 hi2⟩)
  have hziNonneg := (hzQuarter i).1
  have hziLarge : (m : ℤ) < z i := by
    simpa [hi, hziNonneg] using hiOutside
  rcases (cubicGraph_adj_iff_exists_stepFrom x z).mp hxz with ⟨a, ha⟩
  have hstep : z i ≤ x i + 1 := by
    simpa [ha] using cubicStepFrom_coord_le_add_one x a i
  have hxiUpper : x i ≤ m := (if_pos hi ▸ hxBounds i).2
  have hxiEq : x i = m := by omega
  have hconn : ω ∈ connectionEventWithinVertices d
      (slabCornerBoxVertices d m L : Set (Cubic d)) cubicOrigin x :=
    ⟨q, hqOpen, hqBox⟩
  rw [slabCornerOriginExitEvent]
  interval_cases hval : i.val
  · left
    rw [slabCornerConnectionEvent_zero_eq_toSet,
      connectionEventWithinVerticesToSet]
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨?_, hconn⟩⟩
    rw [Finset.mem_coe, slabCornerTargetFace, Finset.mem_filter]
    refine ⟨hxBox, ?_⟩
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
    simpa [hi0] using hxiEq
  · right
    rw [slabCornerOriginTopConnectionEvent,
      connectionEventWithinVerticesToSet]
    apply Set.mem_iUnion.mpr
    refine ⟨x, Set.mem_iUnion.mpr ⟨?_, hconn⟩⟩
    rw [Finset.mem_coe, slabCornerTargetFace, Finset.mem_filter]
    refine ⟨hxBox, ?_⟩
    have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
    simpa [hi1] using hxiEq

/-- The source estimate immediately before (7.82): one half of the rooted quarter-slab
percolation probability lower-bounds the origin-to-right event. -/
theorem regionThetaFrom_half_le_slabCornerConnectionEvent_zero
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) :
    regionThetaFrom d (cubicQuarterSlab d L) p cubicOrigin / 2 ≤
      (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) := by
  let μ := bernoulliBondMeasure d p
  let A := slabCornerConnectionEvent d hd m L ⟨0, by decide⟩
  let B := slabCornerOriginTopConnectionEvent d hd m L
  have hsub : regionThetaFrom d (cubicQuarterSlab d L) p cubicOrigin ≤
      μ.real (A ∪ B) := by
    simpa [regionThetaFrom, μ, A, B, slabCornerOriginExitEvent] using
      measureReal_mono
        (infiniteQuarterSlabCluster_subset_slabCornerOriginExitEvent d hd m L)
        (measure_ne_top _ _)
  have hunion : μ.real (A ∪ B) ≤ μ.real A + μ.real B :=
    measureReal_union_le A B
  have heq : μ.real A = μ.real B := by
    simpa [μ, A, B] using
      slabCornerConnectionEvent_zero_probability_eq_originTop d hd p m L
  rw [← heq] at hunion
  dsimp [μ, A, B] at hsub hunion ⊢
  linarith

/-! ### Cyclic symmetry of the four corner events -/

/-- Counterclockwise quarter-turn of the first two coordinates about the center of
`[0,m]²`, acting trivially in the transverse coordinates. -/
def cubicSlabCornerQuarterTurnIso
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ) : cubicGraph d ≃g cubicGraph d :=
  RelIso.trans (cubicFirstTwoSwapIso d hd)
    (RelIso.trans (cubicCoordinateReflectionIso ⟨0, by omega⟩)
      (cubicTranslationIso cubicOrigin
        (slabCornerVertex d m ⟨1, by decide⟩)))

@[simp]
theorem cubicSlabCornerQuarterTurnIso_apply_zero
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (x : Cubic d) :
    cubicSlabCornerQuarterTurnIso d hd m x ⟨0, by omega⟩ =
      (m : ℤ) - x ⟨1, hd⟩ := by
  simp [cubicSlabCornerQuarterTurnIso, cubicTranslate,
    cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
    slabCornerVertex, cubicOrigin]
  ring

@[simp]
theorem cubicSlabCornerQuarterTurnIso_apply_one
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (x : Cubic d) :
    cubicSlabCornerQuarterTurnIso d hd m x ⟨1, hd⟩ = x ⟨0, by omega⟩ := by
  simp [cubicSlabCornerQuarterTurnIso, cubicTranslate,
    cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
    slabCornerVertex, cubicOrigin]

theorem cubicSlabCornerQuarterTurnIso_apply_of_two_le
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (x : Cubic d)
    (i : Fin d) (hi : 2 ≤ i.val) :
    cubicSlabCornerQuarterTurnIso d hd m x i = x i := by
  have hi0 : i ≠ ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hiVal0 : i.val ≠ 0 := by omega
  have hiVal1 : i.val ≠ 1 := by omega
  simp [cubicSlabCornerQuarterTurnIso, cubicTranslate,
    cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
    slabCornerVertex, cubicOrigin, hiVal0, hiVal1,
    cubicFirstTwoSwapIso_apply_of_two_le d hd x i hi, hi0]

/-- Cyclic successor for the four corners. -/
def slabCornerNext (k : Fin 4) : Fin 4 :=
  ⟨(k.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

@[simp] theorem slabCornerNext_zero : slabCornerNext ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
@[simp] theorem slabCornerNext_one : slabCornerNext ⟨1, by decide⟩ = ⟨2, by decide⟩ := rfl
@[simp] theorem slabCornerNext_two : slabCornerNext ⟨2, by decide⟩ = ⟨3, by decide⟩ := rfl
@[simp] theorem slabCornerNext_three : slabCornerNext ⟨3, by decide⟩ = ⟨0, by decide⟩ := rfl

@[simp]
theorem cubicSlabCornerQuarterTurnIso_corner
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (k : Fin 4) :
    cubicSlabCornerQuarterTurnIso d hd m (slabCornerVertex d m k) =
      slabCornerVertex d m (slabCornerNext k) := by
  fin_cases k <;> ext i
  all_goals
    by_cases hi0 : i.val = 0
    · have hiEq : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hiEq]
      simp [slabCornerVertex, slabCornerNext]
    · by_cases hi1 : i.val = 1
      · have hiEq : i = ⟨1, hd⟩ := Fin.ext hi1
        rw [hiEq]
        simp [slabCornerVertex, slabCornerNext]
      · have hi2 : 2 ≤ i.val := by omega
        rw [cubicSlabCornerQuarterTurnIso_apply_of_two_le d hd m _ i hi2]
        simp [slabCornerVertex, hi0, hi1]

theorem cubicSlabCornerQuarterTurnIso_mem_box_iff
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (x : Cubic d) :
    cubicSlabCornerQuarterTurnIso d hd m x ∈ slabCornerBoxVertices d m L ↔
      x ∈ slabCornerBoxVertices d m L := by
  rw [mem_slabCornerBoxVertices_iff, mem_slabCornerBoxVertices_iff]
  constructor <;> intro h i
  · by_cases hi : i.val < 2
    · interval_cases hval : i.val
      · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
        rw [hi0]
        simpa using h ⟨1, hd⟩
      · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
        rw [hi1]
        have hx1 := h ⟨0, by omega⟩
        simp at hx1 ⊢
        omega
    · have hi2 : 2 ≤ i.val := by omega
      simpa [hi, cubicSlabCornerQuarterTurnIso_apply_of_two_le d hd m x i hi2]
        using h i
  · by_cases hi : i.val < 2
    · interval_cases hval : i.val
      · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
        rw [hi0]
        have hx1 := h ⟨1, hd⟩
        simp at hx1 ⊢
        omega
      · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
        rw [hi1]
        simpa using h ⟨0, by omega⟩
    · have hi2 : 2 ≤ i.val := by omega
      simpa [hi, cubicSlabCornerQuarterTurnIso_apply_of_two_le d hd m x i hi2]
        using h i

theorem cubicGraphIsoRegion_slabCornerQuarterTurn_box
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    cubicGraphIsoRegion (cubicSlabCornerQuarterTurnIso d hd m)
        (slabCornerBoxVertices d m L : Set (Cubic d)) =
      (slabCornerBoxVertices d m L : Set (Cubic d)) := by
  let F := cubicSlabCornerQuarterTurnIso d hd m
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicSlabCornerQuarterTurnIso_mem_box_iff d hd m L x).2 hx
  · intro x hx
    refine ⟨F.symm x, ?_, by simp [F]⟩
    apply (cubicSlabCornerQuarterTurnIso_mem_box_iff d hd m L (F.symm x)).1
    simpa [F] using hx

theorem cubicSlabCornerQuarterTurnIso_mem_targetFace_iff
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) (x : Cubic d) :
    cubicSlabCornerQuarterTurnIso d hd m x ∈
        slabCornerTargetFace d hd m L (slabCornerNext k) ↔
      x ∈ slabCornerTargetFace d hd m L k := by
  fin_cases k <;>
    simp only [slabCornerNext_zero, slabCornerNext_one, slabCornerNext_two,
      slabCornerNext_three, slabCornerTargetFace, Finset.mem_filter]
  all_goals rw [cubicSlabCornerQuarterTurnIso_mem_box_iff]
  all_goals
    constructor <;> rintro ⟨hbox, hcoord⟩
    all_goals refine ⟨hbox, ?_⟩
    all_goals
      have hb0 := mem_slabCornerBoxVertices_iff.mp hbox ⟨0, by omega⟩
      have hb1 := mem_slabCornerBoxVertices_iff.mp hbox ⟨1, hd⟩
      simp at hb0 hb1 hcoord ⊢
      omega

theorem cubicGraphIsoRegion_slabCornerQuarterTurn_targetFace
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) :
    cubicGraphIsoRegion (cubicSlabCornerQuarterTurnIso d hd m)
        (slabCornerTargetFace d hd m L k : Set (Cubic d)) =
      (slabCornerTargetFace d hd m L (slabCornerNext k) : Set (Cubic d)) := by
  let F := cubicSlabCornerQuarterTurnIso d hd m
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicSlabCornerQuarterTurnIso_mem_targetFace_iff d hd m L k x).2 hx
  · intro x hx
    refine ⟨F.symm x, ?_, by simp [F]⟩
    apply (cubicSlabCornerQuarterTurnIso_mem_targetFace_iff
      d hd m L k (F.symm x)).1
    simpa [F] using hx

theorem slabCornerConnectionEvent_eq_toSet
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) :
    slabCornerConnectionEvent d hd m L k =
      connectionEventWithinVerticesToSet d
        (slabCornerBoxVertices d m L : Set (Cubic d))
        (slabCornerVertex d m k)
        (slabCornerTargetFace d hd m L k : Set (Cubic d)) := by
  rw [slabCornerConnectionEvent, connectionEventWithinVerticesToSet]
  ext ω
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨y, hy, hconn⟩ <;> exact ⟨y, hy, hconn⟩

theorem slabCornerConnectionEvent_probability_eq_next
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) (k : Fin 4) :
    (bernoulliBondMeasure d p).real (slabCornerConnectionEvent d hd m L k) =
      (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L (slabCornerNext k)) := by
  rw [slabCornerConnectionEvent_eq_toSet,
    slabCornerConnectionEvent_eq_toSet]
  have h := bernoulliBondMeasure_real_connectionEventWithinVerticesToSet_graphIso
    (cubicSlabCornerQuarterTurnIso d hd m)
    (slabCornerBoxVertices d m L : Set (Cubic d))
    (slabCornerTargetFace d hd m L k : Set (Cubic d))
    p (slabCornerVertex d m k)
  rw [cubicGraphIsoRegion_slabCornerQuarterTurn_box,
    cubicSlabCornerQuarterTurnIso_corner,
    cubicGraphIsoRegion_slabCornerQuarterTurn_targetFace] at h
  exact h

/-- Rotation invariance propagates the source `θ/2` estimate to all four events in (7.82). -/
theorem regionThetaFrom_half_le_slabCornerConnectionEvent
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) (k : Fin 4) :
    regionThetaFrom d (cubicQuarterSlab d L) p cubicOrigin / 2 ≤
      (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L k) := by
  let θ := regionThetaFrom d (cubicQuarterSlab d L) p cubicOrigin
  have h0 : θ / 2 ≤ (bernoulliBondMeasure d p).real
      (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) := by
    simpa [θ] using
      regionThetaFrom_half_le_slabCornerConnectionEvent_zero d hd p m L
  fin_cases k
  · exact h0
  · calc
      θ / 2 ≤ (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) := h0
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨1, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨0, by decide⟩
  · calc
      θ / 2 ≤ (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) := h0
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨1, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨0, by decide⟩
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨2, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨1, by decide⟩
  · calc
      θ / 2 ≤ (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨0, by decide⟩) := h0
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨1, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨0, by decide⟩
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨2, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨1, by decide⟩
      _ = (bernoulliBondMeasure d p).real
          (slabCornerConnectionEvent d hd m L ⟨3, by decide⟩) := by
        simpa using slabCornerConnectionEvent_probability_eq_next
          d hd p m L ⟨2, by decide⟩

/-- Explicit positive constant in (7.83), retaining the exact sprinkling and repair factors. -/
noncomputable def slabCornerAllConnectionLowerBound
    (d L : ℕ) (p₁ p₂ : I) : ℝ :=
  (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ (4 * ((d - 2) * L)) *
    (regionThetaFrom d (cubicQuarterSlab d L) p₁ cubicOrigin / 2) ^ 4

theorem slabCornerAllConnectionLowerBound_pos
    (d L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    0 < slabCornerAllConnectionLowerBound d L p₁ p₂ := by
  have hθ : 0 < regionThetaFrom d (cubicQuarterSlab d L) p₁ cubicOrigin :=
    regionThetaFrom_pos_of_critical_lt_of_connected
      (cubicRegionGraph_cubicQuarterSlab_connected d L) hcrit
      (cubicOrigin_mem_cubicQuarterSlab d L)
  have hp₁lt : (p₁ : ℝ) < 1 := h12.trans_le p₂.2.2
  have hratio : 0 < ((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ)) :=
    div_pos (sub_pos.mpr h12) (sub_pos.mpr hp₁lt)
  exact mul_pos (pow_pos hratio _) (pow_pos (div_pos hθ (by norm_num)) _)

/-- Equation (7.83), derived from supercritical quarter-slab percolation with no hidden
geometric or finite-energy premise. -/
theorem slabCornerAllConnectionLowerBound_le
    (d : ℕ) (hd : 2 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) (m : ℕ) :
    slabCornerAllConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) := by
  have hθnonneg : 0 ≤
      regionThetaFrom d (cubicQuarterSlab d L) p₁ cubicOrigin / 2 :=
    div_nonneg measureReal_nonneg (by norm_num)
  simpa [slabCornerAllConnectionLowerBound] using
    slabCornersConnected_probability_ge d hd h12 m L hθnonneg
      (regionThetaFrom_half_le_slabCornerConnectionEvent d hd p₁ m L)

end Percolation
