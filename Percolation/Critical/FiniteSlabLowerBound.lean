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

/-! ### Transported corner boxes for Figure 7.15 -/

/-- Pullback of the four-corners-connected event along a cubic graph automorphism.  In the
original configuration this is the event that the four transported corners are connected
inside the transported corner box. -/
def transportedSlabCornersConnectedEvent
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (m L : ℕ) :
    Set (EdgeConfiguration d) :=
  cubicGraphIsoConfigurationPullback F ⁻¹'
    allSlabCornersConnectedEvent d m L

theorem measurableSet_transportedSlabCornersConnectedEvent
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (m L : ℕ) :
    MeasurableSet (transportedSlabCornersConnectedEvent F m L) :=
  (measurableSet_allSlabCornersConnectedEvent d m L).preimage
    (measurable_cubicGraphIsoConfigurationPullback F)

theorem isIncreasingEvent_transportedSlabCornersConnectedEvent
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (m L : ℕ) :
    IsIncreasingEvent (transportedSlabCornersConnectedEvent F m L) := by
  intro ω η hωη hω
  apply isIncreasingEvent_allSlabCornersConnectedEvent d m L
    (show cubicGraphIsoConfigurationPullback F ω ⊆
      cubicGraphIsoConfigurationPullback F η by
        intro e he
        exact hωη he)
  exact hω

theorem transportedSlabCornersConnectedEvent_probability
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (p : I) (m L : ℕ) :
    (bernoulliBondMeasure d p).real
        (transportedSlabCornersConnectedEvent F m L) =
      (bernoulliBondMeasure d p).real
        (allSlabCornersConnectedEvent d m L) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦
      μ.real (allSlabCornersConnectedEvent d m L))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      (allSlabCornersConnectedEvent d m L) =
    (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L) at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_allSlabCornersConnectedEvent d m L)] at hmap
  exact hmap

/-- A transported all-corners event supplies each concrete transported corner connection. -/
theorem mem_connectionEventWithinVertices_of_mem_transportedSlabCornersConnectedEvent
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (m L : ℕ)
    (k : Fin 4) {ω : EdgeConfiguration d}
    (hω : ω ∈ transportedSlabCornersConnectedEvent F m L) :
    ω ∈ connectionEventWithinVertices d
      (cubicGraphIsoRegion F (slabCornerBoxVertices d m L : Set (Cubic d)))
      (F (slabCornerVertex d m ⟨0, by decide⟩))
      (F (slabCornerVertex d m k)) := by
  have hbase : cubicGraphIsoConfigurationPullback F ω ∈
      connectionEventWithinVertices d
        (slabCornerBoxVertices d m L : Set (Cubic d))
        (slabCornerVertex d m ⟨0, by decide⟩)
        (slabCornerVertex d m k) := by
    simp only [transportedSlabCornersConnectedEvent, Set.mem_preimage] at hω
    simp only [allSlabCornersConnectedEvent, Set.mem_iInter] at hω
    exact hω k (Finset.mem_univ k)
  exact (cubicGraphIsoConfigurationPullback_mem_connectionEventWithinVertices_iff
    F (slabCornerBoxVertices d m L : Set (Cubic d)) ω
    (slabCornerVertex d m ⟨0, by decide⟩)
    (slabCornerVertex d m k)).1 hbase

/-- Translation placing the first square `U₁` in Figure 7.15. -/
def figure715UpperSquareIso
    (d a b : ℕ) : cubicGraph d ≃g cubicGraph d :=
  cubicTranslationIso cubicOrigin
    (slabCornerVertex d (b - a) ⟨3, by decide⟩)

@[simp]
theorem figure715UpperSquareIso_corner_zero
    (d a b : ℕ) :
    figure715UpperSquareIso d a b (slabCornerVertex d a ⟨0, by decide⟩) =
      slabCornerVertex d (b - a) ⟨3, by decide⟩ := by
  rw [figure715UpperSquareIso, cubicTranslationIso_apply]
  have hzero : slabCornerVertex d a ⟨0, by decide⟩ = cubicOrigin := by
    ext i
    simp [slabCornerVertex, cubicOrigin]
  rw [hzero, cubicTranslate_self]

theorem figure715UpperSquareIso_corner_two
    (d a b : ℕ) (hab : a ≤ b) :
    figure715UpperSquareIso d a b (slabCornerVertex d a ⟨2, by decide⟩) =
      fun i ↦ if i.val = 0 then (a : ℤ)
        else if i.val = 1 then (b : ℤ) else 0 := by
  ext i
  simp only [figure715UpperSquareIso, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, slabCornerVertex]
  by_cases hi0 : i.val = 0
  · simp [hi0]
  · by_cases hi1 : i.val = 1
    · simp [hi1, Nat.cast_sub hab]
    · simp [hi0, hi1]

theorem cubicGraphIsoRegion_figure715UpperSquare_subset_finiteThickSlabS
    (d : ℕ) (hd : 2 ≤ d) {a b n L : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    cubicGraphIsoRegion (figure715UpperSquareIso d a b)
        (slabCornerBoxVertices d a L : Set (Cubic d)) ⊆
      (finiteThickSlabSVertices d n L : Set (Cubic d)) := by
  rintro x ⟨u, hu, rfl⟩
  change figure715UpperSquareIso d a b u ∈ finiteThickSlabSVertices d n L
  rw [mem_finiteThickSlabSVertices_iff]
  have huBounds := mem_slabCornerBoxVertices_iff.mp hu
  intro i
  by_cases hi : i.val < 2
  · interval_cases hval : i.val
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hval
      rw [hi0]
      have hu0 := huBounds ⟨0, by omega⟩
      simp [figure715UpperSquareIso, cubicTranslate, slabCornerVertex,
        cubicOrigin] at hu0 ⊢
      apply Int.ofNat_le.mp
      rw [Int.natCast_natAbs, abs_le]
      constructor <;> omega
    · have hi1 : i = ⟨1, hd⟩ := Fin.ext hval
      rw [hi1]
      have hu1 := huBounds ⟨1, hd⟩
      simp [figure715UpperSquareIso, cubicTranslate, slabCornerVertex,
        cubicOrigin, Nat.cast_sub hab] at hu1 ⊢
      apply Int.ofNat_le.mp
      rw [Int.natCast_natAbs, abs_le]
      constructor <;> omega
  · have hi2 : 2 ≤ i.val := by omega
    have hui := huBounds i
    have hi0 : i.val ≠ 0 := by omega
    have hi1 : i.val ≠ 1 := by omega
    simpa [hi, figure715UpperSquareIso, cubicTranslate, slabCornerVertex,
      cubicOrigin, hi0, hi1] using hui

theorem slabCornerBoxVertices_subset_finiteThickSlabS
    (d : ℕ) {m n L : ℕ} (hmn : m ≤ n) :
    (slabCornerBoxVertices d m L : Set (Cubic d)) ⊆
      (finiteThickSlabSVertices d n L : Set (Cubic d)) := by
  intro x hx
  change x ∈ finiteThickSlabSVertices d n L
  rw [mem_finiteThickSlabSVertices_iff]
  have hxBounds := mem_slabCornerBoxVertices_iff.mp hx
  intro i
  by_cases hi : i.val < 2
  · have hxi := if_pos hi ▸ hxBounds i
    rw [if_pos hi]
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, abs_le]
    constructor <;> omega
  · simpa [hi] using hxBounds i

/-- The transverse-zero planar vertex `(a,b,0,…,0)` in Figure 7.15. -/
def figure715PlanarVertex (d a b : ℕ) : Cubic d :=
  fun i ↦ if i.val = 0 then (a : ℤ)
    else if i.val = 1 then (b : ℤ) else 0

/-- The two all-corners events in Figure 7.15 force the normalized planar vertex to connect to
the origin inside `S_n(L)`. -/
theorem inter_figure715CornerEvents_subset_connectionS
    (d : ℕ) (hd : 2 ≤ d) {a b n L : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    transportedSlabCornersConnectedEvent (figure715UpperSquareIso d a b) a L ∩
        allSlabCornersConnectedEvent d (b - a) L ⊆
      finiteThickSlabSConnectionEvent d n L cubicOrigin
        (figure715PlanarVertex d a b) := by
  rintro ω ⟨hupper, hlower⟩
  have hupperConn :=
    mem_connectionEventWithinVertices_of_mem_transportedSlabCornersConnectedEvent
      (figure715UpperSquareIso d a b) a L ⟨2, by decide⟩ hupper
  rw [figure715UpperSquareIso_corner_zero,
    figure715UpperSquareIso_corner_two d a b hab] at hupperConn
  change ω ∈ connectionEventWithinVertices d
    (cubicGraphIsoRegion (figure715UpperSquareIso d a b)
      (slabCornerBoxVertices d a L : Set (Cubic d)))
    (slabCornerVertex d (b - a) ⟨3, by decide⟩)
    (figure715PlanarVertex d a b) at hupperConn
  have hlowerConn : ω ∈ connectionEventWithinVertices d
      (slabCornerBoxVertices d (b - a) L : Set (Cubic d))
      cubicOrigin (slabCornerVertex d (b - a) ⟨3, by decide⟩) := by
    simp only [allSlabCornersConnectedEvent, Set.mem_iInter] at hlower
    have h := hlower ⟨3, by decide⟩ (Finset.mem_univ _)
    have hstart : slabCornerVertex d (b - a) ⟨0, by decide⟩ = cubicOrigin := by
      ext i
      simp [slabCornerVertex, cubicOrigin]
    rw [hstart] at h
    exact h
  rcases hlowerConn with ⟨q, hqOpen, hqBox⟩
  rcases hupperConn with ⟨r, hrOpen, hrBox⟩
  refine ⟨q.append r, walkIsOpen_append hqOpen hrOpen, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hxq | hxr
  · exact slabCornerBoxVertices_subset_finiteThickSlabS d
      ((Nat.sub_le b a).trans hbn) (hqBox x hxq)
  · exact cubicGraphIsoRegion_figure715UpperSquare_subset_finiteThickSlabS
      d hd hab hbn (hrBox x hxr)

/-- Probability form of Figure 7.15 for a normalized transverse-zero vertex
`0 ≤ a ≤ b ≤ n`. -/
theorem sq_slabCornerLowerBound_le_figure715PlanarConnection
    (d : ℕ) (hd : 2 ≤ d) (p : I) {a b n L : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    δ ^ 2 ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabSConnectionEvent d n L cubicOrigin
        (figure715PlanarVertex d a b)) := by
  let F := figure715UpperSquareIso d a b
  let A := transportedSlabCornersConnectedEvent F a L
  let B := allSlabCornersConnectedEvent d (b - a) L
  have hA : δ ≤ (bernoulliBondMeasure d p).real A := by
    rw [show (bernoulliBondMeasure d p).real A =
        (bernoulliBondMeasure d p).real
          (allSlabCornersConnectedEvent d a L) by
      exact transportedSlabCornersConnectedEvent_probability F p a L]
    exact hcorner a
  have hB : δ ≤ (bernoulliBondMeasure d p).real B := hcorner (b - a)
  calc
    δ ^ 2 = δ * δ := by ring
    _ ≤ (bernoulliBondMeasure d p).real A *
        (bernoulliBondMeasure d p).real B :=
      mul_le_mul hA hB hδ measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) :=
      bernoulliBondMeasure_real_fkg p
        (isIncreasingEvent_transportedSlabCornersConnectedEvent F a L)
        (isIncreasingEvent_allSlabCornersConnectedEvent d (b - a) L)
        (measurableSet_transportedSlabCornersConnectedEvent F a L)
        (measurableSet_allSlabCornersConnectedEvent d (b - a) L)
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin
          (figure715PlanarVertex d a b)) :=
      measureReal_mono
        (inter_figure715CornerEvents_subset_connectionS d hd hab hbn)
        (measure_ne_top _ _)

/-- Inequality (7.86) combined with Figure 7.15, for a normalized vertex whose first two
coordinates are `0 ≤ a ≤ b`. -/
theorem transverseCost_mul_sq_slabCornerLowerBound_le_normalizedConnectionS
    (d : ℕ) (hd : 2 ≤ d) (p : I) {z : Cubic d} {a b n L : ℕ}
    (hz : z ∈ slabCornerBoxVertices d n L)
    (hz0 : z ⟨0, by omega⟩ = a) (hz1 : z ⟨1, hd⟩ = b)
    (hab : a ≤ b) (hbn : b ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    (p : ℝ) ^ ((d - 2) * L) * δ ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z) := by
  let z' := figure715PlanarVertex d a b
  have hz' : z' ∈ slabCornerBoxVertices d n L := by
    rw [mem_slabCornerBoxVertices_iff]
    intro i
    by_cases hi0 : i.val = 0
    · have hiEq : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hiEq]
      simp [z', figure715PlanarVertex]
      omega
    · by_cases hi1 : i.val = 1
      · have hiEq : i = ⟨1, hd⟩ := Fin.ext hi1
        rw [hiEq]
        simp [z', figure715PlanarVertex]
        omega
      · have hi2 : ¬ i.val < 2 := by omega
        simp [z', figure715PlanarVertex, hi0, hi1, hi2]
  have hagree : ∀ i : Fin d, i.val < 2 → z i = z' i := by
    intro i hi
    interval_cases hval : i.val
    · have hiEq : i = ⟨0, by omega⟩ := Fin.ext hval
      rw [hiEq, hz0]
      simp [z', figure715PlanarVertex]
    · have hiEq : i = ⟨1, hd⟩ := Fin.ext hval
      rw [hiEq, hz1]
      simp [z', figure715PlanarVertex]
  obtain ⟨w, hwPath, hwLength, hwBox⟩ :=
    exists_transverse_cubicPath_in_slabCorner hd hz hz' hagree
  let W : Set (EdgeConfiguration d) := {ω | walkIsOpen ω w}
  let B := finiteThickSlabSConnectionEvent d n L cubicOrigin z'
  have hWprob : (p : ℝ) ^ ((d - 2) * L) ≤
      (bernoulliBondMeasure d p).real W := by
    rw [show (bernoulliBondMeasure d p).real W = (p : ℝ) ^ w.length by
      exact bernoulliBondMeasure_real_walkIsOpen p w hwPath.isTrail]
    exact pow_le_pow_of_le_one p.2.1 p.2.2 hwLength
  have hBprob : δ ^ 2 ≤ (bernoulliBondMeasure d p).real B := by
    simpa [B, z'] using
      sq_slabCornerLowerBound_le_figure715PlanarConnection
        d hd p hab hbn hδ hcorner
  have hsub : W ∩ B ⊆ finiteThickSlabSConnectionEvent d n L cubicOrigin z := by
    rintro ω ⟨hW, hB⟩
    rcases hB with ⟨q, hqOpen, hqS⟩
    refine ⟨q.append w.reverse, walkIsOpen_append hqOpen (walkIsOpen_reverse hW), ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hxq | hxw
    · exact hqS x hxq
    · apply slabCornerBoxVertices_subset_finiteThickSlabS d le_rfl
      apply hwBox x
      simpa using hxw
  calc
    (p : ℝ) ^ ((d - 2) * L) * δ ^ 2 ≤
        (bernoulliBondMeasure d p).real W *
          (bernoulliBondMeasure d p).real B :=
      mul_le_mul hWprob hBprob (pow_nonneg hδ _) measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real (W ∩ B) :=
      bernoulliBondMeasure_real_fkg p
        (by intro ω η hωη hω e he; exact hωη (hω e he))
        (isIncreasingEvent_finiteThickSlabSConnectionEvent d n L cubicOrigin z')
        (measurableSet_walkIsOpen w)
        (measurableSet_finiteThickSlabSConnectionEvent d n L cubicOrigin z')
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z) :=
      measureReal_mono hsub (measure_ne_top _ _)

/-! ### Signed-coordinate normalization for the full statement (7.84) -/

theorem cubicFirstTwoSwapIso_mem_finiteThickSlabS_iff
    (d : ℕ) (hd : 2 ≤ d) (n L : ℕ) (x : Cubic d) :
    cubicFirstTwoSwapIso d hd x ∈ finiteThickSlabSVertices d n L ↔
      x ∈ finiteThickSlabSVertices d n L := by
  rw [mem_finiteThickSlabSVertices_iff, mem_finiteThickSlabSVertices_iff]
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

theorem cubicGraphIsoRegion_firstTwoSwap_finiteThickSlabS
    (d : ℕ) (hd : 2 ≤ d) (n L : ℕ) :
    cubicGraphIsoRegion (cubicFirstTwoSwapIso d hd)
        (finiteThickSlabSVertices d n L : Set (Cubic d)) =
      (finiteThickSlabSVertices d n L : Set (Cubic d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicFirstTwoSwapIso_mem_finiteThickSlabS_iff d hd n L x).2 hx
  · intro x hx
    refine ⟨cubicFirstTwoSwapIso d hd x, ?_, ?_⟩
    · exact (cubicFirstTwoSwapIso_mem_finiteThickSlabS_iff d hd n L x).2 hx
    · exact cubicFirstTwoSwapIso_involutive d hd x

theorem cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
    (d n L : ℕ) (j : Fin d) (hj : j.val < 2) (x : Cubic d) :
    cubicCoordinateReflectionIso j x ∈ finiteThickSlabSVertices d n L ↔
      x ∈ finiteThickSlabSVertices d n L := by
  rw [mem_finiteThickSlabSVertices_iff, mem_finiteThickSlabSVertices_iff]
  constructor <;> intro h i
  · by_cases hij : i = j
    · subst i
      simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv, hj]
        using h j
    · by_cases hi : i.val < 2
      · simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
          hij, hi] using h i
      · simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
          hij, hi] using h i
  · by_cases hij : i = j
    · subst i
      simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv, hj]
        using h j
    · by_cases hi : i.val < 2
      · simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
          hij, hi] using h i
      · simpa [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
          hij, hi] using h i

theorem cubicGraphIsoRegion_coordinateReflection_finiteThickSlabS
    (d n L : ℕ) (j : Fin d) (hj : j.val < 2) :
    cubicGraphIsoRegion (cubicCoordinateReflectionIso j)
        (finiteThickSlabSVertices d n L : Set (Cubic d)) =
      (finiteThickSlabSVertices d n L : Set (Cubic d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
      d n L j hj x).2 hx
  · intro x hx
    refine ⟨cubicCoordinateReflectionIso j x, ?_, ?_⟩
    · exact (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
        d n L j hj x).2 hx
    · exact cubicCoordinateReflectionEquiv_apply_self j x

theorem finiteThickSlabSConnectionEvent_probability_swap
    (d : ℕ) (hd : 2 ≤ d) (p : I) (n L : ℕ) (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin x) =
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin
          (cubicFirstTwoSwapIso d hd x)) := by
  unfold finiteThickSlabSConnectionEvent
  simpa [cubicGraphIsoRegion_firstTwoSwap_finiteThickSlabS,
    cubicFirstTwoSwapIso_origin] using
    bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso
      (cubicFirstTwoSwapIso d hd)
      (finiteThickSlabSVertices d n L : Set (Cubic d)) p cubicOrigin x

theorem finiteThickSlabSConnectionEvent_probability_reflection
    (d : ℕ) (p : I) (n L : ℕ) (j : Fin d) (hj : j.val < 2)
    (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin x) =
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin
          (cubicCoordinateReflectionIso j x)) := by
  unfold finiteThickSlabSConnectionEvent
  have horigin : cubicCoordinateReflectionIso j cubicOrigin = cubicOrigin := by
    ext i
    simp [cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv, cubicOrigin]
  have h := bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso
    (cubicCoordinateReflectionIso j)
    (finiteThickSlabSVertices d n L : Set (Cubic d)) p cubicOrigin x
  rw [cubicGraphIsoRegion_coordinateReflection_finiteThickSlabS d n L j hj,
    horigin] at h
  exact h

/-- The `(7.84)` lower bound for points whose first two coordinates are nonnegative; coordinate
exchange removes the ordering assumption from Figure 7.15. -/
theorem transverseCost_mul_sq_slabCornerLowerBound_le_nonnegativeConnectionS
    (d : ℕ) (hd : 2 ≤ d) (p : I) {z : Cubic d} {n L : ℕ}
    (hzS : z ∈ finiteThickSlabSVertices d n L)
    (hz0 : 0 ≤ z ⟨0, by omega⟩) (hz1 : 0 ≤ z ⟨1, hd⟩)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    (p : ℝ) ^ ((d - 2) * L) * δ ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z) := by
  let a := (z ⟨0, by omega⟩).toNat
  let b := (z ⟨1, hd⟩).toNat
  have haCast : (a : ℤ) = z ⟨0, by omega⟩ := by
    simp [a, Int.toNat_of_nonneg hz0]
  have hbCast : (b : ℤ) = z ⟨1, hd⟩ := by
    simp [b, Int.toNat_of_nonneg hz1]
  have hzBounds := mem_finiteThickSlabSVertices_iff.mp hzS
  have han : a ≤ n := by
    change (z ⟨0, by omega⟩).toNat ≤ n
    rw [← Int.natAbs_of_nonneg hz0]
    exact hzBounds ⟨0, by omega⟩
  have hbn : b ≤ n := by
    change (z ⟨1, hd⟩).toNat ≤ n
    rw [← Int.natAbs_of_nonneg hz1]
    exact hzBounds ⟨1, hd⟩
  have hzBox : z ∈ slabCornerBoxVertices d n L := by
    rw [mem_slabCornerBoxVertices_iff]
    intro i
    by_cases hi : i.val < 2
    · interval_cases hval : i.val
      · have hiEq : i = ⟨0, by omega⟩ := Fin.ext hval
        rw [hiEq]
        exact ⟨hz0, haCast ▸ (by exact_mod_cast han)⟩
      · have hiEq : i = ⟨1, hd⟩ := Fin.ext hval
        rw [hiEq]
        exact ⟨hz1, hbCast ▸ (by exact_mod_cast hbn)⟩
    · simpa [hi] using hzBounds i
  by_cases hab : a ≤ b
  · exact transverseCost_mul_sq_slabCornerLowerBound_le_normalizedConnectionS
      d hd p hzBox haCast.symm hbCast.symm hab hbn hδ hcorner
  · have hba : b ≤ a := le_of_not_ge hab
    let z' := cubicFirstTwoSwapIso d hd z
    have hz'Box : z' ∈ slabCornerBoxVertices d n L :=
      (cubicFirstTwoSwapIso_mem_slabCornerBoxVertices_iff d hd n L z).2 hzBox
    have hbound :=
      transverseCost_mul_sq_slabCornerLowerBound_le_normalizedConnectionS
        d hd p hz'Box (by simpa [z'] using hbCast.symm)
          (by simpa [z'] using haCast.symm) hba han hδ hcorner
    rw [finiteThickSlabSConnectionEvent_probability_swap d hd p n L z]
    exact hbound

/-- Equation (7.84): the uniform origin-connection lower bound in `S_n(L)`, derived from a
uniform all-corners lower bound.  Reflections discharge every sign case omitted in the source. -/
theorem transverseCost_mul_sq_slabCornerLowerBound_le_connectionS_origin
    (d : ℕ) (hd : 2 ≤ d) (p : I) {z : Cubic d} {n L : ℕ}
    (hzS : z ∈ finiteThickSlabSVertices d n L)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    (p : ℝ) ^ ((d - 2) * L) * δ ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z) := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, hd⟩
  by_cases hz0 : 0 ≤ z i0
  · by_cases hz1 : 0 ≤ z i1
    · exact transverseCost_mul_sq_slabCornerLowerBound_le_nonnegativeConnectionS
        d hd p hzS hz0 hz1 hδ hcorner
    · let z' := cubicCoordinateReflectionIso i1 z
      have hz'S : z' ∈ finiteThickSlabSVertices d n L :=
        (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
          d n L i1 (by simp [i1]) z).2 hzS
      have hz'0 : 0 ≤ z' i0 := by
        simpa [z', i0, i1, cubicCoordinateReflectionIso,
          cubicCoordinateReflectionEquiv] using hz0
      have hz'1 : 0 ≤ z' i1 := by
        simp [z', cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv]
        omega
      have hbound :=
        transverseCost_mul_sq_slabCornerLowerBound_le_nonnegativeConnectionS
          d hd p hz'S hz'0 hz'1 hδ hcorner
      rw [finiteThickSlabSConnectionEvent_probability_reflection
        d p n L i1 (by simp [i1]) z]
      exact hbound
  · by_cases hz1 : 0 ≤ z i1
    · let z' := cubicCoordinateReflectionIso i0 z
      have hz'S : z' ∈ finiteThickSlabSVertices d n L :=
        (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
          d n L i0 (by simp [i0]) z).2 hzS
      have hz'0 : 0 ≤ z' i0 := by
        simp [z', cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv]
        omega
      have hz'1 : 0 ≤ z' i1 := by
        simpa [z', i0, i1, cubicCoordinateReflectionIso,
          cubicCoordinateReflectionEquiv] using hz1
      have hbound :=
        transverseCost_mul_sq_slabCornerLowerBound_le_nonnegativeConnectionS
          d hd p hz'S hz'0 hz'1 hδ hcorner
      rw [finiteThickSlabSConnectionEvent_probability_reflection
        d p n L i0 (by simp [i0]) z]
      exact hbound
    · let z0 := cubicCoordinateReflectionIso i0 z
      let z' := cubicCoordinateReflectionIso i1 z0
      have hz0S : z0 ∈ finiteThickSlabSVertices d n L :=
        (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
          d n L i0 (by simp [i0]) z).2 hzS
      have hz'S : z' ∈ finiteThickSlabSVertices d n L :=
        (cubicCoordinateReflectionIso_mem_finiteThickSlabS_iff
          d n L i1 (by simp [i1]) z0).2 hz0S
      have hz'0 : 0 ≤ z' i0 := by
        have hneg : 0 ≤ -z i0 := neg_nonneg.mpr (le_of_not_ge hz0)
        simpa [z', z0, i0, i1, cubicCoordinateReflectionIso,
          cubicCoordinateReflectionEquiv] using hneg
      have hz'1 : 0 ≤ z' i1 := by
        have hneg : 0 ≤ -z i1 := neg_nonneg.mpr (le_of_not_ge hz1)
        simpa [z', z0, i0, i1, cubicCoordinateReflectionIso,
          cubicCoordinateReflectionEquiv] using hneg
      have hbound :=
        transverseCost_mul_sq_slabCornerLowerBound_le_nonnegativeConnectionS
          d hd p hz'S hz'0 hz'1 hδ hcorner
      rw [finiteThickSlabSConnectionEvent_probability_reflection
        d p n L i0 (by simp [i0]) z]
      rw [finiteThickSlabSConnectionEvent_probability_reflection
        d p n L i1 (by simp [i1]) z0]
      exact hbound

/-- FKG converts a uniform origin-connection bound into a uniform pair-connection bound in the
same finite region, the final step from (7.84) to (7.79). -/
theorem sq_rootConnectionLowerBound_le_finiteThickSlabSConnection
    (d : ℕ) (p : I) {n L : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L)
    (hy : y ∈ finiteThickSlabSVertices d n L)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hroot : ∀ z ∈ finiteThickSlabSVertices d n L,
      ε ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L cubicOrigin z)) :
    ε ^ 2 ≤ (bernoulliBondMeasure d p).real
      (finiteThickSlabSConnectionEvent d n L x y) := by
  let A := finiteThickSlabSConnectionEvent d n L cubicOrigin x
  let B := finiteThickSlabSConnectionEvent d n L cubicOrigin y
  have hsub : A ∩ B ⊆ finiteThickSlabSConnectionEvent d n L x y := by
    rintro ω ⟨⟨q, hqOpen, hqS⟩, ⟨r, hrOpen, hrS⟩⟩
    refine ⟨q.reverse.append r,
      walkIsOpen_append (walkIsOpen_reverse hqOpen) hrOpen, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzq | hzr
    · exact hqS z (by simpa using hzq)
    · exact hrS z hzr
  calc
    ε ^ 2 = ε * ε := by ring
    _ ≤ (bernoulliBondMeasure d p).real A *
        (bernoulliBondMeasure d p).real B :=
      mul_le_mul (hroot x hx) (hroot y hy) hε measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) :=
      bernoulliBondMeasure_real_fkg p
        (isIncreasingEvent_finiteThickSlabSConnectionEvent d n L cubicOrigin x)
        (isIncreasingEvent_finiteThickSlabSConnectionEvent d n L cubicOrigin y)
        (measurableSet_finiteThickSlabSConnectionEvent d n L cubicOrigin x)
        (measurableSet_finiteThickSlabSConnectionEvent d n L cubicOrigin y)
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y) :=
      measureReal_mono hsub (measure_ne_top _ _)

/-- Equation (7.79), quantitatively derived from a uniform (7.83) corner-box bound. -/
theorem slabCornerLowerBound_four_mul_transverse_le_connectionS
    (d : ℕ) (hd : 2 ≤ d) (p : I) {n L : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L)
    (hy : y ∈ finiteThickSlabSVertices d n L)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcorner : ∀ m, δ ≤ (bernoulliBondMeasure d p).real
      (allSlabCornersConnectedEvent d m L)) :
    ((p : ℝ) ^ ((d - 2) * L) * δ ^ 2) ^ 2 ≤
      (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y) := by
  apply sq_rootConnectionLowerBound_le_finiteThickSlabSConnection
    d p hx hy (mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg hδ _))
  intro z hz
  exact transverseCost_mul_sq_slabCornerLowerBound_le_connectionS_origin
    d hd p hz hδ hcorner

/-- Explicit uniform constant in (7.79), obtained from the (7.83) corner constant. -/
noncomputable def finiteThickSlabSConnectionLowerBound
    (d L : ℕ) (p₁ p₂ : I) : ℝ :=
  ((p₂ : ℝ) ^ ((d - 2) * L) *
    (slabCornerAllConnectionLowerBound d L p₁ p₂) ^ 2) ^ 2

theorem finiteThickSlabSConnectionLowerBound_pos
    (d L : ℕ) {p₁ p₂ : I}
    (hcrit : regionCriticalProbability d (cubicQuarterSlab d L) < (p₁ : ℝ))
    (h12 : (p₁ : ℝ) < p₂) :
    0 < finiteThickSlabSConnectionLowerBound d L p₁ p₂ := by
  have hp₂ : 0 < (p₂ : ℝ) := lt_of_le_of_lt p₁.2.1 h12
  have hcorner := slabCornerAllConnectionLowerBound_pos d L hcrit h12
  exact pow_pos (mul_pos (pow_pos hp₂ _) (pow_pos hcorner _)) _

/-- Exact (7.79) package under the source's intermediate choice (7.81). -/
theorem finiteThickSlabSConnectionLowerBound_le
    (d : ℕ) (hd : 2 ≤ d) (L : ℕ) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) {n : ℕ} {x y : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L)
    (hy : y ∈ finiteThickSlabSVertices d n L) :
    finiteThickSlabSConnectionLowerBound d L p₁ p₂ ≤
      (bernoulliBondMeasure d p₂).real
        (finiteThickSlabSConnectionEvent d n L x y) := by
  have hcornerNonneg : 0 ≤ slabCornerAllConnectionLowerBound d L p₁ p₂ := by
    exact mul_nonneg (pow_nonneg (div_nonneg (sub_nonneg.mpr h12.le)
      (sub_nonneg.mpr p₁.2.2)) _) (pow_nonneg (div_nonneg measureReal_nonneg (by norm_num)) _)
  simpa [finiteThickSlabSConnectionLowerBound] using
    slabCornerLowerBound_four_mul_transverse_le_connectionS
      d hd p₂ hx hy hcornerNonneg
        (fun m ↦ slabCornerAllConnectionLowerBound_le d hd L h12 m)

end Percolation
