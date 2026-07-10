import Percolation.Core.Cubic
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Periodic cubic lattices

This file constructs the finite periodic graph used in Grimmett §5.3 and Appendix I.  Its side
length is `2 * N`; the hypothesis `2 ≤ N` ensures that the positive and negative neighbours in
each coordinate are distinct.
-/

namespace Percolation

open scoped BigOperators

/-- The vertex set of the side-`2N` periodic cubic lattice. -/
abbrev CubicTorus (d N : ℕ) := Fin d → ZMod (2 * N)

/-- The quotient map from the cubic lattice to the side-`2N` periodic lattice. -/
def cubicToTorus {d : ℕ} (N : ℕ) (x : Cubic d) : CubicTorus d N :=
  fun i ↦ (x i : ZMod (2 * N))

@[simp]
theorem cubicToTorus_origin (d N : ℕ) :
    cubicToTorus N (cubicOrigin : Cubic d) = 0 := by
  ext i
  simp [cubicToTorus, cubicOrigin]

/-- A signed nearest-neighbour step on the periodic cubic lattice. -/
def cubicTorusStepFrom {d N : ℕ} (x : CubicTorus d N) (a : CubicDirection d) :
    CubicTorus d N :=
  Function.update x a.1 (x a.1 + if a.2 then 1 else -1)

@[simp]
theorem cubicTorusStepFrom_apply_same {d N : ℕ} (x : CubicTorus d N)
    (i : Fin d) (b : Bool) :
    cubicTorusStepFrom x (i, b) i = x i + if b then 1 else -1 := by
  simp [cubicTorusStepFrom]

@[simp]
theorem cubicTorusStepFrom_apply_of_ne {d N : ℕ} (x : CubicTorus d N)
    {i j : Fin d} (hij : j ≠ i) (b : Bool) :
    cubicTorusStepFrom x (i, b) j = x j := by
  simp [cubicTorusStepFrom, Function.update_of_ne hij]

theorem cubicToTorus_stepFrom {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicToTorus N (cubicStepFrom x a) =
      cubicTorusStepFrom (cubicToTorus N x) a := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubicToTorus, cubicStepFrom, cubicTorusStepFrom,
      cubicDirectionIncrement]
  · simp [cubicToTorus, cubicStepFrom, cubicTorusStepFrom,
      Function.update_of_ne hji]

/-- One orientation of periodic nearest-neighbour adjacency. -/
def cubicTorusStep (d N : ℕ) (x y : CubicTorus d N) : Prop :=
  ∃ i : Fin d, y = cubicTorusStepFrom x (i, true)

/-- The simple periodic nearest-neighbour graph. -/
def cubicTorusGraph (d N : ℕ) : SimpleGraph (CubicTorus d N) :=
  SimpleGraph.fromRel (cubicTorusStep d N)

theorem cubicTorusStepFrom_ne_self {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) (a : CubicDirection d) :
    cubicTorusStepFrom x a ≠ x := by
  intro h
  letI : NeZero (2 * N) := ⟨by omega⟩
  letI : Fact (1 < 2 * N) := ⟨by omega⟩
  have hi := congrFun h a.1
  rcases a with ⟨i, b⟩
  simp only [cubicTorusStepFrom_apply_same] at hi
  by_cases hb : b
  · simp only [hb, if_true] at hi
    have hone : (1 : ZMod (2 * N)) ≠ 0 := one_ne_zero
    apply hone
    exact add_left_cancel (hi.trans (add_zero (x i)).symm)
  · simp only [Bool.eq_false_of_not_eq_true hb] at hi
    have hone : (1 : ZMod (2 * N)) ≠ 0 := one_ne_zero
    apply hone
    have hneg : (-1 : ZMod (2 * N)) = 0 :=
      add_left_cancel (hi.trans (add_zero (x i)).symm)
    exact neg_eq_zero.mp hneg

theorem cubicTorusGraph_adj_stepFrom {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) (a : CubicDirection d) :
    (cubicTorusGraph d N).Adj x (cubicTorusStepFrom x a) := by
  rcases a with ⟨i, b⟩
  rw [cubicTorusGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact cubicTorusStepFrom_ne_self hN x (i, b) |>.symm
  · by_cases hb : b
    · subst b
      exact Or.inl ⟨i, rfl⟩
    · rw [Bool.eq_false_of_not_eq_true hb]
      apply Or.inr
      refine ⟨i, ?_⟩
      ext j
      by_cases hji : j = i
      · subst j
        simp [cubicTorusStepFrom]
      · simp [cubicTorusStepFrom, Function.update_of_ne hji]

theorem cubicTorusGraph_adj_iff_exists_stepFrom {d N : ℕ} (hN : 2 ≤ N)
    (x y : CubicTorus d N) :
    (cubicTorusGraph d N).Adj x y ↔
      ∃ a : CubicDirection d, y = cubicTorusStepFrom x a := by
  constructor
  · intro h
    rw [cubicTorusGraph, SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, ⟨i, hi⟩ | ⟨i, hi⟩⟩
    · exact ⟨(i, true), hi⟩
    · refine ⟨(i, false), ?_⟩
      ext j
      by_cases hji : j = i
      · subst j
        have hj := congrFun hi i
        simp [cubicTorusStepFrom] at hj ⊢
        rw [hj]
        simp [add_assoc]
      · have hj := congrFun hi j
        simp [cubicTorusStepFrom, Function.update_of_ne hji] at hj
        rw [cubicTorusStepFrom_apply_of_ne x hji false]
        exact hj.symm
  · rintro ⟨a, rfl⟩
    exact cubicTorusGraph_adj_stepFrom hN x a

/-- The quotient map is a graph homomorphism. -/
def cubicToTorusHom {d N : ℕ} (hN : 2 ≤ N) :
    cubicGraph d →g cubicTorusGraph d N where
  toFun := cubicToTorus N
  map_rel' := by
    intro x y hxy
    obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy
    subst y
    rw [cubicToTorus_stepFrom]
    exact cubicTorusGraph_adj_stepFrom hN _ _

/-- No two lattice vertices in an `ℓ1` ball of radius `< N` are identified by the
side-`2N` quotient.  This is the local injectivity used in Appendix I. -/
theorem cubicToTorus_injOn_metricBall {d N r : ℕ} (hrN : r < N) :
    Set.InjOn (cubicToTorus N)
      {x : Cubic d | cubicL1Dist cubicOrigin x ≤ r} := by
  intro x hx y hy hxy
  change cubicL1Dist cubicOrigin x ≤ r at hx
  change cubicL1Dist cubicOrigin y ≤ r at hy
  funext i
  have hcast : (x i : ZMod (2 * N)) = (y i : ZMod (2 * N)) :=
    congrFun hxy i
  have hdiv : ((2 * N : ℕ) : ℤ) ∣ y i - x i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (y i) (2 * N)).mp hcast
  have hcoord : (y i - x i).natAbs ≤ cubicL1Dist x y :=
    cubicL1Dist_coord_le x y i
  have htriangle : cubicL1Dist x y ≤
      cubicL1Dist cubicOrigin x + cubicL1Dist cubicOrigin y := by
    have h := cubicL1Dist_triangle x cubicOrigin y
    simpa [cubicL1Dist_comm] using h
  have hlt : (y i - x i).natAbs < 2 * N := by
    omega
  have hzero : y i - x i = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
    simpa using hlt
  omega

/-! ### Lifting finite torus walks to the cubic lattice -/

def cubicTorusVerticesFrom {d N : ℕ} (x : CubicTorus d N) :
    List (CubicDirection d) → List (CubicTorus d N)
  | [] => [x]
  | a :: steps => x :: cubicTorusVerticesFrom (cubicTorusStepFrom x a) steps

def cubicTorusEndpointFrom {d N : ℕ} (x : CubicTorus d N) :
    List (CubicDirection d) → CubicTorus d N
  | [] => x
  | a :: steps => cubicTorusEndpointFrom (cubicTorusStepFrom x a) steps

theorem cubicToTorus_cubicVerticesFrom {d N : ℕ} (x : Cubic d)
    (steps : List (CubicDirection d)) :
    (cubicVerticesFrom x steps).map (cubicToTorus N) =
      cubicTorusVerticesFrom (cubicToTorus N x) steps := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
      simp only [cubicVerticesFrom, cubicTorusVerticesFrom, List.map_cons,
        List.cons.injEq, true_and]
      rw [ih, cubicToTorus_stepFrom]

theorem cubicToTorus_cubicEndpointFrom {d N : ℕ} (x : Cubic d)
    (steps : List (CubicDirection d)) :
    cubicToTorus N (cubicEndpointFrom x steps) =
      cubicTorusEndpointFrom (cubicToTorus N x) steps := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
      simp only [cubicEndpointFrom, cubicTorusEndpointFrom]
      rw [ih, cubicToTorus_stepFrom]

noncomputable def cubicTorusDartDirection {d N : ℕ} (hN : 2 ≤ N)
    (a : (cubicTorusGraph d N).Dart) : CubicDirection d :=
  Classical.choose ((cubicTorusGraph_adj_iff_exists_stepFrom hN a.fst a.snd).mp a.adj)

theorem cubicTorusDartDirection_spec {d N : ℕ} (hN : 2 ≤ N)
    (a : (cubicTorusGraph d N).Dart) :
    a.snd = cubicTorusStepFrom a.fst (cubicTorusDartDirection hN a) :=
  Classical.choose_spec ((cubicTorusGraph_adj_iff_exists_stepFrom hN a.fst a.snd).mp a.adj)

noncomputable def cubicTorusWalkDirections {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v) :
    List (CubicDirection d) :=
  w.darts.map (cubicTorusDartDirection hN)

@[simp]
theorem cubicTorusWalkDirections_length {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v) :
    (cubicTorusWalkDirections hN w).length = w.length := by
  simp [cubicTorusWalkDirections]

theorem cubicTorusVerticesFrom_walkDirections {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v) :
    cubicTorusVerticesFrom u (cubicTorusWalkDirections hN w) = w.support := by
  induction w with
  | nil => rfl
  | @cons u y v huy p ih =>
      change u :: cubicTorusVerticesFrom
          (cubicTorusStepFrom u (cubicTorusDartDirection hN ⟨(u, y), huy⟩))
          (cubicTorusWalkDirections hN p) = u :: p.support
      rw [← cubicTorusDartDirection_spec hN ⟨(u, y), huy⟩, ih]

theorem cubicTorusEndpointFrom_walkDirections {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v) :
    cubicTorusEndpointFrom u (cubicTorusWalkDirections hN w) = v := by
  induction w with
  | nil => rfl
  | @cons u y v huy p ih =>
      change cubicTorusEndpointFrom
          (cubicTorusStepFrom u (cubicTorusDartDirection hN ⟨(u, y), huy⟩))
          (cubicTorusWalkDirections hN p) = v
      rw [← cubicTorusDartDirection_spec hN ⟨(u, y), huy⟩, ih]

/-- Lift a torus walk after choosing a lattice lift of its first vertex. -/
noncomputable def cubicLiftOfTorusWalk {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v)
    (x : Cubic d) :
    (cubicGraph d).Walk x
      (cubicEndpointFrom x (cubicTorusWalkDirections hN w)) :=
  cubicWalkFrom x (cubicTorusWalkDirections hN w)

theorem cubicLiftOfTorusWalk_endpoint_projection {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v)
    (x : Cubic d) (hx : cubicToTorus N x = u) :
    cubicToTorus N (cubicEndpointFrom x (cubicTorusWalkDirections hN w)) = v := by
  rw [cubicToTorus_cubicEndpointFrom, hx,
    cubicTorusEndpointFrom_walkDirections hN w]

theorem cubicLiftOfTorusWalk_support_projection {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} (w : (cubicTorusGraph d N).Walk u v)
    (x : Cubic d) (hx : cubicToTorus N x = u) :
    (cubicLiftOfTorusWalk hN w x).support.map (cubicToTorus N) = w.support := by
  rw [cubicLiftOfTorusWalk, cubicWalkFrom_support,
    cubicToTorus_cubicVerticesFrom, hx,
    cubicTorusVerticesFrom_walkDirections hN w]

theorem cubicLiftOfTorusWalk_isPath {d N : ℕ} (hN : 2 ≤ N)
    {u v : CubicTorus d N} {w : (cubicTorusGraph d N).Walk u v}
    (hw : w.IsPath) (x : Cubic d) (hx : cubicToTorus N x = u) :
    (cubicLiftOfTorusWalk hN w x).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  apply List.Nodup.of_map (cubicToTorus N)
  rw [cubicLiftOfTorusWalk_support_projection hN w x hx]
  exact hw.support_nodup

/-- For side length at least four, the `2d` signed directions give distinct neighbours. -/
theorem cubicTorusStepFrom_injective_direction {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) : Function.Injective (cubicTorusStepFrom x) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  letI : Fact (1 < 2 * N) := ⟨by omega⟩
  have hinc (b : Bool) :
      (if b then 1 else -1 : ZMod (2 * N)) ≠ 0 := by
    cases b <;> simp
  have htwo : (2 : ZMod (2 * N)) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hv2 : (2 : ZMod (2 * N)).val = 2 :=
      ZMod.val_natCast_of_lt (n := 2 * N) (a := 2) (by omega)
    rw [hv2] at hv
    simp at hv
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  by_cases hij : i = j
  · subst j
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exfalso
        have hi := congrFun h i
        simp only [cubicTorusStepFrom_apply_same, if_true] at hi
        have hnegone : (-1 : ZMod (2 * N)) = 1 := add_left_cancel hi
        apply htwo
        calc
          (2 : ZMod (2 * N)) = 1 + 1 := by norm_num
          _ = 1 + (-1) := congrArg (fun t : ZMod (2 * N) ↦ 1 + t) hnegone.symm
          _ = 0 := by simp
      · exfalso
        have hi := congrFun h i
        simp only [cubicTorusStepFrom_apply_same, if_true] at hi
        have honeNeg : (1 : ZMod (2 * N)) = -1 := add_left_cancel hi
        apply htwo
        calc
          (2 : ZMod (2 * N)) = 1 + 1 := by norm_num
          _ = 1 + (-1) := congrArg (fun t : ZMod (2 * N) ↦ 1 + t) honeNeg
          _ = 0 := by simp
      · rfl
    exact congrArg (fun c : Bool ↦ (i, c)) hbc
  · have hfalse : False := by
      have hi := congrFun h i
      rw [cubicTorusStepFrom_apply_same,
        cubicTorusStepFrom_apply_of_ne x hij c] at hi
      apply hinc b
      exact add_left_cancel (hi.trans (add_zero (x i)).symm)
    exact hfalse.elim

theorem cubicTorus_card (d N : ℕ) (hN : 2 ≤ N) :
    Nat.card (CubicTorus d N) = (2 * N) ^ d := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card]
  simp [CubicTorus]

/-- Signed directions are equivalent to neighbours of a periodic vertex. -/
noncomputable def cubicTorusDirectionEquivNeighbor {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) :
    CubicDirection d ≃ (cubicTorusGraph d N).neighborSet x :=
  Equiv.ofBijective
    (fun a ↦ ⟨cubicTorusStepFrom x a, cubicTorusGraph_adj_stepFrom hN x a⟩)
    ⟨fun a b h ↦ cubicTorusStepFrom_injective_direction hN x (congrArg Subtype.val h),
      fun y ↦ by
        obtain ⟨a, ha⟩ := (cubicTorusGraph_adj_iff_exists_stepFrom hN x y.1).mp y.2
        exact ⟨a, Subtype.ext ha.symm⟩⟩

/-- Every periodic vertex has exactly `2d` neighbours when `2 ≤ N`. -/
theorem cubicTorus_degree {d N : ℕ} (hN : 2 ≤ N) (x : CubicTorus d N) :
    Nat.card ((cubicTorusGraph d N).neighborSet x) = 2 * d := by
  rw [Nat.card_congr (cubicTorusDirectionEquivNeighbor hN x).symm]
  simp [CubicDirection]
  omega

/-- Translation by a periodic vector. -/
def cubicTorusTranslate {d N : ℕ} (z x : CubicTorus d N) : CubicTorus d N :=
  fun i ↦ x i + z i

@[simp]
theorem cubicTorusTranslate_zero {d N : ℕ} (x : CubicTorus d N) :
    cubicTorusTranslate 0 x = x := by
  ext i
  simp [cubicTorusTranslate]

theorem cubicTorusTranslate_stepFrom {d N : ℕ} (z x : CubicTorus d N)
    (a : CubicDirection d) :
    cubicTorusTranslate z (cubicTorusStepFrom x a) =
      cubicTorusStepFrom (cubicTorusTranslate z x) a := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubicTorusTranslate, cubicTorusStepFrom, add_assoc, add_comm]
  · simp [cubicTorusTranslate, cubicTorusStepFrom, Function.update_of_ne hji]

theorem cubicTorusTranslate_injective {d N : ℕ} (z : CubicTorus d N) :
    Function.Injective (cubicTorusTranslate z) := by
  intro x y h
  ext i
  exact add_right_cancel (congrFun h i)

/-- Periodic translation as a graph automorphism. -/
noncomputable def cubicTorusTranslationIso {d N : ℕ} (hN : 2 ≤ N)
    (z : CubicTorus d N) : cubicTorusGraph d N ≃g cubicTorusGraph d N where
  toEquiv :=
    { toFun := cubicTorusTranslate z
      invFun := cubicTorusTranslate (-z)
      left_inv := by
        intro x
        ext i
        simp [cubicTorusTranslate]
      right_inv := by
        intro x
        ext i
        simp [cubicTorusTranslate] }
  map_rel_iff' := by
    intro x y
    rw [cubicTorusGraph_adj_iff_exists_stepFrom hN,
      cubicTorusGraph_adj_iff_exists_stepFrom hN]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, cubicTorusTranslate_injective z ?_⟩
      exact ha.trans (cubicTorusTranslate_stepFrom z x a).symm
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg (cubicTorusTranslate z) ha).trans
        (cubicTorusTranslate_stepFrom z x a)⟩

end Percolation
