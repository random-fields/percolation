import Percolation.Planar.TriangularHexDual
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Counting simple walks in the hexagonal dual

After its first edge, a non-backtracking walk in the degree-three hexagonal graph has two
choices.  Five successive choices in one fixed turning direction complete the remaining five
edges of an elementary hexagon.  Consequently that one continuation is unavailable to a simple
walk.  Grouping choices in blocks of five is the strict improvement from `32` to `31` used by
the triangular-lattice Peierls estimate.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The two direction labels other than `k`, cyclically ordered. -/
def triangularHexTurnDirection (k : Fin 3) (b : Bool) : Fin 3 :=
  if k = 0 then if b then 2 else 1
  else if k = 1 then if b then 0 else 2
  else if b then 1 else 0

@[simp]
theorem triangularHexTurnDirection_zero_false :
    triangularHexTurnDirection 0 false = 1 := rfl

@[simp]
theorem triangularHexTurnDirection_zero_true :
    triangularHexTurnDirection 0 true = 2 := rfl

@[simp]
theorem triangularHexTurnDirection_one_false :
    triangularHexTurnDirection 1 false = 2 := rfl

@[simp]
theorem triangularHexTurnDirection_one_true :
    triangularHexTurnDirection 1 true = 0 := rfl

@[simp]
theorem triangularHexTurnDirection_two_false :
    triangularHexTurnDirection 2 false = 0 := rfl

@[simp]
theorem triangularHexTurnDirection_two_true :
    triangularHexTurnDirection 2 true = 1 := rfl

theorem triangularHexTurnDirection_ne (k : Fin 3) (b : Bool) :
    triangularHexTurnDirection k b ≠ k := by
  fin_cases k <;> cases b <;> decide

theorem triangularHexTurnDirection_injective (k : Fin 3) :
    Function.Injective (triangularHexTurnDirection k) := by
  intro b c h
  fin_cases k <;> cases b <;> cases c <;> simp_all

theorem exists_triangularHexTurnDirection_of_ne
    {k l : Fin 3} (hkl : l ≠ k) :
    ∃ b : Bool, l = triangularHexTurnDirection k b := by
  fin_cases k <;> fin_cases l <;> simp_all

/-- Endpoint obtained by following a word of direction labels in the hexagonal graph. -/
def triangularHexAdvance :
    TriangularHexVertex → List (Fin 3) → TriangularHexVertex
  | x, [] => x
  | x, k :: ks => triangularHexAdvance (triangularHexNeighbor x k) ks

@[simp]
theorem triangularHexAdvance_nil (x : TriangularHexVertex) :
    triangularHexAdvance x [] = x := rfl

@[simp]
theorem triangularHexAdvance_cons
    (x : TriangularHexVertex) (k : Fin 3) (ks : List (Fin 3)) :
    triangularHexAdvance x (k :: ks) =
      triangularHexAdvance (triangularHexNeighbor x k) ks := rfl

/-- The canonical hexagonal walk following a word of direction labels. -/
def triangularHexWalkFrom (x : TriangularHexVertex) :
    (ks : List (Fin 3)) → triangularHexGraph.Walk x (triangularHexAdvance x ks)
  | [] => .nil
  | k :: ks => .cons (triangularHexGraph_adj_neighbor x k)
      (triangularHexWalkFrom (triangularHexNeighbor x k) ks)

@[simp]
theorem triangularHexWalkFrom_length
    (x : TriangularHexVertex) (ks : List (Fin 3)) :
    (triangularHexWalkFrom x ks).length = ks.length := by
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih => simp [triangularHexWalkFrom, ih]

@[simp]
theorem triangularHexWalkFrom_snd
    (x : TriangularHexVertex) (k : Fin 3) (ks : List (Fin 3)) :
    (triangularHexWalkFrom x (k :: ks)).snd = triangularHexNeighbor x k := by
  simp [triangularHexWalkFrom]

/-- The unique direction label of a directed hexagonal edge. -/
noncomputable def triangularHexStepDirection
    {x y : TriangularHexVertex} (hxy : triangularHexGraph.Adj x y) : Fin 3 :=
  Classical.choose ((triangularHexGraph_adj_iff x y).mp hxy)

theorem triangularHexStepDirection_spec
    {x y : TriangularHexVertex} (hxy : triangularHexGraph.Adj x y) :
    y = triangularHexNeighbor x (triangularHexStepDirection hxy) :=
  Classical.choose_spec ((triangularHexGraph_adj_iff x y).mp hxy)

/-- Direction word read from a hexagonal walk. -/
noncomputable def triangularHexWalkDirections :
    {x y : TriangularHexVertex} → triangularHexGraph.Walk x y → List (Fin 3)
  | _, _, .nil => []
  | _, _, .cons hxy w => triangularHexStepDirection hxy :: triangularHexWalkDirections w

@[simp]
theorem triangularHexWalkDirections_nil (x : TriangularHexVertex) :
    triangularHexWalkDirections
      (SimpleGraph.Walk.nil : triangularHexGraph.Walk x x) = [] := rfl

@[simp]
theorem triangularHexWalkDirections_cons
    {x y z : TriangularHexVertex} (hxy : triangularHexGraph.Adj x y)
    (w : triangularHexGraph.Walk y z) :
    triangularHexWalkDirections (.cons hxy w) =
      triangularHexStepDirection hxy :: triangularHexWalkDirections w := rfl

@[simp]
theorem triangularHexWalkDirections_length
    {x y : TriangularHexVertex} (w : triangularHexGraph.Walk x y) :
    (triangularHexWalkDirections w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [ih]

/-- The `i`th vertex is obtained by following the first `i` direction labels. -/
theorem triangularHexWalk_getVert_eq_advance_take
    {x y : TriangularHexVertex} (w : triangularHexGraph.Walk x y) (i : ℕ) :
    w.getVert i =
      triangularHexAdvance x ((triangularHexWalkDirections w).take i) := by
  induction w generalizing i with
  | nil => simp [triangularHexAdvance]
  | @cons x y z hxy w ih =>
      cases i with
      | zero => simp [triangularHexAdvance]
      | succ i =>
          simp only [SimpleGraph.Walk.getVert_cons_succ,
            triangularHexWalkDirections_cons, List.take_succ_cons,
            triangularHexAdvance_cons]
          rw [← triangularHexStepDirection_spec hxy]
          exact ih i

/-- Reading direction labels determines a rooted walk, including its endpoint. -/
theorem triangularHexWalkDirections_injective_from (x : TriangularHexVertex) :
    Function.Injective
      (fun q : Σ y, triangularHexGraph.Walk x y ↦
        triangularHexWalkDirections q.2) := by
  rintro ⟨y, w⟩ ⟨z, q⟩ hdirs
  change triangularHexWalkDirections w = triangularHexWalkDirections q at hdirs
  have hlen : w.length = q.length := by
    rw [← triangularHexWalkDirections_length w,
      ← triangularHexWalkDirections_length q, hdirs]
  have hyz : y = z := by
    rw [← w.getVert_length, ← q.getVert_length,
      triangularHexWalk_getVert_eq_advance_take,
      triangularHexWalk_getVert_eq_advance_take, hlen, hdirs]
  subst z
  have hwq : w = q := by
    apply SimpleGraph.Walk.ext_getVert_le_length hlen
    intro i hi
    rw [triangularHexWalk_getVert_eq_advance_take,
      triangularHexWalk_getVert_eq_advance_take, hdirs]
  subst q
  rfl

/-- Six edges obtained by repeatedly making the same turn close an elementary hexagon. -/
theorem triangularHexAdvance_six_same_turn
    (x : TriangularHexVertex) (k : Fin 3) (b : Bool) :
    let k₁ := triangularHexTurnDirection k b
    let k₂ := triangularHexTurnDirection k₁ b
    let k₃ := triangularHexTurnDirection k₂ b
    let k₄ := triangularHexTurnDirection k₃ b
    let k₅ := triangularHexTurnDirection k₄ b
    triangularHexAdvance x [k, k₁, k₂, k₃, k₄, k₅] = x := by
  rcases x with ⟨x, o⟩
  fin_cases k <;> cases b <;> cases o <;>
    apply Prod.ext
  all_goals
    first
    | · ext i
        fin_cases i <;>
          simp [triangularHexAdvance, triangularHexNeighbor,
            triangularHexTurnDirection, squareVertex]
    | · simp [triangularHexAdvance, triangularHexNeighbor,
          triangularHexTurnDirection]

/-! ### Direction and turn codes for rooted simple cycles -/

/-- Direction of the edge in position `i` of a nonempty walk. -/
noncomputable def triangularHexWalkDirectionAt
    {x y : TriangularHexVertex} (w : triangularHexGraph.Walk x y)
    (i : Fin w.length) : Fin 3 :=
  triangularHexStepDirection (w.adj_getVert_succ i.isLt)

theorem triangularHexWalkDirectionAt_spec
    {x y : TriangularHexVertex} (w : triangularHexGraph.Walk x y)
    (i : Fin w.length) :
    w.getVert (i + 1) =
      triangularHexNeighbor (w.getVert i) (triangularHexWalkDirectionAt w i) :=
  triangularHexStepDirection_spec (w.adj_getVert_succ i.isLt)

/-- Consecutive direction labels of a simple cycle differ: equality would immediately traverse
the preceding edge backwards. -/
theorem triangularHexWalkDirectionAt_ne_succ_of_isCycle
    {x : TriangularHexVertex} {w : triangularHexGraph.Walk x x}
    (hw : w.IsCycle) {i : ℕ} (hi : i + 1 < w.length) :
    triangularHexWalkDirectionAt w ⟨i, by omega⟩ ≠
      triangularHexWalkDirectionAt w ⟨i + 1, hi⟩ := by
  intro heq
  have hfirst := triangularHexWalkDirectionAt_spec w ⟨i, by omega⟩
  have hsecond := triangularHexWalkDirectionAt_spec w ⟨i + 1, hi⟩
  have hrepeat : w.getVert (i + 2) = w.getVert i := by
    calc
      w.getVert (i + 2) =
          triangularHexNeighbor (w.getVert (i + 1))
            (triangularHexWalkDirectionAt w ⟨i + 1, hi⟩) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond
      _ = triangularHexNeighbor
          (triangularHexNeighbor (w.getVert i)
            (triangularHexWalkDirectionAt w ⟨i, by omega⟩))
          (triangularHexWalkDirectionAt w ⟨i, by omega⟩) := by
            rw [← heq, hfirst]
      _ = w.getVert i := triangularHexNeighbor_involutive _ _
  exact hw.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
    (by simpa using hrepeat.symm)

/-- The Boolean choice taking one direction label to a specified different label. -/
noncomputable def triangularHexTurnBit (k l : Fin 3) : Bool := by
  classical
  exact if h : l ≠ k then Classical.choose (exists_triangularHexTurnDirection_of_ne h)
    else false

theorem triangularHexTurnBit_spec {k l : Fin 3} (hkl : l ≠ k) :
    l = triangularHexTurnDirection k (triangularHexTurnBit k l) := by
  rw [triangularHexTurnBit, dif_pos hkl]
  exact Classical.choose_spec (exists_triangularHexTurnDirection_of_ne hkl)

/-- A first direction and the subsequent left/right turn bits. -/
abbrev TriangularHexTurnCode (n : ℕ) :=
  Fin 3 × (Fin (n - 1) → Bool)

/-- Rooted simple hexagonal cycles of a prescribed length. -/
abbrev RootedTriangularHexCycle (x : TriangularHexVertex) (n : ℕ) :=
  {w : triangularHexGraph.Walk x x // w.IsCycle ∧ w.length = n}

/-- Turn code of a rooted simple cycle. -/
noncomputable def rootedTriangularHexCycleTurnCode
    {x : TriangularHexVertex} {n : ℕ} (c : RootedTriangularHexCycle x n) :
    TriangularHexTurnCode n := by
  have hn : 0 < n := by
    rw [← c.2.2]
    exact c.2.1.three_le_length.trans_lt' (by omega)
  refine ⟨triangularHexWalkDirectionAt c.1 ⟨0, by omega⟩, fun i ↦ ?_⟩
  have hi : (i : ℕ) + 1 < c.1.length := by
    rw [c.2.2]
    omega
  exact triangularHexTurnBit
    (triangularHexWalkDirectionAt c.1 ⟨i, by omega⟩)
    (triangularHexWalkDirectionAt c.1 ⟨i + 1, hi⟩)

private theorem rootedTriangularHexCycleTurnCode_direction_eq
    {x : TriangularHexVertex} {n : ℕ}
    {c d : RootedTriangularHexCycle x n}
    (hcode : rootedTriangularHexCycleTurnCode c =
      rootedTriangularHexCycleTurnCode d) :
    ∀ i : ℕ, (hi : i < n) →
      triangularHexWalkDirectionAt c.1 ⟨i, by simpa [c.2.2] using hi⟩ =
        triangularHexWalkDirectionAt d.1 ⟨i, by simpa [d.2.2] using hi⟩ := by
  intro i
  induction i with
  | zero =>
      intro hi
      exact congrArg Prod.fst hcode
  | succ i ih =>
      intro hi
      have hiPrev : i < n := by omega
      have hiTurn : i < n - 1 := by omega
      have hcNe := triangularHexWalkDirectionAt_ne_succ_of_isCycle c.2.1
        (i := i) (by rw [c.2.2]; omega)
      have hdNe := triangularHexWalkDirectionAt_ne_succ_of_isCycle d.2.1
        (i := i) (by rw [d.2.2]; omega)
      have hturn := congrFun (congrArg Prod.snd hcode) ⟨i, hiTurn⟩
      have hcSpec := triangularHexTurnBit_spec hcNe.symm
      have hdSpec := triangularHexTurnBit_spec hdNe.symm
      change triangularHexWalkDirectionAt c.1
          ⟨i + 1, by rw [c.2.2]; omega⟩ =
        triangularHexWalkDirectionAt d.1
          ⟨i + 1, by rw [d.2.2]; omega⟩
      calc
        triangularHexWalkDirectionAt c.1 ⟨i + 1, by rw [c.2.2]; omega⟩ =
            triangularHexTurnDirection
              (triangularHexWalkDirectionAt c.1 ⟨i, by rw [c.2.2]; omega⟩)
              ((rootedTriangularHexCycleTurnCode c).2 ⟨i, hiTurn⟩) := hcSpec
        _ = triangularHexTurnDirection
              (triangularHexWalkDirectionAt d.1 ⟨i, by rw [d.2.2]; omega⟩)
              ((rootedTriangularHexCycleTurnCode d).2 ⟨i, hiTurn⟩) := by
                rw [ih hiPrev, hturn]
        _ = triangularHexWalkDirectionAt d.1
              ⟨i + 1, by rw [d.2.2]; omega⟩ := hdSpec.symm

/-- The rooted turn code is injective. -/
theorem rootedTriangularHexCycleTurnCode_injective
    (x : TriangularHexVertex) (n : ℕ) :
    Function.Injective
      (rootedTriangularHexCycleTurnCode :
        RootedTriangularHexCycle x n → TriangularHexTurnCode n) := by
  intro c d hcode
  have hdir := rootedTriangularHexCycleTurnCode_direction_eq hcode
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length (by rw [c.2.2, d.2.2])
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
      have hin : i < n := by rw [c.2.2] at hi; omega
      rw [triangularHexWalkDirectionAt_spec c.1 ⟨i, by rw [c.2.2]; omega⟩,
        triangularHexWalkDirectionAt_spec d.1 ⟨i, by rw [d.2.2]; omega⟩,
        ih (by omega), hdir i hin]

private theorem rootedTriangularHexCycle_direction_succ_eq_turn
    {x : TriangularHexVertex} {n : ℕ}
    (c : RootedTriangularHexCycle x n) {i : ℕ} (hi : i + 1 < n) :
    triangularHexWalkDirectionAt c.1 ⟨i + 1, by rw [c.2.2]; omega⟩ =
      triangularHexTurnDirection
        (triangularHexWalkDirectionAt c.1 ⟨i, by rw [c.2.2]; omega⟩)
        ((rootedTriangularHexCycleTurnCode c).2 ⟨i, by omega⟩) := by
  have hne := triangularHexWalkDirectionAt_ne_succ_of_isCycle c.2.1
    (i := i) (by rw [c.2.2]; omega)
  exact triangularHexTurnBit_spec hne.symm

/-- No block of five turn bits which closes an elementary hexagon can occur strictly before the
closing endpoint of a simple cycle. -/
theorem rootedTriangularHexCycle_not_five_false_turns
    {x : TriangularHexVertex} {n : ℕ}
    (c : RootedTriangularHexCycle x n) {i : ℕ} (hi : i + 6 < n) :
    ¬ (∀ j : Fin 5,
      (rootedTriangularHexCycleTurnCode c).2
        ⟨i + j, by omega⟩ = false) := by
  intro hfalse
  let d₀ := triangularHexWalkDirectionAt c.1 ⟨i, by rw [c.2.2]; omega⟩
  let d₁ := triangularHexWalkDirectionAt c.1 ⟨i + 1, by rw [c.2.2]; omega⟩
  let d₂ := triangularHexWalkDirectionAt c.1 ⟨i + 2, by rw [c.2.2]; omega⟩
  let d₃ := triangularHexWalkDirectionAt c.1 ⟨i + 3, by rw [c.2.2]; omega⟩
  let d₄ := triangularHexWalkDirectionAt c.1 ⟨i + 4, by rw [c.2.2]; omega⟩
  let d₅ := triangularHexWalkDirectionAt c.1 ⟨i + 5, by rw [c.2.2]; omega⟩
  have hd₁ : d₁ = triangularHexTurnDirection d₀ false := by
    have hb := hfalse ⟨0, by omega⟩
    have ht := rootedTriangularHexCycle_direction_succ_eq_turn c (i := i) (by omega)
    simpa [d₀, d₁] using ht.trans (congrArg (triangularHexTurnDirection _ ) hb)
  have hd₂ : d₂ = triangularHexTurnDirection d₁ false := by
    have hb := hfalse ⟨1, by omega⟩
    have ht := rootedTriangularHexCycle_direction_succ_eq_turn c (i := i + 1) (by omega)
    simpa [d₁, d₂, Nat.add_assoc] using
      ht.trans (congrArg (triangularHexTurnDirection _ ) hb)
  have hd₃ : d₃ = triangularHexTurnDirection d₂ false := by
    have hb := hfalse ⟨2, by omega⟩
    have ht := rootedTriangularHexCycle_direction_succ_eq_turn c (i := i + 2) (by omega)
    simpa [d₂, d₃, Nat.add_assoc] using
      ht.trans (congrArg (triangularHexTurnDirection _ ) hb)
  have hd₄ : d₄ = triangularHexTurnDirection d₃ false := by
    have hb := hfalse ⟨3, by omega⟩
    have ht := rootedTriangularHexCycle_direction_succ_eq_turn c (i := i + 3) (by omega)
    simpa [d₃, d₄, Nat.add_assoc] using
      ht.trans (congrArg (triangularHexTurnDirection _ ) hb)
  have hd₅ : d₅ = triangularHexTurnDirection d₄ false := by
    have hb := hfalse ⟨4, by omega⟩
    have ht := rootedTriangularHexCycle_direction_succ_eq_turn c (i := i + 4) (by omega)
    simpa [d₄, d₅, Nat.add_assoc] using
      ht.trans (congrArg (triangularHexTurnDirection _ ) hb)
  have hs₀ := triangularHexWalkDirectionAt_spec c.1 ⟨i, by rw [c.2.2]; omega⟩
  have hs₁ := triangularHexWalkDirectionAt_spec c.1 ⟨i + 1, by rw [c.2.2]; omega⟩
  have hs₂ := triangularHexWalkDirectionAt_spec c.1 ⟨i + 2, by rw [c.2.2]; omega⟩
  have hs₃ := triangularHexWalkDirectionAt_spec c.1 ⟨i + 3, by rw [c.2.2]; omega⟩
  have hs₄ := triangularHexWalkDirectionAt_spec c.1 ⟨i + 4, by rw [c.2.2]; omega⟩
  have hs₅ := triangularHexWalkDirectionAt_spec c.1 ⟨i + 5, by rw [c.2.2]; omega⟩
  have hs₀' : c.1.getVert (i + 1) =
      triangularHexNeighbor (c.1.getVert i) d₀ := by simpa [d₀] using hs₀
  have hs₁' : c.1.getVert (i + 2) =
      triangularHexNeighbor (c.1.getVert (i + 1)) d₁ := by
    simpa [d₁, Nat.add_assoc] using hs₁
  have hs₂' : c.1.getVert (i + 3) =
      triangularHexNeighbor (c.1.getVert (i + 2)) d₂ := by
    simpa [d₂, Nat.add_assoc] using hs₂
  have hs₃' : c.1.getVert (i + 4) =
      triangularHexNeighbor (c.1.getVert (i + 3)) d₃ := by
    simpa [d₃, Nat.add_assoc] using hs₃
  have hs₄' : c.1.getVert (i + 5) =
      triangularHexNeighbor (c.1.getVert (i + 4)) d₄ := by
    simpa [d₄, Nat.add_assoc] using hs₄
  have hs₅' : c.1.getVert (i + 6) =
      triangularHexNeighbor (c.1.getVert (i + 5)) d₅ := by
    simpa [d₅, Nat.add_assoc] using hs₅
  have hrepeat : c.1.getVert (i + 6) = c.1.getVert i := by
    rw [hs₅', hs₄', hs₃', hs₂', hs₁', hs₀']
    change triangularHexNeighbor
        (triangularHexNeighbor
          (triangularHexNeighbor
            (triangularHexNeighbor
              (triangularHexNeighbor
                (triangularHexNeighbor (c.1.getVert i) d₀) d₁) d₂) d₃) d₄) d₅ =
      c.1.getVert i
    simp only [hd₁, hd₂, hd₃, hd₄, hd₅]
    simpa [triangularHexAdvance] using
      (triangularHexAdvance_six_same_turn (c.1.getVert i) d₀ false)
  have heqIndex := c.2.1.getVert_injOn'
    (by simp only [Set.mem_setOf_eq]; rw [c.2.2]; omega)
    (by simp only [Set.mem_setOf_eq]; rw [c.2.2]; omega)
    hrepeat.symm
  omega

/-! ### The 31-per-block bound -/

/-- A five-turn block other than the one which closes an elementary hexagon. -/
abbrev NonClosingTriangularHexTurnBlock :=
  {f : Fin 5 → Bool // f ≠ fun _ ↦ false}

noncomputable instance : Fintype NonClosingTriangularHexTurnBlock := by
  classical
  infer_instance

theorem card_nonClosingTriangularHexTurnBlock :
    Fintype.card NonClosingTriangularHexTurnBlock = 31 := by
  classical
  rw [Fintype.card_subtype_compl]
  norm_num

/-- Number of complete five-turn blocks which occur strictly before the possible final closing
block. -/
def triangularHexStrictBlockCount (n : ℕ) : ℕ :=
  (n - 1) / 5 - 1

/-- Number of turn bits left after the strict blocks. -/
def triangularHexTurnRemainder (n : ℕ) : ℕ :=
  (n - 1) - 5 * triangularHexStrictBlockCount n

theorem triangularHexTurnRemainder_le_nine {n : ℕ} (hn : 3 ≤ n) :
    triangularHexTurnRemainder n ≤ 9 := by
  unfold triangularHexTurnRemainder triangularHexStrictBlockCount
  omega

private theorem five_mul_triangularHexStrictBlockCount_le
    {n : ℕ} (hn : 3 ≤ n) :
    5 * triangularHexStrictBlockCount n ≤ n - 1 := by
  have hdiv := Nat.mul_div_le (n - 1) 5
  unfold triangularHexStrictBlockCount
  omega

private theorem five_mul_triangularHexStrictBlockCount_add_remainder
    {n : ℕ} (hn : 3 ≤ n) :
    5 * triangularHexStrictBlockCount n + triangularHexTurnRemainder n = n - 1 := by
  have hle := five_mul_triangularHexStrictBlockCount_le hn
  unfold triangularHexTurnRemainder
  omega

private theorem triangularHexStrictBlock_index_lt
    {n : ℕ} (hn : 3 ≤ n) (j : Fin (triangularHexStrictBlockCount n)) :
    5 * (j : ℕ) + 6 < n := by
  have hdiv := Nat.mul_div_le (n - 1) 5
  have hj := j.isLt
  unfold triangularHexStrictBlockCount at hj
  omega

/-- Finite code space after grouping strict turn blocks. -/
abbrev TriangularHexStrictBlockCode (n : ℕ) :=
  Fin 3 ×
    (Fin (triangularHexStrictBlockCount n) → NonClosingTriangularHexTurnBlock) ×
    (Fin (triangularHexTurnRemainder n) → Bool)

/-- Group the turn bits of a rooted simple cycle into strict five-turn blocks and a bounded
remainder. -/
noncomputable def rootedTriangularHexCycleStrictBlockCode
    {x : TriangularHexVertex} {n : ℕ} (c : RootedTriangularHexCycle x n) :
    TriangularHexStrictBlockCode n := by
  let m := triangularHexStrictBlockCount n
  let r := triangularHexTurnRemainder n
  have hn : 3 ≤ n := by simpa [c.2.2] using c.2.1.three_le_length
  let bits := (rootedTriangularHexCycleTurnCode c).2
  refine ⟨(rootedTriangularHexCycleTurnCode c).1,
    fun j ↦ ⟨fun t ↦ bits ⟨5 * (j : ℕ) + t, by
      have hj := triangularHexStrictBlock_index_lt hn j
      omega⟩, ?_⟩,
    fun t ↦ bits ⟨5 * m + t, by
      have hsum := five_mul_triangularHexStrictBlockCount_add_remainder hn
      have ht := t.isLt
      change 5 * m + r = n - 1 at hsum
      omega⟩⟩
  intro hblock
  exact (rootedTriangularHexCycle_not_five_false_turns c
    (i := 5 * (j : ℕ)) (triangularHexStrictBlock_index_lt hn j))
      (fun t ↦ congrFun hblock t)

private theorem rootedTriangularHexCycleStrictBlockCode_turns_eq
    {x : TriangularHexVertex} {n : ℕ}
    {c d : RootedTriangularHexCycle x n}
    (hcode : rootedTriangularHexCycleStrictBlockCode c =
      rootedTriangularHexCycleStrictBlockCode d) :
    (rootedTriangularHexCycleTurnCode c).2 =
      (rootedTriangularHexCycleTurnCode d).2 := by
  funext i
  let m := triangularHexStrictBlockCount n
  by_cases hi : (i : ℕ) < 5 * m
  · let j : Fin m := ⟨(i : ℕ) / 5, by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa [mul_comm] using hi⟩
    let t : Fin 5 := ⟨(i : ℕ) % 5, Nat.mod_lt _ (by omega)⟩
    have hij : 5 * (j : ℕ) + (t : ℕ) = (i : ℕ) := by
      dsimp [j, t]
      omega
    have hblocks := congrArg (fun code ↦ code.2.1 j) hcode
    have hfun := congrArg (fun block : NonClosingTriangularHexTurnBlock ↦ block.1 t) hblocks
    simpa [rootedTriangularHexCycleStrictBlockCode, m, j, t, hij] using hfun
  · have him : 5 * m ≤ (i : ℕ) := by omega
    have hn : 3 ≤ n := by
      simpa [c.2.2] using c.2.1.three_le_length
    have hsum := five_mul_triangularHexStrictBlockCount_add_remainder hn
    let t : Fin (triangularHexTurnRemainder n) :=
      ⟨(i : ℕ) - 5 * m, by
        change 5 * m + triangularHexTurnRemainder n = n - 1 at hsum
        omega⟩
    have hit : 5 * m + (t : ℕ) = (i : ℕ) := by
      dsimp [t]
      omega
    have htail := congrArg (fun code ↦ code.2.2 t) hcode
    simpa [rootedTriangularHexCycleStrictBlockCode, m, t, hit] using htail

theorem rootedTriangularHexCycleStrictBlockCode_injective
    (x : TriangularHexVertex) (n : ℕ) :
    Function.Injective
      (rootedTriangularHexCycleStrictBlockCode :
        RootedTriangularHexCycle x n → TriangularHexStrictBlockCode n) := by
  intro c d hcode
  apply rootedTriangularHexCycleTurnCode_injective x n
  apply Prod.ext
  · exact congrArg (fun code ↦ code.1) hcode
  · exact rootedTriangularHexCycleStrictBlockCode_turns_eq hcode

noncomputable instance rootedTriangularHexCycleFintype
    (x : TriangularHexVertex) (n : ℕ) :
    Fintype (RootedTriangularHexCycle x n) := by
  classical
  exact Fintype.ofInjective rootedTriangularHexCycleStrictBlockCode
    (rootedTriangularHexCycleStrictBlockCode_injective x n)

noncomputable def rootedTriangularHexCycleStrictBlockCodeEmbedding
    (x : TriangularHexVertex) (n : ℕ) :
    RootedTriangularHexCycle x n ↪ TriangularHexStrictBlockCode n :=
  ⟨rootedTriangularHexCycleStrictBlockCode,
    rootedTriangularHexCycleStrictBlockCode_injective x n⟩

/-- Rooted length-n simple cycles have the strict block-count bound. -/
theorem card_rootedTriangularHexCycle_le
    (x : TriangularHexVertex) (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (RootedTriangularHexCycle x n) ≤
      3 * 31 ^ triangularHexStrictBlockCount n * 512 := by
  calc
    Fintype.card (RootedTriangularHexCycle x n) ≤
        Fintype.card (TriangularHexStrictBlockCode n) :=
      Fintype.card_le_of_embedding
        (rootedTriangularHexCycleStrictBlockCodeEmbedding x n)
    _ = 3 * 31 ^ triangularHexStrictBlockCount n *
          2 ^ triangularHexTurnRemainder n := by
      simp [TriangularHexStrictBlockCode,
        card_nonClosingTriangularHexTurnBlock, Fintype.card_fun]
      ring
    _ ≤ 3 * 31 ^ triangularHexStrictBlockCount n * 512 := by
      gcongr
      simpa using Nat.pow_le_pow_right (by omega)
        (triangularHexTurnRemainder_le_nine hn)

/-! ### Positive-ray normalization and finite-family probability -/

/-- Upward-oriented triangular face incident to the horizontal primal ray edge at coordinate
k. -/
def triangularHexPositiveRayVertex (k : ℕ) : TriangularHexVertex :=
  (squareVertex (k : ℤ) 0, false)

/-- Rooted cycles with a positive-ray coordinate bounded by their length. This deliberately
overcounts normalized contours: no first-edge condition is imposed. -/
abbrev PositiveRayRootedTriangularHexCycle (n : ℕ) :=
  Σ k : Fin n, RootedTriangularHexCycle (triangularHexPositiveRayVertex k) n

noncomputable instance positiveRayRootedTriangularHexCycleFintype (n : ℕ) :
    Fintype (PositiveRayRootedTriangularHexCycle n) := by
  classical
  infer_instance

theorem card_positiveRayRootedTriangularHexCycle_le
    (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (PositiveRayRootedTriangularHexCycle n) ≤
      n * (3 * 31 ^ triangularHexStrictBlockCount n * 512) := by
  rw [Fintype.card_sigma]
  calc
    ∑ k : Fin n,
        Fintype.card (RootedTriangularHexCycle
          (triangularHexPositiveRayVertex k) n) ≤
      ∑ _k : Fin n, (3 * 31 ^ triangularHexStrictBlockCount n * 512) :=
        Finset.sum_le_sum fun k _ ↦
          card_rootedTriangularHexCycle_le (triangularHexPositiveRayVertex k) n hn
    _ = n * (3 * 31 ^ triangularHexStrictBlockCount n * 512) := by
      simp

/-- Event that one of the overcounted positive-ray-rooted length-n cycles crosses only closed
primal bonds. -/
def positiveRayTriangularHexClosedCycleEvent
    (n : ℕ) : Set TriangularConfiguration :=
  {ω | ∃ c : PositiveRayRootedTriangularHexCycle n,
    ω ∈ triangularHexWalkClosedEvent c.2.1}

theorem measurableSet_positiveRayTriangularHexClosedCycleEvent (n : ℕ) :
    MeasurableSet (positiveRayTriangularHexClosedCycleEvent n) := by
  classical
  rw [show positiveRayTriangularHexClosedCycleEvent n =
      ⋃ c : PositiveRayRootedTriangularHexCycle n,
        triangularHexWalkClosedEvent c.2.1 by
    ext ω
    simp [positiveRayTriangularHexClosedCycleEvent]]
  exact MeasurableSet.iUnion fun c ↦
    measurableSet_triangularHexWalkClosedEvent c.2.1

/-- Finite union bound for normalized closed dual cycles. -/
theorem inhomogeneousTriangularBondMeasure_real_positiveRayClosedCycleEvent_le
    (p : I) (n : ℕ) (hn : 3 ≤ n) :
    (inhomogeneousTriangularBondMeasure p p p).real
        (positiveRayTriangularHexClosedCycleEvent n) ≤
      (n * (3 * 31 ^ triangularHexStrictBlockCount n * 512) : ℕ) *
        (1 - (p : ℝ)) ^ n := by
  classical
  calc
    (inhomogeneousTriangularBondMeasure p p p).real
        (positiveRayTriangularHexClosedCycleEvent n) =
      (inhomogeneousTriangularBondMeasure p p p).real
        (⋃ c : PositiveRayRootedTriangularHexCycle n,
          triangularHexWalkClosedEvent c.2.1) := by
            congr 1
            ext ω
            simp [positiveRayTriangularHexClosedCycleEvent]
    _ ≤ ∑ c : PositiveRayRootedTriangularHexCycle n,
        (inhomogeneousTriangularBondMeasure p p p).real
          (triangularHexWalkClosedEvent c.2.1) :=
      measureReal_iUnion_fintype_le _
    _ = Fintype.card (PositiveRayRootedTriangularHexCycle n) *
        (1 - (p : ℝ)) ^ n := by
      rw [Finset.sum_congr rfl (fun c _ ↦ by
        rw [inhomogeneousTriangularBondMeasure_real_triangularHexWalkClosedEvent
          p c.2.1 c.2.2.1.isTrail, c.2.2.2])]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (n * (3 * 31 ^ triangularHexStrictBlockCount n * 512) : ℕ) *
        (1 - (p : ℝ)) ^ n := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_positiveRayRootedTriangularHexCycle_le n hn)
        (pow_nonneg (by exact sub_nonneg.mpr p.2.2) n)

end Percolation
