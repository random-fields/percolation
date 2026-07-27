import Percolation.Extensions.LongRangeCuts
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.ChainOfFn

/-!
# The mean-degree criterion for long-range percolation

This file formalizes Grimmett's branching comparison (12.2).  At the critical equality the
usual first-moment estimate `mu^n` does not decay.  We retain the elementary observation hidden
in the branching argument: a self-avoiding path cannot immediately reverse either edge in any
disjoint consecutive pair.  If one density is positive, deleting that one reversing pair makes
the total two-step weight strictly smaller than one.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

/-- A nonzero signed displacement, encoded by its positive length minus one and its sign. -/
abbrev LongRangeSignedStep := ℕ × Bool

/-- The integer displacement represented by a signed step. -/
def longRangeStepDisplacement (s : LongRangeSignedStep) : ℤ :=
  if s.2 then (s.1 + 1 : ℕ) else -((s.1 + 1 : ℕ) : ℤ)

theorem longRangeStepDisplacement_ne_zero (s : LongRangeSignedStep) :
    longRangeStepDisplacement s ≠ 0 := by
  rcases s with ⟨n, b⟩
  cases b <;> simp only [longRangeStepDisplacement, Bool.false_eq_true, ↓reduceIte,
    Bool.true_eq, Nat.cast_add, Nat.cast_one, neg_eq_zero] <;> omega

@[simp]
theorem longRangeStepDisplacement_natAbs (s : LongRangeSignedStep) :
    (longRangeStepDisplacement s).natAbs = s.1 + 1 := by
  rcases s with ⟨n, b⟩
  cases b
  · simp only [longRangeStepDisplacement, Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg]
    convert Int.natAbs_natCast (n + 1) using 1 <;> norm_num
  · simp only [longRangeStepDisplacement, Bool.true_eq, ↓reduceIte]
    convert Int.natAbs_natCast (n + 1) using 1 <;> norm_num

/-- Reverse the sign of a step without changing its length. -/
def longRangeStepReverse (s : LongRangeSignedStep) : LongRangeSignedStep :=
  (s.1, !s.2)

@[simp]
theorem longRangeStepReverse_reverse (s : LongRangeSignedStep) :
    longRangeStepReverse (longRangeStepReverse s) = s := by
  rcases s with ⟨n, b⟩
  cases b <;> rfl

@[simp]
theorem longRangeStepDisplacement_reverse (s : LongRangeSignedStep) :
    longRangeStepDisplacement (longRangeStepReverse s) =
      -longRangeStepDisplacement s := by
  rcases s with ⟨n, b⟩
  cases b <;> simp [longRangeStepReverse, longRangeStepDisplacement]

/-- Extended-nonnegative weight of one signed displacement. -/
def longRangeStepWeight (p : LongRangeProfile) (s : LongRangeSignedStep) : ℝ≥0∞ :=
  ENNReal.ofReal (p (s.1 + 1) : ℝ)

@[simp]
theorem longRangeStepWeight_reverse (p : LongRangeProfile) (s : LongRangeSignedStep) :
    longRangeStepWeight p (longRangeStepReverse s) = longRangeStepWeight p s := by
  rfl

/-- Mean degree at one vertex, `2 * sum p(n)`, in an endpoint-safe codomain. -/
noncomputable def longRangeMeanDegreeENNReal (p : LongRangeProfile) : ℝ≥0∞ :=
  2 * ∑' n : ℕ, ENNReal.ofReal (p n : ℝ)

theorem tsum_longRangeStepWeight (p : LongRangeProfile) :
    ∑' s : LongRangeSignedStep, longRangeStepWeight p s =
      longRangeMeanDegreeENNReal p := by
  change (∑' s : ℕ × Bool, longRangeStepWeight p s) = _
  rw [ENNReal.tsum_prod']
  have hbool (n : ℕ) :
      (∑' b : Bool, longRangeStepWeight p (n, b)) =
        2 * ENNReal.ofReal (p (n + 1) : ℝ) := by
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [longRangeStepWeight]
    rw [two_mul]
  simp_rw [hbool]
  rw [ENNReal.tsum_mul_left]
  have hshift : (∑' n : ℕ, ENNReal.ofReal (p (n + 1) : ℝ)) =
      ∑' n : ℕ, ENNReal.ofReal (p n : ℝ) := by
    have h := tsum_eq_zero_add'
      (f := fun n : ℕ ↦ ENNReal.ofReal (p n : ℝ)) ENNReal.summable
    simpa using h.symm
  rw [hshift]
  rfl

/-- Weight of a consecutive pair after deleting an immediate reversal. -/
noncomputable def longRangeNonreversingPairWeight (p : LongRangeProfile)
    (s : LongRangeSignedStep × LongRangeSignedStep) : ℝ≥0∞ :=
  if s.2 = longRangeStepReverse s.1 then 0
  else longRangeStepWeight p s.1 * longRangeStepWeight p s.2

/-- Total weight of a nonreversing two-step block. -/
noncomputable def longRangeNonreversingPairMass (p : LongRangeProfile) : ℝ≥0∞ :=
  ∑' s : LongRangeSignedStep × LongRangeSignedStep,
    longRangeNonreversingPairWeight p s

theorem longRangeNonreversingPairMass_le_meanDegree_sq (p : LongRangeProfile) :
    longRangeNonreversingPairMass p ≤ longRangeMeanDegreeENNReal p ^ 2 := by
  unfold longRangeNonreversingPairMass
  calc
    (∑' s : LongRangeSignedStep × LongRangeSignedStep,
        longRangeNonreversingPairWeight p s) ≤
        ∑' s : LongRangeSignedStep × LongRangeSignedStep,
          longRangeStepWeight p s.1 * longRangeStepWeight p s.2 := by
      apply ENNReal.tsum_le_tsum
      intro s
      simp only [longRangeNonreversingPairWeight]
      split_ifs <;> simp
    _ = (∑' a : LongRangeSignedStep, longRangeStepWeight p a) *
        ∑' b : LongRangeSignedStep, longRangeStepWeight p b := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]
    _ = longRangeMeanDegreeENNReal p ^ 2 := by
      rw [tsum_longRangeStepWeight]
      simp [pow_two]

/-- At the critical mean-degree equality, the deletion of one positive reversing pair still
makes the two-step mass strictly subunit. -/
theorem longRangeNonreversingPairMass_lt_one
    (p : LongRangeProfile) (hmean : longRangeMeanDegreeENNReal p ≤ 1)
    (hpos : ∃ n : ℕ, 0 < ENNReal.ofReal (p n : ℝ)) :
    longRangeNonreversingPairMass p < 1 := by
  obtain ⟨n, hn⟩ := hpos
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    simpa using hn
  let a : LongRangeSignedStep := (n - 1, true)
  have haLength : a.1 + 1 = n := by
    dsimp [a]
    omega
  let c : LongRangeSignedStep × LongRangeSignedStep :=
    (a, longRangeStepReverse a)
  let full : LongRangeSignedStep × LongRangeSignedStep → ℝ≥0∞ := fun s ↦
    longRangeStepWeight p s.1 * longRangeStepWeight p s.2
  let rest : ℝ≥0∞ := ∑' s, if s = c then 0 else full s
  have hcpos : 0 < full c := by
    dsimp [full, c]
    rw [longRangeStepWeight_reverse]
    simp only [longRangeStepWeight, haLength]
    exact ENNReal.mul_pos hn.ne' hn.ne'
  have hmassRest : longRangeNonreversingPairMass p ≤ rest := by
    unfold longRangeNonreversingPairMass rest
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hsc : s = c
    · subst s
      simp [longRangeNonreversingPairWeight, c]
    · simp only [hsc, ↓reduceIte]
      simp only [longRangeNonreversingPairWeight]
      split_ifs <;> simp [full]
  have hfull : (∑' s, full s) = longRangeMeanDegreeENNReal p ^ 2 := by
    dsimp [full]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, tsum_longRangeStepWeight]
    simp [pow_two]
  have hsplit : (∑' s, full s) = full c + rest := by
    rw [ENNReal.tsum_eq_add_tsum_ite c]
    dsimp only [rest]
    congr 1
    apply tsum_congr
    intro s
    by_cases hs : s = c <;> simp [hs]
  have hrestLt : rest < 1 := by
    have htotal : full c + rest ≤ 1 := by
      rw [← hsplit, hfull]
      calc
        longRangeMeanDegreeENNReal p ^ 2 =
            longRangeMeanDegreeENNReal p * longRangeMeanDegreeENNReal p := by simp [pow_two]
        _ ≤ 1 * 1 := mul_le_mul' hmean hmean
        _ = 1 := one_mul 1
    have hrestSub : rest ≤ 1 - full c :=
      ENNReal.le_sub_of_add_le_left (by
        exact ne_top_of_le_ne_top (by simp) (le_trans (self_le_add_right _ _) htotal)) htotal
    exact hrestSub.trans_lt (ENNReal.sub_lt_self (by simp) one_ne_zero hcpos.ne')
  exact hmassRest.trans_lt hrestLt

/-- Product-sum identity for a finite family of countable ENNReal weights. -/
theorem ennreal_tsum_fin_product {α : Type*} (w : α → ℝ≥0∞) :
    ∀ n : ℕ, (∑' f : Fin n → α, ∏ i, w (f i)) = (∑' a, w a) ^ n
  | 0 => by simp
  | n + 1 => by
      let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ α)
      rw [← e.tsum_eq]
      have heval (c : α × (Fin n → α)) :
          (∏ i, w (e c i)) = w c.1 * ∏ i, w (c.2 i) := by
        change (∏ i, w ((Fin.cons c.1 c.2 : Fin (n + 1) → α) i)) = _
        rw [Fin.prod_univ_succ]
        simp
      simp_rw [heval]
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ennreal_tsum_fin_product w n, ENNReal.tsum_mul_right, pow_succ']

/-! ### Encoding complete-graph walks by signed increments -/

/-- Encode a nonzero integer as a signed step. -/
def longRangeStepOfNonzero (z : ℤ) (hz : z ≠ 0) : LongRangeSignedStep :=
  if hzpos : 0 < z then (z.natAbs - 1, true) else (z.natAbs - 1, false)

@[simp]
theorem longRangeStepDisplacement_stepOfNonzero (z : ℤ) (hz : z ≠ 0) :
    longRangeStepDisplacement (longRangeStepOfNonzero z hz) = z := by
  have habspos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  by_cases hzpos : 0 < z
  · simp only [longRangeStepOfNonzero, dif_pos hzpos, longRangeStepDisplacement,
      Bool.true_eq, ↓reduceIte]
    have hsucc : z.natAbs - 1 + 1 = z.natAbs := by omega
    rw [hsucc, Int.natCast_natAbs, abs_of_pos hzpos]
  · have hzneg : z < 0 := by omega
    simp only [longRangeStepOfNonzero, dif_neg hzpos, longRangeStepDisplacement,
      Bool.false_eq_true, ↓reduceIte]
    have hsucc : z.natAbs - 1 + 1 = z.natAbs := by omega
    rw [hsucc, Int.natCast_natAbs, abs_of_neg hzneg]
    simp

theorem longRangeStepWeight_stepOfNonzero (p : LongRangeProfile)
    (z : ℤ) (hz : z ≠ 0) :
    longRangeStepWeight p (longRangeStepOfNonzero z hz) =
      ENNReal.ofReal (p z.natAbs : ℝ) := by
  have hdisp := congrArg Int.natAbs
    (longRangeStepDisplacement_stepOfNonzero z hz)
  rw [longRangeStepDisplacement_natAbs] at hdisp
  simp only [longRangeStepWeight, hdisp]

/-- Signed increments traversed by a complete-graph walk, in chronological order. -/
def longRangeStepsOfWalk {x y : ℤ} :
    (⊤ : SimpleGraph ℤ).Walk x y → List LongRangeSignedStep
  | .nil => []
  | @SimpleGraph.Walk.cons _ _ u v z huv w =>
      longRangeStepOfNonzero (v - u) (sub_ne_zero.mpr huv.ne.symm) ::
        longRangeStepsOfWalk w

@[simp]
theorem longRangeStepsOfWalk_nil (x : ℤ) :
    longRangeStepsOfWalk (SimpleGraph.Walk.nil : (⊤ : SimpleGraph ℤ).Walk x x) = [] :=
  rfl

@[simp]
theorem longRangeStepsOfWalk_cons {u v z : ℤ}
    (huv : (⊤ : SimpleGraph ℤ).Adj u v) (w : (⊤ : SimpleGraph ℤ).Walk v z) :
    longRangeStepsOfWalk (SimpleGraph.Walk.cons huv w) =
      longRangeStepOfNonzero (v - u) (sub_ne_zero.mpr huv.ne.symm) ::
        longRangeStepsOfWalk w :=
  rfl

@[simp]
theorem length_longRangeStepsOfWalk {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    (longRangeStepsOfWalk w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [ih]

/-- A walk from a fixed starting vertex is uniquely determined by its signed increments. -/
theorem sigma_walk_eq_of_longRangeStepsOfWalk_eq {x y z : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y)
    (v : (⊤ : SimpleGraph ℤ).Walk x z)
    (hsteps : longRangeStepsOfWalk w = longRangeStepsOfWalk v) :
    (⟨y, w⟩ : Σ t, (⊤ : SimpleGraph ℤ).Walk x t) = ⟨z, v⟩ := by
  induction w generalizing z with
  | nil =>
      cases v with
      | nil => rfl
      | cons h q => simp at hsteps
  | @cons u y t huy p ih =>
      cases v with
      | nil => simp at hsteps
      | @cons _ z' z hz' q =>
          simp only [longRangeStepsOfWalk_cons, List.cons.injEq] at hsteps
          have hdisp := congrArg longRangeStepDisplacement hsteps.1
          simp only [longRangeStepDisplacement_stepOfNonzero] at hdisp
          have hyz : y = z' := by omega
          subst z'
          have htail := ih q hsteps.2
          cases htail
          rfl

/-- The vector of increments of a walk. -/
def longRangeStepVectorOfWalk {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    List.Vector LongRangeSignedStep w.length :=
  ⟨longRangeStepsOfWalk w, length_longRangeStepsOfWalk w⟩

/-- Regroup an even-length increment vector into consecutive pairs. -/
def longRangeStepPairingEquiv (m : ℕ) :
    (Fin (m * 2) → LongRangeSignedStep) ≃
      (Fin m → LongRangeSignedStep × LongRangeSignedStep) :=
  (Equiv.piCongrLeft (fun _ : Fin (m * 2) ↦ LongRangeSignedStep)
      (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2))).symm |>.trans
    ((Equiv.curry (Fin m) (Fin 2) LongRangeSignedStep).trans
      (Equiv.piCongrRight fun _ : Fin m ↦ finTwoArrowEquiv LongRangeSignedStep))

@[simp]
theorem longRangeStepPairingEquiv_apply_fst (m : ℕ)
    (f : Fin (m * 2) → LongRangeSignedStep) (i : Fin m) :
    (longRangeStepPairingEquiv m f i).1 =
      f (finProdFinEquiv (i, (0 : Fin 2))) := by
  rfl

@[simp]
theorem longRangeStepPairingEquiv_apply_snd (m : ℕ)
    (f : Fin (m * 2) → LongRangeSignedStep) (i : Fin m) :
    (longRangeStepPairingEquiv m f i).2 =
      f (finProdFinEquiv (i, (1 : Fin 2))) := by
  rfl

@[simp]
theorem longRangeStepOfNonzero_displacement (s : LongRangeSignedStep) :
    longRangeStepOfNonzero (longRangeStepDisplacement s)
      (longRangeStepDisplacement_ne_zero s) = s := by
  rcases s with ⟨n, b⟩
  cases b with
  | false =>
      simp only [longRangeStepDisplacement, Bool.false_eq_true, ↓reduceIte,
        longRangeStepOfNonzero]
      rw [dif_neg (by omega : ¬0 < -((n + 1 : ℕ) : ℤ))]
      congr 1
  | true =>
      simp only [longRangeStepDisplacement, Bool.true_eq, ↓reduceIte,
        longRangeStepOfNonzero]
      rw [dif_pos (by omega : 0 < ((n + 1 : ℕ) : ℤ))]
      congr 1

/-- Construct the unique complete-graph walk starting at `x` with the prescribed signed
increments.  The endpoint remains in a sigma type because it is determined by the list. -/
def longRangeWalkOfSteps (x : ℤ) :
    List LongRangeSignedStep → Σ y : ℤ, (⊤ : SimpleGraph ℤ).Walk x y
  | [] => ⟨x, SimpleGraph.Walk.nil⟩
  | s :: l =>
      let y := x + longRangeStepDisplacement s
      let q := longRangeWalkOfSteps y l
      ⟨q.1, SimpleGraph.Walk.cons
        ((SimpleGraph.top_adj x y).mpr (by
          dsimp [y]
          exact (add_ne_left.mpr (longRangeStepDisplacement_ne_zero s)).symm)) q.2⟩

@[simp]
theorem longRangeStepsOfWalk_walkOfSteps (x : ℤ) (l : List LongRangeSignedStep) :
    longRangeStepsOfWalk (longRangeWalkOfSteps x l).2 = l := by
  induction l generalizing x with
  | nil => rfl
  | cons s l ih =>
      simp only [longRangeWalkOfSteps, longRangeStepsOfWalk_cons]
      have hne : x + longRangeStepDisplacement s - x ≠ 0 := by
        simpa only [add_sub_cancel_left] using longRangeStepDisplacement_ne_zero s
      have hhead : longRangeStepOfNonzero
          (x + longRangeStepDisplacement s - x) hne = s := by
        simpa only [add_sub_cancel_left] using longRangeStepOfNonzero_displacement s
      rw [hhead, ih]

@[simp]
theorem longRangeWalkOfSteps_length (x : ℤ) (l : List LongRangeSignedStep) :
    (longRangeWalkOfSteps x l).2.length = l.length := by
  rw [← length_longRangeStepsOfWalk, longRangeStepsOfWalk_walkOfSteps]

/-- The original walk is recovered from its increment list, including its endpoint. -/
theorem longRangeWalkOfSteps_stepsOfWalk {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    longRangeWalkOfSteps x (longRangeStepsOfWalk w) = ⟨y, w⟩ := by
  exact sigma_walk_eq_of_longRangeStepsOfWalk_eq
    (longRangeWalkOfSteps x (longRangeStepsOfWalk w)).2 w
    (longRangeStepsOfWalk_walkOfSteps x _)

/-- The complete-graph walk encoded by a fixed-length step function. -/
def longRangeWalkOfStepFunction (x : ℤ) {n : ℕ}
    (f : Fin n → LongRangeSignedStep) :
    (⊤ : SimpleGraph ℤ).Walk x (longRangeWalkOfSteps x (List.ofFn f)).1 :=
  (longRangeWalkOfSteps x (List.ofFn f)).2

@[simp]
theorem longRangeWalkOfStepFunction_length (x : ℤ) {n : ℕ}
    (f : Fin n → LongRangeSignedStep) :
    (longRangeWalkOfStepFunction x f).length = n := by
  simp [longRangeWalkOfStepFunction]

/-- A fixed-length signed-step sequence is self-avoiding when its constructed walk is a path. -/
def longRangeStepFunctionIsPath (x : ℤ) {n : ℕ}
    (f : Fin n → LongRangeSignedStep) : Prop :=
  (longRangeWalkOfStepFunction x f).IsPath

/-- The event that some open self-avoiding long-range path of exactly `n` edges starts at `x`. -/
def longRangeOpenPathOfLengthEvent (x : ℤ) (n : ℕ) : Set LongRangeConfiguration :=
  {ω | ∃ f : Fin n → LongRangeSignedStep,
    longRangeStepFunctionIsPath x f ∧
      longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)}

theorem measurableSet_longRangeOpenPathOfLengthEvent (x : ℤ) (n : ℕ) :
    MeasurableSet (longRangeOpenPathOfLengthEvent x n) := by
  classical
  rw [show longRangeOpenPathOfLengthEvent x n =
      ⋃ f : Fin n → LongRangeSignedStep,
        if longRangeStepFunctionIsPath x f then
          {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅ by
    ext ω
    simp [longRangeOpenPathOfLengthEvent]]
  exact MeasurableSet.iUnion fun f ↦ by
    split_ifs
    · exact measurableSet_longRangeWalkIsOpen _
    · exact MeasurableSet.empty

/-! ### Exact path weights and the nonreversal constraint -/

/-- Product of the opening probabilities of the distinct edges of a walk. -/
noncomputable def longRangeWalkOpenWeight (p : LongRangeProfile) {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) : ℝ≥0∞ :=
  ∏ e ∈ longRangeWalkEdgeFinset w,
    ENNReal.ofReal (p (longRangeEdgeDistance e) : ℝ)

/-- The probability that all edges of a fixed walk are open is its distinct-edge product. -/
theorem longRangeMeasure_walkIsOpen (p : LongRangeProfile) {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    longRangeMeasure p {ω | longRangeWalkIsOpen ω w} =
      longRangeWalkOpenWeight p w := by
  rw [longRangeWalkIsOpen_event_eq, ← ofReal_measureReal]
  rw [longRangeMeasure_real_superset_finset]
  unfold longRangeWalkOpenWeight
  rw [ENNReal.ofReal_prod_of_nonneg]
  exact fun _ _ ↦ (p _).2.1

theorem map_longRangeEdgeWeight_edges_eq_steps (p : LongRangeProfile) {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    w.edges.map (fun e ↦ ENNReal.ofReal (p (longRangeEdgeDistance e) : ℝ)) =
      (longRangeStepsOfWalk w).map (longRangeStepWeight p) := by
  induction w with
  | nil => rfl
  | @cons u v y huv w ih =>
      simp only [SimpleGraph.Walk.edges_cons, longRangeStepsOfWalk_cons, List.map_cons, ih]
      congr 1
      simpa [longRangeEdgeDistance_mk] using
        (longRangeStepWeight_stepOfNonzero p (v - u)
          (sub_ne_zero.mpr huv.ne.symm)).symm

/-- On a trail, the distinct-edge product equals the chronological increment product. -/
theorem longRangeWalkOpenWeight_eq_steps_product (p : LongRangeProfile) {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) (hw : w.IsTrail) :
    longRangeWalkOpenWeight p w =
      ((longRangeStepsOfWalk w).map (longRangeStepWeight p)).prod := by
  unfold longRangeWalkOpenWeight longRangeWalkEdgeFinset
  rw [List.prod_toFinset _ hw.edges_nodup]
  exact congrArg List.prod (map_longRangeEdgeWeight_edges_eq_steps p w)

/-- Consecutive increments of a path never immediately reverse. -/
theorem longRangeStepsOfWalk_isChain_nonreverse {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) (hw : w.IsPath) :
    (longRangeStepsOfWalk w).IsChain
      (fun a b ↦ b ≠ longRangeStepReverse a) := by
  induction w with
  | nil => exact List.isChain_nil
  | @cons u v y huv w ih =>
      cases w with
      | nil => exact List.isChain_singleton _
      | @cons _ z y hvz q =>
          simp only [longRangeStepsOfWalk_cons, List.isChain_cons_cons]
          constructor
          · intro hreverse
            have hdisp := congrArg longRangeStepDisplacement hreverse
            simp only [longRangeStepDisplacement_stepOfNonzero,
              longRangeStepDisplacement_reverse] at hdisp
            have huz : u = z := by omega
            have hnmem := (List.nodup_cons.mp hw.isTrail.edges_nodup).1
            apply hnmem
            simp only [SimpleGraph.Walk.darts_cons, List.map_cons,
              SimpleGraph.Dart.edge_mk, List.mem_cons]
            left
            subst z
            exact Sym2.eq_swap
          · exact ih hw.of_cons

theorem longRangeStepPairingEquiv_ne_reverse_of_isPath (x : ℤ) (m : ℕ)
    (f : Fin (m * 2) → LongRangeSignedStep)
    (hf : longRangeStepFunctionIsPath x f) (i : Fin m) :
    (longRangeStepPairingEquiv m f i).2 ≠
      longRangeStepReverse (longRangeStepPairingEquiv m f i).1 := by
  have hchain := longRangeStepsOfWalk_isChain_nonreverse
    (longRangeWalkOfStepFunction x f) hf
  have hsteps : longRangeStepsOfWalk (longRangeWalkOfStepFunction x f) =
      List.ofFn f := by
    exact longRangeStepsOfWalk_walkOfSteps x (List.ofFn f)
  rw [hsteps, List.isChain_ofFn] at hchain
  have hrel := hchain (2 * i.1) (by
    have hi := i.2
    omega)
  rw [longRangeStepPairingEquiv_apply_fst,
    longRangeStepPairingEquiv_apply_snd]
  simpa [finProdFinEquiv, Nat.add_comm] using hrel

/-- Regrouping a product over `2m` increments into `m` consecutive two-step blocks. -/
theorem longRangeStepWeight_product_eq_pair_product (p : LongRangeProfile) (m : ℕ)
    (f : Fin (m * 2) → LongRangeSignedStep) :
    (∏ j, longRangeStepWeight p (f j)) =
      ∏ i, longRangeStepWeight p (longRangeStepPairingEquiv m f i).1 *
        longRangeStepWeight p (longRangeStepPairingEquiv m f i).2 := by
  calc
    (∏ j, longRangeStepWeight p (f j)) =
        ∏ ij : Fin m × Fin 2,
          longRangeStepWeight p (f (finProdFinEquiv ij)) :=
      (finProdFinEquiv.prod_comp (fun j ↦ longRangeStepWeight p (f j))).symm
    _ = ∏ i : Fin m, ∏ j : Fin 2,
          longRangeStepWeight p (f (finProdFinEquiv (i, j))) := by
      rw [Fintype.prod_prod_type]
    _ = ∏ i, longRangeStepWeight p (longRangeStepPairingEquiv m f i).1 *
          longRangeStepWeight p (longRangeStepPairingEquiv m f i).2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Fin.prod_univ_two]
      rfl

/-- A self-avoiding `2m`-step path has exactly the product of its nonreversing block weights. -/
theorem longRangeWalkOpenWeight_eq_pair_product_of_isPath (p : LongRangeProfile)
    (x : ℤ) (m : ℕ) (f : Fin (m * 2) → LongRangeSignedStep)
    (hf : longRangeStepFunctionIsPath x f) :
    longRangeWalkOpenWeight p (longRangeWalkOfStepFunction x f) =
      ∏ i, longRangeNonreversingPairWeight p
        (longRangeStepPairingEquiv m f i) := by
  rw [longRangeWalkOpenWeight_eq_steps_product p _ hf.isTrail]
  have hsteps : longRangeStepsOfWalk (longRangeWalkOfStepFunction x f) =
      List.ofFn f := longRangeStepsOfWalk_walkOfSteps x _
  rw [hsteps]
  simp only [List.map_ofFn, List.prod_ofFn]
  change (∏ j, longRangeStepWeight p (f j)) = _
  rw [longRangeStepWeight_product_eq_pair_product]
  apply Finset.prod_congr rfl
  intro i hi
  rw [longRangeNonreversingPairWeight, if_neg]
  exact longRangeStepPairingEquiv_ne_reverse_of_isPath x m f hf i

/-- The union bound over self-avoiding paths of length `2m`, with the deleted-reversal
two-step mass as its geometric ratio. -/
theorem longRangeMeasure_openPath_even_le (p : LongRangeProfile) (x : ℤ) (m : ℕ) :
    longRangeMeasure p (longRangeOpenPathOfLengthEvent x (m * 2)) ≤
      longRangeNonreversingPairMass p ^ m := by
  classical
  rw [show longRangeOpenPathOfLengthEvent x (m * 2) =
      ⋃ f : Fin (m * 2) → LongRangeSignedStep,
        if longRangeStepFunctionIsPath x f then
          {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅ by
    ext ω
    simp [longRangeOpenPathOfLengthEvent]]
  calc
    longRangeMeasure p (⋃ f : Fin (m * 2) → LongRangeSignedStep,
        if longRangeStepFunctionIsPath x f then
          {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅) ≤
        ∑' f : Fin (m * 2) → LongRangeSignedStep,
          longRangeMeasure p (if longRangeStepFunctionIsPath x f then
            {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅) :=
      measure_iUnion_le _
    _ = ∑' f : Fin (m * 2) → LongRangeSignedStep,
          if hf : longRangeStepFunctionIsPath x f then
            ∏ i, longRangeNonreversingPairWeight p
              (longRangeStepPairingEquiv m f i) else 0 := by
      apply tsum_congr
      intro f
      split_ifs with hf
      · rw [longRangeMeasure_walkIsOpen,
          longRangeWalkOpenWeight_eq_pair_product_of_isPath p x m f hf]
      · simp
    _ ≤ ∑' f : Fin (m * 2) → LongRangeSignedStep,
          ∏ i, longRangeNonreversingPairWeight p
            (longRangeStepPairingEquiv m f i) := by
      apply ENNReal.tsum_le_tsum
      intro f
      split_ifs <;> simp
    _ = ∑' g : Fin m → LongRangeSignedStep × LongRangeSignedStep,
          ∏ i, longRangeNonreversingPairWeight p (g i) :=
      (longRangeStepPairingEquiv m).tsum_eq
        (fun g ↦ ∏ i, longRangeNonreversingPairWeight p (g i))
    _ = longRangeNonreversingPairMass p ^ m := by
      exact ennreal_tsum_fin_product (longRangeNonreversingPairWeight p) m

/-- Split an odd-length increment sequence into its first step and consecutive pairs in the
remaining even-length tail. -/
def longRangeOddStepPairingEquiv (m : ℕ) :
    (Fin (m * 2 + 1) → LongRangeSignedStep) ≃
      LongRangeSignedStep ×
        (Fin m → LongRangeSignedStep × LongRangeSignedStep) :=
  (Fin.consEquiv (fun _ : Fin (m * 2 + 1) ↦ LongRangeSignedStep)).symm |>.trans
    (Equiv.prodCongr (Equiv.refl LongRangeSignedStep) (longRangeStepPairingEquiv m))

@[simp]
theorem longRangeOddStepPairingEquiv_apply_fst (m : ℕ)
    (f : Fin (m * 2 + 1) → LongRangeSignedStep) :
    (longRangeOddStepPairingEquiv m f).1 = f 0 := by
  simp [longRangeOddStepPairingEquiv]

@[simp]
theorem longRangeOddStepPairingEquiv_apply_snd (m : ℕ)
    (f : Fin (m * 2 + 1) → LongRangeSignedStep) :
    (longRangeOddStepPairingEquiv m f).2 =
      longRangeStepPairingEquiv m (fun j ↦ f j.succ) := by
  simp [longRangeOddStepPairingEquiv]
  congr 1

theorem longRangeOddStepPairingEquiv_ne_reverse_of_isPath (x : ℤ) (m : ℕ)
    (f : Fin (m * 2 + 1) → LongRangeSignedStep)
    (hf : longRangeStepFunctionIsPath x f) (i : Fin m) :
    ((longRangeOddStepPairingEquiv m f).2 i).2 ≠
      longRangeStepReverse ((longRangeOddStepPairingEquiv m f).2 i).1 := by
  have hchain := longRangeStepsOfWalk_isChain_nonreverse
    (longRangeWalkOfStepFunction x f) hf
  have hsteps : longRangeStepsOfWalk (longRangeWalkOfStepFunction x f) =
      List.ofFn f := longRangeStepsOfWalk_walkOfSteps x _
  rw [hsteps, List.isChain_ofFn] at hchain
  have hrel := hchain (2 * i.1 + 1) (by
    have hi := i.2
    omega)
  rw [longRangeOddStepPairingEquiv_apply_snd,
    longRangeStepPairingEquiv_apply_fst,
    longRangeStepPairingEquiv_apply_snd]
  simpa [finProdFinEquiv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrel

theorem longRangeOddStepWeight_product_eq_pair_product (p : LongRangeProfile) (m : ℕ)
    (f : Fin (m * 2 + 1) → LongRangeSignedStep) :
    (∏ j, longRangeStepWeight p (f j)) =
      longRangeStepWeight p (longRangeOddStepPairingEquiv m f).1 *
        ∏ i, longRangeStepWeight p ((longRangeOddStepPairingEquiv m f).2 i).1 *
          longRangeStepWeight p ((longRangeOddStepPairingEquiv m f).2 i).2 := by
  rw [Fin.prod_univ_succ]
  rw [longRangeStepWeight_product_eq_pair_product p m (fun j ↦ f j.succ)]
  rw [longRangeOddStepPairingEquiv_apply_fst,
    longRangeOddStepPairingEquiv_apply_snd]

theorem longRangeWalkOpenWeight_eq_odd_pair_product_of_isPath
    (p : LongRangeProfile) (x : ℤ) (m : ℕ)
    (f : Fin (m * 2 + 1) → LongRangeSignedStep)
    (hf : longRangeStepFunctionIsPath x f) :
    longRangeWalkOpenWeight p (longRangeWalkOfStepFunction x f) =
      longRangeStepWeight p (longRangeOddStepPairingEquiv m f).1 *
        ∏ i, longRangeNonreversingPairWeight p
          ((longRangeOddStepPairingEquiv m f).2 i) := by
  rw [longRangeWalkOpenWeight_eq_steps_product p _ hf.isTrail]
  have hsteps : longRangeStepsOfWalk (longRangeWalkOfStepFunction x f) =
      List.ofFn f := longRangeStepsOfWalk_walkOfSteps x _
  rw [hsteps]
  simp only [List.map_ofFn, List.prod_ofFn]
  change (∏ j, longRangeStepWeight p (f j)) = _
  rw [longRangeOddStepWeight_product_eq_pair_product]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [longRangeNonreversingPairWeight, if_neg]
  exact longRangeOddStepPairingEquiv_ne_reverse_of_isPath x m f hf i

/-- Odd-length paths carry one unrestricted signed-step factor and `m` nonreversing pairs. -/
theorem longRangeMeasure_openPath_odd_le (p : LongRangeProfile) (x : ℤ) (m : ℕ) :
    longRangeMeasure p (longRangeOpenPathOfLengthEvent x (m * 2 + 1)) ≤
      longRangeMeanDegreeENNReal p * longRangeNonreversingPairMass p ^ m := by
  classical
  rw [show longRangeOpenPathOfLengthEvent x (m * 2 + 1) =
      ⋃ f : Fin (m * 2 + 1) → LongRangeSignedStep,
        if longRangeStepFunctionIsPath x f then
          {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅ by
    ext ω
    simp [longRangeOpenPathOfLengthEvent]]
  calc
    longRangeMeasure p (⋃ f : Fin (m * 2 + 1) → LongRangeSignedStep,
        if longRangeStepFunctionIsPath x f then
          {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅) ≤
        ∑' f : Fin (m * 2 + 1) → LongRangeSignedStep,
          longRangeMeasure p (if longRangeStepFunctionIsPath x f then
            {ω | longRangeWalkIsOpen ω (longRangeWalkOfStepFunction x f)} else ∅) :=
      measure_iUnion_le _
    _ = ∑' f : Fin (m * 2 + 1) → LongRangeSignedStep,
          if hf : longRangeStepFunctionIsPath x f then
            longRangeStepWeight p (longRangeOddStepPairingEquiv m f).1 *
              ∏ i, longRangeNonreversingPairWeight p
                ((longRangeOddStepPairingEquiv m f).2 i) else 0 := by
      apply tsum_congr
      intro f
      split_ifs with hf
      · rw [longRangeMeasure_walkIsOpen,
          longRangeWalkOpenWeight_eq_odd_pair_product_of_isPath p x m f hf]
      · simp
    _ ≤ ∑' f : Fin (m * 2 + 1) → LongRangeSignedStep,
          longRangeStepWeight p (longRangeOddStepPairingEquiv m f).1 *
            ∏ i, longRangeNonreversingPairWeight p
              ((longRangeOddStepPairingEquiv m f).2 i) := by
      apply ENNReal.tsum_le_tsum
      intro f
      split_ifs <;> simp
    _ = ∑' g : LongRangeSignedStep ×
          (Fin m → LongRangeSignedStep × LongRangeSignedStep),
          longRangeStepWeight p g.1 *
            ∏ i, longRangeNonreversingPairWeight p (g.2 i) :=
      (longRangeOddStepPairingEquiv m).tsum_eq
        (fun g ↦ longRangeStepWeight p g.1 *
          ∏ i, longRangeNonreversingPairWeight p (g.2 i))
    _ = (∑' s : LongRangeSignedStep, longRangeStepWeight p s) *
          ∑' g : Fin m → LongRangeSignedStep × LongRangeSignedStep,
            ∏ i, longRangeNonreversingPairWeight p (g i) := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]
    _ = longRangeMeanDegreeENNReal p * longRangeNonreversingPairMass p ^ m := by
      rw [tsum_longRangeStepWeight,
        ennreal_tsum_fin_product (longRangeNonreversingPairWeight p) m]
      rfl

/-! ### Almost-sure local finiteness -/

/-- The coordinate event that the edge reached from `x` by signed step `s` is open. -/
def longRangeIncidentStepEvent (x : ℤ) (s : LongRangeSignedStep) :
    Set LongRangeConfiguration :=
  {ω | s(x, x + longRangeStepDisplacement s) ∈ ω}

theorem longRangeMeasure_incidentStepEvent (p : LongRangeProfile)
    (x : ℤ) (s : LongRangeSignedStep) :
    longRangeMeasure p (longRangeIncidentStepEvent x s) =
      longRangeStepWeight p s := by
  rw [← ofReal_measureReal]
  simp only [longRangeIncidentStepEvent, longRangeMeasure_real_edgeOpen,
    longRangeEdgeDensity_mk, longRangeStepWeight]
  congr 2
  rw [show x + longRangeStepDisplacement s - x =
    longRangeStepDisplacement s by omega]
  rw [longRangeStepDisplacement_natAbs]

theorem tsum_longRangeMeasure_incidentStepEvent_le_meanDegree
    (p : LongRangeProfile) (x : ℤ) (b : Bool) :
    (∑' n : ℕ, longRangeMeasure p (longRangeIncidentStepEvent x (n, b))) ≤
      longRangeMeanDegreeENNReal p := by
  simp_rw [longRangeMeasure_incidentStepEvent]
  rw [← tsum_longRangeStepWeight p]
  exact ENNReal.tsum_comp_le_tsum_of_injective
    (fun _ _ h ↦ congrArg Prod.fst h)
    (longRangeStepWeight p)

/-- Under finite mean degree, every vertex has only finitely many open incident bonds almost
surely.  This is a direct Borel--Cantelli argument and does not assume local finiteness in the
sample space. -/
theorem longRange_ae_neighborSet_finite_of_meanDegree_le_one
    (p : LongRangeProfile) (hmean : longRangeMeanDegreeENNReal p ≤ 1) :
    ∀ᵐ ω ∂longRangeMeasure p,
      ∀ x : ℤ, (longRangeOpenGraph ω).neighborSet x |>.Finite := by
  rw [ae_all_iff]
  intro x
  have hsum (b : Bool) :
      (∑' n : ℕ, longRangeMeasure p (longRangeIncidentStepEvent x (n, b))) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((tsum_longRangeMeasure_incidentStepEvent_le_meanDegree p x b).trans hmean)
  filter_upwards [ae_eventually_notMem (hsum false),
    ae_eventually_notMem (hsum true)] with ω hneg hpos
  rw [Filter.eventually_atTop] at hneg hpos
  obtain ⟨Nneg, hNneg⟩ := hneg
  obtain ⟨Npos, hNpos⟩ := hpos
  let N := max Nneg Npos
  let S : Finset ℤ := ((Finset.range N).product Finset.univ).image
    (fun s : ℕ × Bool ↦ x + longRangeStepDisplacement s)
  apply S.finite_toSet.subset
  intro y hy
  have hxy : x ≠ y := (longRangeOpenGraph_adj.mp hy).2
  let t := longRangeStepOfNonzero (y - x) (sub_ne_zero.mpr hxy.symm)
  have hyt : y = x + longRangeStepDisplacement t := by
    rw [longRangeStepDisplacement_stepOfNonzero]
    omega
  have hopen : ω ∈ longRangeIncidentStepEvent x t := by
    change s(x, x + longRangeStepDisplacement t) ∈ ω
    rw [← hyt]
    exact (longRangeOpenGraph_adj.mp hy).1
  have htN : t.1 < N := by
    by_cases hb : t.2 = true
    · by_contra hge
      have hnot := hNpos t.1
        ((le_max_right Nneg Npos).trans (Nat.le_of_not_gt hge))
      apply hnot
      have ht : (t.1, true) = t := by
        exact Prod.ext rfl hb.symm
      rw [ht]
      exact hopen
    · have hbfalse : t.2 = false := Bool.eq_false_of_not_eq_true hb
      by_contra hge
      have hnot := hNneg t.1
        ((le_max_left Nneg Npos).trans (Nat.le_of_not_gt hge))
      apply hnot
      have ht : (t.1, false) = t := by
        exact Prod.ext rfl hbfalse.symm
      rw [ht]
      exact hopen
  rw [hyt]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨t, Finset.mem_product.mpr ⟨Finset.mem_range.mpr htN, Finset.mem_univ _⟩, rfl⟩)

/-! ### Infinite locally finite clusters contain arbitrarily long paths -/

/-- Vertices reachable from `x` by a walk of at most `n` edges. -/
def graphReachableWithin {V : Type*} (G : SimpleGraph V) (x : V) (n : ℕ) : Set V :=
  {y | ∃ w : G.Walk x y, w.length ≤ n}

theorem finite_graphReachableWithin_of_neighborSet_finite {V : Type*}
    (G : SimpleGraph V) (hlocal : ∀ x, (G.neighborSet x).Finite) :
    ∀ (n : ℕ) (x : V), (graphReachableWithin G x n).Finite
  | 0, x => by
      apply Set.finite_singleton x |>.subset
      rintro y ⟨w, hw⟩
      have hlen : w.length = 0 := Nat.eq_zero_of_le_zero hw
      simpa using (w.eq_of_length_eq_zero hlen).symm
  | n + 1, x => by
      let T : Set V := {x} ∪ ⋃ v ∈ G.neighborSet x, graphReachableWithin G v n
      have hT : T.Finite := by
        apply Set.Finite.union (Set.finite_singleton x)
        exact (hlocal x).biUnion fun v hv ↦
          finite_graphReachableWithin_of_neighborSet_finite G hlocal n v
      apply hT.subset
      rintro y ⟨w, hw⟩
      cases w with
      | nil => exact Set.mem_union_left _ (Set.mem_singleton x)
      | @cons _ v y hxv q =>
          refine Set.mem_union_right _ ?_
          refine Set.mem_iUnion.2 ⟨v, ?_⟩
          refine Set.mem_iUnion.2 ⟨hxv, ?_⟩
          exact ⟨q, by simpa using hw⟩

/-- In a locally finite graph, an infinite root component contains a path of every prescribed
finite length. -/
theorem exists_isPath_length_eq_of_reachableSet_infinite_of_neighborSet_finite
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hlocal : ∀ x, (G.neighborSet x).Finite) (x : V)
    (hinf : ({y | G.Reachable x y} : Set V).Infinite) (n : ℕ) :
    ∃ (y : V) (w : G.Walk x y), w.IsPath ∧ w.length = n := by
  have hfinite := finite_graphReachableWithin_of_neighborSet_finite G hlocal n x
  have hnsub : ¬({y | G.Reachable x y} : Set V) ⊆ graphReachableWithin G x n := by
    intro hsub
    exact hinf (hfinite.subset hsub)
  obtain ⟨y, hyreach, hyn⟩ := Set.not_subset.mp hnsub
  rcases hyreach with ⟨q⟩
  let w : G.Walk x y := q.toPath
  have hnle : n ≤ w.length := by
    by_contra h
    apply hyn
    exact ⟨w, Nat.le_of_lt (Nat.lt_of_not_ge h)⟩
  refine ⟨w.getVert n, w.take n, ?_, ?_⟩
  · exact q.toPath.property.take n
  simp [SimpleGraph.Walk.take_length, inf_eq_left.mpr hnle]

/-- Every complete-graph path has a fixed-length signed-step encoding whose reconstruction is
definitionally the same sigma-packaged walk. -/
theorem exists_longRangeStepFunction_walk_eq {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    ∃ f : Fin w.length → LongRangeSignedStep,
      longRangeWalkOfSteps x (List.ofFn f) = ⟨y, w⟩ := by
  let f : Fin w.length → LongRangeSignedStep :=
    (longRangeStepVectorOfWalk w).get
  refine ⟨f, ?_⟩
  have hof : List.ofFn f = longRangeStepsOfWalk w := by
    simpa [f, longRangeStepVectorOfWalk] using
      List.ofFn_get (longRangeStepsOfWalk w)
  rw [hof]
  exact longRangeWalkOfSteps_stepsOfWalk w

theorem mem_longRangeOpenPathOfLengthEvent_of_open_isPath
    {ω : LongRangeConfiguration} {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) (hw : w.IsPath)
    (hopen : longRangeWalkIsOpen ω w) :
    ω ∈ longRangeOpenPathOfLengthEvent x w.length := by
  obtain ⟨f, hf⟩ := exists_longRangeStepFunction_walk_eq w
  let q := longRangeWalkOfSteps x (List.ofFn f)
  have hq : q.2.IsPath ∧ longRangeWalkIsOpen ω q.2 := by
    rw [show q = ⟨y, w⟩ from hf]
    exact ⟨hw, hopen⟩
  exact ⟨f, hq.1, hq.2⟩

theorem longRangeNonreversingPairMass_lt_one_of_meanDegree_le_one
    (p : LongRangeProfile) (hmean : longRangeMeanDegreeENNReal p ≤ 1) :
    longRangeNonreversingPairMass p < 1 := by
  by_cases hpos : ∃ n : ℕ, 0 < ENNReal.ofReal (p n : ℝ)
  · exact longRangeNonreversingPairMass_lt_one p hmean hpos
  · push_neg at hpos
    have hweight : ∀ s : LongRangeSignedStep, longRangeStepWeight p s = 0 := by
      intro s
      exact nonpos_iff_eq_zero.mp (hpos (s.1 + 1))
    unfold longRangeNonreversingPairMass
    simp [longRangeNonreversingPairWeight, hweight]

/-- On the full-measure locally finite event, an infinite root cluster forces every even path
length event. -/
theorem mem_longRangeOpenPath_even_of_cluster_infinite
    {ω : LongRangeConfiguration} (hlocal : ∀ x, (longRangeOpenGraph ω).neighborSet x |>.Finite)
    {x : ℤ} (hinf : (longRangeCluster ω x).Infinite) (m : ℕ) :
    ω ∈ longRangeOpenPathOfLengthEvent x (m * 2) := by
  change ({y | (longRangeOpenGraph ω).Reachable x y} : Set ℤ).Infinite at hinf
  obtain ⟨y, w, hwpath, hwlen⟩ :=
    exists_isPath_length_eq_of_reachableSet_infinite_of_neighborSet_finite
      (longRangeOpenGraph ω) hlocal x hinf (m * 2)
  let q := w.map (longRangeOpenGraphHom ω)
  have hqpath : q.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective (fun _ _ h ↦ h) hwpath
  have hqopen : longRangeWalkIsOpen ω q :=
    longRangeWalkIsOpen_map_openGraphHom w
  have hmem := mem_longRangeOpenPathOfLengthEvent_of_open_isPath q hqpath hqopen
  simpa [q, hwlen] using hmem

/-- The rooted percolation event is null when the mean degree is at most one.  This includes
the equality case in Grimmett's displayed criterion (12.2). -/
theorem longRangeMeasure_percolationEvent_eq_zero_of_meanDegree_le_one
    (p : LongRangeProfile) (hmean : longRangeMeanDegreeENNReal p ≤ 1) (x : ℤ) :
    longRangeMeasure p (longRangePercolationEvent x) = 0 := by
  let L : Set LongRangeConfiguration :=
    {ω | ∀ z : ℤ, (longRangeOpenGraph ω).neighborSet z |>.Finite}
  have hLae : ∀ᵐ ω ∂longRangeMeasure p, ω ∈ L :=
    longRange_ae_neighborSet_finite_of_meanDegree_le_one p hmean
  have hLcompl : longRangeMeasure p Lᶜ = 0 := mem_ae_iff.mp hLae
  let q := longRangeNonreversingPairMass p
  have hq : q < 1 :=
    longRangeNonreversingPairMass_lt_one_of_meanDegree_le_one p hmean
  have hsubset (m : ℕ) :
      longRangePercolationEvent x ∩ L ⊆
        longRangeOpenPathOfLengthEvent x (m * 2) := by
    intro ω hω
    exact mem_longRangeOpenPath_even_of_cluster_infinite hω.2
      (mem_longRangePercolationEvent_iff_cluster_infinite.mp hω.1) m
  have hle (m : ℕ) :
      longRangeMeasure p (longRangePercolationEvent x ∩ L) ≤ q ^ m :=
    (measure_mono (hsubset m)).trans (longRangeMeasure_openPath_even_le p x m)
  have hinter : longRangeMeasure p (longRangePercolationEvent x ∩ L) = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hle
    · exact bot_le
  apply measure_mono_null
    (t := (longRangePercolationEvent x ∩ L) ∪ Lᶜ)
  · intro ω hω
    by_cases hωL : ω ∈ L
    · exact Set.mem_union_left _ ⟨hω, hωL⟩
    · exact Set.mem_union_right _ hωL
  · exact measure_union_null hinter hLcompl

/-- Criterion (12.2): if `2 * sum p_n ≤ 1`, every component is finite almost surely. -/
theorem longRangeMeasure_real_allComponentsFinite_eq_one_of_meanDegree_le_one
    (p : LongRangeProfile) (hmean : longRangeMeanDegreeENNReal p ≤ 1) :
    (longRangeMeasure p).real longRangeAllComponentsFiniteEvent = 1 := by
  have hcompl : longRangeAllComponentsFiniteEventᶜ =
      ⋃ x : ℤ, longRangePercolationEvent x := by
    ext ω
    simp only [longRangeAllComponentsFiniteEvent, Set.mem_compl_iff,
      Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      push_neg at h
      obtain ⟨x, hx⟩ := h
      exact ⟨x, mem_longRangePercolationEvent_iff_cluster_infinite.mpr
        hx⟩
    · rintro ⟨x, hx⟩ hall
      exact (mem_longRangePercolationEvent_iff_cluster_infinite.mp hx) (hall x)
  have hcomplZero : longRangeMeasure p longRangeAllComponentsFiniteEventᶜ = 0 := by
    rw [hcompl]
    exact measure_iUnion_null fun x ↦
      longRangeMeasure_percolationEvent_eq_zero_of_meanDegree_le_one p hmean x
  have hrealCompl : (longRangeMeasure p).real longRangeAllComponentsFiniteEventᶜ = 0 := by
    simp [Measure.real, hcomplZero]
  rw [probReal_compl_eq_one_sub measurableSet_longRangeAllComponentsFiniteEvent] at hrealCompl
  linarith

end Percolation
