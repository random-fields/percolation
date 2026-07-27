import Percolation.Bernoulli.StochasticDomination
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Sequential domination on finite Boolean cubes

This file isolates the finite algebra behind Grimmett's criterion (7.64).  A probability mass on
Boolean strings is exposed one coordinate at a time.  If the conditional mass of a `true` bit is
at least `p` after every exact prefix history (in the ratio-free form), then every increasing
event is at least as likely as under iid Bernoulli density `p`.

The formulation deliberately multiplies by the history mass.  It therefore remains meaningful
on null histories and is the finite kernel used later for the countable site-exploration law.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped unitInterval

/-- Coordinatewise order on Boolean strings, written in the direction relevant to open sites. -/
def BoolVectorLE {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ i, x i = true → y i = true

/-- An event on Boolean strings is increasing for coordinatewise inclusion. -/
def IsIncreasingBoolEvent {n : ℕ} (A : Set (Fin n → Bool)) : Prop :=
  ∀ ⦃x y⦄, BoolVectorLE x y → x ∈ A → y ∈ A

/-- The mass assigned by `w` to the configurations in `A`. -/
noncomputable def boolEventMass {n : ℕ} (w : (Fin n → Bool) → ℝ)
    (A : Set (Fin n → Bool)) : ℝ :=
  ∑ x, A.indicator w x

/-- Restriction of a Boolean string to its first `i` coordinates. -/
def boolPrefix {n i : ℕ} (hi : i ≤ n) (x : Fin n → Bool) : Fin i → Bool :=
  fun j ↦ x (Fin.castLE hi j)

/-- Mass of an exact length-`i` prefix history. -/
def boolPrefixMass {n i : ℕ} (w : (Fin n → Bool) → ℝ) (hi : i ≤ n)
    (s : Fin i → Bool) : ℝ :=
  ∑ x, if boolPrefix hi x = s then w x else 0

/-- Mass of an exact prefix history followed by an open next coordinate. -/
def boolPrefixOpenMass {n i : ℕ} (w : (Fin n → Bool) → ℝ) (hi : i < n)
    (s : Fin i → Bool) : ℝ :=
  ∑ x, if boolPrefix hi.le x = s ∧ x ⟨i, hi⟩ = true then w x else 0

/-- Ratio-free sequential lower bound.  The usual conditional statement is recovered whenever
the prefix history has positive mass. -/
def HasSequentialLowerBound {n : ℕ} (w : (Fin n → Bool) → ℝ) (p : ℝ) : Prop :=
  ∀ i (hi : i < n) (s : Fin i → Bool),
    p * boolPrefixMass w hi.le s ≤ boolPrefixOpenMass w hi s

/-- Marginalize the final Boolean coordinate. -/
def boolInitMass {n : ℕ} (w : (Fin (n + 1) → Bool) → ℝ) (s : Fin n → Bool) : ℝ :=
  w (Fin.snoc s true) + w (Fin.snoc s false)

/-- Every sum over length `n+1` Boolean strings splits according to its last bit. -/
theorem sum_boolVector_snoc {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, F x = ∑ s : Fin n → Bool, (F (Fin.snoc s true) + F (Fin.snoc s false)) := by
  calc
    ∑ x, F x = ∑ z : Bool × (Fin n → Bool), F ((Fin.snocEquiv fun _ ↦ Bool) z) :=
      (Equiv.sum_comp (Fin.snocEquiv fun _ ↦ Bool) F).symm
    _ = ∑ b : Bool, ∑ s : Fin n → Bool, F (Fin.snoc s b) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = (∑ s : Fin n → Bool, F (Fin.snoc s true)) +
        ∑ s : Fin n → Bool, F (Fin.snoc s false) := by
      rw [Fintype.sum_bool]
    _ = _ := by rw [← Finset.sum_add_distrib]

@[simp]
theorem boolPrefix_snoc_castSucc {n i : ℕ} (hi : i ≤ n) (s : Fin n → Bool) (b : Bool) :
    boolPrefix (hi.trans (Nat.le_succ n)) (Fin.snoc s b) = boolPrefix hi s := by
  funext j
  have hj : Fin.castLE (hi.trans (Nat.le_succ n)) j =
      Fin.castSucc (Fin.castLE hi j) := Fin.ext rfl
  rw [boolPrefix, boolPrefix, hj, Fin.snoc_castSucc]

@[simp]
theorem boolPrefix_snoc_full {n : ℕ} (s : Fin n → Bool) (b : Bool) :
    boolPrefix (Nat.le_succ n) (Fin.snoc s b) = s := by
  funext j
  have hj : Fin.castLE (Nat.le_succ n) j = Fin.castSucc j := Fin.ext rfl
  rw [boolPrefix, hj, Fin.snoc_castSucc]

@[simp]
theorem boolPrefix_self {n : ℕ} (s : Fin n → Bool) :
    boolPrefix (le_refl n) s = s := by
  funext j
  have hj : Fin.castLE (le_refl n) j = j := Fin.ext rfl
  rw [boolPrefix, hj]

@[simp]
theorem boolSnoc_natLast {n : ℕ} (s : Fin n → Bool) (b : Bool) :
    (Fin.snoc s b : Fin (n + 1) → Bool) ⟨n, Nat.lt_succ_self n⟩ = b := by
  have hidx : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
  rw [hidx]
  exact @Fin.snoc_last n (fun _ : Fin (n + 1) ↦ Bool) b s

theorem boolPrefixMass_init {n i : ℕ} (w : (Fin (n + 1) → Bool) → ℝ)
    (hi : i ≤ n) (s : Fin i → Bool) :
    boolPrefixMass (boolInitMass w) hi s =
      boolPrefixMass w (hi.trans (Nat.le_succ n)) s := by
  rw [boolPrefixMass, boolPrefixMass, sum_boolVector_snoc]
  apply Finset.sum_congr rfl
  intro x _hx
  have hprefix (b : Bool) :
      boolPrefix (hi.trans (Nat.le_succ n)) (Fin.snoc x b) = boolPrefix hi x :=
    boolPrefix_snoc_castSucc hi x b
  rw [hprefix true, hprefix false]
  simp only [boolInitMass]
  split_ifs <;> ring

theorem boolPrefixOpenMass_init {n i : ℕ} (w : (Fin (n + 1) → Bool) → ℝ)
    (hi : i < n) (s : Fin i → Bool) :
    boolPrefixOpenMass (boolInitMass w) hi s =
      boolPrefixOpenMass (n := n + 1) w (hi.trans (Nat.lt_succ_self n)) s := by
  rw [boolPrefixOpenMass, boolPrefixOpenMass, sum_boolVector_snoc]
  apply Finset.sum_congr rfl
  intro x _hx
  have hprefix (b : Bool) :
      boolPrefix (hi.le.trans (Nat.le_succ n)) (Fin.snoc x b) = boolPrefix hi.le x :=
    boolPrefix_snoc_castSucc hi.le x b
  rw [hprefix true, hprefix false]
  simp only [boolInitMass]
  have hcast (b : Bool) :
      (Fin.snoc x b : Fin (n + 1) → Bool) ⟨i, hi.trans (Nat.lt_succ_self n)⟩ =
        x ⟨i, hi⟩ := by
    have hj : (⟨i, hi.trans (Nat.lt_succ_self n)⟩ : Fin (n + 1)) =
        Fin.castSucc ⟨i, hi⟩ := Fin.ext rfl
    rw [hj, Fin.snoc_castSucc]
  rw [hcast true, hcast false]
  split_ifs <;> ring

/-- Sequential lower bounds survive removal of the last coordinate. -/
theorem HasSequentialLowerBound.init {n : ℕ} {w : (Fin (n + 1) → Bool) → ℝ} {p : ℝ}
    (h : HasSequentialLowerBound w p) : HasSequentialLowerBound (boolInitMass w) p := by
  intro i hi s
  rw [boolPrefixMass_init, boolPrefixOpenMass_init]
  exact h i (hi.trans (Nat.lt_succ_self n)) s

theorem boolPrefixMass_last {n : ℕ} (w : (Fin (n + 1) → Bool) → ℝ)
    (s : Fin n → Bool) :
    boolPrefixMass w (Nat.le_succ n) s = boolInitMass w s := by
  classical
  rw [boolPrefixMass, sum_boolVector_snoc]
  rw [Finset.sum_add_distrib]
  have hprefix (x : Fin n → Bool) (b : Bool) :
      boolPrefix (Nat.le_succ n) (Fin.snoc x b) = x := boolPrefix_snoc_full x b
  simp_rw [hprefix]
  simp only [boolInitMass]
  change
    (∑ x, if x = s then w (Fin.snoc x true) else 0) +
      (∑ x, if x = s then w (Fin.snoc x false) else 0) = _
  have hsum (b : Bool) :
      (∑ x, if x = s then w (Fin.snoc x b) else 0) = w (Fin.snoc s b) := by
    calc
      (∑ x, if x = s then w (Fin.snoc x b) else 0) =
          (if s = s then w (Fin.snoc s b) else 0) := by
        apply Finset.sum_eq_single s
        · intro x _hx hxs
          simp [hxs]
        · simp
      _ = w (Fin.snoc s b) := by simp
  rw [hsum true, hsum false]

theorem boolPrefixOpenMass_last {n : ℕ} (w : (Fin (n + 1) → Bool) → ℝ)
    (s : Fin n → Bool) :
    boolPrefixOpenMass w (Nat.lt_succ_self n) s = w (Fin.snoc s true) := by
  rw [boolPrefixOpenMass, sum_boolVector_snoc]
  simp

/-! ### Increasing events and the finite comparison theorem -/

/-- Product Bernoulli mass on a Boolean string. -/
def iidBoolWeight (n : ℕ) (p : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then p else 1 - p

@[simp]
theorem iidBoolWeight_snoc_true {n : ℕ} (p : ℝ) (x : Fin n → Bool) :
    iidBoolWeight (n + 1) p (Fin.snoc x true) = iidBoolWeight n p x * p := by
  rw [iidBoolWeight, Fin.prod_univ_castSucc]
  simp [iidBoolWeight]

@[simp]
theorem iidBoolWeight_snoc_false {n : ℕ} (p : ℝ) (x : Fin n → Bool) :
    iidBoolWeight (n + 1) p (Fin.snoc x false) = iidBoolWeight n p x * (1 - p) := by
  rw [iidBoolWeight, Fin.prod_univ_castSucc]
  simp [iidBoolWeight]

@[simp]
theorem boolInitMass_iidBoolWeight {n : ℕ} (p : ℝ) :
    boolInitMass (iidBoolWeight (n + 1) p) = iidBoolWeight n p := by
  funext x
  simp [boolInitMass]
  ring

theorem iidBoolWeight_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Fin n → Bool) : 0 ≤ iidBoolWeight n p x := by
  apply Finset.prod_nonneg
  intro i _hi
  by_cases hxi : x i = true
  · simp [hxi, hp0]
  · have : x i = false := Bool.eq_false_of_not_eq_true hxi
    simp [this]
    linarith

/-- Removing the last bit from an event, with the removed bit fixed to `b`. -/
def boolInitSection {n : ℕ} (A : Set (Fin (n + 1) → Bool)) (b : Bool) :
    Set (Fin n → Bool) :=
  {x | Fin.snoc x b ∈ A}

theorem boolVectorLE_snoc {n : ℕ} {x y : Fin n → Bool} (hxy : BoolVectorLE x y)
    (b : Bool) : BoolVectorLE (Fin.snoc x b) (Fin.snoc y b) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using hxy j

theorem boolVectorLE_snoc_false_true {n : ℕ} (x : Fin n → Bool) :
    BoolVectorLE (Fin.snoc x false) (Fin.snoc x true) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · simp

theorem IsIncreasingBoolEvent.initSection {n : ℕ} {A : Set (Fin (n + 1) → Bool)}
    (hA : IsIncreasingBoolEvent A) (b : Bool) :
    IsIncreasingBoolEvent (boolInitSection A b) := by
  intro x y hxy hx
  exact hA (boolVectorLE_snoc hxy b) hx

theorem IsIncreasingBoolEvent.initSection_false_subset_true {n : ℕ}
    {A : Set (Fin (n + 1) → Bool)} (hA : IsIncreasingBoolEvent A) :
    boolInitSection A false ⊆ boolInitSection A true := by
  intro x hx
  exact hA (boolVectorLE_snoc_false_true x) hx

/-- Split an event mass according to the final Boolean coordinate. -/
theorem boolEventMass_snoc {n : ℕ} (w : (Fin (n + 1) → Bool) → ℝ)
    (A : Set (Fin (n + 1) → Bool)) :
    boolEventMass w A =
      ∑ x : Fin n → Bool,
        ((boolInitSection A true).indicator (fun _ ↦ w (Fin.snoc x true)) x +
          (boolInitSection A false).indicator (fun _ ↦ w (Fin.snoc x false)) x) := by
  classical
  rw [boolEventMass, sum_boolVector_snoc]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [boolInitSection]
  by_cases ht : Fin.snoc x true ∈ A <;> by_cases hf : Fin.snoc x false ∈ A <;>
    simp [Set.indicator, ht, hf]

/-- One final sequential step compares the event mass with the corresponding mixture of its two
initial sections. -/
theorem boolEventMass_step_lowerBound {n : ℕ} {w : (Fin (n + 1) → Bool) → ℝ}
    {p : ℝ} (hseq : HasSequentialLowerBound w p) {A : Set (Fin (n + 1) → Bool)}
    (hA : IsIncreasingBoolEvent A) :
    (1 - p) * boolEventMass (boolInitMass w) (boolInitSection A false) +
        p * boolEventMass (boolInitMass w) (boolInitSection A true) ≤
      boolEventMass w A := by
  classical
  have hlast (x : Fin n → Bool) :
      p * boolInitMass w x ≤ w (Fin.snoc x true) := by
    simpa [boolPrefixMass_last, boolPrefixOpenMass_last] using
      hseq n (Nat.lt_succ_self n) x
  rw [boolEventMass_snoc]
  simp only [boolEventMass, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hf : x ∈ boolInitSection A false
  · have ht : x ∈ boolInitSection A true :=
      hA.initSection_false_subset_true hf
    simp [Set.indicator_of_mem hf, Set.indicator_of_mem ht]
    simp [boolInitMass]
    ring_nf
    exact le_rfl
  · by_cases ht : x ∈ boolInitSection A true
    · simp [Set.indicator_of_notMem hf, Set.indicator_of_mem ht]
      exact hlast x
    · simp [Set.indicator_of_notMem hf, Set.indicator_of_notMem ht]

/-- Total mass is preserved when the final coordinate is marginalized. -/
theorem sum_boolInitMass {n : ℕ} (w : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, boolInitMass w x = ∑ x, w x := by
  rw [sum_boolVector_snoc]
  rfl

theorem boolInitMass_nonneg {n : ℕ} {w : (Fin (n + 1) → Bool) → ℝ}
    (hw : ∀ x, 0 ≤ w x) (x : Fin n → Bool) : 0 ≤ boolInitMass w x := by
  exact add_nonneg (hw _) (hw _)

/-- The iid event mass obeys the usual last-coordinate recursion. -/
theorem boolEventMass_iid_snoc {n : ℕ} (p : ℝ) (A : Set (Fin (n + 1) → Bool)) :
    boolEventMass (iidBoolWeight (n + 1) p) A =
      (1 - p) * boolEventMass (iidBoolWeight n p) (boolInitSection A false) +
        p * boolEventMass (iidBoolWeight n p) (boolInitSection A true) := by
  classical
  rw [boolEventMass_snoc]
  simp only [boolEventMass, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hf : x ∈ boolInitSection A false <;>
    by_cases ht : x ∈ boolInitSection A true <;>
      simp [Set.indicator, hf, ht] <;> ring

/-- **Finite sequential domination (Grimmett (7.64), finite kernel).** Every increasing event
has at least its iid Bernoulli-`p` mass.  The assumptions are purely finite and ratio-free. -/
theorem iidBoolEventMass_le_of_hasSequentialLowerBound :
    ∀ {n : ℕ} {w : (Fin n → Bool) → ℝ} {p : ℝ},
      0 ≤ p → p ≤ 1 → (∀ x, 0 ≤ w x) → (∑ x, w x = 1) →
      HasSequentialLowerBound w p →
      ∀ {A : Set (Fin n → Bool)}, IsIncreasingBoolEvent A →
        boolEventMass (iidBoolWeight n p) A ≤ boolEventMass w A := by
  intro n
  induction n with
  | zero =>
      intro w p hp0 hp1 hw0 hsum _hseq A _hA
      have hfun : ∀ x : Fin 0 → Bool, x = Fin.elim0 := fun x ↦ funext fun i ↦ Fin.elim0 i
      have hw : w Fin.elim0 = 1 := by simpa [hfun] using hsum
      by_cases hA0 : (Fin.elim0 : Fin 0 → Bool) ∈ A
      · simp [boolEventMass, Set.indicator_of_mem hA0, iidBoolWeight, hfun, hw]
      · simp [boolEventMass, Set.indicator_of_notMem hA0, hfun]
  | succ n ih =>
      intro w p hp0 hp1 hw0 hsum hseq A hA
      have hinit0 : ∀ x, 0 ≤ boolInitMass w x := boolInitMass_nonneg hw0
      have hinitsum : ∑ x, boolInitMass w x = 1 := by
        rw [sum_boolInitMass, hsum]
      have ihFalse := ih hp0 hp1 hinit0 hinitsum hseq.init (hA.initSection false)
      have ihTrue := ih hp0 hp1 hinit0 hinitsum hseq.init (hA.initSection true)
      have hmix :
          (1 - p) * boolEventMass (iidBoolWeight n p) (boolInitSection A false) +
              p * boolEventMass (iidBoolWeight n p) (boolInitSection A true) ≤
            (1 - p) * boolEventMass (boolInitMass w) (boolInitSection A false) +
              p * boolEventMass (boolInitMass w) (boolInitSection A true) := by
        gcongr
      calc
        boolEventMass (iidBoolWeight (n + 1) p) A =
            (1 - p) * boolEventMass (iidBoolWeight n p) (boolInitSection A false) +
              p * boolEventMass (iidBoolWeight n p) (boolInitSection A true) := by
                exact boolEventMass_iid_snoc p A
        _ ≤ _ := hmix
        _ ≤ boolEventMass w A := boolEventMass_step_lowerBound hseq hA

/-! ### Measure-level finite criterion -/

/-- The canonical equivalence between subsets of `Fin n` and Boolean strings. -/
noncomputable def finiteSetBoolEquiv (n : ℕ) : Set (Fin n) ≃ (Fin n → Bool) where
  toFun ω i := @decide (i ∈ ω) (Classical.propDecidable _)
  invFun x := {i | x i = true}
  left_inv ω := by ext i; simp
  right_inv x := by
    funext i
    generalize h : x i = b
    cases b <;> simp [h]

@[simp]
theorem mem_finiteSetBoolEquiv_symm {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    i ∈ (finiteSetBoolEquiv n).symm x ↔ x i = true := Iff.rfl

/-- Atomic mass of a finite site law, indexed by its Boolean encoding. -/
noncomputable def finiteSetBoolMass {n : ℕ} (μ : Measure (Set (Fin n)))
    (x : Fin n → Bool) : ℝ :=
  μ.real {(finiteSetBoolEquiv n).symm x}

/-- Measure-level form of the ratio-free finite prefix hypothesis. -/
def HasFiniteSequentialLowerBound {n : ℕ} (μ : Measure (Set (Fin n))) (p : ℝ) : Prop :=
  HasSequentialLowerBound (finiteSetBoolMass μ) p

/-- On a finite measurable space, a set's real mass is the sum of its singleton masses. -/
theorem measureReal_eq_sum_indicator_singleton {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) :
    μ.real A = ∑ x, A.indicator (fun x ↦ μ.real {x}) x := by
  classical
  let F : Finset X := A.toFinite.toFinset
  have hF : (F : Set X) = A := Set.Finite.coe_toFinset A.toFinite
  have hsum := sum_measureReal_singleton (μ := μ) F
  rw [hF] at hsum
  rw [← hsum]
  calc
    (∑ x ∈ F, μ.real {x}) =
        ∑ x ∈ F, A.indicator (fun x ↦ μ.real {x}) x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Set.indicator_of_mem]
      simpa [F] using hx
    _ = ∑ x, A.indicator (fun x ↦ μ.real {x}) x := by
      apply Finset.sum_subset (Finset.subset_univ F)
      intro x _hx hxF
      rw [Set.indicator_of_notMem]
      simpa [F] using hxF

/-- Pull an event on finite subsets back to Boolean strings. -/
def boolEventOfSetEvent {n : ℕ} (A : Set (Set (Fin n))) : Set (Fin n → Bool) :=
  {x | (finiteSetBoolEquiv n).symm x ∈ A}

theorem IsIncreasingEvent.isIncreasingBoolEvent {n : ℕ} {A : Set (Set (Fin n))}
    (hA : IsIncreasingEvent A) : IsIncreasingBoolEvent (boolEventOfSetEvent A) := by
  intro x y hxy hx
  apply hA _ hx
  intro i hi
  rw [mem_finiteSetBoolEquiv_symm] at hi ⊢
  exact hxy i hi

theorem boolEventMass_finiteSetBoolMass {n : ℕ} (μ : Measure (Set (Fin n)))
    [IsProbabilityMeasure μ] (A : Set (Set (Fin n))) :
    boolEventMass (finiteSetBoolMass μ) (boolEventOfSetEvent A) = μ.real A := by
  classical
  let e := (finiteSetBoolEquiv n).symm
  let g : Set (Fin n) → ℝ := fun ω ↦ A.indicator (fun ξ ↦ μ.real {ξ}) ω
  have hsum := Equiv.sum_comp e g
  rw [measureReal_eq_sum_indicator_singleton μ A]
  simpa [boolEventMass, finiteSetBoolMass, boolEventOfSetEvent, e, g] using hsum

theorem finiteSetBoolMass_setBernoulli {n : ℕ} (p : I) :
    finiteSetBoolMass (setBer((Set.univ : Set (Fin n)), p)) =
      iidBoolWeight n (p : ℝ) := by
  funext x
  rw [finiteSetBoolMass, setBernoulli_real_singleton p (by simp) Set.finite_univ]
  rw [show ((finiteSetBoolEquiv n).symm x).ncard =
      (Finset.univ.filter fun i ↦ x i = true).card by
    rw [Set.ncard_eq_toFinset_card ((finiteSetBoolEquiv n).symm x)
      ((finiteSetBoolEquiv n).symm x).toFinite]
    congr 1
    ext i
    simp]
  rw [show ((Set.univ : Set (Fin n)) \ (finiteSetBoolEquiv n).symm x).ncard =
      (Finset.univ.filter fun i ↦ x i = false).card by
    rw [Set.ncard_eq_toFinset_card _
      (Set.univ \ (finiteSetBoolEquiv n).symm x).toFinite]
    congr 1
    ext i
    cases x i <;> simp]
  rw [← Finset.prod_const, ← Finset.prod_const]
  change
    (∏ _i ∈ Finset.univ.filter (fun i ↦ x i = true), (p : ℝ)) *
        ∏ _i ∈ Finset.univ.filter (fun i ↦ x i = false), (1 - p : ℝ) =
      iidBoolWeight n (p : ℝ) x
  rw [iidBoolWeight]
  calc
    (∏ _i ∈ Finset.univ.filter (fun i ↦ x i = true), (p : ℝ)) *
        ∏ _i ∈ Finset.univ.filter (fun i ↦ x i = false), (1 - p : ℝ) =
      (∏ i ∈ Finset.univ.filter (fun i ↦ x i = true),
          (if x i then (p : ℝ) else 1 - p)) *
        ∏ i ∈ Finset.univ.filter (fun i ↦ ¬x i = true),
          (if x i then (p : ℝ) else 1 - p) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp [hi.2]
      · apply Finset.prod_bij (fun i _ ↦ i)
        · intro i hi
          simp only [Finset.mem_filter] at hi ⊢
          rcases hi with ⟨_, hi⟩
          simp [hi]
        · intro
          simp
        · intro
          simp
        · intro i hi
          simp only [Finset.mem_filter] at hi
          rcases hi with ⟨_, hi⟩
          simp [hi]
    _ = _ := Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i ↦ x i = true) (fun i ↦ if x i then (p : ℝ) else 1 - p)

/-- **Finite sequential criterion (7.64), event form.** -/
theorem finiteSequentialLowerBound_measureReal_le {n : ℕ} (μ : Measure (Set (Fin n)))
    [IsProbabilityMeasure μ] (p : I) (hseq : HasFiniteSequentialLowerBound μ (p : ℝ))
    {A : Set (Set (Fin n))} (hA : IsIncreasingEvent A) :
    setBer((Set.univ : Set (Fin n)), p).real A ≤ μ.real A := by
  have hmass0 : ∀ x, 0 ≤ finiteSetBoolMass μ x := fun _ ↦ measureReal_nonneg
  have hmassSum : ∑ x, finiteSetBoolMass μ x = 1 := by
    let e := (finiteSetBoolEquiv n).symm
    have hsum := Equiv.sum_comp e (fun ω : Set (Fin n) ↦ μ.real {ω})
    calc
      ∑ x, finiteSetBoolMass μ x = ∑ ω : Set (Fin n), μ.real {ω} := by
        simpa [finiteSetBoolMass, e] using hsum
      _ = μ.real Set.univ := by
        rw [measureReal_eq_sum_indicator_singleton μ Set.univ]
        simp
      _ = 1 := probReal_univ
  have hfinite := iidBoolEventMass_le_of_hasSequentialLowerBound p.2.1 p.2.2
    hmass0 hmassSum hseq hA.isIncreasingBoolEvent
  rw [← finiteSetBoolMass_setBernoulli p,
    boolEventMass_finiteSetBoolMass, boolEventMass_finiteSetBoolMass] at hfinite
  exact hfinite

/-- **Finite sequential criterion (7.64), exact expectation form.** -/
theorem finiteSequentialLowerBound_stochasticallyDominates {n : ℕ}
    (μ : Measure (Set (Fin n))) [IsProbabilityMeasure μ] (p : I)
    (hseq : HasFiniteSequentialLowerBound μ (p : ℝ)) :
    StochasticallyDominates μ setBer((Set.univ : Set (Fin n)), p) := by
  rw [stochasticallyDominates_iff_measureReal_le]
  intro A _hAm hA
  exact finiteSequentialLowerBound_measureReal_le μ p hseq hA

end Percolation
