import Percolation.Critical.AdaptiveAnswerHistory

/-!
# Finite sequential domination for chronological adaptive queries

This is the finite decision-tree core missing from the source-facing proof of Grimmett Lemma
7.24.  A query rule chooses the next vertex from the literal preceding history.  The leaf weight
of a Boolean answer vector is the probability of its exact adaptive history.  Ratio-free lower
bounds for every queried extension imply `HasSequentialLowerBound` for these leaf weights, so the
existing finite Bernoulli comparison theorem applies without pretending that the entire explored
cluster is an iid-dominated site field.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {V Omega : Type*}

/-- Run a deterministic query rule on a list of chronological Boolean answers, starting from an
already fixed history. -/
def adaptiveQueryHistoryFrom
    (query : List (V × Bool) → V) :
    List (V × Bool) → List Bool → List (V × Bool)
  | history, [] => history
  | history, b :: bits =>
      adaptiveQueryHistoryFrom query
        (history ++ [(query history, b)]) bits

/-- Chronological vertex/answer history generated from a Boolean answer list. -/
def adaptiveQueryHistory
    (query : List (V × Bool) → V) (bits : List Bool) : List (V × Bool) :=
  adaptiveQueryHistoryFrom query [] bits

@[simp]
theorem length_adaptiveQueryHistoryFrom
    (query : List (V × Bool) → V) (history : List (V × Bool)) (bits : List Bool) :
    (adaptiveQueryHistoryFrom query history bits).length = history.length + bits.length := by
  induction bits generalizing history with
  | nil => simp [adaptiveQueryHistoryFrom]
  | cons b bits ih =>
      simp only [adaptiveQueryHistoryFrom, ih, List.length_append, List.length_cons,
        List.length_nil]
      omega

@[simp]
theorem length_adaptiveQueryHistory
    (query : List (V × Bool) → V) (bits : List Bool) :
    (adaptiveQueryHistory query bits).length = bits.length := by
  simp [adaptiveQueryHistory]

@[simp]
theorem adaptiveQueryHistoryFrom_nil
    (query : List (V × Bool) → V) (history : List (V × Bool)) :
    adaptiveQueryHistoryFrom query history [] = history :=
  rfl

theorem adaptiveQueryHistoryFrom_append
    (query : List (V × Bool) → V)
    (history : List (V × Bool)) (bits tail : List Bool) :
    adaptiveQueryHistoryFrom query history (bits ++ tail) =
      adaptiveQueryHistoryFrom query
        (adaptiveQueryHistoryFrom query history bits) tail := by
  induction bits generalizing history with
  | nil => rfl
  | cons b bits ih =>
      simp only [List.cons_append, adaptiveQueryHistoryFrom]
      exact ih (history ++ [(query history, b)])

theorem adaptiveQueryHistoryFrom_append_singleton
    (query : List (V × Bool) → V)
    (history : List (V × Bool)) (bits : List Bool) (b : Bool) :
    adaptiveQueryHistoryFrom query history (bits ++ [b]) =
      adaptiveQueryHistoryFrom query history bits ++
        [(query (adaptiveQueryHistoryFrom query history bits), b)] := by
  rw [adaptiveQueryHistoryFrom_append]
  rfl

theorem adaptiveQueryHistory_append_singleton
    (query : List (V × Bool) → V) (bits : List Bool) (b : Bool) :
    adaptiveQueryHistory query (bits ++ [b]) =
      adaptiveQueryHistory query bits ++
        [(query (adaptiveQueryHistory query bits), b)] :=
  adaptiveQueryHistoryFrom_append_singleton query [] bits b

theorem list_ofFn_snoc {n : ℕ} (bits : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc bits b) = List.ofFn bits ++ [b] := by
  rw [← Fin.append_right_eq_snoc bits (fun _ : Fin 1 => b), List.ofFn_fin_append]
  simp

theorem adaptiveQueryHistory_ofFn_snoc
    (query : List (V × Bool) → V) {n : ℕ}
    (bits : Fin n → Bool) (b : Bool) :
    adaptiveQueryHistory query (List.ofFn (Fin.snoc bits b)) =
      adaptiveQueryHistory query (List.ofFn bits) ++
        [(query (adaptiveQueryHistory query (List.ofFn bits)), b)] := by
  rw [list_ofFn_snoc, adaptiveQueryHistory_append_singleton]

/-- Atomic decision-tree weight of a finite chronological Boolean answer vector. -/
noncomputable def adaptiveQueryWeight
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) (n : ℕ)
    (bits : Fin n → Bool) : ℝ :=
  mu.real (adaptiveAnswerHistoryEvent answer
    (adaptiveQueryHistory query (List.ofFn bits)))

/-- Marginalizing the last answer of the depth-`n+1` decision tree gives the depth-`n` tree. -/
theorem boolInitMass_adaptiveQueryWeight
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V) (n : ℕ) :
    boolInitMass (adaptiveQueryWeight mu answer query (n + 1)) =
      adaptiveQueryWeight mu answer query n := by
  funext bits
  let history := adaptiveQueryHistory query (List.ofFn bits)
  have hpartition := measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
    mu hanswer history (query history)
  simp only [boolInitMass, adaptiveQueryWeight]
  rw [adaptiveQueryHistory_ofFn_snoc, adaptiveQueryHistory_ofFn_snoc]
  exact hpartition

theorem adaptiveQueryWeight_nonneg
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) (n : ℕ) (bits : Fin n → Bool) :
    0 ≤ adaptiveQueryWeight mu answer query n bits :=
  measureReal_nonneg

/-- The exact depth-`n` history cells have total probability one. -/
theorem sum_adaptiveQueryWeight_eq_one
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V) :
    ∀ n, ∑ bits, adaptiveQueryWeight mu answer query n bits = 1 := by
  intro n
  induction n with
  | zero =>
      simp [adaptiveQueryWeight, adaptiveQueryHistory, probReal_univ]
  | succ n ih =>
      let weight := adaptiveQueryWeight mu answer query (n + 1)
      calc
        (∑ bits, adaptiveQueryWeight mu answer query (n + 1) bits) =
            ∑ bits, boolInitMass weight bits := by
          exact (sum_boolInitMass weight).symm
        _ = ∑ bits, adaptiveQueryWeight mu answer query n bits := by
          rw [boolInitMass_adaptiveQueryWeight mu hanswer query n]
        _ = 1 := ih

/-- Exact ratio-free Bernoulli extensions along the histories actually generated by `query`
identify every adaptive leaf mass with the ordinary iid Boolean weight.  No premise is imposed
on malformed histories whose stored query coordinates disagree with `query`. -/
theorem adaptiveQueryWeight_eq_iidBoolWeight_of_exactAlong
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V) (q : ℝ)
    (hexact : ∀ bits : List Bool,
      mu.real (adaptiveAnswerHistoryEvent answer
          (adaptiveQueryHistory query bits ++
            [(query (adaptiveQueryHistory query bits), true)])) =
        q * mu.real (adaptiveAnswerHistoryEvent answer
          (adaptiveQueryHistory query bits))) :
    ∀ (n : ℕ) (bits : Fin n → Bool),
      adaptiveQueryWeight mu answer query n bits = iidBoolWeight n q bits := by
  intro n
  induction n with
  | zero =>
      intro bits
      simp [adaptiveQueryWeight, adaptiveQueryHistory, iidBoolWeight, probReal_univ]
  | succ n ih =>
      intro bits
      let initBits := Fin.init bits
      let b := bits (Fin.last n)
      have hbits : Fin.snoc initBits b = bits := Fin.snoc_init_self bits
      let history := adaptiveQueryHistory query (List.ofFn initBits)
      have hhistory : adaptiveQueryHistory query (List.ofFn bits) =
          history ++ [(query history, b)] := by
        rw [← hbits, adaptiveQueryHistory_ofFn_snoc]
      have hinitBits := ih initBits
      have htrue := hexact (List.ofFn initBits)
      have htrue' :
          mu.real (adaptiveAnswerHistoryEvent answer
              (history ++ [(query history, true)])) =
            q * mu.real (adaptiveAnswerHistoryEvent answer history) := by
        simpa [history] using htrue
      have hpartition := measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
        mu hanswer history (query history)
      have hfalse :
          mu.real (adaptiveAnswerHistoryEvent answer
              (history ++ [(query history, false)])) =
            (1 - q) * mu.real (adaptiveAnswerHistoryEvent answer history) := by
        linarith
      cases hb : b
      · simp only [hb] at hhistory hbits ⊢
        rw [adaptiveQueryWeight, hhistory, hfalse, ← hbits,
          iidBoolWeight_snoc_false]
        have hbase :
            mu.real (adaptiveAnswerHistoryEvent answer history) =
              iidBoolWeight n q initBits := by
          simpa [adaptiveQueryWeight, history] using hinitBits
        calc
          (1 - q) * mu.real (adaptiveAnswerHistoryEvent answer history) =
              (1 - q) * iidBoolWeight n q initBits :=
            congrArg (fun x : ℝ => (1 - q) * x) hbase
          _ = iidBoolWeight n q initBits * (1 - q) := mul_comm _ _
      · simp only [hb] at hhistory hbits ⊢
        rw [adaptiveQueryWeight, hhistory, htrue', ← hbits,
          iidBoolWeight_snoc_true]
        have hbase :
            mu.real (adaptiveAnswerHistoryEvent answer history) =
              iidBoolWeight n q initBits := by
          simpa [adaptiveQueryWeight, history] using hinitBits
        calc
          q * mu.real (adaptiveAnswerHistoryEvent answer history) =
              q * iidBoolWeight n q initBits :=
            congrArg (fun x : ℝ => q * x) hbase
          _ = iidBoolWeight n q initBits * q := mul_comm _ _

/-- Build a full sequential lower bound from the corresponding initial-tree bound and the last
query inequality. -/
theorem hasSequentialLowerBound_succ_of_init_last
    {n : ℕ} {weight : (Fin (n + 1) → Bool) → ℝ} {q : ℝ}
    (hinit : HasSequentialLowerBound (boolInitMass weight) q)
    (hlast : ∀ bits : Fin n → Bool,
      q * boolInitMass weight bits ≤ weight (Fin.snoc bits true)) :
    HasSequentialLowerBound weight q := by
  intro i hi bits
  by_cases hin : i = n
  · subst i
    simpa [boolPrefixMass_last, boolPrefixOpenMass_last] using hlast bits
  · have hi' : i < n := by omega
    rw [← boolPrefixMass_init weight hi'.le bits,
      ← boolPrefixOpenMass_init weight hi' bits]
    exact hinit i hi' bits

/-- Exact-history lower bounds imply the existing finite Boolean sequential criterion for every
decision-tree depth. -/
theorem adaptiveQueryWeight_hasSequentialLowerBound
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop) {q : ℝ}
    (hlower : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    (hquery : ∀ bits : List Bool,
      admissible (adaptiveQueryHistory query bits)
        (query (adaptiveQueryHistory query bits))) :
    ∀ n, HasSequentialLowerBound (adaptiveQueryWeight mu answer query n) q := by
  intro n
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      apply hasSequentialLowerBound_succ_of_init_last
      · simpa [boolInitMass_adaptiveQueryWeight mu hanswer query n] using ih
      · intro bits
        let history := adaptiveQueryHistory query (List.ofFn bits)
        have hstep := hlower history (query history) (hquery (List.ofFn bits))
        rw [boolInitMass_adaptiveQueryWeight mu hanswer query n]
        simp only [adaptiveQueryWeight]
        rw [adaptiveQueryHistory_ofFn_snoc]
        exact hstep

/-- Finite decision-tree comparison with iid Bernoulli answers. -/
theorem iidBoolEventMass_le_adaptiveQueryWeight
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop) (q : I)
    (hlower : HasAdaptiveAnswerLowerBoundOn mu answer admissible (q : ℝ))
    (hquery : ∀ bits : List Bool,
      admissible (adaptiveQueryHistory query bits)
        (query (adaptiveQueryHistory query bits)))
    {n : ℕ} {A : Set (Fin n → Bool)} (hA : IsIncreasingBoolEvent A) :
    boolEventMass (iidBoolWeight n (q : ℝ)) A ≤
      boolEventMass (adaptiveQueryWeight mu answer query n) A := by
  exact iidBoolEventMass_le_of_hasSequentialLowerBound q.2.1 q.2.2
    (adaptiveQueryWeight_nonneg mu answer query n)
    (sum_adaptiveQueryWeight_eq_one mu hanswer query n)
    (adaptiveQueryWeight_hasSequentialLowerBound mu hanswer query admissible hlower hquery n)
    hA

end AdaptiveSiteExploration

end Percolation
