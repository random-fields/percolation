import Percolation.Bernoulli.Increasing

/-!
# The finite cube model and the transfer pack

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.1 and the finite-volume computations
underlying §§2.2–2.5 (source id `grimmett-percolation-1999`).

Events and observables depending on a finite coordinate set `E` are governed by the finite
product measure on the cube `{0,1}^E`, realized here as the weighted sum over
`E.powerset`. This file sets up that finite model —

* `Percolation.finiteBernoulliWeight`/`finiteBernoulliWeightFamily` — the homogeneous and
  inhomogeneous product weights `p^{|s|}(1-p)^{|E|-|s|}` and `∏_{e∈s} q e ∏_{e∈E\s}(1-q e)`;
* `Percolation.finiteBernoulliExpectation`/`finiteBernoulliProbability` (and `…Family`
  variants) — expectations and probabilities on the finite cube, with `p : ℝ` so that
  calculus in `p` (Russo's formula) applies directly;
* `Percolation.finiteCylinder` — the cylinder event of the ambient space prescribing the
  trace on `E`;
* `Percolation.eventTrace`, `Percolation.IsIncreasingTrace` — traces of ambient events —

and proves the *transfer pack* connecting the finite model to the ambient measure
`setBer((Set.univ : Set ι), p)`:

* `Percolation.DependsOn.measurableSet` — a finitely supported event is measurable;
* `Percolation.DependsOnFun.integral_setBernoulli` — the integral of a finitely supported
  observable is its finite-cube expectation;
* `Percolation.DependsOn.setBernoulli_real_eq_finiteBernoulliProbability` — the probability
  of a finitely supported event is its finite-cube probability;
* support-enlargement invariance and the `bernoulliBondMeasure` specializations.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval

variable {ι : Type*}

/-! ### Weights -/

/-- Homogeneous Bernoulli weight of the trace `s` on the finite support `E`. -/
def finiteBernoulliWeight (E : Finset ι) (p : ℝ) (s : Finset ι) : ℝ :=
  p ^ s.card * (1 - p) ^ (E.card - s.card)

/-- Inhomogeneous Bernoulli weight with density `q e` at the coordinate `e`. This is the
finite-volume form of Grimmett's multiparameter measure `P_𝐩` (p. 44). -/
def finiteBernoulliWeightFamily [DecidableEq ι] (E : Finset ι) (q : ι → ℝ)
    (s : Finset ι) : ℝ :=
  (∏ e ∈ s, q e) * ∏ e ∈ E \ s, (1 - q e)

theorem finiteBernoulliWeightFamily_const [DecidableEq ι] {E s : Finset ι} (hs : s ⊆ E)
    (p : ℝ) :
    finiteBernoulliWeightFamily E (fun _ => p) s = finiteBernoulliWeight E p s := by
  rw [finiteBernoulliWeightFamily, finiteBernoulliWeight, Finset.prod_const,
    Finset.prod_const, Finset.card_sdiff_of_subset hs]

theorem finiteBernoulliWeight_nonneg {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) : 0 ≤ finiteBernoulliWeight E p s :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

theorem finiteBernoulliWeight_pos {E : Finset ι} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (s : Finset ι) : 0 < finiteBernoulliWeight E p s :=
  mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)

theorem finiteBernoulliWeightFamily_nonneg [DecidableEq ι] {E : Finset ι} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1) {s : Finset ι} (hs : s ⊆ E) :
    0 ≤ finiteBernoulliWeightFamily E q s :=
  mul_nonneg (Finset.prod_nonneg fun e he => hq0 e (hs he))
    (Finset.prod_nonneg fun e he => by
      have := hq1 e (Finset.mem_sdiff.mp he).1
      linarith)

/-- The weights over the powerset of `E` sum to one — the binomial identity
`∑_s ∏_{e∈s} q e ∏_{e∈E\s} (1-q e) = ∏_{e∈E} (q e + (1 - q e)) = 1`, valid for **all** real
densities. -/
theorem sum_finiteBernoulliWeightFamily [DecidableEq ι] (E : Finset ι) (q : ι → ℝ) :
    ∑ s ∈ E.powerset, finiteBernoulliWeightFamily E q s = 1 := by
  have h := Finset.prod_add q (fun e => 1 - q e) E
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  have h2 : ∑ s ∈ E.powerset, finiteBernoulliWeightFamily E q s =
      ∑ t ∈ E.powerset, (∏ i ∈ t, q i) * ∏ i ∈ E \ t, (1 - q i) := rfl
  rw [h2, ← h]

theorem sum_finiteBernoulliWeight (E : Finset ι) (p : ℝ) :
    ∑ s ∈ E.powerset, finiteBernoulliWeight E p s = 1 := by
  classical
  rw [← sum_finiteBernoulliWeightFamily E fun _ => p]
  exact Finset.sum_congr rfl fun s hs =>
    (finiteBernoulliWeightFamily_const (Finset.mem_powerset.mp hs) p).symm

/-! ### Finite expectations and probabilities -/

/-- Expectation of an observable on the finite cube `{0,1}^E`, encoded as the weighted sum
over the powerset of `E`. The density is a real parameter so that differentiation in `p`
makes sense on all of `ℝ`. -/
def finiteBernoulliExpectation (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) : ℝ :=
  ∑ s ∈ E.powerset, finiteBernoulliWeight E p s * X s

/-- Fubini for two finite Bernoulli cubes. -/
theorem finiteBernoulliExpectation_comm {κ : Type*}
    (E : Finset ι) (F : Finset κ) (p q : ℝ) (X : Finset ι → Finset κ → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ finiteBernoulliExpectation F q (X s)) =
      finiteBernoulliExpectation F q (fun t ↦ finiteBernoulliExpectation E p (fun s ↦ X s t)) := by
  simp only [finiteBernoulliExpectation, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Probability of a trace event on the finite cube `{0,1}^E`. -/
noncomputable def finiteBernoulliProbability (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    ℝ :=
  finiteBernoulliExpectation E p (T.indicator fun _ => 1)

theorem finiteBernoulliProbability_eq_sum_indicator (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliProbability E p T =
      ∑ s ∈ E.powerset, finiteBernoulliWeight E p s * T.indicator (fun _ => 1) s :=
  rfl

/-- Inhomogeneous expectation on the finite cube — the finite-volume multiparameter model
behind Russo's formula. -/
def finiteBernoulliExpectationFamily [DecidableEq ι] (E : Finset ι) (q : ι → ℝ)
    (X : Finset ι → ℝ) : ℝ :=
  ∑ s ∈ E.powerset, finiteBernoulliWeightFamily E q s * X s

/-- Inhomogeneous probability on the finite cube. -/
noncomputable def finiteBernoulliProbabilityFamily [DecidableEq ι] (E : Finset ι)
    (q : ι → ℝ) (T : Set (Finset ι)) : ℝ :=
  finiteBernoulliExpectationFamily E q (T.indicator fun _ => 1)

theorem finiteBernoulliExpectationFamily_const [DecidableEq ι] (E : Finset ι) (p : ℝ)
    (X : Finset ι → ℝ) :
    finiteBernoulliExpectationFamily E (fun _ => p) X = finiteBernoulliExpectation E p X :=
  Finset.sum_congr rfl fun s hs => by
    rw [finiteBernoulliWeightFamily_const (Finset.mem_powerset.mp hs)]

theorem finiteBernoulliProbabilityFamily_const [DecidableEq ι] (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily E (fun _ => p) T = finiteBernoulliProbability E p T :=
  finiteBernoulliExpectationFamily_const E p _

theorem finiteBernoulliExpectation_congr {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (h : ∀ s ∈ E.powerset, X s = Y s) :
    finiteBernoulliExpectation E p X = finiteBernoulliExpectation E p Y :=
  Finset.sum_congr rfl fun s hs => by rw [h s hs]

theorem finiteBernoulliExpectation_add (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s => X s + Y s) =
      finiteBernoulliExpectation E p X + finiteBernoulliExpectation E p Y := by
  rw [finiteBernoulliExpectation, finiteBernoulliExpectation, finiteBernoulliExpectation,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => mul_add _ _ _

theorem finiteBernoulliExpectation_const_mul (E : Finset ι) (p c : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s => c * X s) =
      c * finiteBernoulliExpectation E p X := by
  rw [finiteBernoulliExpectation, finiteBernoulliExpectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem finiteBernoulliExpectation_const (E : Finset ι) (p c : ℝ) :
    finiteBernoulliExpectation E p (fun _ => c) = c := by
  rw [finiteBernoulliExpectation]
  have : ∀ s ∈ E.powerset, finiteBernoulliWeight E p s * c =
      c * finiteBernoulliWeight E p s := fun s _ => mul_comm _ _
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_finiteBernoulliWeight, mul_one]

theorem finiteBernoulliExpectation_one (E : Finset ι) (p : ℝ) :
    finiteBernoulliExpectation E p (fun _ => 1) = 1 :=
  finiteBernoulliExpectation_const E p 1

theorem finiteBernoulliExpectation_nonneg {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X : Finset ι → ℝ} (hX : ∀ s ∈ E.powerset, 0 ≤ X s) :
    0 ≤ finiteBernoulliExpectation E p X :=
  Finset.sum_nonneg fun s hs =>
    mul_nonneg (finiteBernoulliWeight_nonneg hp0 hp1 s) (hX s hs)

theorem finiteBernoulliExpectation_mono {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X Y : Finset ι → ℝ} (hXY : ∀ s ∈ E.powerset, X s ≤ Y s) :
    finiteBernoulliExpectation E p X ≤ finiteBernoulliExpectation E p Y :=
  Finset.sum_le_sum fun s hs =>
    mul_le_mul_of_nonneg_left (hXY s hs) (finiteBernoulliWeight_nonneg hp0 hp1 s)

theorem finiteBernoulliProbability_nonneg {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Set (Finset ι)) : 0 ≤ finiteBernoulliProbability E p T :=
  finiteBernoulliExpectation_nonneg hp0 hp1 fun _s _ =>
    Set.indicator_apply_nonneg fun _ => zero_le_one

theorem finiteBernoulliProbability_le_one {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Set (Finset ι)) : finiteBernoulliProbability E p T ≤ 1 := by
  have h := finiteBernoulliExpectation_mono (E := E) hp0 hp1
    (X := T.indicator fun _ => 1) (Y := fun _ => 1) fun s _ =>
      Set.indicator_apply_le' (fun _ => le_refl 1) fun _ => zero_le_one
  rw [finiteBernoulliExpectation_one] at h
  exact h

theorem finiteBernoulliProbability_mono {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T U : Set (Finset ι)} (hTU : T ⊆ U) :
    finiteBernoulliProbability E p T ≤ finiteBernoulliProbability E p U :=
  finiteBernoulliExpectation_mono hp0 hp1 fun s _ =>
    Set.indicator_le_indicator_of_subset hTU (fun _ => zero_le_one) s

@[simp] theorem finiteBernoulliProbability_empty (E : Finset ι) (p : ℝ) :
    finiteBernoulliProbability E p (∅ : Set (Finset ι)) = 0 := by
  rw [finiteBernoulliProbability]
  have h : ∀ s ∈ E.powerset,
      (∅ : Set (Finset ι)).indicator (fun _ => (1 : ℝ)) s = (fun _ => (0 : ℝ)) s :=
    fun _s _ => by simp
  rw [finiteBernoulliExpectation_congr h]
  simpa using finiteBernoulliExpectation_const E p 0

@[simp] theorem finiteBernoulliProbability_univ (E : Finset ι) (p : ℝ) :
    finiteBernoulliProbability E p (Set.univ : Set (Finset ι)) = 1 := by
  rw [finiteBernoulliProbability]
  have h : ∀ s ∈ E.powerset,
      (Set.univ : Set (Finset ι)).indicator (fun _ => (1 : ℝ)) s = (fun _ => (1 : ℝ)) s :=
    fun _s _ => by simp
  rw [finiteBernoulliExpectation_congr h, finiteBernoulliExpectation_one]

/-! ### Cylinders -/

/-- The cylinder of the ambient space prescribing the trace `s` on the finite support `E`:
configurations that agree with `s` on every coordinate of `E`. -/
def finiteCylinder (E s : Finset ι) : Set (Set ι) :=
  {ω | ∀ e ∈ E, (e ∈ ω ↔ e ∈ s)}

theorem mem_finiteCylinder {E s : Finset ι} {ω : Set ι} :
    ω ∈ finiteCylinder E s ↔ ∀ e ∈ E, (e ∈ ω ↔ e ∈ s) :=
  Iff.rfl

theorem mem_finiteCylinder_restrictTo (E : Finset ι) (ω : Set ι) :
    ω ∈ finiteCylinder E (restrictTo E ω) := by
  intro e he
  simp [mem_restrictTo, he]

/-- Two configurations in the same cylinder have the same trace. -/
theorem restrictTo_eq_of_mem_finiteCylinder {E s : Finset ι} (hs : s ⊆ E) {ω : Set ι}
    (hω : ω ∈ finiteCylinder E s) : restrictTo E ω = s := by
  ext e
  rw [mem_restrictTo]
  constructor
  · rintro ⟨heE, heω⟩
    exact (hω e heE).mp heω
  · intro hes
    exact ⟨hs hes, (hω e (hs hes)).mpr hes⟩

theorem finiteCylinder_eq_superset_inter_disjoint [DecidableEq ι] {E s : Finset ι}
    (hs : s ⊆ E) :
    finiteCylinder E s =
      {ω : Set ι | (s : Set ι) ⊆ ω} ∩ {ω : Set ι | Disjoint ((E \ s : Finset ι) : Set ι) ω} := by
  ext ω
  constructor
  · intro hω
    refine ⟨fun e hes => ?_, Set.disjoint_left.mpr fun e hed heω => ?_⟩
    · have hes' : e ∈ s := by simpa using hes
      exact (hω e (hs hes')).mpr hes'
    · have hed' : e ∈ E \ s := by simpa using hed
      rw [Finset.mem_sdiff] at hed'
      exact hed'.2 ((hω e hed'.1).mp heω)
  · rintro ⟨hsub, hdisj⟩ e heE
    constructor
    · intro heω
      by_contra hes
      exact Set.disjoint_left.mp hdisj (by simp [heE, hes]) heω
    · intro hes
      exact hsub (by simpa using hes)

theorem measurableSet_finiteCylinder {E s : Finset ι} (hs : s ⊆ E) :
    MeasurableSet (finiteCylinder E s) := by
  classical
  rw [finiteCylinder_eq_superset_inter_disjoint hs]
  exact (measurableSet_superset_finset s).inter (measurableSet_disjoint_finset (E \ s))

/-- Distinct traces give disjoint cylinders. -/
theorem pairwiseDisjoint_finiteCylinder (E : Finset ι) :
    Set.PairwiseDisjoint (↑E.powerset : Set (Finset ι)) (finiteCylinder E) := by
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_powerset] at hs ht
  refine Set.disjoint_left.mpr fun ω hωs hωt => hst ?_
  rw [← restrictTo_eq_of_mem_finiteCylinder hs hωs,
    ← restrictTo_eq_of_mem_finiteCylinder ht hωt]

/-- The cylinder probability: the trace of the ambient Bernoulli measure on a finite support
is the finite Bernoulli weight (Grimmett's finite-dimensional product formula, p. 33). -/
theorem setBernoulli_real_finiteCylinder {E s : Finset ι} (hs : s ⊆ E) (p : I) :
    setBer((Set.univ : Set ι), p).real (finiteCylinder E s) =
      finiteBernoulliWeight E (p : ℝ) s := by
  classical
  rw [finiteCylinder_eq_superset_inter_disjoint hs]
  have hdisj : Disjoint (s : Set ι) ((E \ s : Finset ι) : Set ι) := by
    rw [Set.disjoint_left]
    intro e hes hed
    rw [Finset.coe_sdiff, Set.mem_diff] at hed
    exact hed.2 hes
  have := setBernoulli_real_open_closed_on_finset_univ s (E \ s) p hdisj
  rw [show {ω : Set ι | (s : Set ι) ⊆ ω} ∩
        {ω : Set ι | Disjoint ((E \ s : Finset ι) : Set ι) ω} =
      {ω : Set ι | (s : Set ι) ⊆ ω ∧ Disjoint ((E \ s : Finset ι) : Set ι) ω} from rfl,
    this, Finset.card_sdiff_of_subset hs]
  rfl

/-! ### Traces of events -/

/-- The trace of an ambient event: the finite sets whose coercion belongs to the event. -/
def eventTrace (A : Set (Set ι)) : Set (Finset ι) :=
  {s | (↑s : Set ι) ∈ A}

@[simp] theorem mem_eventTrace {A : Set (Set ι)} {s : Finset ι} :
    s ∈ eventTrace A ↔ (↑s : Set ι) ∈ A :=
  Iff.rfl

/-- A trace event is increasing when it is upward closed for finite-set inclusion. -/
def IsIncreasingTrace (T : Set (Finset ι)) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → s ∈ T → t ∈ T

theorem IsIncreasingEvent.isIncreasingTrace_eventTrace {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) : IsIncreasingTrace (eventTrace A) :=
  fun _ _ hst hs => hA (Finset.coe_subset.mpr hst) hs

/-- Membership of a finitely supported event is read off the trace. -/
theorem DependsOn.mem_iff_eventTrace {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    (ω : Set ι) : ω ∈ A ↔ restrictTo E ω ∈ eventTrace A := by
  rw [mem_eventTrace]
  exact hA.mem_iff_restrictTo_mem ω

/-! ### The transfer pack -/

/-- Pointwise decomposition of a finitely supported observable over the cylinder partition:
exactly one cylinder of the powerset contains any given configuration. -/
theorem DependsOnFun.eq_sum_indicator_finiteCylinder {E : Finset ι} {X : Set ι → ℝ}
    (hX : DependsOnFun E X) (ω : Set ι) :
    X ω = ∑ s ∈ E.powerset,
      (finiteCylinder E s).indicator (fun _ => X (↑s : Set ι)) ω := by
  classical
  rw [Finset.sum_eq_single (restrictTo E ω)]
  · rw [Set.indicator_of_mem (mem_finiteCylinder_restrictTo E ω)]
    refine hX fun e he => ?_
    simp [mem_restrictTo, he]
  · intro s hs hne
    refine Set.indicator_of_notMem (fun hω => hne ?_) _
    exact (restrictTo_eq_of_mem_finiteCylinder (Finset.mem_powerset.mp hs) hω).symm ▸ rfl
  · intro h
    exact absurd (Finset.mem_powerset.mpr (restrictTo_subset E ω)) h

/-- A finitely supported event is measurable: it is the finite disjoint union of the
cylinders of its trace. -/
theorem DependsOn.measurableSet {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) :
    MeasurableSet A := by
  classical
  have hrepr : A = ⋃ s ∈ E.powerset.filter (fun s : Finset ι => (↑s : Set ι) ∈ A),
      finiteCylinder E s := by
    ext ω
    rw [Set.mem_iUnion₂]
    constructor
    · intro hω
      exact ⟨restrictTo E ω,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (restrictTo_subset E ω),
          (hA.mem_iff_restrictTo_mem ω).mp hω⟩,
        mem_finiteCylinder_restrictTo E ω⟩
    · rintro ⟨s, hs, hω⟩
      have hsA := (Finset.mem_filter.mp hs).2
      exact (hA fun e he => hω e he).mpr hsA
  rw [hrepr]
  exact (E.powerset.filter _).measurableSet_biUnion fun s hs =>
    measurableSet_finiteCylinder (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)

/-- **Transfer of expectations.** The ambient integral of a finitely supported observable is
its finite-cube expectation. Measurability is automatic from the finite support. -/
theorem DependsOnFun.integral_setBernoulli {E : Finset ι} {X : Set ι → ℝ}
    (hX : DependsOnFun E X) (p : I) :
    ∫ ω, X ω ∂ setBer((Set.univ : Set ι), p) =
      finiteBernoulliExpectation E (p : ℝ) (fun s => X (↑s : Set ι)) := by
  classical
  have hrw : (fun ω : Set ι => X ω) = fun ω => ∑ s ∈ E.powerset,
      (finiteCylinder E s).indicator (fun _ => X (↑s : Set ι)) ω :=
    funext fun ω => hX.eq_sum_indicator_finiteCylinder ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [integral_indicator_const _
        (measurableSet_finiteCylinder (Finset.mem_powerset.mp hs)),
      setBernoulli_real_finiteCylinder (Finset.mem_powerset.mp hs) p, smul_eq_mul]
  · intro s hs
    exact (integrable_const _).indicator
      (measurableSet_finiteCylinder (Finset.mem_powerset.mp hs))

/-- **Transfer of probabilities.** The ambient probability of a finitely supported event is
the finite-cube probability of its trace (Grimmett p. 33: events defined in terms of
finitely many edges are computed on the finite cube). -/
theorem DependsOn.setBernoulli_real_eq_finiteBernoulliProbability {E : Finset ι}
    {A : Set (Set ι)} (hA : DependsOn E A) (p : I) :
    setBer((Set.univ : Set ι), p).real A =
      finiteBernoulliProbability E (p : ℝ) (eventTrace A) := by
  have hind := (hA.indicator_dependsOnFun).integral_setBernoulli p
  rw [integral_indicator_const (1 : ℝ) hA.measurableSet, smul_eq_mul, mul_one] at hind
  rw [hind, finiteBernoulliProbability]
  refine finiteBernoulliExpectation_congr fun s _ => ?_
  by_cases hs : (↑s : Set ι) ∈ A
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (mem_eventTrace.mpr hs)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (by simpa using hs)]

/-- Enlarging the support does not change the finite-cube probability of the trace of a
finitely supported event. -/
theorem DependsOn.finiteBernoulliProbability_eventTrace_congr {E F : Finset ι}
    {A : Set (Set ι)} (hA : DependsOn E A) (hEF : E ⊆ F) (p : I) :
    finiteBernoulliProbability F (p : ℝ) (eventTrace A) =
      finiteBernoulliProbability E (p : ℝ) (eventTrace A) := by
  rw [← hA.setBernoulli_real_eq_finiteBernoulliProbability p,
    ← (hA.mono hEF).setBernoulli_real_eq_finiteBernoulliProbability p]

/-- A finite Bernoulli set hits a fixed subset `S ⊆ E` with probability
`1 - (1-p)^|S|`. -/
theorem finiteBernoulliProbability_hits_finset [DecidableEq ι]
    {E S : Finset ι} (hSE : S ⊆ E) (p : I) :
    finiteBernoulliProbability E p {t : Finset ι | ∃ x ∈ S, x ∈ t} =
      1 - (1 - (p : ℝ)) ^ S.card := by
  let A : Set (Set ι) := {t | ∃ x ∈ S, x ∈ t}
  let B : Set (Set ι) := {t | Disjoint (S : Set ι) t}
  have hAdep : DependsOn E A := by
    intro ω η htrace
    constructor
    · rintro ⟨x, hxS, hxω⟩
      exact ⟨x, hxS, htrace x (hSE hxS) |>.mp hxω⟩
    · rintro ⟨x, hxS, hxη⟩
      exact ⟨x, hxS, htrace x (hSE hxS) |>.mpr hxη⟩
  have hBdep : DependsOn E B := by
    intro ω η htrace
    simp only [B, Set.disjoint_left]
    constructor <;> intro h x hxS hx
    · exact h hxS (htrace x (hSE hxS) |>.mpr hx)
    · exact h hxS (htrace x (hSE hxS) |>.mp hx)
  have htrace : eventTrace A = {t : Finset ι | ∃ x ∈ S, x ∈ t} := by
    ext t
    rfl
  have hcomp : A = Bᶜ := by
    ext t
    simp [A, B, Set.disjoint_left]
  rw [← htrace, ← hAdep.setBernoulli_real_eq_finiteBernoulliProbability p,
    hcomp, measureReal_compl hBdep.measurableSet, probReal_univ,
    setBernoulli_real_disjoint_finset_univ]

/-! ### Cubic lattice specializations -/

/-- Transfer of probabilities for the cubic-lattice Bernoulli bond measure. -/
theorem DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)} (hA : DependsOn E A) (p : I) :
    (bernoulliBondMeasure d p).real A =
      finiteBernoulliProbability E (p : ℝ) (eventTrace A) := by
  simpa [bernoulliBondMeasure] using hA.setBernoulli_real_eq_finiteBernoulliProbability p

/-- Transfer of expectations for the cubic-lattice Bernoulli bond measure. -/
theorem DependsOnFun.bernoulliBondMeasure_integral_eq_finiteBernoulliExpectation {d : ℕ}
    {E : Finset (CubicEdge d)} {X : EdgeConfiguration d → ℝ} (hX : DependsOnFun E X)
    (p : I) :
    ∫ ω, X ω ∂ bernoulliBondMeasure d p =
      finiteBernoulliExpectation E (p : ℝ) (fun s => X (↑s : Set (CubicEdge d))) := by
  simpa [bernoulliBondMeasure] using hX.integral_setBernoulli p

end Percolation
