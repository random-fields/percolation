import Percolation.Bernoulli.Sprinkling

/-!
# Upward distance to an increasing event

This file formalizes Grimmett (2.48)--(2.49).  A configuration has upward distance at most `r`
from an event `A` when opening at most `r` currently closed coordinates puts it in `A`.
For `p₁ < p₂`, inequality (2.49) states

`((p₂-p₁)/(1-p₁))^r P_{p₁}(F_A ≤ r) ≤ P_{p₂}(A)`.

Unlike a fixed-edge finite-energy estimate, the repair set may depend on the configuration.
This is the probability tool required by Grimmett's path-dependent repair in (7.83).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

variable {ι : Type*}

/-- Finite sets of currently closed coordinates whose opening puts `ω` in `A`. -/
def upwardRepairSets (r : ℕ) (A : Set (Set ι)) (ω : Set ι) : Set (Finset ι) :=
  {B | B.card ≤ r ∧ Disjoint (B : Set ι) ω ∧ ω ∪ (B : Set ι) ∈ A}

/-- The event `{F_A ≤ r}` from (2.48)--(2.49). -/
def upwardDistanceAtMost (r : ℕ) (A : Set (Set ι)) : Set (Set ι) :=
  {ω | (upwardRepairSets r A ω).Nonempty}

theorem mem_upwardDistanceAtMost {r : ℕ} {A : Set (Set ι)} {ω : Set ι} :
    ω ∈ upwardDistanceAtMost r A ↔
      ∃ B : Finset ι,
        B.card ≤ r ∧ Disjoint (B : Set ι) ω ∧ ω ∪ (B : Set ι) ∈ A :=
  Iff.rfl

theorem upwardDistanceAtMost_zero (A : Set (Set ι)) :
    upwardDistanceAtMost 0 A = A := by
  ext ω
  constructor
  · rintro ⟨B, hBcard, _hdisj, hmem⟩
    have hB : B = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hBcard)
    simpa [hB] using hmem
  · intro hω
    exact ⟨∅, by simp, by simp, by simpa using hω⟩

/-- The event that a fixed finite set repairs a configuration is measurable. -/
theorem measurableSet_mem_upwardRepairSets [DecidableEq ι]
    {A : Set (Set ι)} (hAm : MeasurableSet A) (r : ℕ) (B : Finset ι) :
    MeasurableSet {ω : Set ι | B ∈ upwardRepairSets r A ω} := by
  by_cases hcard : B.card ≤ r
  · have hrepr : {ω : Set ι | B ∈ upwardRepairSets r A ω} =
        {ω : Set ι | Disjoint (B : Set ι) ω} ∩
          (fun ω : Set ι => ω ∪ (B : Set ι)) ⁻¹' A := by
      ext ω
      simp [upwardRepairSets, hcard]
    rw [hrepr]
    have hunion : MeasurableSet
        ((fun ω : Set ι => ω ∪ (B : Set ι)) ⁻¹' A) := by
      convert measurable_diff_union (∅ : Finset ι) B hAm using 1
      ext ω
      simp
    exact (measurableSet_disjoint_finset B).inter hunion
  · have hrepr : {ω : Set ι | B ∈ upwardRepairSets r A ω} = ∅ := by
      ext ω
      simp [upwardRepairSets, hcard]
    rw [hrepr]
    exact MeasurableSet.empty

theorem measurableSet_upwardDistanceAtMost [Countable ι]
    {A : Set (Set ι)} (hAm : MeasurableSet A) (r : ℕ) :
    MeasurableSet (upwardDistanceAtMost r A) := by
  classical
  have hrepr : upwardDistanceAtMost r A =
      ⋃ B : Finset ι, {ω : Set ι | B ∈ upwardRepairSets r A ω} := by
    ext ω
    constructor
    · rintro ⟨B, hB⟩
      exact Set.mem_iUnion.mpr ⟨B, hB⟩
    · rintro h
      obtain ⟨B, hB⟩ := Set.mem_iUnion.mp h
      exact ⟨B, hB⟩
  rw [hrepr]
  exact MeasurableSet.iUnion fun B ↦ measurableSet_mem_upwardRepairSets hAm r B

open Classical in
/-- Canonical least-code repair set, with junk value `∅` off `{F_A≤r}`. -/
noncomputable def minimalUpwardRepair
    (enc : Finset ι → ℕ) (r : ℕ) (A : Set (Set ι)) (ω : Set ι) : Finset ι :=
  if h : (upwardRepairSets r A ω).Nonempty then
    (Nat.sInf_mem (h.image enc)).choose
  else ∅

theorem minimalUpwardRepair_mem {enc : Finset ι → ℕ} {r : ℕ}
    {A : Set (Set ι)} {ω : Set ι} (h : (upwardRepairSets r A ω).Nonempty) :
    minimalUpwardRepair enc r A ω ∈ upwardRepairSets r A ω := by
  rw [minimalUpwardRepair, dif_pos h]
  exact (Nat.sInf_mem (h.image enc)).choose_spec.1

theorem enc_minimalUpwardRepair_le {enc : Finset ι → ℕ} {r : ℕ}
    {A : Set (Set ι)} {ω : Set ι} {B : Finset ι}
    (hB : B ∈ upwardRepairSets r A ω) :
    enc (minimalUpwardRepair enc r A ω) ≤ enc B := by
  have h : (upwardRepairSets r A ω).Nonempty := ⟨B, hB⟩
  rw [minimalUpwardRepair, dif_pos h, (Nat.sInf_mem (h.image enc)).choose_spec.2]
  exact Nat.sInf_le ⟨B, hB, rfl⟩

/-- Partition block of `{F_A≤r}` with canonical repair exactly `B`. -/
def upwardRepairEvent
    (enc : Finset ι → ℕ) (r : ℕ) (A : Set (Set ι)) (B : Finset ι) : Set (Set ι) :=
  {ω | ω ∈ upwardDistanceAtMost r A ∧ minimalUpwardRepair enc r A ω = B}

theorem mem_upwardRepairSets_of_mem_upwardRepairEvent
    {enc : Finset ι → ℕ} {r : ℕ} {A : Set (Set ι)} {B : Finset ι} {ω : Set ι}
    (hω : ω ∈ upwardRepairEvent enc r A B) :
    B ∈ upwardRepairSets r A ω :=
  hω.2 ▸ minimalUpwardRepair_mem hω.1

theorem upwardRepairEvent_eq {enc : Finset ι → ℕ} (henc : Function.Injective enc)
    (r : ℕ) (A : Set (Set ι)) (B : Finset ι) :
    upwardRepairEvent enc r A B =
      upwardDistanceAtMost r A ∩
        ({ω | B ∈ upwardRepairSets r A ω} ∩
          ⋂ B' ∈ {B' : Finset ι | enc B' < enc B},
            {ω | B' ∈ upwardRepairSets r A ω}ᶜ) := by
  ext ω
  simp only [upwardRepairEvent, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_compl_iff]
  constructor
  · rintro ⟨hnear, rfl⟩
    refine ⟨hnear, minimalUpwardRepair_mem hnear, fun B' hB' hmem ↦ ?_⟩
    exact absurd hB' (not_lt.mpr (enc_minimalUpwardRepair_le hmem))
  · rintro ⟨hnear, hBmem, hmin⟩
    refine ⟨hnear, ?_⟩
    by_contra hne
    have hlt : enc (minimalUpwardRepair enc r A ω) < enc B :=
      lt_of_le_of_ne (enc_minimalUpwardRepair_le hBmem) fun h ↦ hne (henc h)
    exact hmin _ hlt (minimalUpwardRepair_mem hnear)

theorem measurableSet_upwardRepairEvent [Countable ι] {enc : Finset ι → ℕ}
    (henc : Function.Injective enc) {A : Set (Set ι)} (hAm : MeasurableSet A)
    (r : ℕ) (B : Finset ι) :
    MeasurableSet (upwardRepairEvent enc r A B) := by
  classical
  rw [upwardRepairEvent_eq henc r A B]
  exact (measurableSet_upwardDistanceAtMost hAm r).inter
    ((measurableSet_mem_upwardRepairSets hAm r B).inter
      (MeasurableSet.biInter (Set.to_countable _) fun B' _ ↦
        (measurableSet_mem_upwardRepairSets hAm r B').compl))

/-! ### Coupling blocks for the proof of (2.49) -/

/-- The `p`-threshold configuration with the coordinates of `B` forced closed. -/
def clearedThreshold (B : Finset ι) (p : I) (X : ι → ℝ) : Set ι :=
  thresholdConfiguration p X \ (B : Set ι)

theorem clearedThreshold_eq_of_disjoint {B : Finset ι} {p : I} {X : ι → ℝ}
    (h : Disjoint (B : Set ι) (thresholdConfiguration p X)) :
    clearedThreshold B p X = thresholdConfiguration p X := by
  ext e
  simp only [clearedThreshold, Set.mem_diff, Finset.mem_coe]
  constructor
  · exact fun he ↦ he.1
  · intro he
    exact ⟨he, fun heB ↦ Set.disjoint_left.mp h heB he⟩

theorem measurable_clearedThreshold_coordSigma
    (B : Finset ι) (p : I) :
    Measurable[coordSigma ι ((B : Set ι)ᶜ)] (clearedThreshold B p) := by
  classical
  have hcomp : clearedThreshold B p =
      (fun P : ι → Prop => {i | P i}) ∘
        fun (X : ι → ℝ) (e : ι) => (X e < (p : ℝ) ∧ e ∉ B : Prop) := by
    funext X
    ext e
    simp [clearedThreshold, thresholdConfiguration]
  rw [hcomp]
  refine Measurable.comp (by fun_prop) ?_
  refine @measurable_pi_lambda _ _ _ (coordSigma ι ((B : Set ι)ᶜ)) _ _ fun e ↦ ?_
  by_cases he : e ∈ B
  · have hconst : (fun X : ι → ℝ => (X e < (p : ℝ) ∧ e ∉ B : Prop)) =
        fun _ => False := by
      funext X
      simp [he]
    rw [hconst]
    exact measurable_const
  · have heq : (fun X : ι → ℝ => (X e < (p : ℝ) ∧ e ∉ B : Prop)) =
        (fun x : ℝ => (x < (p : ℝ) : Prop)) ∘ fun X : ι → ℝ => X e := by
      funext X
      simp [he]
    rw [heq]
    exact (measurable_lt_prop _).comp (measurable_eval_coordSigma (by simpa using he))

theorem volume_restrict_Icc_Ici (p : I) :
    volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Ici (p : ℝ)) =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [Measure.restrict_apply measurableSet_Ici]
  have h : Set.Ici (p : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (p : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨hxp, _hx0, hx1⟩
      exact ⟨hxp, hx1⟩
    · rintro ⟨hxp, hx1⟩
      exact ⟨hxp, p.2.1.trans hxp, hx1⟩
  rw [h, Real.volume_Icc]

theorem measurableSet_forall_lt (B : Finset ι) (c : ℝ) :
    MeasurableSet {X : ι → ℝ | ∀ e ∈ B, X e < c} := by
  have h : {X : ι → ℝ | ∀ e ∈ B, X e < c} =
      ⋂ e ∈ (B : Set ι), (fun X : ι → ℝ => X e) ⁻¹' Set.Iio c := by
    ext X
    simp
  rw [h]
  exact MeasurableSet.biInter B.countable_toSet fun e _ ↦
    measurable_pi_apply e measurableSet_Iio

/-- Per-repair-set block comparison for (2.49). -/
theorem couplingMeasure_upwardRepairEvent_block_le [Countable ι]
    {enc : Finset ι → ℕ} (henc : Function.Injective enc)
    {A : Set (Set ι)} (hAm : MeasurableSet A) {p₁ p₂ : I}
    (r : ℕ) (B : Finset ι) :
    ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        couplingMeasure ι (thresholdConfiguration p₁ ⁻¹'
          upwardRepairEvent enc r A B) ≤
      ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
        couplingMeasure ι
          (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent enc r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) := by
  classical
  by_cases hcard : B.card ≤ r
  · have hCmble : MeasurableSet[coordSigma ι ((B : Set ι)ᶜ)]
        (clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B) :=
      measurable_clearedThreshold_coordSigma B p₁
        (measurableSet_upwardRepairEvent henc hAm r B)
    have hW : thresholdConfiguration p₁ ⁻¹' upwardRepairEvent enc r A B =
        (B : Set ι).pi (fun _ => Set.Ici (p₁ : ℝ)) ∩
          clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B := by
      ext X
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Set.mem_Ici,
        Finset.mem_coe]
      constructor
      · intro hX
        have hrepair := mem_upwardRepairSets_of_mem_upwardRepairEvent hX
        have hdisj := hrepair.2.1
        have hbox : ∀ e ∈ B, (p₁ : ℝ) ≤ X e := by
          intro e he
          exact not_lt.mp fun heopen ↦
            Set.disjoint_left.mp hdisj (Finset.mem_coe.mpr he) heopen
        exact ⟨hbox, by rwa [clearedThreshold_eq_of_disjoint hdisj]⟩
      · rintro ⟨hbox, hX⟩
        have hdisj : Disjoint (B : Set ι) (thresholdConfiguration p₁ X) := by
          rw [Set.disjoint_left]
          intro e heB heopen
          exact (not_lt_of_ge (hbox e (Finset.mem_coe.mp heB))) heopen
        rwa [clearedThreshold_eq_of_disjoint hdisj] at hX
    have hK : thresholdConfiguration p₁ ⁻¹' upwardRepairEvent enc r A B ∩
          {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)} =
        (B : Set ι).pi (fun _ => Set.Ico (p₁ : ℝ) (p₂ : ℝ)) ∩
          clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B := by
      rw [hW]
      ext X
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_Ici, Set.mem_Ico,
        Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨⟨hlower, hC⟩, hupper⟩
        exact ⟨fun e he ↦ ⟨hlower e he, hupper e he⟩, hC⟩
      · rintro ⟨hinterval, hC⟩
        exact ⟨⟨fun e he ↦ (hinterval e he).1, hC⟩,
          fun e he ↦ (hinterval e he).2⟩
    have hμW : couplingMeasure ι
          (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent enc r A B) =
        ENNReal.ofReal (1 - (p₁ : ℝ)) ^ B.card *
          couplingMeasure ι
            (clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B) := by
      rw [hW, couplingMeasure_pi_inter B (fun _ ↦ measurableSet_Ici) hCmble]
      congr 1
      simp only [Finset.prod_const]
      rw [volume_restrict_Icc_Ici]
    have hμK : couplingMeasure ι
          (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent enc r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) =
        ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ B.card *
          couplingMeasure ι
            (clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B) := by
      rw [hK, couplingMeasure_pi_inter B (fun _ ↦ measurableSet_Ico) hCmble]
      congr 1
      simp only [Finset.prod_const]
      rw [volume_restrict_Icc_Ico]
    rw [hμW, hμK]
    set a := ENNReal.ofReal (1 - (p₁ : ℝ))
    set b := ENNReal.ofReal ((p₂ : ℝ) - p₁)
    set c := couplingMeasure ι
      (clearedThreshold B p₁ ⁻¹' upwardRepairEvent enc r A B)
    have hba : b ≤ a := ENNReal.ofReal_le_ofReal (by linarith [p₂.2.2])
    calc
      b ^ r * (a ^ B.card * c) =
          b ^ (r - B.card) * (b ^ B.card * (a ^ B.card * c)) := by
        rw [← pow_sub_mul_pow b hcard, mul_assoc]
      _ ≤ a ^ (r - B.card) * (b ^ B.card * (a ^ B.card * c)) :=
        mul_le_mul_left (pow_le_pow_left' hba _) _
      _ = a ^ r * (b ^ B.card * c) := by
        rw [← pow_sub_mul_pow a hcard]
        ring
  · have hempty : thresholdConfiguration p₁ ⁻¹'
        upwardRepairEvent enc r A B = ∅ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hX
      exact hcard (mem_upwardRepairSets_of_mem_upwardRepairEvent hX).1
    rw [hempty]
    simp

/-- Coupling form of Grimmett (2.49), before converting the product measures to real-valued
Bernoulli probabilities. -/
theorem couplingMeasure_upwardDistance_le [Countable ι]
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) (r : ℕ) :
    ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        couplingMeasure ι (thresholdConfiguration p₁ ⁻¹' upwardDistanceAtMost r A) ≤
      ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
        couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' A) := by
  classical
  obtain ⟨enc⟩ := nonempty_embedding_nat (Finset ι)
  have hcover : thresholdConfiguration p₁ ⁻¹' upwardDistanceAtMost r A =
      ⋃ B : Finset ι,
        thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B := by
    ext X
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hX
      exact ⟨minimalUpwardRepair (⇑enc) r A (thresholdConfiguration p₁ X), hX, rfl⟩
    · rintro ⟨B, hB⟩
      exact hB.1
  have hWm : ∀ B : Finset ι, MeasurableSet
      (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B) := fun B ↦
    measurable_thresholdConfiguration p₁
      (measurableSet_upwardRepairEvent enc.injective hAm r B)
  have hKm : ∀ B : Finset ι, MeasurableSet
      (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) := fun B ↦
    (hWm B).inter (measurableSet_forall_lt B (p₂ : ℝ))
  have hWdisj : Pairwise (Function.onFun Disjoint fun B : Finset ι ↦
      thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B) := by
    intro B B' hne
    rw [Function.onFun, Set.disjoint_left]
    intro X hX hX'
    exact hne (hX.2.symm.trans hX'.2)
  have hKdisj : Pairwise (Function.onFun Disjoint fun B : Finset ι ↦
      thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) := fun B B' hne ↦
    (hWdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hKsub : ∀ B : Finset ι,
      thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
          {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)} ⊆
        thresholdConfiguration p₂ ⁻¹' A := by
    rintro B X ⟨hXW, hXupper⟩
    have hrepair := mem_upwardRepairSets_of_mem_upwardRepairEvent hXW
    refine hAinc ?_ hrepair.2.2
    intro e he
    rcases he with he₁ | heB
    · exact thresholdConfiguration_mono h12.le X he₁
    · exact hXupper e (Finset.mem_coe.mp heB)
  calc
    ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        couplingMeasure ι (thresholdConfiguration p₁ ⁻¹' upwardDistanceAtMost r A) =
      ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        ∑' B : Finset ι, couplingMeasure ι
          (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B) := by
      rw [hcover, measure_iUnion hWdisj hWm]
    _ = ∑' B : Finset ι, ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
          couplingMeasure ι
            (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B) :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' B : Finset ι, ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
          couplingMeasure ι
            (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
              {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) :=
      ENNReal.tsum_le_tsum fun B ↦
        couplingMeasure_upwardRepairEvent_block_le enc.injective hAm r B
    _ = ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
        ∑' B : Finset ι, couplingMeasure ι
          (thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r * couplingMeasure ι
        (⋃ B : Finset ι,
          thresholdConfiguration p₁ ⁻¹' upwardRepairEvent (⇑enc) r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, X e < (p₂ : ℝ)}) := by
      rw [measure_iUnion hKdisj hKm]
    _ ≤ ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
        couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' A) :=
      mul_le_mul_right (measure_mono (Set.iUnion_subset hKsub)) _

/-- Grimmett inequality (2.49): sprinkling from `p₁` to `p₂` pays for a configuration-dependent
upward repair of at most `r` closed coordinates. -/
theorem IsIncreasingEvent.setBernoulli_real_upwardDistanceAtMost_le [Countable ι]
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) (r : ℕ) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ r *
        setBer((Set.univ : Set ι), p₁).real (upwardDistanceAtMost r A) ≤
      setBer((Set.univ : Set ι), p₂).real A := by
  have hDm := measurableSet_upwardDistanceAtMost hAm r
  have hkey := couplingMeasure_upwardDistance_le (ι := ι) hAinc hAm h12 r
  have hmap₁ : couplingMeasure ι
      (thresholdConfiguration p₁ ⁻¹' upwardDistanceAtMost r A) =
      setBer((Set.univ : Set ι), p₁) (upwardDistanceAtMost r A) := by
    rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p₁,
      Measure.map_apply (measurable_thresholdConfiguration p₁) hDm]
  have hmap₂ : couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' A) =
      setBer((Set.univ : Set ι), p₂) A := by
    rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p₂,
      Measure.map_apply (measurable_thresholdConfiguration p₂) hAm]
  rw [hmap₁, hmap₂] at hkey
  have hne : ENNReal.ofReal (1 - (p₁ : ℝ)) ^ r *
      setBer((Set.univ : Set ι), p₂) A ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hne hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ (p₂ : ℝ) - p₁),
    ENNReal.toReal_ofReal (by linarith [p₁.2.2] : (0 : ℝ) ≤ 1 - (p₁ : ℝ)),
    ← measureReal_def, ← measureReal_def] at hreal
  have hden : 0 < 1 - (p₁ : ℝ) := by linarith [p₂.2.2]
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hden r)]
  simpa [mul_comm] using hreal

/-- Cubic-bond specialization of Grimmett (2.49). -/
theorem IsIncreasingEvent.bernoulliBondMeasure_real_upwardDistanceAtMost_le
    {d : ℕ} {A : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) (r : ℕ) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ r *
        (bernoulliBondMeasure d p₁).real (upwardDistanceAtMost r A) ≤
      (bernoulliBondMeasure d p₂).real A := by
  simpa [bernoulliBondMeasure] using
    hAinc.setBernoulli_real_upwardDistanceAtMost_le hAm h12 r

end Percolation
