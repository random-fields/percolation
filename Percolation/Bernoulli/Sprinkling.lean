import Percolation.Bernoulli.Coupling
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne

/-!
# The ACCFR sprinkling inequality (Theorem 2.45)

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.6, Theorem (2.45) and inequality
(2.46), pp. 49–51 (source id `grimmett-percolation-1999`).

For an increasing event `A`, Grimmett's *interior of depth `r`*, `I_r(A)`, consists of the
configurations that remain in `A` after any perturbation of at most `r` coordinates. The
Aizenman–Chayes–Chayes–Fröhlich–Russo theorem states that a small "sprinkling"
`p₁ → p₂` of extra open edges suffices to move from `A` to its deep interior:

`1 - P_{p₂}(I_r(A)) ≤ (p₂ / (p₂ - p₁))^r (1 - P_{p₁}(A))`.

This file formalizes the notions and the theorem:

* `Percolation.WithinRadius`, `Percolation.interiorDepth` — Grimmett's sphere `S_r(ω)`
  (as the induced proximity relation) and interior `I_r(A)`;
* `Percolation.witnessSets`, `Percolation.minimalWitness`, `Percolation.witnessEvent` —
  the small witness sets `B ⊆ ω` with `ω \ B ∉ A` certifying `ω ∉ I_r(A)`, and the
  countable partition of `I_r(A)ᶜ` by the minimal witness;
* `Percolation.measurableSet_interiorDepth` — measurability of `I_r(A)` over a countable
  index set;
* `Percolation.coordSigma`, `Percolation.couplingMeasure_pi_inter` — independence of
  disjoint coordinate blocks of the uniform coupling and the resulting factorization of
  box events against events supported off the box;
* `Percolation.IsIncreasingEvent.one_sub_setBernoulli_real_interiorDepth_le` —
  **Theorem (2.45)/(2.46)**, proved by Grimmett's conditioning-on-the-witness argument
  run on the uniform coupling of `P_{p₁}` and `P_{p₂}`;
* `Percolation.IsIncreasingEvent.one_sub_bernoulliBondMeasure_real_interiorDepth_le` —
  the cubic-lattice specialization.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

variable {ι : Type*}

/-! ### Spheres and interiors of events -/

/-- Two configurations are within radius `r` when they differ in at most `r` coordinates:
`ω'` lies in Grimmett's sphere `S_r(ω)` (p. 50). -/
def WithinRadius (r : ℕ) (ω ω' : Set ι) : Prop :=
  ∃ D : Finset ι, D.card ≤ r ∧ ∀ e ∉ D, (e ∈ ω ↔ e ∈ ω')

theorem withinRadius_self (r : ℕ) (ω : Set ι) : WithinRadius r ω ω :=
  ⟨∅, by simp, fun _ _ => Iff.rfl⟩

/-- Grimmett's *interior of depth `r`*, `I_r(A)`: the configurations all of whose
perturbations in at most `r` coordinates remain in `A` (p. 50). -/
def interiorDepth (r : ℕ) (A : Set (Set ι)) : Set (Set ι) :=
  {ω | ∀ ω', WithinRadius r ω ω' → ω' ∈ A}

theorem interiorDepth_subset (r : ℕ) (A : Set (Set ι)) : interiorDepth r A ⊆ A :=
  fun ω hω => hω ω (withinRadius_self r ω)

/-- Removing a finite set of coordinates and inserting another is a measurable operation
on configurations (coordinatewise Boolean, mirroring `measurable_thresholdConfiguration`). -/
theorem measurable_diff_union (D s : Finset ι) :
    Measurable fun ω : Set ι => (ω \ ↑D) ∪ ↑s := by
  classical
  have hcomp : (fun ω : Set ι => (ω \ ↑D) ∪ (↑s : Set ι)) =
      MeasurableEquiv.setOf ∘ (fun (P : ι → Prop) (e : ι) => ((P e ∧ e ∉ D) ∨ e ∈ s : Prop)) ∘
        MeasurableEquiv.setOf.symm := by
    funext ω
    ext e
    simp only [Function.comp_apply, MeasurableEquiv.coe_setOf, Set.mem_setOf_eq,
      Set.mem_union, Set.mem_diff, Finset.mem_coe]
    constructor
    · rintro (⟨heω, heD⟩ | hes)
      · exact Or.inl ⟨heω, heD⟩
      · exact Or.inr hes
    · rintro (⟨heω, heD⟩ | hes)
      · exact Or.inl ⟨heω, heD⟩
      · exact Or.inr hes
  rw [hcomp]
  refine MeasurableEquiv.setOf.measurable.comp (Measurable.comp ?_
    MeasurableEquiv.setOf.symm.measurable)
  exact measurable_pi_lambda _ fun e =>
    (measurable_from_top : Measurable fun P : Prop => ((P ∧ e ∉ D) ∨ e ∈ s : Prop)).comp
      (measurable_pi_apply e)

/-- Removing a finite set of coordinates is a measurable operation on configurations. -/
theorem measurable_diff_finset (D : Finset ι) :
    Measurable fun ω : Set ι => ω \ ↑D := by
  simpa using measurable_diff_union D ∅

/-- The interior of depth `r` as a countable intersection of preimages of `A` under the
override maps prescribing the trace on a small coordinate set. -/
theorem interiorDepth_eq_iInter (r : ℕ) (A : Set (Set ι)) :
    interiorDepth r A =
      ⋂ (D : Finset ι) (_ : D.card ≤ r) (s : Finset ι) (_ : s ⊆ D),
        (fun ω : Set ι => (ω \ ↑D) ∪ ↑s) ⁻¹' A := by
  classical
  ext ω
  simp only [interiorDepth, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h D hD s hs
    refine h _ ⟨D, hD, fun e he => ?_⟩
    have hes : e ∉ s := fun h' => he (hs h')
    simp only [Set.mem_union, Set.mem_diff, Finset.mem_coe]
    exact ⟨fun heω => Or.inl ⟨heω, he⟩,
      fun h' => h'.elim And.left fun h'' => absurd h'' hes⟩
  · rintro h ω' ⟨D, hD, hagree⟩
    have hω' : ω' = (ω \ ↑D) ∪ ↑(D.filter (· ∈ ω')) := by
      ext e
      simp only [Set.mem_union, Set.mem_diff, Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_coe]
      by_cases he : e ∈ D
      · exact ⟨fun h' => Or.inr ⟨he, h'⟩,
          fun h' => h'.elim (fun h'' => absurd he h''.2) And.right⟩
      · exact ⟨fun h' => Or.inl ⟨(hagree e he).mpr h', he⟩,
          fun h' => h'.elim (fun h'' => (hagree e he).mp h''.1)
            fun h'' => absurd h''.1 he⟩
    rw [hω']
    exact h D hD (D.filter (· ∈ ω')) (Finset.filter_subset _ _)

/-- The interior of depth `r` of a measurable event is measurable (countable index set). -/
theorem measurableSet_interiorDepth [Countable ι] {A : Set (Set ι)}
    (hA : MeasurableSet A) (r : ℕ) : MeasurableSet (interiorDepth r A) := by
  rw [interiorDepth_eq_iInter r A]
  exact MeasurableSet.iInter fun D => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      measurable_diff_union D s hA

/-! ### Witness sets for failure of deep interiority -/

/-- The witnesses to `ω ∉ I_r(A)` for an increasing event: coordinate sets of size at most
`r` inside `ω` whose removal exits `A`. -/
def witnessSets (r : ℕ) (A : Set (Set ι)) (ω : Set ι) : Set (Finset ι) :=
  {B | B.card ≤ r ∧ ↑B ⊆ ω ∧ ω \ ↑B ∉ A}

theorem mem_witnessSets {r : ℕ} {A : Set (Set ι)} {ω : Set ι} {B : Finset ι} :
    B ∈ witnessSets r A ω ↔ B.card ≤ r ∧ ↑B ⊆ ω ∧ ω \ ↑B ∉ A :=
  Iff.rfl

/-- For an increasing event, every configuration outside the interior of depth `r` has a
downward witness: some `B ⊆ ω` with `|B| ≤ r` and `ω \ B ∉ A` (Grimmett p. 50). -/
theorem IsIncreasingEvent.witnessSets_nonempty {A : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) {r : ℕ} {ω : Set ι}
    (hω : ω ∉ interiorDepth r A) : (witnessSets r A ω).Nonempty := by
  classical
  rw [interiorDepth, Set.mem_setOf_eq] at hω
  push Not at hω
  obtain ⟨ω', ⟨D, hDcard, hagree⟩, hnA⟩ := hω
  refine ⟨D.filter (· ∈ ω), le_trans (Finset.card_filter_le D _) hDcard, ?_, ?_⟩
  · intro e he
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
  · intro hmem
    refine hnA (hAinc (fun e he => ?_) hmem)
    obtain ⟨heω, heB⟩ := he
    have heD : e ∉ D := fun heD =>
      heB (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨heD, heω⟩))
    exact (hagree e heD).mp heω

open Classical in
/-- The minimal witness for `ω ∉ I_r(A)` relative to an encoding `enc` of the finite
coordinate sets into `ℕ`: the witness with the least code (junk value `∅` when no witness
exists). This realizes Grimmett's "earliest such set `B`" (p. 51). -/
noncomputable def minimalWitness (enc : Finset ι → ℕ) (r : ℕ) (A : Set (Set ι))
    (ω : Set ι) : Finset ι :=
  if h : (witnessSets r A ω).Nonempty then (Nat.sInf_mem (h.image enc)).choose else ∅

theorem minimalWitness_mem {enc : Finset ι → ℕ} {r : ℕ} {A : Set (Set ι)} {ω : Set ι}
    (h : (witnessSets r A ω).Nonempty) :
    minimalWitness enc r A ω ∈ witnessSets r A ω := by
  rw [minimalWitness, dif_pos h]
  exact (Nat.sInf_mem (h.image enc)).choose_spec.1

theorem enc_minimalWitness_le {enc : Finset ι → ℕ} {r : ℕ} {A : Set (Set ι)} {ω : Set ι}
    {B : Finset ι} (hB : B ∈ witnessSets r A ω) :
    enc (minimalWitness enc r A ω) ≤ enc B := by
  have h : (witnessSets r A ω).Nonempty := ⟨B, hB⟩
  rw [minimalWitness, dif_pos h, (Nat.sInf_mem (h.image enc)).choose_spec.2]
  exact Nat.sInf_le ⟨B, hB, rfl⟩

/-- The event that `ω` fails deep interiority with minimal witness exactly `B`. These
events partition `I_r(A)ᶜ` over the countably many finite sets `B`. -/
def witnessEvent (enc : Finset ι → ℕ) (r : ℕ) (A : Set (Set ι)) (B : Finset ι) :
    Set (Set ι) :=
  {ω | ω ∉ interiorDepth r A ∧ minimalWitness enc r A ω = B}

theorem IsIncreasingEvent.mem_witnessSets_of_mem_witnessEvent {A : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) {enc : Finset ι → ℕ} {r : ℕ} {B : Finset ι} {ω : Set ι}
    (hω : ω ∈ witnessEvent enc r A B) : B ∈ witnessSets r A ω :=
  hω.2 ▸ minimalWitness_mem (hAinc.witnessSets_nonempty hω.1)

/-- The minimal-witness event as a countable Boolean combination of witness conditions. -/
theorem witnessEvent_eq {enc : Finset ι → ℕ} (henc : Function.Injective enc)
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (r : ℕ) (B : Finset ι) :
    witnessEvent enc r A B =
      (interiorDepth r A)ᶜ ∩ ({ω | B ∈ witnessSets r A ω} ∩
        ⋂ B' ∈ {B' : Finset ι | enc B' < enc B}, {ω | B' ∈ witnessSets r A ω}ᶜ) := by
  ext ω
  simp only [witnessEvent, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_iInter]
  constructor
  · rintro ⟨hnot, rfl⟩
    refine ⟨hnot, minimalWitness_mem (hAinc.witnessSets_nonempty hnot),
      fun B' hB' hmem => ?_⟩
    exact absurd hB' (not_lt.mpr (enc_minimalWitness_le hmem))
  · rintro ⟨hnot, hBmem, hmin⟩
    refine ⟨hnot, ?_⟩
    by_contra hne
    have hlt : enc (minimalWitness enc r A ω) < enc B :=
      lt_of_le_of_ne (enc_minimalWitness_le hBmem) fun h => hne (henc h)
    exact hmin _ hlt (minimalWitness_mem ⟨B, hBmem⟩)

/-- The event that a fixed finite set is a witness is measurable. -/
theorem measurableSet_mem_witnessSets {A : Set (Set ι)} (hAm : MeasurableSet A)
    (r : ℕ) (B : Finset ι) : MeasurableSet {ω : Set ι | B ∈ witnessSets r A ω} := by
  classical
  by_cases hcard : B.card ≤ r
  · have hrepr : {ω : Set ι | B ∈ witnessSets r A ω} =
        {ω : Set ι | (↑B : Set ι) ⊆ ω} ∩ (fun ω : Set ι => ω \ ↑B) ⁻¹' Aᶜ := by
      ext ω
      simp [mem_witnessSets, hcard]
    rw [hrepr]
    exact (measurableSet_superset_finset B).inter (measurable_diff_finset B hAm.compl)
  · have hrepr : {ω : Set ι | B ∈ witnessSets r A ω} = ∅ := by
      ext ω
      simp [mem_witnessSets, hcard]
    rw [hrepr]
    exact MeasurableSet.empty

theorem measurableSet_witnessEvent [Countable ι] {enc : Finset ι → ℕ}
    (henc : Function.Injective enc) {A : Set (Set ι)} (hAinc : IsIncreasingEvent A)
    (hAm : MeasurableSet A) (r : ℕ) (B : Finset ι) :
    MeasurableSet (witnessEvent enc r A B) := by
  rw [witnessEvent_eq henc hAinc r B]
  exact (measurableSet_interiorDepth hAm r).compl.inter
    ((measurableSet_mem_witnessSets hAm r B).inter
      (MeasurableSet.biInter (Set.to_countable _) fun B' _ =>
        (measurableSet_mem_witnessSets hAm r B').compl))

/-! ### Coordinate blocks of the uniform coupling -/

/-- The σ-algebra generated by the coordinates in `S` on the coupling space `ι → ℝ`. -/
@[reducible] def coordSigma (ι : Type*) (S : Set ι) : MeasurableSpace (ι → ℝ) :=
  ⨆ e ∈ S, MeasurableSpace.comap (fun X : ι → ℝ => X e) inferInstance

theorem coordSigma_le (S : Set ι) :
    coordSigma ι S ≤ (inferInstance : MeasurableSpace (ι → ℝ)) :=
  iSup₂_le fun e _ => (measurable_pi_apply e).comap_le

theorem coordSigma_mono {S T : Set ι} (hST : S ⊆ T) :
    coordSigma ι S ≤ coordSigma ι T := by
  refine iSup₂_le fun e heS => ?_
  exact le_iSup₂_of_le e (hST heS) le_rfl

theorem measurable_eval_coordSigma {S : Set ι} {e : ι} (he : e ∈ S) :
    Measurable[coordSigma ι S] fun X : ι → ℝ => X e :=
  Measurable.of_comap_le (le_iSup₂ (f := fun (e : ι) (_ : e ∈ S) =>
    MeasurableSpace.comap (fun X : ι → ℝ => X e) inferInstance) e he)

/-- A measurable event invariant under changes outside `S` belongs to the coordinate
σ-algebra generated by `S`.  This factor-through-a-canonical-restriction lemma is the
real-coordinate counterpart of `DependsOn.measurableSet_generateFrom_coordinateEvents`. -/
theorem measurableSet_coordSigma_of_eqOn
    {S : Set ι} {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    (hcongr : ∀ X Y : ι → ℝ, (∀ e ∈ S, X e = Y e) → (X ∈ A ↔ Y ∈ A)) :
    MeasurableSet[coordSigma ι S] A := by
  classical
  let restrictTo : (ι → ℝ) → (ι → ℝ) := fun X e => if e ∈ S then X e else 0
  have hrestrict : Measurable[coordSigma ι S] restrictTo := by
    refine @measurable_pi_lambda _ _ _ (coordSigma ι S) _ _ fun e => ?_
    by_cases he : e ∈ S
    · simpa [restrictTo, he] using measurable_eval_coordSigma he
    · simp [restrictTo, he]
  have hpreimage : A = restrictTo ⁻¹' A := by
    ext X
    exact hcongr X (restrictTo X) fun e he => by simp [restrictTo, he]
  rw [hpreimage]
  exact hA.preimage hrestrict

/-- Complementary coordinate blocks are independent under the uniform coupling. -/
theorem indep_coordSigma_compl (S : Set ι) :
    Indep (coordSigma ι S) (coordSigma ι Sᶜ) (couplingMeasure ι) := by
  have h : iIndepFun (fun (e : ι) (X : ι → ℝ) => X e) (couplingMeasure ι) := by
    rw [couplingMeasure]
    exact iIndepFun_infinitePi (X := fun (_ : ι) => (id : ℝ → ℝ)) fun _ => measurable_id
  have h' : iIndep (fun e : ι =>
      MeasurableSpace.comap (fun X : ι → ℝ => X e) inferInstance) (couplingMeasure ι) :=
    (iIndepFun_iff_iIndep _ _ _).mp h
  exact indep_biSup_compl (fun e => (measurable_pi_apply e).comap_le) h' S

/-- Events on disjoint coordinate sets are independent under the common-uniform product law. -/
theorem indepSet_of_measurableSet_coordSigma_of_disjoint
    {S T : Set ι} (hST : Disjoint S T)
    {A B : Set (ι → ℝ)}
    (hA : MeasurableSet[coordSigma ι S] A)
    (hB : MeasurableSet[coordSigma ι T] B) :
    IndepSet A B (couplingMeasure ι) := by
  have hTcomp : T ⊆ Sᶜ := by
    intro e heT
    change e ∉ S
    exact fun heS => Set.disjoint_left.mp hST heS heT
  have hBcomp : MeasurableSet[coordSigma ι Sᶜ] B :=
    (coordSigma_mono hTcomp) B hB
  exact (indep_coordSigma_compl S).indepSet_of_measurableSet hA hBcomp

/-- **Block factorization for the uniform coupling**: a box event over the coordinates of
`B` decouples from any event measurable in the coordinates off `B`, and the box
probability is the product of its one-dimensional marginals. -/
theorem couplingMeasure_pi_inter (B : Finset ι) {S : ι → Set ℝ}
    (hS : ∀ e, MeasurableSet (S e)) {C : Set (ι → ℝ)}
    (hC : MeasurableSet[coordSigma ι ((↑B : Set ι)ᶜ)] C) :
    couplingMeasure ι ((↑B : Set ι).pi S ∩ C) =
      (∏ e ∈ B, volume.restrict (Set.Icc (0 : ℝ) 1) (S e)) * couplingMeasure ι C := by
  have hboxB : MeasurableSet[coordSigma ι (↑B : Set ι)] ((↑B : Set ι).pi S) := by
    have hrepr : (↑B : Set ι).pi S =
        ⋂ e ∈ (↑B : Set ι), (fun X : ι → ℝ => X e) ⁻¹' S e := by
      ext X
      simp [Set.mem_pi]
    rw [hrepr]
    exact MeasurableSet.biInter B.countable_toSet fun e he =>
      measurable_eval_coordSigma he (hS e)
  have hboxm : MeasurableSet ((↑B : Set ι).pi S) :=
    MeasurableSet.pi B.countable_toSet fun e _ => hS e
  have hCm : MeasurableSet C := coordSigma_le _ C hC
  have hindep := (indep_coordSigma_compl (↑B : Set ι)).indepSet_of_measurableSet hboxB hC
  rw [(indepSet_iff_measure_inter_eq_mul hboxm hCm (couplingMeasure ι)).mp hindep]
  congr 1
  rw [couplingMeasure, Measure.infinitePi_pi _ fun e _ => hS e]

/-- The event that finitely many coordinates all exceed a level is measurable. -/
theorem measurableSet_forall_le (B : Finset ι) (c : ℝ) :
    MeasurableSet {X : ι → ℝ | ∀ e ∈ B, c ≤ X e} := by
  have h : {X : ι → ℝ | ∀ e ∈ B, c ≤ X e} =
      ⋂ e ∈ (↑B : Set ι), (fun X : ι → ℝ => X e) ⁻¹' Set.Ici c := by
    ext X
    simp
  rw [h]
  exact MeasurableSet.biInter B.countable_toSet fun e _ =>
    measurable_pi_apply e measurableSet_Ici

/-! ### One-dimensional marginal masses -/

theorem volume_restrict_Icc_Iio (p : I) :
    volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Iio (p : ℝ)) = ENNReal.ofReal (p : ℝ) := by
  rw [Measure.restrict_apply measurableSet_Iio]
  have h : Set.Iio (p : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (0 : ℝ) (p : ℝ) := by
    ext x
    constructor
    · rintro ⟨hxp, hx0, _⟩
      exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨hxp, hx0, le_trans (le_of_lt hxp) p.2.2⟩
  rw [h, Real.volume_Ico, sub_zero]

theorem volume_restrict_Icc_Ico (p q : I) :
    volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Ico (p : ℝ) (q : ℝ)) =
      ENNReal.ofReal ((q : ℝ) - p) := by
  rw [Measure.restrict_apply measurableSet_Ico]
  have h : Set.Ico (p : ℝ) (q : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (p : ℝ) (q : ℝ) :=
    Set.inter_eq_self_of_subset_left fun x hx =>
      ⟨le_trans p.2.1 hx.1, le_trans (le_of_lt hx.2) q.2.2⟩
  rw [h, Real.volume_Ico]

/-! ### The forced threshold configuration -/

/-- The `p`-threshold configuration with the coordinates of `B` forced open. On the box
`{∀ e ∈ B, X e < p}` it agrees with `thresholdConfiguration p`, and it is measurable in
the coordinates off `B`. -/
def forcedThreshold (B : Finset ι) (p : I) (X : ι → ℝ) : Set ι :=
  ↑B ∪ (thresholdConfiguration p X \ ↑B)

theorem forcedThreshold_eq_of_subset {B : Finset ι} {p : I} {X : ι → ℝ}
    (h : (↑B : Set ι) ⊆ thresholdConfiguration p X) :
    forcedThreshold B p X = thresholdConfiguration p X :=
  Set.union_diff_cancel h

theorem measurable_forcedThreshold_coordSigma (B : Finset ι) (p : I) :
    Measurable[coordSigma ι ((↑B : Set ι)ᶜ)] (forcedThreshold B p) := by
  classical
  have hcomp : forcedThreshold B p =
      (fun P : ι → Prop => {i | P i}) ∘
        fun (X : ι → ℝ) (e : ι) => (e ∈ B ∨ (X e < (p : ℝ) ∧ e ∉ B) : Prop) := by
    funext X
    ext e
    simp only [forcedThreshold, thresholdConfiguration, Function.comp_apply,
      Set.mem_union, Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq]
  have hcoord : Measurable[coordSigma ι ((↑B : Set ι)ᶜ)]
      fun (X : ι → ℝ) (e : ι) => (e ∈ B ∨ (X e < (p : ℝ) ∧ e ∉ B) : Prop) := by
    refine @measurable_pi_lambda _ _ _ (coordSigma ι ((↑B : Set ι)ᶜ)) _ _ fun e => ?_
    by_cases he : e ∈ B
    · have hconst : (fun X : ι → ℝ => (e ∈ B ∨ (X e < (p : ℝ) ∧ e ∉ B) : Prop)) =
          fun _ => True := funext fun X => eq_true (Or.inl he)
      rw [hconst]
      exact measurable_const
    · have heq : (fun X : ι → ℝ => (e ∈ B ∨ (X e < (p : ℝ) ∧ e ∉ B) : Prop)) =
          (fun x : ℝ => (x < (p : ℝ) : Prop)) ∘ fun X : ι → ℝ => X e :=
        funext fun X => propext
          ⟨fun h => h.elim (fun h' => absurd h' he) And.left, fun h => Or.inr ⟨h, he⟩⟩
      rw [heq]
      exact (measurable_lt_prop _).comp (measurable_eval_coordSigma (by simpa using he))
  rw [hcomp]
  exact Measurable.comp (by fun_prop) hcoord

/-! ### The per-witness block estimate -/

/-- **The per-witness block estimate** (Grimmett p. 51, in cross-multiplied `ℝ≥0∞` form):
on the event that the sprinkled configuration `η_{p₂}` has minimal witness `B`, the
witness coordinates lie in `[0, p₂)`; conditioning them into `[p₁, p₂)` — which keeps
`η_{p₁}` off the witness — costs at most the factor `((p₂ - p₁)/p₂)^{|B|}`. -/
theorem couplingMeasure_witnessEvent_block_le [Countable ι] {enc : Finset ι → ℕ}
    (henc : Function.Injective enc) {A : Set (Set ι)} (hAinc : IsIncreasingEvent A)
    (hAm : MeasurableSet A) {p₁ p₂ : I} (r : ℕ) (B : Finset ι) :
    ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B) ≤
      ENNReal.ofReal (p₂ : ℝ) ^ r *
        couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B ∩
          {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) := by
  classical
  by_cases hcard : B.card ≤ r
  · have hCmble : MeasurableSet[coordSigma ι ((↑B : Set ι)ᶜ)]
        (forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B) :=
      measurable_forcedThreshold_coordSigma B p₂
        (measurableSet_witnessEvent henc hAinc hAm r B)
    have hW : thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B =
        (↑B : Set ι).pi (fun _ => Set.Iio (p₂ : ℝ)) ∩
          forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B := by
      ext X
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi, Set.mem_Iio,
        Finset.mem_coe]
      constructor
      · intro hX
        have hsub : (↑B : Set ι) ⊆ thresholdConfiguration p₂ X :=
          (hAinc.mem_witnessSets_of_mem_witnessEvent hX).2.1
        exact ⟨fun e he => hsub (Finset.mem_coe.mpr he),
          by rwa [forcedThreshold_eq_of_subset hsub]⟩
      · rintro ⟨hbox, hX⟩
        have hsub : (↑B : Set ι) ⊆ thresholdConfiguration p₂ X := fun e he =>
          hbox e (Finset.mem_coe.mp he)
        rwa [forcedThreshold_eq_of_subset hsub] at hX
    have hK : thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e} =
        (↑B : Set ι).pi (fun _ => Set.Ico (p₁ : ℝ) (p₂ : ℝ)) ∩
          forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B := by
      rw [hW]
      ext X
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_Iio, Set.mem_Ico,
        Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨⟨hbox, hXC⟩, hcl⟩
        exact ⟨fun e he => ⟨hcl e he, hbox e he⟩, hXC⟩
      · rintro ⟨hbox, hXC⟩
        exact ⟨⟨fun e he => (hbox e he).2, hXC⟩, fun e he => (hbox e he).1⟩
    have hμW : couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B) =
        ENNReal.ofReal (p₂ : ℝ) ^ B.card *
          couplingMeasure ι (forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B) := by
      rw [hW, couplingMeasure_pi_inter B (fun _ => measurableSet_Iio) hCmble]
      congr 1
      simp only [Finset.prod_const]
      rw [volume_restrict_Icc_Iio]
    have hμK : couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) =
        ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ B.card *
          couplingMeasure ι (forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B) := by
      rw [hK, couplingMeasure_pi_inter B (fun _ => measurableSet_Ico) hCmble]
      congr 1
      simp only [Finset.prod_const]
      rw [volume_restrict_Icc_Ico]
    rw [hμW, hμK]
    set c := couplingMeasure ι (forcedThreshold B p₂ ⁻¹' witnessEvent enc r A B) with hc
    set a := ENNReal.ofReal (p₂ : ℝ) with ha
    set b := ENNReal.ofReal ((p₂ : ℝ) - p₁) with hb
    have hba : b ≤ a := ENNReal.ofReal_le_ofReal (by linarith [p₁.2.1])
    calc b ^ r * (a ^ B.card * c)
        = b ^ (r - B.card) * (b ^ B.card * (a ^ B.card * c)) := by
          rw [← pow_sub_mul_pow b hcard, mul_assoc]
      _ ≤ a ^ (r - B.card) * (b ^ B.card * (a ^ B.card * c)) :=
          mul_le_mul_left (pow_le_pow_left' hba _) _
      _ = a ^ r * (b ^ B.card * c) := by
          rw [← pow_sub_mul_pow a hcard]
          ring
  · have hempty : thresholdConfiguration p₂ ⁻¹' witnessEvent enc r A B = ∅ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hX
      exact hcard (hAinc.mem_witnessSets_of_mem_witnessEvent hX).1
    rw [hempty]
    simp

/-! ### The sprinkling inequality -/

/-- **The coupling form of the sprinkling bound**: on the joint space of Grimmett's
uniform coupling, failure of deep interiority at density `p₂` together with
`[p₁, p₂)`-values on the minimal witness forces `η_{p₁} ∉ A`; summing the per-witness
blocks over the countable partition gives the cross-multiplied inequality. -/
theorem couplingMeasure_sprinkling_le [Countable ι] {A : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A) {p₁ p₂ : I}
    (h12 : (p₁ : ℝ) < p₂) (r : ℕ) :
    ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
        couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' (interiorDepth r A)ᶜ) ≤
      ENNReal.ofReal (p₂ : ℝ) ^ r *
        couplingMeasure ι (thresholdConfiguration p₁ ⁻¹' Aᶜ) := by
  classical
  obtain ⟨enc⟩ := nonempty_embedding_nat (Finset ι)
  have hcover : thresholdConfiguration p₂ ⁻¹' (interiorDepth r A)ᶜ =
      ⋃ B : Finset ι, thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B := by
    ext X
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hX
      exact ⟨minimalWitness (⇑enc) r A (thresholdConfiguration p₂ X), hX, rfl⟩
    · rintro ⟨B, hB⟩
      exact hB.1
  have hWm : ∀ B : Finset ι, MeasurableSet
      (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B) := fun B =>
    measurable_thresholdConfiguration p₂
      (measurableSet_witnessEvent enc.injective hAinc hAm r B)
  have hKm : ∀ B : Finset ι, MeasurableSet
      (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) := fun B =>
    (hWm B).inter (measurableSet_forall_le B (p₁ : ℝ))
  have hWdisj : Pairwise (Function.onFun Disjoint
      fun B : Finset ι => thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B) := by
    intro B B' hne
    rw [Function.onFun, Set.disjoint_left]
    intro X hX hX'
    exact hne (hX.2.symm.trans hX'.2)
  have hKdisj : Pairwise (Function.onFun Disjoint
      fun B : Finset ι => thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) := fun B B' hne =>
    (hWdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hKsub : ∀ B : Finset ι,
      thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
        {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e} ⊆
      thresholdConfiguration p₁ ⁻¹' Aᶜ := by
    rintro B X ⟨hXW, hXcl⟩
    have hBW := hAinc.mem_witnessSets_of_mem_witnessEvent hXW
    have hsub : thresholdConfiguration p₁ X ⊆ thresholdConfiguration p₂ X \ ↑B := by
      intro e he
      have he1 : X e < (p₁ : ℝ) := he
      refine ⟨lt_trans he1 h12, fun heB => ?_⟩
      exact absurd he1 (not_lt.mpr (hXcl e (Finset.mem_coe.mp heB)))
    exact fun hmem => hBW.2.2 (hAinc hsub hmem)
  calc ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r *
      couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' (interiorDepth r A)ᶜ)
      = ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r * ∑' B : Finset ι, couplingMeasure ι
          (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B) := by
        rw [hcover, measure_iUnion hWdisj hWm]
    _ = ∑' B : Finset ι, ENNReal.ofReal ((p₂ : ℝ) - p₁) ^ r * couplingMeasure ι
          (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' B : Finset ι, ENNReal.ofReal (p₂ : ℝ) ^ r * couplingMeasure ι
          (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) :=
        ENNReal.tsum_le_tsum fun B =>
          couplingMeasure_witnessEvent_block_le enc.injective hAinc hAm r B
    _ = ENNReal.ofReal (p₂ : ℝ) ^ r * ∑' B : Finset ι, couplingMeasure ι
          (thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (p₂ : ℝ) ^ r * couplingMeasure ι
          (⋃ B : Finset ι, thresholdConfiguration p₂ ⁻¹' witnessEvent (⇑enc) r A B ∩
            {X : ι → ℝ | ∀ e ∈ B, (p₁ : ℝ) ≤ X e}) := by
        rw [measure_iUnion hKdisj hKm]
    _ ≤ ENNReal.ofReal (p₂ : ℝ) ^ r *
          couplingMeasure ι (thresholdConfiguration p₁ ⁻¹' Aᶜ) :=
        mul_le_mul_right (measure_mono (Set.iUnion_subset hKsub)) _

/-- **The ACCFR sprinkling inequality** (Grimmett Theorem (2.45), inequality (2.46),
pp. 49–51): for an increasing measurable event `A` and densities `p₁ < p₂`, the
probability of missing the interior of depth `r` at density `p₂` is controlled by the
probability of missing `A` at density `p₁`:

`1 - P_{p₂}(I_r(A)) ≤ (p₂ / (p₂ - p₁))^r (1 - P_{p₁}(A))`. -/
theorem IsIncreasingEvent.one_sub_setBernoulli_real_interiorDepth_le [Countable ι]
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) {r : ℕ} (_hr : 1 ≤ r) :
    1 - setBer((Set.univ : Set ι), p₂).real (interiorDepth r A) ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ r * (1 - setBer((Set.univ : Set ι), p₁).real A) := by
  have hIm : MeasurableSet (interiorDepth r A) := measurableSet_interiorDepth hAm r
  have hkey := couplingMeasure_sprinkling_le (ι := ι) hAinc hAm h12 r
  have hmap₂ : couplingMeasure ι (thresholdConfiguration p₂ ⁻¹' (interiorDepth r A)ᶜ) =
      setBer((Set.univ : Set ι), p₂) (interiorDepth r A)ᶜ := by
    rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p₂,
      Measure.map_apply (measurable_thresholdConfiguration p₂) hIm.compl]
  have hmap₁ : couplingMeasure ι (thresholdConfiguration p₁ ⁻¹' Aᶜ) =
      setBer((Set.univ : Set ι), p₁) Aᶜ := by
    rw [← couplingMeasure_map_thresholdConfiguration (ι := ι) p₁,
      Measure.map_apply (measurable_thresholdConfiguration p₁) hAm.compl]
  rw [hmap₂, hmap₁] at hkey
  have hne : ENNReal.ofReal (p₂ : ℝ) ^ r * setBer((Set.univ : Set ι), p₁) Aᶜ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hne hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by linarith [p₁.2.1] : (0 : ℝ) ≤ (p₂ : ℝ) - p₁),
    ENNReal.toReal_ofReal p₂.2.1, ← measureReal_def, ← measureReal_def,
    measureReal_compl hIm, measureReal_compl hAm, probReal_univ, probReal_univ] at hreal
  have hd : (0 : ℝ) < (p₂ : ℝ) - p₁ := sub_pos.mpr h12
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hd r)]
  linarith [hreal]

/-! ### The cubic lattice specialization -/

/-- **The sprinkling inequality on the cubic lattice** (Grimmett Theorem (2.45)). -/
theorem IsIncreasingEvent.one_sub_bernoulliBondMeasure_real_interiorDepth_le {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) {r : ℕ} (hr : 1 ≤ r) :
    1 - (bernoulliBondMeasure d p₂).real (interiorDepth r A) ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ r * (1 - (bernoulliBondMeasure d p₁).real A) := by
  simpa [bernoulliBondMeasure] using
    hAinc.one_sub_setBernoulli_real_interiorDepth_le hAm h12 hr

end Percolation
