import Percolation.Bernoulli.LSSDilutionSequential

/-!
# Finite event decomposition for the LSS induction

This file formalizes the `N⁰ ∪ N¹ ∪ M` partition in the proof of Grimmett Theorem
7.65, equations (7.119)--(7.122).  Keeping the original-field and retention-field events
separate is essential: on `N¹` the source cancels the independent retention bits and retains
only the condition that the corresponding original sites are open.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Finite Fubini with the second coordinate outermost, stated for real probabilities. -/
theorem measureReal_prod_eq_sum_swap_sections
    {α β : Type*} [MeasurableSpace α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (mu : Measure α) (nu : Measure β)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    (mu.prod nu).real A =
      ∑ y, nu.real {y} * mu.real ((fun x ↦ (x, y)) ⁻¹' A) := by
  rw [measureReal_def, Measure.prod_apply_symm hA, lintegral_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y _hy
    rw [ENNReal.toReal_mul]
    simp only [measureReal_def]
    ring
  · intro y _hy
    exact ENNReal.mul_ne_top (measure_ne_top mu _) (measure_ne_top nu _)

/-- The independently diluted field has the prescribed values `z` on the finite set `C`. -/
def dilutedConstraintEvent {ι : Type*} (C : Finset ι) (z : Set ι) :
    Set (Set ι × Set ι) :=
  {yz | ∀ x ∈ C, (x ∈ yz.1 ∧ x ∈ yz.2) ↔ x ∈ z}

/-- All sites in `C` are open in the original field. -/
def originalOpenOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | (C : Set ι) ⊆ yz.1}

/-- One specified site is open in the original field. -/
def originalOpenAtProductEvent {ι : Type*} (x : ι) :
    Set (Set ι × Set ι) :=
  {yz | x ∈ yz.1}

/-- All sites in `C` are retained by the auxiliary iid field. -/
def retentionOpenOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | (C : Set ι) ⊆ yz.2}

/-- Every retention bit in `C` is closed.  This is Grimmett's event `B⁰`. -/
def retentionClosedOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | Disjoint (C : Set ι) yz.2}

theorem measurableSet_dilutedConstraintEvent
    {ι : Type*} [Fintype ι] [MeasurableSpace (Set ι)]
    [MeasurableSingletonClass (Set ι)] (C : Finset ι) (z : Set ι) :
    MeasurableSet (dilutedConstraintEvent C z) :=
  Set.toFinite _ |>.measurableSet

theorem measurableSet_originalOpenOnProductEvent
    {ι : Type*} [Fintype ι] [MeasurableSpace (Set ι)]
    [MeasurableSingletonClass (Set ι)] (C : Finset ι) :
    MeasurableSet (originalOpenOnProductEvent C) :=
  Set.toFinite _ |>.measurableSet

theorem measurableSet_retentionOpenOnProductEvent
    {ι : Type*} [Fintype ι] [MeasurableSpace (Set ι)]
    [MeasurableSingletonClass (Set ι)] (C : Finset ι) :
    MeasurableSet (retentionOpenOnProductEvent C) :=
  Set.toFinite _ |>.measurableSet

theorem measurableSet_retentionClosedOnProductEvent
    {ι : Type*} [Fintype ι] [MeasurableSpace (Set ι)]
    [MeasurableSingletonClass (Set ι)] (C : Finset ι) :
    MeasurableSet (retentionClosedOnProductEvent C) :=
  Set.toFinite _ |>.measurableSet

/-- The auxiliary iid field closes every coordinate in `C` with probability
`(1-p)^|C|`, including when viewed on the full product space. -/
theorem prod_setBernoulli_real_retentionClosedOnProductEvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (C : Finset ι) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        (retentionClosedOnProductEvent C) =
      (1 - (p : ℝ)) ^ C.card := by
  have hevent : retentionClosedOnProductEvent C =
      Set.univ ×ˢ {retained : Set ι | Disjoint (C : Set ι) retained} := by
    ext yz
    simp [retentionClosedOnProductEvent]
  rw [hevent, measureReal_prod_prod, probReal_univ,
    one_mul, setBernoulli_real_disjoint_finset_univ]

/-- Likewise, retaining every coordinate in `C` contributes `p^|C|`. -/
theorem prod_setBernoulli_real_retentionOpenOnProductEvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (C : Finset ι) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        (retentionOpenOnProductEvent C) =
      (p : ℝ) ^ C.card := by
  have hevent : retentionOpenOnProductEvent C =
      Set.univ ×ˢ {retained : Set ι | (C : Set ι) ⊆ retained} := by
    ext yz
    simp [retentionOpenOnProductEvent]
  rw [hevent, measureReal_prod_prod, probReal_univ,
    one_mul, setBernoulli_real_superset_finset_univ]

/-- Earlier prescribed zeros lying within graph distance `k` of the current site. -/
noncomputable def lssNearZero {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) : Finset ι :=
  by
    classical
    exact C.filter fun x ↦ G.edist current x ≤ k ∧ x ∉ z

/-- Earlier prescribed ones lying within graph distance `k` of the current site. -/
noncomputable def lssNearOne {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) : Finset ι :=
  by
    classical
    exact C.filter fun x ↦ G.edist current x ≤ k ∧ x ∈ z

/-- Earlier sites outside the dependence neighborhood of the current site. -/
noncomputable def lssFar {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) : Finset ι :=
  by
    classical
    exact C.filter fun x ↦ (k : ℕ∞) < G.edist current x

theorem mem_lssNearZero {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι) (C : Finset ι) (z : Set ι)
    (x : ι) :
    x ∈ lssNearZero G k current C z ↔
      x ∈ C ∧ G.edist current x ≤ k ∧ x ∉ z := by
  classical
  simp [lssNearZero]

theorem mem_lssNearOne {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι) (C : Finset ι) (z : Set ι)
    (x : ι) :
    x ∈ lssNearOne G k current C z ↔
      x ∈ C ∧ G.edist current x ≤ k ∧ x ∈ z := by
  classical
  simp [lssNearOne]

theorem mem_lssFar {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι) (C : Finset ι) (x : ι) :
    x ∈ lssFar G k current C ↔
      x ∈ C ∧ (k : ℕ∞) < G.edist current x := by
  classical
  simp [lssFar]

theorem pairwiseDisjoint_lssNearZero_lssNearOne_lssFar
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) :
    Disjoint (lssNearZero G k current C z) (lssNearOne G k current C z) ∧
      Disjoint (lssNearZero G k current C z) (lssFar G k current C) ∧
      Disjoint (lssNearOne G k current C z) (lssFar G k current C) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxzero hxone
    exact (mem_lssNearZero G k current C z x).mp hxzero |>.2.2
      ((mem_lssNearOne G k current C z x).mp hxone |>.2.2)
  · rw [Finset.disjoint_left]
    intro x hxzero hxfar
    exact (not_lt_of_ge
      ((mem_lssNearZero G k current C z x).mp hxzero |>.2.1))
      ((mem_lssFar G k current C x).mp hxfar |>.2)
  ·
    rw [Finset.disjoint_left]
    intro x hxone hxfar
    exact (not_lt_of_ge
      ((mem_lssNearOne G k current C z x).mp hxone |>.2.1))
      ((mem_lssFar G k current C x).mp hxfar |>.2)

/-- The source partition `N⁰ ∪ N¹ ∪ M` is exactly the set of earlier sites. -/
theorem lssNearZero_union_lssNearOne_union_lssFar
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) :
    lssNearZero G k current C z ∪ lssNearOne G k current C z ∪
        lssFar G k current C = C := by
  classical
  ext x
  simp only [Finset.mem_union, mem_lssNearZero, mem_lssNearOne, mem_lssFar]
  constructor
  · aesop
  · intro hx
    by_cases hnear : G.edist current x ≤ k
    · by_cases hxz : x ∈ z <;> aesop
    · right
      exact ⟨hx, lt_of_not_ge hnear⟩

theorem lssNearZero_card_add_lssNearOne_card_le
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) (B : ℕ)
    (hB : (C.filter fun x ↦ G.edist current x ≤ k).card ≤ B) :
    (lssNearZero G k current C z).card +
        (lssNearOne G k current C z).card ≤ B := by
  classical
  have hdisj : Disjoint (lssNearZero G k current C z)
      (lssNearOne G k current C z) := by
    rw [Finset.disjoint_left]
    intro x hxzero hxone
    exact (mem_lssNearZero G k current C z x).mp hxzero |>.2.2
      ((mem_lssNearOne G k current C z x).mp hxone |>.2.2)
  rw [← Finset.card_union_of_disjoint hdisj]
  apply (Finset.card_le_card ?_).trans hB
  intro x hx
  rw [Finset.mem_union] at hx
  rw [Finset.mem_filter]
  rcases hx with hx | hx
  · exact ⟨(mem_lssNearZero G k current C z x).mp hx |>.1,
      (mem_lssNearZero G k current C z x).mp hx |>.2.1⟩
  · exact ⟨(mem_lssNearOne G k current C z x).mp hx |>.1,
      (mem_lssNearOne G k current C z x).mp hx |>.2.1⟩

/-- The diluted constraint splits exactly into the three source classes. -/
theorem dilutedConstraintEvent_eq_lss_partition
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) :
    dilutedConstraintEvent C z =
      (((dilutedConstraintEvent (lssNearZero G k current C z) z ∩
          originalOpenOnProductEvent (lssNearOne G k current C z)) ∩
        retentionOpenOnProductEvent (lssNearOne G k current C z)) ∩
      dilutedConstraintEvent (lssFar G k current C) z) := by
  classical
  ext yz
  simp only [dilutedConstraintEvent, originalOpenOnProductEvent,
    retentionOpenOnProductEvent, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro x hx
      exact h x ((mem_lssNearZero G k current C z x).mp hx).1
    · intro x hx
      have hxC := (mem_lssNearOne G k current C z x).mp hx |>.1
      exact (h x hxC).mpr ((mem_lssNearOne G k current C z x).mp hx).2.2 |>.1
    · intro x hx
      have hxC := (mem_lssNearOne G k current C z x).mp hx |>.1
      exact (h x hxC).mpr ((mem_lssNearOne G k current C z x).mp hx).2.2 |>.2
    · intro x hx
      exact h x ((mem_lssFar G k current C x).mp hx).1
  · rintro ⟨⟨⟨hzero, honeY⟩, honeZ⟩, hfar⟩ x hxC
    have hxpartition :
        (x ∈ lssNearZero G k current C z ∨
          x ∈ lssNearOne G k current C z) ∨
        x ∈ lssFar G k current C := by
      rw [← Finset.mem_union, ← Finset.mem_union,
        lssNearZero_union_lssNearOne_union_lssFar G k current C z]
      exact hxC
    rcases hxpartition with (hxzero | hxone) | hxfar
    · exact hzero x hxzero
    · constructor
      · intro _
        exact (mem_lssNearOne G k current C z x).mp hxone |>.2.2
      · intro _
        exact ⟨honeY hxone, honeZ hxone⟩
    · exact hfar x hxfar

/-- Closing every retention bit in `N⁰` is a subevent of the product-zero condition there. -/
theorem retentionClosedOnProductEvent_subset_dilutedConstraintEvent_nearZero
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) (k : ℕ)
    (current : ι) (C : Finset ι) (z : Set ι) :
    retentionClosedOnProductEvent (lssNearZero G k current C z) ⊆
      dilutedConstraintEvent (lssNearZero G k current C z) z := by
  intro yz hyz x hx
  have hxnotz := (mem_lssNearZero G k current C z x).mp hx |>.2.2
  have hxnotretained : x ∉ yz.2 := by
    exact Set.disjoint_left.1 hyz hx
  simp [hxnotz, hxnotretained]

/-- After fixing the retention field, a diluted constraint only reads the listed original
coordinates. -/
theorem dependsOn_dilutedConstraint_originalSection
    {ι : Type*} [DecidableEq ι] (C : Finset ι) (z retained : Set ι) :
    DependsOn C {original | (original, retained) ∈ dilutedConstraintEvent C z} := by
  intro y y' hyy'
  simp only [dilutedConstraintEvent, Set.mem_setOf_eq]
  constructor <;> intro h x hx
  · simpa [hyy' x hx] using h x hx
  · simpa [hyy' x hx] using h x hx

/-- The symmetric section statement for the auxiliary retention field. -/
theorem dependsOn_dilutedConstraint_retentionSection
    {ι : Type*} [DecidableEq ι] (C : Finset ι) (z original : Set ι) :
    DependsOn C {retained | (original, retained) ∈ dilutedConstraintEvent C z} := by
  intro y y' hyy'
  simp only [dilutedConstraintEvent, Set.mem_setOf_eq]
  constructor <;> intro h x hx
  · simpa [hyy' x hx] using h x hx
  · simpa [hyy' x hx] using h x hx

theorem dependsOn_retentionClosedEvent
    {ι : Type*} [DecidableEq ι] (C : Finset ι) :
    DependsOn C {retained : Set ι | Disjoint (C : Set ι) retained} := by
  intro y y' hyy'
  simp only [Set.mem_setOf_eq, Set.disjoint_left]
  constructor <;> intro h x hxC hx
  · exact h hxC ((hyy' x hxC).mpr hx)
  · exact h hxC ((hyy' x hxC).mp hx)

/-- A `DependsOn` certificate is exactly measurability in the corresponding site-coordinate
sigma-algebra. -/
theorem DependsOn.measurableSet_siteCoordinateMeasurableSpace
    {ι : Type*} [DecidableEq ι] {C : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn C A) :
    MeasurableSet[siteCoordinateMeasurableSpace ι (C : Set ι)] A := by
  simpa [siteCoordinateMeasurableSpace, coordinateEvents] using
    hA.measurableSet_generateFrom_coordinateEvents (Set.Subset.rfl)

/-- Equation (7.120), ratio-free factorization form.  A current original-field bit is
independent of a diluted history whose original coordinates all lie beyond distance `k`;
the auxiliary retention configuration may be arbitrary. -/
theorem productMeasure_real_originalClosed_inter_dilutedConstraint_far
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu) (p : I)
    (current : ι) (C : Finset ι) (z : Set ι) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        ({yz : Set ι × Set ι | current ∉ yz.1} ∩
          dilutedConstraintEvent (lssFar G k current C) z) =
      mu.real {original : Set ι | current ∉ original} *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent (lssFar G k current C) z) := by
  classical
  let M := lssFar G k current C
  let nu := setBer((Set.univ : Set ι), p)
  let closed : Set (Set ι) := {original | current ∉ original}
  let farEvent : Set (Set ι × Set ι) := dilutedConstraintEvent M z
  have hsep : ∀ x ∈ ({current} : Set ι), ∀ y ∈ (M : Set ι),
      (k : ℕ∞) < G.edist x y := by
    intro x hx y hy
    have hxcurrent : x = current := by simpa using hx
    subst x
    exact (mem_lssFar G k current C y).mp hy |>.2
  have hindep := hmu ({current} : Set ι) (M : Set ι) hsep
  have hclosed : MeasurableSet[siteCoordinateMeasurableSpace ι ({current} : Set ι)]
      closed := by
    apply MeasurableSet.compl
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨current, Set.mem_singleton current, rfl⟩
  have hfarEvent : MeasurableSet farEvent :=
    measurableSet_dilutedConstraintEvent M z
  have hinter : MeasurableSet
      ({yz : Set ι × Set ι | current ∉ yz.1} ∩ farEvent) :=
    (Set.toFinite _).measurableSet
  change (mu.prod nu).real
      ({yz : Set ι × Set ι | current ∉ yz.1} ∩ farEvent) =
    mu.real closed * (mu.prod nu).real farEvent
  rw [measureReal_prod_eq_sum_swap_sections mu nu hinter,
    measureReal_prod_eq_sum_swap_sections mu nu hfarEvent,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro retained _hretained
  let farSection : Set (Set ι) :=
    {original | (original, retained) ∈ farEvent}
  have hsection : MeasurableSet[siteCoordinateMeasurableSpace ι (M : Set ι)]
      farSection := by
    exact (dependsOn_dilutedConstraint_originalSection M z retained
      ).measurableSet_siteCoordinateMeasurableSpace
  have hfactor := (hindep.indepSet_of_measurableSet hclosed hsection).measure_inter_eq_mul
  have hfactorReal := congrArg ENNReal.toReal hfactor
  rw [ENNReal.toReal_mul] at hfactorReal
  change nu.real {retained} * mu.real (closed ∩ farSection) =
    mu.real closed * (nu.real {retained} * mu.real farSection)
  rw [show mu.real (closed ∩ farSection) = mu.real closed * mu.real farSection by
    simpa only [measureReal_def] using hfactorReal]
  ring

/-- The one-site marginal hypothesis in (7.66) bounds the complementary closed-site mass. -/
theorem measureReal_originalClosed_le_one_sub_of_le_open
    {ι : Type*} [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (current : ι) (theta : ℝ)
    (hmarginal : theta ≤ mu.real {original : Set ι | current ∈ original}) :
    mu.real {original : Set ι | current ∉ original} ≤ 1 - theta := by
  have hopen : MeasurableSet {original : Set ι | current ∈ original} :=
    measurableSet_mem current
  have hclosed : {original : Set ι | current ∉ original} =
      {original : Set ι | current ∈ original}ᶜ := by
    ext original
    simp
  rw [hclosed, measureReal_compl hopen, probReal_univ]
  linarith

/-- Inequality form of (7.120), ready for substitution into (7.119). -/
theorem productMeasure_real_originalClosed_inter_dilutedConstraint_far_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu) (p : I)
    (current : ι) (C : Finset ι) (z : Set ι) (theta : ℝ)
    (hmarginal : theta ≤ mu.real {original : Set ι | current ∈ original}) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        ({yz : Set ι × Set ι | current ∉ yz.1} ∩
          dilutedConstraintEvent (lssFar G k current C) z) ≤
      (1 - theta) *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent (lssFar G k current C) z) := by
  rw [productMeasure_real_originalClosed_inter_dilutedConstraint_far
    G k mu hmu p current C z]
  gcongr
  exact measureReal_originalClosed_le_one_sub_of_le_open mu current theta hmarginal

/-- Equation (7.121), ratio-free form.  Closing the independent retention bits on `N⁰`
contributes exactly `(1-p)^|N⁰|` to an event whose remaining retention support is disjoint. -/
theorem productMeasure_real_retentionClosed_inter_originalOpen_inter_dilutedConstraint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (Nzero None M : Finset ι) (z : Set ι)
    (hdisj : Disjoint Nzero M) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        ((retentionClosedOnProductEvent Nzero ∩
          originalOpenOnProductEvent None) ∩
          dilutedConstraintEvent M z) =
      (1 - (p : ℝ)) ^ Nzero.card *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (originalOpenOnProductEvent None ∩ dilutedConstraintEvent M z) := by
  classical
  let nu := setBer((Set.univ : Set ι), p)
  let Bzero : Set (Set ι) :=
    {retained | Disjoint (Nzero : Set ι) retained}
  let Aone : Set (Set ι) := {original | (None : Set ι) ⊆ original}
  let farEvent : Set (Set ι × Set ι) := dilutedConstraintEvent M z
  have hleft : MeasurableSet
      ((retentionClosedOnProductEvent Nzero ∩
        originalOpenOnProductEvent None) ∩ farEvent) :=
    (Set.toFinite _).measurableSet
  have hright : MeasurableSet
      (originalOpenOnProductEvent None ∩ farEvent) :=
    (Set.toFinite _).measurableSet
  change (mu.prod nu).real
      ((retentionClosedOnProductEvent Nzero ∩
        originalOpenOnProductEvent None) ∩ farEvent) =
    (1 - (p : ℝ)) ^ Nzero.card *
      (mu.prod nu).real (originalOpenOnProductEvent None ∩ farEvent)
  rw [measureReal_prod_eq_sum_sections mu nu hleft,
    measureReal_prod_eq_sum_sections mu nu hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro original _horiginal
  by_cases hone : original ∈ Aone
  · change (None : Set ι) ⊆ original at hone
    let farSection : Set (Set ι) :=
      {retained | (original, retained) ∈ farEvent}
    have hBzero : MeasurableSet[MeasurableSpace.generateFrom
        (coordinateEvents (Nzero : Set ι))] Bzero := by
      exact (dependsOn_retentionClosedEvent Nzero
        ).measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
    have hfarSection : MeasurableSet[MeasurableSpace.generateFrom
        (coordinateEvents (M : Set ι))] farSection := by
      exact (dependsOn_dilutedConstraint_retentionSection M z original
        ).measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
    have hsetDisj : Disjoint (Nzero : Set ι) (M : Set ι) := by
      rw [Set.disjoint_left]
      intro x hxzero hxM
      exact Finset.disjoint_left.mp hdisj hxzero hxM
    have hfactor := ((indep_generateFrom_coordinateEvents p hsetDisj
      ).indepSet_of_measurableSet hBzero hfarSection).measure_inter_eq_mul
    have hfactorReal := congrArg ENNReal.toReal hfactor
    rw [ENNReal.toReal_mul] at hfactorReal
    have hBzeroMass : nu.real Bzero = (1 - (p : ℝ)) ^ Nzero.card := by
      exact setBernoulli_real_disjoint_finset_univ Nzero p
    have hleftSection : (Prod.mk original) ⁻¹'
        ((retentionClosedOnProductEvent Nzero ∩
          originalOpenOnProductEvent None) ∩ farEvent) =
        Bzero ∩ farSection := by
      ext retained
      simp [retentionClosedOnProductEvent, originalOpenOnProductEvent,
        Bzero, farSection, hone]
    have hrightSection : (Prod.mk original) ⁻¹'
        (originalOpenOnProductEvent None ∩ farEvent) = farSection := by
      ext retained
      simp [originalOpenOnProductEvent, farSection, hone]
    rw [hleftSection, hrightSection]
    change mu.real {original} * nu.real (Bzero ∩ farSection) =
      (1 - (p : ℝ)) ^ Nzero.card *
        (mu.real {original} * nu.real farSection)
    rw [show nu.real (Bzero ∩ farSection) =
        nu.real Bzero * nu.real farSection by
      simpa only [measureReal_def] using hfactorReal,
      hBzeroMass]
    ring
  · change ¬ (None : Set ι) ⊆ original at hone
    have hleftSection : (Prod.mk original) ⁻¹'
        ((retentionClosedOnProductEvent Nzero ∩
          originalOpenOnProductEvent None) ∩ farEvent) = ∅ := by
      ext retained
      simp [retentionClosedOnProductEvent, originalOpenOnProductEvent, hone]
    have hrightSection : (Prod.mk original) ⁻¹'
        (originalOpenOnProductEvent None ∩ farEvent) = ∅ := by
      ext retained
      simp [originalOpenOnProductEvent, hone]
    rw [hleftSection, hrightSection]
    simp

/-- Open-bit counterpart of (7.121).  This is the exact factor canceled when the source
replaces previously conditioned original ones by previously conditioned diluted ones. -/
theorem productMeasure_real_retentionOpen_inter_originalOpen_inter_dilutedConstraint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (retainedSites originalSites M : Finset ι) (z : Set ι)
    (hdisj : Disjoint retainedSites M) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        ((retentionOpenOnProductEvent retainedSites ∩
          originalOpenOnProductEvent originalSites) ∩
          dilutedConstraintEvent M z) =
      (p : ℝ) ^ retainedSites.card *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (originalOpenOnProductEvent originalSites ∩
            dilutedConstraintEvent M z) := by
  classical
  let nu := setBer((Set.univ : Set ι), p)
  let retainedOpen : Set (Set ι) :=
    {retained | (retainedSites : Set ι) ⊆ retained}
  let originalOpen : Set (Set ι) :=
    {original | (originalSites : Set ι) ⊆ original}
  let farEvent : Set (Set ι × Set ι) := dilutedConstraintEvent M z
  have hleft : MeasurableSet
      ((retentionOpenOnProductEvent retainedSites ∩
        originalOpenOnProductEvent originalSites) ∩ farEvent) :=
    (Set.toFinite _).measurableSet
  have hright : MeasurableSet
      (originalOpenOnProductEvent originalSites ∩ farEvent) :=
    (Set.toFinite _).measurableSet
  change (mu.prod nu).real
      ((retentionOpenOnProductEvent retainedSites ∩
        originalOpenOnProductEvent originalSites) ∩ farEvent) =
    (p : ℝ) ^ retainedSites.card *
      (mu.prod nu).real
        (originalOpenOnProductEvent originalSites ∩ farEvent)
  rw [measureReal_prod_eq_sum_sections mu nu hleft,
    measureReal_prod_eq_sum_sections mu nu hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro original _horiginal
  by_cases hopen : original ∈ originalOpen
  · change (originalSites : Set ι) ⊆ original at hopen
    let farSection : Set (Set ι) :=
      {retained | (original, retained) ∈ farEvent}
    have hretainedOpen : MeasurableSet[MeasurableSpace.generateFrom
        (coordinateEvents (retainedSites : Set ι))] retainedOpen := by
      have hdep : DependsOn retainedSites retainedOpen := by
        intro y y' hyy'
        simp only [retainedOpen, Set.mem_setOf_eq]
        constructor <;> intro h x hx
        · exact (hyy' x hx).mp (h hx)
        · exact (hyy' x hx).mpr (h hx)
      exact hdep.measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
    have hfarSection : MeasurableSet[MeasurableSpace.generateFrom
        (coordinateEvents (M : Set ι))] farSection := by
      exact (dependsOn_dilutedConstraint_retentionSection M z original
        ).measurableSet_generateFrom_coordinateEvents Set.Subset.rfl
    have hsetDisj : Disjoint (retainedSites : Set ι) (M : Set ι) := by
      rw [Set.disjoint_left]
      intro x hxretained hxM
      exact Finset.disjoint_left.mp hdisj hxretained hxM
    have hfactor := ((indep_generateFrom_coordinateEvents p hsetDisj
      ).indepSet_of_measurableSet hretainedOpen hfarSection).measure_inter_eq_mul
    have hfactorReal := congrArg ENNReal.toReal hfactor
    rw [ENNReal.toReal_mul] at hfactorReal
    have hretainedMass : nu.real retainedOpen = (p : ℝ) ^ retainedSites.card := by
      exact setBernoulli_real_superset_finset_univ retainedSites p
    have hleftSection : (Prod.mk original) ⁻¹'
        ((retentionOpenOnProductEvent retainedSites ∩
          originalOpenOnProductEvent originalSites) ∩ farEvent) =
        retainedOpen ∩ farSection := by
      ext retained
      simp [retentionOpenOnProductEvent, originalOpenOnProductEvent,
        retainedOpen, farSection, hopen]
    have hrightSection : (Prod.mk original) ⁻¹'
        (originalOpenOnProductEvent originalSites ∩ farEvent) = farSection := by
      ext retained
      simp [originalOpenOnProductEvent, farSection, hopen]
    rw [hleftSection, hrightSection]
    change mu.real {original} * nu.real (retainedOpen ∩ farSection) =
      (p : ℝ) ^ retainedSites.card *
        (mu.real {original} * nu.real farSection)
    rw [show nu.real (retainedOpen ∩ farSection) =
        nu.real retainedOpen * nu.real farSection by
      simpa only [measureReal_def] using hfactorReal,
      hretainedMass]
    ring
  · change ¬ (originalSites : Set ι) ⊆ original at hopen
    have hleftSection : (Prod.mk original) ⁻¹'
        ((retentionOpenOnProductEvent retainedSites ∩
          originalOpenOnProductEvent originalSites) ∩ farEvent) = ∅ := by
      ext retained
      simp [retentionOpenOnProductEvent, originalOpenOnProductEvent, hopen]
    have hrightSection : (Prod.mk original) ⁻¹'
        (originalOpenOnProductEvent originalSites ∩ farEvent) = ∅ := by
      ext retained
      simp [originalOpenOnProductEvent, hopen]
    rw [hleftSection, hrightSection]
    simp

/-- Adding a disjoint set of prescribed ones to a diluted history is the same event as opening
those sites in both the original and retention fields. -/
theorem dilutedConstraintEvent_union_true
    {ι : Type*} [DecidableEq ι]
    (M ones : Finset ι) (z : Set ι) (hdisj : Disjoint M ones) :
    dilutedConstraintEvent (M ∪ ones) (z ∪ (ones : Set ι)) =
      (originalOpenOnProductEvent ones ∩
        retentionOpenOnProductEvent ones) ∩ dilutedConstraintEvent M z := by
  ext yz
  simp only [dilutedConstraintEvent, originalOpenOnProductEvent,
    retentionOpenOnProductEvent, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.mem_union, Set.mem_union]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x hxones
      exact (h x (Or.inr hxones)).mpr (Or.inr hxones) |>.1
    · intro x hxones
      exact (h x (Or.inr hxones)).mpr (Or.inr hxones) |>.2
    · intro x hxM
      have hxnotones : x ∉ ones := fun hxones ↦
        Finset.disjoint_left.mp hdisj hxM hxones
      simpa [hxnotones] using h x (Or.inl hxM)
  · rintro ⟨⟨hopenY, hopenZ⟩, hM⟩ x (hxM | hxones)
    · have hxnotones : x ∉ ones := fun hxones ↦
        Finset.disjoint_left.mp hdisj hxM hxones
      simpa [hxnotones] using hM x hxM
    · constructor
      · intro _
        exact Or.inr hxones
      · intro _
        exact ⟨hopenY hxones, hopenZ hxones⟩

/-- Prescribing diluted values on a union is the intersection of the two finite
constraint events.  No disjointness hypothesis is needed because the prescribed value
set is shared. -/
theorem dilutedConstraintEvent_union
    {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (z : Set ι) :
    dilutedConstraintEvent (A ∪ B) z =
      dilutedConstraintEvent A z ∩ dilutedConstraintEvent B z := by
  ext yz
  simp only [dilutedConstraintEvent, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.mem_union]
  aesop

/-- Normal form of the `N⁰ ∪ N¹ ∪ M` partition: the auxiliary retention bits on
`N¹` are the only coordinates factored out of the remaining event. -/
theorem dilutedConstraintEvent_eq_lss_retention_factor
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι)
    (C : Finset ι) (z : Set ι) :
    dilutedConstraintEvent C z =
      (retentionOpenOnProductEvent (lssNearOne G k current C z) ∩
        originalOpenOnProductEvent (lssNearOne G k current C z)) ∩
      dilutedConstraintEvent
        (lssNearZero G k current C z ∪ lssFar G k current C) z := by
  classical
  rw [dilutedConstraintEvent_eq_lss_partition G k current C z,
    dilutedConstraintEvent_union]
  ext yz
  simp only [Set.mem_inter_iff]
  tauto

/-- Ratio-free complement arithmetic: a relative upper bound on failure inside a
measurable history is equivalent to the corresponding lower bound on success. -/
theorem mul_measureReal_le_inter_of_compl_inter_le
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (success history : Set Ω) (a : ℝ)
    (hsuccess : MeasurableSet success) (hhistory : MeasurableSet history)
    (hfailure : mu.real (successᶜ ∩ history) ≤
      (1 - a) * mu.real history) :
    a * mu.real history ≤ mu.real (history ∩ success) := by
  have hdisjoint : Disjoint (history ∩ success) (successᶜ ∩ history) := by
    rw [Set.disjoint_left]
    exact fun _ hopen hclosed ↦ hclosed.1 hopen.2
  have hunion : (history ∩ success) ∪ (successᶜ ∩ history) = history := by
    ext omega
    by_cases h : omega ∈ success <;> simp [h]
  have hsum : mu.real (history ∩ success) +
      mu.real (successᶜ ∩ history) = mu.real history := by
    rw [← measureReal_union hdisjoint
      (hsuccess.compl.inter hhistory), hunion]
  linarith

/-- Grimmett's reduced history `A⁰ ∩ A¹ ∩ A`, after the independent
retention-open bits on `N¹` have been removed. -/
noncomputable def lssReducedHistoryEvent
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι)
    (C : Finset ι) (z : Set ι) : Set (Set ι × Set ι) :=
  originalOpenOnProductEvent (lssNearOne G k current C z) ∩
    dilutedConstraintEvent
      (lssNearZero G k current C z ∪ lssFar G k current C) z

theorem measurableSet_lssReducedHistoryEvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ) (current : ι)
    (C : Finset ι) (z : Set ι) :
    MeasurableSet (lssReducedHistoryEvent G k current C z) :=
  (measurableSet_originalOpenOnProductEvent _).inter
    (measurableSet_dilutedConstraintEvent _ _)

/-- The failure part of the reduced history can forget all near constraints and is then
controlled by `k`-dependence.  This is the upper-bound half of (7.119). -/
theorem productMeasure_real_originalClosed_inter_lssReducedHistoryEvent_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu) (p : I)
    (current : ι) (C : Finset ι) (z : Set ι) (theta : ℝ)
    (hmarginal : theta ≤ mu.real {original : Set ι | current ∈ original}) :
    (mu.prod setBer((Set.univ : Set ι), p)).real
        ({yz : Set ι × Set ι | current ∉ yz.1} ∩
          lssReducedHistoryEvent G k current C z) ≤
      (1 - theta) *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent (lssFar G k current C) z) := by
  calc
    (mu.prod setBer((Set.univ : Set ι), p)).real
          ({yz : Set ι × Set ι | current ∉ yz.1} ∩
            lssReducedHistoryEvent G k current C z) ≤
        (mu.prod setBer((Set.univ : Set ι), p)).real
          ({yz : Set ι × Set ι | current ∉ yz.1} ∩
            dilutedConstraintEvent (lssFar G k current C) z) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro yz hyz
      refine ⟨hyz.1, ?_⟩
      intro x hx
      exact hyz.2.2 x (Finset.mem_union_right _ hx)
    _ ≤ _ := productMeasure_real_originalClosed_inter_dilutedConstraint_far_le
      G k mu hmu p current C z theta hmarginal

/-- General finite-set form of the induction claim (7.117), restricted to histories smaller
than `J`.  The current coordinate is required to be new, exactly as in the source. -/
def HasLSSConstraintLowerBoundBelow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) (p : I) (a : ℝ) (J : ℕ) : Prop :=
  ∀ C : Finset ι, ∀ z : Set ι, ∀ current : ι,
    C.card < J → current ∉ C →
      a * (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent C z) ≤
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent C z ∩ originalOpenAtProductEvent current)

/-- Equation (7.122), ratio-free form.  The preceding induction claims multiply to give an
`a^|N¹|` lower bound for opening every original site in `N¹`, conditional on a disjoint
diluted history. -/
theorem pow_mul_measureReal_dilutedConstraint_le_originalOpen_inter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (a : ℝ) (J : ℕ)
    (hp : 0 < (p : ℝ)) (ha : 0 ≤ a)
    (hlower : HasLSSConstraintLowerBoundBelow mu p a J)
    (M ones : Finset ι) (z : Set ι)
    (hdisj : Disjoint M ones) (hcard : M.card + ones.card ≤ J) :
    a ^ ones.card *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent M z) ≤
      (mu.prod setBer((Set.univ : Set ι), p)).real
        (originalOpenOnProductEvent ones ∩ dilutedConstraintEvent M z) := by
  classical
  induction ones using Finset.induction_on generalizing M z with
  | empty =>
      simp [originalOpenOnProductEvent]
  | @insert x ones hx ih =>
      have hxM : x ∉ M := by
        intro hxM
        exact Finset.disjoint_left.mp hdisj hxM (Finset.mem_insert_self x ones)
      have hdisjMones : Disjoint M ones :=
        hdisj.mono_right (Finset.subset_insert x ones)
      have hcardSmall : M.card + ones.card < J := by
        rw [Finset.card_insert_of_notMem hx] at hcard
        omega
      have hprev := ih M z hdisjMones hcardSmall.le
      let enlargedValues : Set ι := z ∪ (ones : Set ι)
      have hMonesCard : (M ∪ ones).card < J := by
        rw [Finset.card_union_of_disjoint hdisjMones]
        exact hcardSmall
      have hxUnion : x ∉ M ∪ ones := by simp [hxM, hx]
      have hconditional := hlower (M ∪ ones) enlargedValues x
        hMonesCard hxUnion
      have hhistory : dilutedConstraintEvent (M ∪ ones) enlargedValues =
          (retentionOpenOnProductEvent ones ∩
            originalOpenOnProductEvent ones) ∩ dilutedConstraintEvent M z := by
        rw [dilutedConstraintEvent_union_true M ones z hdisjMones]
        ext yz
        simp [Set.inter_comm]
      have hhistoryOpen :
          dilutedConstraintEvent (M ∪ ones) enlargedValues ∩
              originalOpenAtProductEvent x =
            (retentionOpenOnProductEvent ones ∩
              originalOpenOnProductEvent (insert x ones)) ∩
                dilutedConstraintEvent M z := by
        rw [hhistory]
        ext yz
        simp [originalOpenOnProductEvent, originalOpenAtProductEvent,
          Set.insert_subset_iff, Set.inter_assoc, Set.inter_comm, and_comm]
      rw [hhistoryOpen, hhistory] at hconditional
      rw [productMeasure_real_retentionOpen_inter_originalOpen_inter_dilutedConstraint
          mu p ones ones M z hdisjMones.symm,
        productMeasure_real_retentionOpen_inter_originalOpen_inter_dilutedConstraint
          mu p ones (insert x ones) M z hdisjMones.symm] at hconditional
      have hretainedPos : 0 < (p : ℝ) ^ ones.card := pow_pos hp _
      have hstep :
          a * (mu.prod setBer((Set.univ : Set ι), p)).real
              (originalOpenOnProductEvent ones ∩ dilutedConstraintEvent M z) ≤
            (mu.prod setBer((Set.univ : Set ι), p)).real
              (originalOpenOnProductEvent (insert x ones) ∩
                dilutedConstraintEvent M z) := by
        apply le_of_mul_le_mul_left _ hretainedPos
        simpa [mul_assoc, mul_left_comm, mul_comm] using hconditional
      rw [Finset.card_insert_of_notMem hx, pow_succ]
      calc
        a ^ ones.card * a *
              (mu.prod setBer((Set.univ : Set ι), p)).real
                (dilutedConstraintEvent M z) =
            a * (a ^ ones.card *
              (mu.prod setBer((Set.univ : Set ι), p)).real
                (dilutedConstraintEvent M z)) := by ring
        _ ≤ a * (mu.prod setBer((Set.univ : Set ι), p)).real
              (originalOpenOnProductEvent ones ∩ dilutedConstraintEvent M z) := by
          exact mul_le_mul_of_nonneg_left hprev ha
        _ ≤ _ := hstep

/-- The lower-bound half of (7.119).  Event `B⁰` supplies the independent
`(1-p)^|N⁰|` factor, while the induction kernel (7.122) supplies `a^|N¹|`. -/
theorem pow_mul_measureReal_dilutedFar_le_lssReducedHistoryEvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (p : I) (a : ℝ) (J : ℕ)
    (hp : 0 < (p : ℝ)) (ha : 0 ≤ a)
    (hlower : HasLSSConstraintLowerBoundBelow mu p a J)
    (current : ι) (C : Finset ι) (z : Set ι)
    (hcard : C.card ≤ J) :
    (1 - (p : ℝ)) ^ (lssNearZero G k current C z).card *
        a ^ (lssNearOne G k current C z).card *
        (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent (lssFar G k current C) z) ≤
      (mu.prod setBer((Set.univ : Set ι), p)).real
        (lssReducedHistoryEvent G k current C z) := by
  classical
  let Nzero := lssNearZero G k current C z
  let None := lssNearOne G k current C z
  let M := lssFar G k current C
  have hparts := pairwiseDisjoint_lssNearZero_lssNearOne_lssFar
    G k current C z
  have hNzeroM : Disjoint Nzero M := hparts.2.1
  have hMNone : Disjoint M None := hparts.2.2.symm
  have hMNoneCard : M.card + None.card ≤ J := by
    rw [← Finset.card_union_of_disjoint hMNone]
    apply (Finset.card_le_card ?_).trans hcard
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxM | hxNone
    · exact (mem_lssFar G k current C x).mp hxM |>.1
    · exact (mem_lssNearOne G k current C z x).mp hxNone |>.1
  have hAone := pow_mul_measureReal_dilutedConstraint_le_originalOpen_inter
    mu p a J hp ha hlower M None z hMNone hMNoneCard
  have hretentionNonneg : 0 ≤ (1 - (p : ℝ)) ^ Nzero.card := by
    exact pow_nonneg (sub_nonneg.mpr p.2.2) _
  have hscaled :
      (1 - (p : ℝ)) ^ Nzero.card *
          (a ^ None.card *
            (mu.prod setBer((Set.univ : Set ι), p)).real
              (dilutedConstraintEvent M z)) ≤
        (1 - (p : ℝ)) ^ Nzero.card *
          (mu.prod setBer((Set.univ : Set ι), p)).real
            (originalOpenOnProductEvent None ∩ dilutedConstraintEvent M z) :=
    mul_le_mul_of_nonneg_left hAone hretentionNonneg
  have hfactor :=
    productMeasure_real_retentionClosed_inter_originalOpen_inter_dilutedConstraint
      mu p Nzero None M z hNzeroM
  have hsubset :
      ((retentionClosedOnProductEvent Nzero ∩
          originalOpenOnProductEvent None) ∩ dilutedConstraintEvent M z) ⊆
        lssReducedHistoryEvent G k current C z := by
    rintro yz ⟨⟨hclosed, hopen⟩, hfar⟩
    refine ⟨hopen, ?_⟩
    rw [dilutedConstraintEvent_union]
    exact ⟨retentionClosedOnProductEvent_subset_dilutedConstraintEvent_nearZero
      G k current C z hclosed, hfar⟩
  calc
    (1 - (p : ℝ)) ^ Nzero.card * a ^ None.card *
          (mu.prod setBer((Set.univ : Set ι), p)).real
            (dilutedConstraintEvent M z) =
        (1 - (p : ℝ)) ^ Nzero.card *
          (a ^ None.card *
            (mu.prod setBer((Set.univ : Set ι), p)).real
              (dilutedConstraintEvent M z)) := by ring
    _ ≤ (1 - (p : ℝ)) ^ Nzero.card *
          (mu.prod setBer((Set.univ : Set ι), p)).real
            (originalOpenOnProductEvent None ∩
              dilutedConstraintEvent M z) := hscaled
    _ = (mu.prod setBer((Set.univ : Set ι), p)).real
          ((retentionClosedOnProductEvent Nzero ∩
            originalOpenOnProductEvent None) ∩
              dilutedConstraintEvent M z) := hfactor.symm
    _ ≤ _ := measureReal_mono hsubset (measure_ne_top _ _)

/-- Equation (7.119) on the reduced history, before restoring the independent retention
bits on `N¹`. -/
theorem mul_measureReal_lssReducedHistoryEvent_le_originalOpen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (p : I) (a theta : ℝ) (B J : ℕ)
    (hp : 0 < (p : ℝ)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B)
    (hlower : HasLSSConstraintLowerBoundBelow mu p a J)
    (current : ι) (C : Finset ι) (z : Set ι)
    (hCcard : C.card ≤ J)
    (hnearCard : (C.filter fun x ↦ G.edist current x ≤ k).card ≤ B)
    (hmarginal : theta ≤ mu.real {original : Set ι | current ∈ original}) :
    a * (mu.prod setBer((Set.univ : Set ι), p)).real
          (lssReducedHistoryEvent G k current C z) ≤
      (mu.prod setBer((Set.univ : Set ι), p)).real
        (lssReducedHistoryEvent G k current C z ∩
          originalOpenAtProductEvent current) := by
  let P := mu.prod setBer((Set.univ : Set ι), p)
  let Nzero := lssNearZero G k current C z
  let None := lssNearOne G k current C z
  let M := lssFar G k current C
  let R := lssReducedHistoryEvent G k current C z
  have hcard : Nzero.card + None.card ≤ B :=
    lssNearZero_card_add_lssNearOne_card_le
      G k current C z B hnearCard
  have hmixed : 1 - theta ≤
      (1 - a) * (1 - (p : ℝ)) ^ Nzero.card * a ^ None.card :=
    one_sub_le_lss_mixed_factor B Nzero.card None.card p
      ha0 ha1 hcard hzero hone
  have hRlower := pow_mul_measureReal_dilutedFar_le_lssReducedHistoryEvent
    G k mu p a J hp ha0 hlower current C z hCcard
  have hfailureUpper :=
    productMeasure_real_originalClosed_inter_lssReducedHistoryEvent_le
      G k mu hmu p current C z theta hmarginal
  have hfailure : P.real
      ((originalOpenAtProductEvent current)ᶜ ∩ R) ≤
        (1 - a) * P.real R := by
    calc
      P.real ((originalOpenAtProductEvent current)ᶜ ∩ R) ≤
          (1 - theta) * P.real (dilutedConstraintEvent M z) := by
        simpa [P, R, M, originalOpenAtProductEvent] using hfailureUpper
      _ ≤ ((1 - a) * (1 - (p : ℝ)) ^ Nzero.card *
            a ^ None.card) * P.real (dilutedConstraintEvent M z) :=
        mul_le_mul_of_nonneg_right hmixed (measureReal_nonneg)
      _ = (1 - a) *
          ((1 - (p : ℝ)) ^ Nzero.card * a ^ None.card *
            P.real (dilutedConstraintEvent M z)) := by ring
      _ ≤ (1 - a) * P.real R := by
        apply mul_le_mul_of_nonneg_left
        · simpa [P, R, M, Nzero, None] using hRlower
        · linarith
  exact mul_measureReal_le_inter_of_compl_inter_le P
    (originalOpenAtProductEvent current) R a
    (Set.toFinite _).measurableSet
    (measurableSet_lssReducedHistoryEvent G k current C z)
    hfailure

/-- One outer induction step for (7.117).  The exact iid retention factor on `N¹`
is restored on both sides after applying the reduced-history estimate. -/
theorem lssConstraintLowerBound_of_lowerBelow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (p : I) (a theta : ℝ) (B J : ℕ)
    (hp : 0 < (p : ℝ)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B)
    (hlower : HasLSSConstraintLowerBoundBelow mu p a J)
    (current : ι) (C : Finset ι) (z : Set ι)
    (hcurrent : current ∉ C) (hCcard : C.card ≤ J)
    (hnearCard : (C.filter fun x ↦ G.edist current x ≤ k).card ≤ B)
    (hmarginal : theta ≤ mu.real {original : Set ι | current ∈ original}) :
    a * (mu.prod setBer((Set.univ : Set ι), p)).real
          (dilutedConstraintEvent C z) ≤
      (mu.prod setBer((Set.univ : Set ι), p)).real
        (dilutedConstraintEvent C z ∩
          originalOpenAtProductEvent current) := by
  classical
  let P := mu.prod setBer((Set.univ : Set ι), p)
  let Nzero := lssNearZero G k current C z
  let None := lssNearOne G k current C z
  let M := lssFar G k current C
  let U := Nzero ∪ M
  let R := lssReducedHistoryEvent G k current C z
  have hparts := pairwiseDisjoint_lssNearZero_lssNearOne_lssFar
    G k current C z
  have hNoneU : Disjoint None U := by
    rw [Finset.disjoint_union_right]
    exact ⟨hparts.1.symm, hparts.2.2⟩
  have hcurrentNone : current ∉ None := by
    intro h
    exact hcurrent ((mem_lssNearOne G k current C z current).mp h).1
  have hReduced := mul_measureReal_lssReducedHistoryEvent_le_originalOpen
    G k mu hmu p a theta B J hp ha0 ha1 hzero hone hlower
    current C z hCcard hnearCard hmarginal
  have hRnorm : R =
      originalOpenOnProductEvent None ∩ dilutedConstraintEvent U z := by
    rfl
  have hRsuccess : R ∩ originalOpenAtProductEvent current =
      originalOpenOnProductEvent (insert current None) ∩
        dilutedConstraintEvent U z := by
    rw [hRnorm]
    ext yz
    simp only [originalOpenOnProductEvent, originalOpenAtProductEvent,
      Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_insert,
      Set.insert_subset_iff]
    tauto
  have hReducedNormalized :
      a * P.real
          (originalOpenOnProductEvent None ∩ dilutedConstraintEvent U z) ≤
        P.real
          (originalOpenOnProductEvent (insert current None) ∩
            dilutedConstraintEvent U z) := by
    change a * P.real R ≤
      P.real (R ∩ originalOpenAtProductEvent current) at hReduced
    rw [hRsuccess, hRnorm] at hReduced
    exact hReduced
  have hscaled := mul_le_mul_of_nonneg_left hReducedNormalized
    (pow_nonneg p.2.1 None.card)
  have hfactorHistory :=
    productMeasure_real_retentionOpen_inter_originalOpen_inter_dilutedConstraint
      mu p None None U z hNoneU
  have hfactorSuccess :=
    productMeasure_real_retentionOpen_inter_originalOpen_inter_dilutedConstraint
      mu p None (insert current None) U z hNoneU
  have hhistory : dilutedConstraintEvent C z =
      (retentionOpenOnProductEvent None ∩
        originalOpenOnProductEvent None) ∩ dilutedConstraintEvent U z := by
    simpa [Nzero, None, M, U] using
      dilutedConstraintEvent_eq_lss_retention_factor G k current C z
  have hsuccess : dilutedConstraintEvent C z ∩
        originalOpenAtProductEvent current =
      (retentionOpenOnProductEvent None ∩
        originalOpenOnProductEvent (insert current None)) ∩
          dilutedConstraintEvent U z := by
    rw [hhistory]
    ext yz
    simp only [originalOpenOnProductEvent, originalOpenAtProductEvent,
      Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_insert,
      Set.insert_subset_iff]
    tauto
  calc
    a * P.real (dilutedConstraintEvent C z) =
        a * ((p : ℝ) ^ None.card *
          P.real (originalOpenOnProductEvent None ∩
            dilutedConstraintEvent U z)) := by rw [hhistory, hfactorHistory]
    _ = (p : ℝ) ^ None.card *
          (a * P.real (originalOpenOnProductEvent None ∩
            dilutedConstraintEvent U z)) := by ring
    _ ≤ (p : ℝ) ^ None.card *
          P.real (originalOpenOnProductEvent (insert current None) ∩
            dilutedConstraintEvent U z) := hscaled
    _ = P.real (dilutedConstraintEvent C z ∩
          originalOpenAtProductEvent current) := by
      rw [hsuccess, hfactorSuccess]

/-- The full finite strong induction (7.117), for arbitrary finite conditioned sets and a
new current coordinate.  The neighborhood bound is uniform in the current site. -/
theorem lssConstraintLowerBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (k : ℕ)
    (mu : Measure (Set ι)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (p : I) (a theta : ℝ) (B : ℕ)
    (hp : 0 < (p : ℝ)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B)
    (hmarginal : ∀ current : ι,
      theta ≤ mu.real {original : Set ι | current ∈ original})
    (hneighbor : ∀ current : ι,
      (Finset.univ.filter fun x ↦ G.edist current x ≤ k).card ≤ B) :
    ∀ C : Finset ι, ∀ z : Set ι, ∀ current : ι,
      current ∉ C →
        a * (mu.prod setBer((Set.univ : Set ι), p)).real
            (dilutedConstraintEvent C z) ≤
          (mu.prod setBer((Set.univ : Set ι), p)).real
            (dilutedConstraintEvent C z ∩
              originalOpenAtProductEvent current) := by
  classical
  suffices h : ∀ n : ℕ, ∀ C : Finset ι, C.card = n →
      ∀ z : Set ι, ∀ current : ι, current ∉ C →
        a * (mu.prod setBer((Set.univ : Set ι), p)).real
            (dilutedConstraintEvent C z) ≤
          (mu.prod setBer((Set.univ : Set ι), p)).real
            (dilutedConstraintEvent C z ∩
              originalOpenAtProductEvent current) by
    intro C z current hcurrent
    exact h C.card C rfl z current hcurrent
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro C hCcard z current hcurrent
      have hlower : HasLSSConstraintLowerBoundBelow mu p a n := by
        intro C' z' current' hsmall hcurrent'
        exact ih C'.card hsmall C' rfl z' current' hcurrent'
      have hnear :
          (C.filter fun x ↦ G.edist current x ≤ k).card ≤ B := by
        apply (Finset.card_le_card ?_).trans (hneighbor current)
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      apply lssConstraintLowerBound_of_lowerBelow
        G k mu hmu p a theta B n hp ha0 ha1 hzero hone hlower
        current C z hcurrent
      · omega
      · exact hnear
      · exact hmarginal current

/-- The set of coordinates prescribed open by an exact Boolean prefix. -/
def finiteBoolPrefixTrueSet {n i : ℕ} (hi : i ≤ n)
    (s : Fin i → Bool) : Set (Fin n) :=
  Fin.castLE hi '' {j : Fin i | s j = true}

/-- The general finite constraint event specializes exactly to the prefix event used by
the sequential-domination API. -/
theorem dilutedProductPrefixEvent_eq_dilutedConstraintEvent
    {n i : ℕ} (hi : i ≤ n) (s : Fin i → Bool) :
    dilutedProductPrefixEvent hi s =
      dilutedConstraintEvent (finiteBoolPrefixCoordinates hi)
        (finiteBoolPrefixTrueSet hi s) := by
  classical
  ext yz
  simp only [dilutedProductPrefixEvent, finiteBoolPrefixEvent,
    Set.mem_preimage, Set.mem_setOf_eq, dilutedConstraintEvent,
    finiteBoolPrefixCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
    siteDilutionMap, finiteSetBoolEquiv, Equiv.coe_fn_mk,
    finiteBoolPrefixTrueSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    let j : Fin i := ⟨x.1, hx⟩
    have hxcast : Fin.castLE hi j = x := Fin.ext rfl
    have hj := congrFun h j
    simp only [boolPrefix] at hj
    rw [← hxcast]
    have himage :
        (∃ j', s j' = true ∧ Fin.castLE hi j' = Fin.castLE hi j) ↔
          s j = true := by
      constructor
      · rintro ⟨j', hj', hj'eq⟩
        have hj'eqj : j' = j := Fin.castLE_injective hi hj'eq
        simpa [hj'eqj] using hj'
      · intro hjtrue
        exact ⟨j, hjtrue, rfl⟩
    rw [himage]
    constructor
    · intro hopen
      have hj' := hj
      simp [hopen] at hj'
      exact hj'
    · intro hjtrue
      by_contra hopen
      have hj' := hj
      simp [hopen, hjtrue] at hj'
  · intro h
    funext j
    simp only [boolPrefix]
    have hj := h (Fin.castLE hi j) (by simp)
    cases hs : s j with
    | false =>
        have hnot : Fin.castLE hi j ∉ yz.1 ∩ yz.2 := by
          intro hopen
          rcases hj.mp hopen with ⟨j', hj', hj'eq⟩
          have hj'eqj : j' = j := Fin.castLE_injective hi hj'eq
          subst j'
          simp [hs] at hj'
        simp [hnot]
    | true =>
        have hopen : Fin.castLE hi j ∈ yz.1 ∩ yz.2 :=
          hj.mpr ⟨j, hs, rfl⟩
        simp [hopen]

/-- Specialization of (7.117) to the ordered prefixes used by the finite sequential
criterion. -/
theorem hasLSSOriginalConditionalLowerBound_of_kDependent
    {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (p : I) (a theta : ℝ) (B : ℕ)
    (hp : 0 < (p : ℝ)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B)
    (hmarginal : ∀ current : Fin n,
      theta ≤ mu.real {original : Set (Fin n) | current ∈ original})
    (hneighbor : ∀ current : Fin n,
      (Finset.univ.filter fun x ↦ G.edist current x ≤ k).card ≤ B) :
    HasLSSOriginalConditionalLowerBound mu p a := by
  intro i hi s
  let C := finiteBoolPrefixCoordinates hi.le
  let z := finiteBoolPrefixTrueSet hi.le s
  have hcurrent : (⟨i, hi⟩ : Fin n) ∉ C :=
    current_notMem_finiteBoolPrefixCoordinates hi
  have hbound := lssConstraintLowerBound
    G k mu hmu p a theta B hp ha0 ha1 hzero hone hmarginal hneighbor
    C z ⟨i, hi⟩ hcurrent
  rw [dilutedProductPrefixEvent_eq_dilutedConstraintEvent]
  simpa [C, z, originalProductCoordinateOpenEvent,
    originalOpenAtProductEvent] using hbound

/-- The finite diluted law satisfies the sequential lower bound `a p` under the LSS
hypotheses. -/
theorem hasFiniteSequentialLowerBound_siteDilutionLaw_of_kDependent
    {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (p : I) (a theta : ℝ) (B : ℕ)
    (hp : 0 < (p : ℝ)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hzero : 1 - theta ≤ (1 - a) * (1 - (p : ℝ)) ^ B)
    (hone : 1 - theta ≤ (1 - a) * a ^ B)
    (hmarginal : ∀ current : Fin n,
      theta ≤ mu.real {original : Set (Fin n) | current ∈ original})
    (hneighbor : ∀ current : Fin n,
      (Finset.univ.filter fun x ↦ G.edist current x ≤ k).card ≤ B) :
    HasFiniteSequentialLowerBound (siteDilutionLaw mu p) (a * (p : ℝ)) :=
  hasFiniteSequentialLowerBound_siteDilutionLaw_of_original mu p
    (hasLSSOriginalConditionalLowerBound_of_kDependent
      G k mu hmu p a theta B hp ha0 ha1 hzero hone hmarginal hneighbor)

/-- Finite-volume LSS domination with the explicit parameter choice from
(7.114)--(7.115).  This is the complete finite theorem underlying Theorem 7.65. -/
theorem finite_lssDomination
    {n : ℕ} (G : SimpleGraph (Fin n)) (k B : ℕ)
    (hneighbor : ∀ current : Fin n,
      (Finset.univ.filter fun x ↦ G.edist current x ≤ k).card ≤ B)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (hmarginal : ∀ current : Fin n,
      (lssMarginalThresholdUnit B q hq : ℝ) ≤
        mu.real {original : Set (Fin n) | current ∈ original}) :
    StochasticallyDominates mu
      setBer((Set.univ : Set (Fin n)), q) := by
  let a : ℝ := lssAuxiliaryDensity (q : ℝ)
  let delta : I := lssMarginalThresholdUnit B q hq
  obtain ⟨ha0, ha1, hqaa, _hdelta, hparameters⟩ :=
    lss_parameter_selection B q hq
  let aI : I := ⟨a, ha0.le, ha1.le⟩
  let aaI : I := ⟨a * a,
    mul_nonneg ha0.le ha0.le,
    (mul_le_mul ha1.le ha1.le ha0.le zero_le_one).trans_eq (mul_one 1)⟩
  have hendpoint := hparameters delta (le_rfl)
  have hseq : HasFiniteSequentialLowerBound
      (siteDilutionLaw mu aI) (aaI : ℝ) := by
    simpa [aaI, aI, a, delta] using
      hasFiniteSequentialLowerBound_siteDilutionLaw_of_kDependent
        G k mu hmu aI a (delta : ℝ) B ha0 ha0.le ha1.le
        hendpoint.1 hendpoint.2 hmarginal hneighbor
  have hOriginalDiluted : StochasticallyDominates mu (siteDilutionLaw mu aI) :=
    stochasticallyDominates_siteDilutionLaw mu aI
  have hDilutedAA : StochasticallyDominates (siteDilutionLaw mu aI)
      setBer((Set.univ : Set (Fin n)), aaI) :=
    finiteSequentialLowerBound_stochasticallyDominates
      (siteDilutionLaw mu aI) aaI hseq
  have hAAQ : StochasticallyDominates
      setBer((Set.univ : Set (Fin n)), aaI)
      setBer((Set.univ : Set (Fin n)), q) := by
    apply setBernoulli_stochasticallyDominates
    exact_mod_cast hqaa
  exact hOriginalDiluted.trans (hDilutedAA.trans hAAQ)

end Percolation
