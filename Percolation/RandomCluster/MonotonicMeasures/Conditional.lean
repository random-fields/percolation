import Percolation.RandomCluster.MonotonicMeasures.FKG

/-!
# Conditional monotonic measures on finite cubes

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, Section 2.2,
especially equations (2.20)-(2.23) and the `(b) => (a)`, `(b) => (c)`,
`(c) => (d)` parts of Theorem 2.24.

The ambient cube is encoded as `Set ι`. For a coordinate set `F : Set ι` and a
boundary condition `ξ`, the conditional cube is represented as
`Set (ConditionCoord F)`, with `conditionSplice F ξ ωF` gluing the inside
configuration `ωF` to `ξ` off `F`.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace FiniteCubeMeasure

/-- Coordinates inside the conditioned set `F`, as a dedicated finite type. -/
structure ConditionCoord (F : Set ι) where
  /-- The ambient coordinate. -/
  val : ι
  /-- The proof that the coordinate belongs to the conditioned set. -/
  mem : val ∈ F

noncomputable instance conditionCoordFintype (F : Set ι) : Fintype (ConditionCoord F) := by
  classical
  exact Fintype.ofEquiv {e : ι // e ∈ F}
    { toFun := fun e => ⟨e.1, e.2⟩
      invFun := fun e => ⟨e.val, e.mem⟩
      left_inv := by
        intro e
        rfl
      right_inv := by
        intro e
        cases e
        rfl }

/-- Splice an inside configuration on `F` with a boundary condition off `F`. -/
noncomputable def conditionSplice (F : Set ι) (ξ : Set ι)
    (ωF : Set (ConditionCoord F)) : Set ι := by
  classical
  exact {e | if h : e ∈ F then (⟨e, h⟩ : ConditionCoord F) ∈ ωF else e ∈ ξ}

omit [Fintype ι] in
theorem mem_conditionSplice_of_mem {F : Set ι} {ξ : Set ι}
    {ωF : Set (ConditionCoord F)}
    {e : ι} (he : e ∈ F) :
    e ∈ conditionSplice F ξ ωF ↔ (⟨e, he⟩ : ConditionCoord F) ∈ ωF := by
  simp [conditionSplice, he]

omit [Fintype ι] in
theorem mem_conditionSplice_of_notMem {F : Set ι} {ξ : Set ι}
    {ωF : Set (ConditionCoord F)}
    {e : ι} (he : e ∉ F) :
    e ∈ conditionSplice F ξ ωF ↔ e ∈ ξ := by
  simp [conditionSplice, he]

omit [Fintype ι] in
theorem conditionSplice_mono {F : Set ι} {ξ : Set ι}
    {ωF ηF : Set (ConditionCoord F)}
    (hωη : ωF ⊆ ηF) :
    conditionSplice F ξ ωF ⊆ conditionSplice F ξ ηF := by
  intro e he
  by_cases hF : e ∈ F
  · exact (mem_conditionSplice_of_mem hF).2
      (hωη ((mem_conditionSplice_of_mem hF).1 he))
  · exact (mem_conditionSplice_of_notMem hF).2 ((mem_conditionSplice_of_notMem hF).1 he)

omit [Fintype ι] in
theorem conditionSplice_inter (F : Set ι) (ξ : Set ι)
    (ωF ηF : Set (ConditionCoord F)) :
    conditionSplice F ξ (ωF ∩ ηF) =
      conditionSplice F ξ ωF ∩ conditionSplice F ξ ηF := by
  ext e
  by_cases hF : e ∈ F
  · simp [mem_conditionSplice_of_mem hF]
  · simp [mem_conditionSplice_of_notMem hF]

omit [Fintype ι] in
theorem conditionSplice_union (F : Set ι) (ξ : Set ι)
    (ωF ηF : Set (ConditionCoord F)) :
    conditionSplice F ξ (ωF ∪ ηF) =
      conditionSplice F ξ ωF ∪ conditionSplice F ξ ηF := by
  ext e
  by_cases hF : e ∈ F
  · simp [mem_conditionSplice_of_mem hF]
  · simp [mem_conditionSplice_of_notMem hF]

omit [Fintype ι] in
theorem conditionSplice_inter_of_subset {F : Set ι} {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (ωF ηF : Set (ConditionCoord F)) :
    conditionSplice F ξ (ωF ∩ ηF) =
      conditionSplice F ξ ωF ∩ conditionSplice F ζ ηF := by
  ext e
  by_cases hF : e ∈ F
  · simp [mem_conditionSplice_of_mem hF]
  · rw [mem_conditionSplice_of_notMem hF, Set.mem_inter_iff,
      mem_conditionSplice_of_notMem hF, mem_conditionSplice_of_notMem hF]
    constructor
    · intro he
      exact ⟨he, hξζ he⟩
    · exact fun he => he.1

omit [Fintype ι] in
theorem conditionSplice_union_of_subset {F : Set ι} {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (ωF ηF : Set (ConditionCoord F)) :
    conditionSplice F ζ (ωF ∪ ηF) =
      conditionSplice F ξ ωF ∪ conditionSplice F ζ ηF := by
  ext e
  by_cases hF : e ∈ F
  · simp [mem_conditionSplice_of_mem hF]
  · rw [mem_conditionSplice_of_notMem hF, Set.mem_union, mem_conditionSplice_of_notMem hF,
      mem_conditionSplice_of_notMem hF]
    constructor
    · exact fun he => Or.inr he
    · intro he
      exact he.elim (fun h => hξζ h) id

/-- The mass of the conditioning cylinder `Ω_F^ξ`. -/
noncomputable def conditionDenom (μ : FiniteCubeMeasure ι) (F : Set ι) (ξ : Set ι) : ℝ :=
  ∑ ωF : Set (ConditionCoord F), μ (conditionSplice F ξ ωF)

theorem conditionDenom_pos_of_strictPositive (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (F : Set ι) (ξ : Set ι) :
    0 < conditionDenom μ F ξ := by
  classical
  rw [conditionDenom]
  refine Finset.sum_pos (fun ωF _ => hμ (conditionSplice F ξ ωF)) ?_
  exact ⟨(∅ : Set (ConditionCoord F)), Finset.mem_univ _⟩

/-- The conditional measure on the coordinates in `F`, with boundary condition `ξ` off `F`. -/
noncomputable def conditionOn (μ : FiniteCubeMeasure ι) (F : Set ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ F ξ) : FiniteCubeMeasure (ConditionCoord F) where
  mass := fun ωF => μ (conditionSplice F ξ ωF) / conditionDenom μ F ξ
  nonneg := by
    intro ωF
    exact div_nonneg (μ.nonneg _) (le_of_lt hden)
  sum_mass := by
    change (∑ ωF : Set (ConditionCoord F),
      μ (conditionSplice F ξ ωF) / conditionDenom μ F ξ) = 1
    rw [← Finset.sum_div]
    field_simp [conditionDenom, ne_of_gt hden]
    rw [conditionDenom]

theorem conditionOn_apply (μ : FiniteCubeMeasure ι) (F : Set ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ F ξ) (ωF : Set (ConditionCoord F)) :
    conditionOn μ F ξ hden ωF =
      μ (conditionSplice F ξ ωF) / conditionDenom μ F ξ :=
  rfl

theorem conditionOn_strictPositive (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive)
    (F : Set ι) (ξ : Set ι) (hden : 0 < conditionDenom μ F ξ) :
    (conditionOn μ F ξ hden).StrictPositive := by
  intro ωF
  exact div_pos (hμ _) hden

/-- The configuration obtained by forcing coordinate `e` to be open. -/
def forceOpen (e : ι) (ω : Set ι) : Set ι :=
  insert e ω

/-- The configuration obtained by forcing coordinate `e` to be closed. -/
def forceClosed (e : ι) (ω : Set ι) : Set ι :=
  ω \ {e}

omit [Fintype ι] in
/-- Complementing finite-cube configurations is an involutive equivalence. -/
noncomputable def configComplEquiv : Set ι ≃ Set ι where
  toFun := fun ω => ωᶜ
  invFun := fun ω => ωᶜ
  left_inv := by
    intro ω
    simp
  right_inv := by
    intro ω
    simp

/-- Push a finite cube measure through configuration complementation. -/
noncomputable def complMeasure (μ : FiniteCubeMeasure ι) : FiniteCubeMeasure ι where
  mass := fun ω => μ ωᶜ
  nonneg := by
    intro ω
    exact μ.nonneg _
  sum_mass := by
    rw [← μ.sum_mass]
    rw [Fintype.sum_equiv (configComplEquiv (ι := ι)) (fun ω : Set ι => μ ωᶜ)
      (fun η : Set ι => μ η)]
    intro ω
    simp [configComplEquiv]

theorem complMeasure_apply (μ : FiniteCubeMeasure ι) (ω : Set ι) :
    complMeasure μ ω = μ ωᶜ :=
  rfl

theorem complMeasure_strictPositive (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive) :
    (complMeasure μ).StrictPositive := by
  intro ω
  exact hμ _

omit [Fintype ι] in
theorem compl_forceOpen (e : ι) (ω : Set ι) :
    (forceOpen e ω)ᶜ = forceClosed e ωᶜ := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

omit [Fintype ι] in
theorem compl_forceClosed (e : ι) (ω : Set ι) :
    (forceClosed e ω)ᶜ = forceOpen e ωᶜ := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

/-- Coordinates open in `ω` and closed in `η`. -/
noncomputable def openClosedDisagreeFinset (ω η : Set ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun e => e ∈ ω ∧ e ∉ η

/-- Coordinates closed in `ω` and open in `η`. -/
noncomputable def closedOpenDisagreeFinset (ω η : Set ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun e => e ∉ ω ∧ e ∈ η

/-- Hamming distance between two finite-cube configurations. -/
noncomputable def hammingDistance (ω η : Set ι) : ℕ :=
  (openClosedDisagreeFinset ω η).card + (closedOpenDisagreeFinset ω η).card

theorem mem_openClosedDisagreeFinset (e : ι) (ω η : Set ι) :
    e ∈ openClosedDisagreeFinset ω η ↔ e ∈ ω ∧ e ∉ η := by
  classical
  simp [openClosedDisagreeFinset]

theorem mem_closedOpenDisagreeFinset (e : ι) (ω η : Set ι) :
    e ∈ closedOpenDisagreeFinset ω η ↔ e ∉ ω ∧ e ∈ η := by
  classical
  simp [closedOpenDisagreeFinset]

theorem disjoint_openClosed_closedOpenDisagreeFinset (ω η : Set ι) :
    Disjoint (openClosedDisagreeFinset ω η) (closedOpenDisagreeFinset ω η) := by
  classical
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [mem_openClosedDisagreeFinset] at he₁
  rw [mem_closedOpenDisagreeFinset] at he₂
  exact he₂.1 he₁.1

theorem hammingDistance_comm (ω η : Set ι) :
    hammingDistance ω η = hammingDistance η ω := by
  classical
  have h₁ : openClosedDisagreeFinset ω η = closedOpenDisagreeFinset η ω := by
    ext e
    simp [openClosedDisagreeFinset, closedOpenDisagreeFinset, and_comm]
  have h₂ : closedOpenDisagreeFinset ω η = openClosedDisagreeFinset η ω := by
    ext e
    simp [openClosedDisagreeFinset, closedOpenDisagreeFinset, and_comm]
  simp [hammingDistance, h₁, h₂, Nat.add_comm]

theorem openClosedDisagreeFinset_compl (ω η : Set ι) :
    openClosedDisagreeFinset ωᶜ ηᶜ = closedOpenDisagreeFinset ω η := by
  classical
  ext e
  simp [mem_openClosedDisagreeFinset, mem_closedOpenDisagreeFinset]

theorem closedOpenDisagreeFinset_compl (ω η : Set ι) :
    closedOpenDisagreeFinset ωᶜ ηᶜ = openClosedDisagreeFinset ω η := by
  classical
  ext e
  simp [mem_openClosedDisagreeFinset, mem_closedOpenDisagreeFinset]

theorem hammingDistance_compl_compl (ω η : Set ι) :
    hammingDistance ωᶜ ηᶜ = hammingDistance ω η := by
  simp [hammingDistance, openClosedDisagreeFinset_compl, closedOpenDisagreeFinset_compl,
    Nat.add_comm]

theorem hammingDistance_eq_zero_iff (ω η : Set ι) :
    hammingDistance ω η = 0 ↔ ω = η := by
  classical
  rw [hammingDistance, Nat.add_eq_zero_iff]
  constructor
  · intro h
    ext e
    constructor
    · intro heω
      by_contra heη
      have hemem : e ∈ openClosedDisagreeFinset ω η := by
        rw [mem_openClosedDisagreeFinset]
        exact ⟨heω, heη⟩
      have hcard : (openClosedDisagreeFinset ω η).card = 0 := h.1
      have hfin : openClosedDisagreeFinset ω η = ∅ := Finset.card_eq_zero.mp hcard
      rw [hfin] at hemem
      simp at hemem
    · intro heη
      by_contra heω
      have hemem : e ∈ closedOpenDisagreeFinset ω η := by
        rw [mem_closedOpenDisagreeFinset]
        exact ⟨heω, heη⟩
      have hcard : (closedOpenDisagreeFinset ω η).card = 0 := h.2
      have hfin : closedOpenDisagreeFinset ω η = ∅ := Finset.card_eq_zero.mp hcard
      rw [hfin] at hemem
      simp at hemem
  · intro h
    subst h
    constructor
    · apply Finset.card_eq_zero.mpr
      ext e
      simp [mem_openClosedDisagreeFinset]
    · apply Finset.card_eq_zero.mpr
      ext e
      simp [mem_closedOpenDisagreeFinset]

theorem card_openClosedDisagreeFinset_forceClosed_left_lt {e : ι} {ω η : Set ι}
    (he : e ∈ openClosedDisagreeFinset ω η) :
    (openClosedDisagreeFinset (forceClosed e ω) η).card <
      (openClosedDisagreeFinset ω η).card := by
  classical
  have hset : openClosedDisagreeFinset (forceClosed e ω) η =
      (openClosedDisagreeFinset ω η).erase e := by
    ext x
    by_cases hxe : x = e
    · subst hxe
      simp [mem_openClosedDisagreeFinset, forceClosed]
    · simp [mem_openClosedDisagreeFinset, forceClosed, hxe]
  rw [hset]
  exact Finset.card_erase_lt_of_mem he

theorem closedOpenDisagreeFinset_forceClosed_left (e : ι) {ω η : Set ι}
    (heη : e ∉ η) :
    closedOpenDisagreeFinset (forceClosed e ω) η = closedOpenDisagreeFinset ω η := by
  classical
  ext x
  by_cases hxe : x = e
  · subst hxe
    simp [mem_closedOpenDisagreeFinset, forceClosed, heη]
  · simp [mem_closedOpenDisagreeFinset, forceClosed, hxe]

theorem hammingDistance_forceClosed_left_lt {e : ι} {ω η : Set ι}
    (he : e ∈ openClosedDisagreeFinset ω η) :
    hammingDistance (forceClosed e ω) η < hammingDistance ω η := by
  classical
  have heη : e ∉ η := (mem_openClosedDisagreeFinset e ω η).1 he |>.2
  rw [hammingDistance,
    closedOpenDisagreeFinset_forceClosed_left e heη, hammingDistance]
  have hcard := card_openClosedDisagreeFinset_forceClosed_left_lt he
  omega

theorem card_openClosedDisagreeFinset_left_bridge (e : ι) {ω η : Set ι}
    (heω : e ∈ ω) (heη : e ∉ η) :
    (openClosedDisagreeFinset ω (η ∪ forceClosed e ω)).card = 1 := by
  classical
  have hset : openClosedDisagreeFinset ω (η ∪ forceClosed e ω) = {e} := by
    ext x
    by_cases hxe : x = e
    · subst hxe
      simp [mem_openClosedDisagreeFinset, forceClosed, heω, heη]
    · simp [mem_openClosedDisagreeFinset, forceClosed, hxe]
      tauto
  rw [hset]
  simp

theorem closedOpenDisagreeFinset_left_bridge (e : ι) (ω η : Set ι) :
    closedOpenDisagreeFinset ω (η ∪ forceClosed e ω) =
      closedOpenDisagreeFinset ω η := by
  classical
  ext x
  simp [mem_closedOpenDisagreeFinset, forceClosed]
  tauto

theorem hammingDistance_left_bridge_lt {e : ι} {ω η : Set ι}
    (he : e ∈ openClosedDisagreeFinset ω η)
    (hmore : 1 < (openClosedDisagreeFinset ω η).card) :
    hammingDistance ω (η ∪ forceClosed e ω) < hammingDistance ω η := by
  classical
  have he' := (mem_openClosedDisagreeFinset e ω η).1 he
  rw [hammingDistance, card_openClosedDisagreeFinset_left_bridge e he'.1 he'.2,
    closedOpenDisagreeFinset_left_bridge, hammingDistance]
  omega

/-- The event that a conditional coordinate is open. -/
def coordOpenEvent {F : Set ι} (eF : ConditionCoord F) :
    Set (Set (ConditionCoord F)) :=
  {ωF | eF ∈ ωF}

omit [Fintype ι] in
theorem isIncreasingEvent_coordOpenEvent {F : Set ι} (eF : ConditionCoord F) :
    IsIncreasingEvent (coordOpenEvent eF) := by
  intro ωF ηF hωη hω
  exact hωη hω

/-- The unique coordinate in the one-point conditional cube over `{e}`. -/
def singletonConditionCoord (e : ι) : ConditionCoord ({e} : Set ι) :=
  ⟨e, rfl⟩

omit [Fintype ι] in
/-- Splicing the full one-point conditional configuration forces the coordinate open. -/
theorem conditionSplice_singleton_univ (e : ι) (ξ : Set ι) :
    conditionSplice ({e} : Set ι) ξ
        (Set.univ : Set (ConditionCoord ({e} : Set ι))) =
      forceOpen e ξ := by
  ext x
  by_cases hx : x = e
  · subst hx
    simp [forceOpen, mem_conditionSplice_of_mem]
  · have hxF : x ∉ ({e} : Set ι) := by simpa using hx
    simp [forceOpen, mem_conditionSplice_of_notMem hxF, hx]

omit [Fintype ι] in
/-- Splicing the empty one-point conditional configuration forces the coordinate closed. -/
theorem conditionSplice_singleton_empty (e : ι) (ξ : Set ι) :
    conditionSplice ({e} : Set ι) ξ
        (∅ : Set (ConditionCoord ({e} : Set ι))) =
      forceClosed e ξ := by
  ext x
  by_cases hx : x = e
  · subst hx
    simp [forceClosed, mem_conditionSplice_of_mem]
  · have hxF : x ∉ ({e} : Set ι) := by simpa using hx
    simp [forceClosed, mem_conditionSplice_of_notMem hxF, hx]

omit [Fintype ι] in
lemma set_eq_univ_of_singletonConditionCoord_mem (e : ι)
    {ωF : Set (ConditionCoord ({e} : Set ι))}
    (hmem : singletonConditionCoord e ∈ ωF) : ωF = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    rcases x with ⟨x, hxF⟩
    have hx_eq : x = e := by simpa using hxF
    subst hx_eq
    exact hmem

omit [Fintype ι] in
lemma set_eq_empty_of_singletonConditionCoord_notMem (e : ι)
    {ωF : Set (ConditionCoord ({e} : Set ι))}
    (hmem : singletonConditionCoord e ∉ ωF) : ωF = ∅ := by
  ext x
  constructor
  · intro hx
    rcases x with ⟨x, hxF⟩
    have hx_eq : x = e := by simpa using hxF
    subst hx_eq
    exact False.elim (hmem hx)
  · intro hx
    simp at hx

omit [Fintype ι] in
noncomputable def singletonConditionSetEquivBool (e : ι) :
    Set (ConditionCoord ({e} : Set ι)) ≃ Bool := by
  classical
  exact
    { toFun := fun ωF => if singletonConditionCoord e ∈ ωF then true else false
      invFun := fun b => if b then Set.univ else ∅
      left_inv := by
        intro ωF
        by_cases hmem : singletonConditionCoord e ∈ ωF
        · rw [set_eq_univ_of_singletonConditionCoord_mem e hmem]
          simp
        · rw [set_eq_empty_of_singletonConditionCoord_notMem e hmem]
          simp
      right_inv := by
        intro b
        cases b <;> simp }

theorem sum_singletonConditionCoord (e : ι)
    (f : Set (ConditionCoord ({e} : Set ι)) → ℝ) :
    (∑ ωF, f ωF) = f ∅ + f Set.univ := by
  classical
  rw [Fintype.sum_equiv (singletonConditionSetEquivBool e) f
    (fun b => f (if b then Set.univ else ∅))]
  · simp
    ring
  · intro x
    simp [singletonConditionSetEquivBool]
    by_cases hmem : singletonConditionCoord e ∈ x
    · rw [set_eq_univ_of_singletonConditionCoord_mem e hmem]
      simp
    · rw [set_eq_empty_of_singletonConditionCoord_notMem e hmem]
      simp

theorem conditionDenom_singleton (μ : FiniteCubeMeasure ι) (e : ι) (ξ : Set ι) :
    conditionDenom μ ({e} : Set ι) ξ = μ (forceClosed e ξ) + μ (forceOpen e ξ) := by
  rw [conditionDenom, sum_singletonConditionCoord e]
  rw [conditionSplice_singleton_empty, conditionSplice_singleton_univ]

/-- One-point conditional probability that coordinate `e` is open. -/
noncomputable def onePointOpenProb (μ : FiniteCubeMeasure ι) (e : ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ ({e} : Set ι) ξ) : ℝ :=
  (conditionOn μ ({e} : Set ι) ξ hden).prob
    (coordOpenEvent (singletonConditionCoord e))

theorem prob_coordOpenEvent_singleton (μ : FiniteCubeMeasure ι) (e : ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ ({e} : Set ι) ξ) :
    (conditionOn μ ({e} : Set ι) ξ hden).prob
      (coordOpenEvent (singletonConditionCoord e)) =
      conditionOn μ ({e} : Set ι) ξ hden Set.univ := by
  rw [prob, expect]
  classical
  rw [Finset.sum_eq_single Set.univ]
  · simp [coordOpenEvent]
  · intro b _ hne
    have hnot : singletonConditionCoord e ∉ b := by
      intro hmem
      exact hne (set_eq_univ_of_singletonConditionCoord_mem e hmem)
    simp [coordOpenEvent, hnot]
  · intro hnot
    simp at hnot

theorem onePointOpenProb_eq_div (μ : FiniteCubeMeasure ι) (e : ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ ({e} : Set ι) ξ) :
    onePointOpenProb μ e ξ hden =
      μ (forceOpen e ξ) / (μ (forceClosed e ξ) + μ (forceOpen e ξ)) := by
  rw [onePointOpenProb, prob_coordOpenEvent_singleton, conditionOn_apply,
    conditionSplice_singleton_univ, conditionDenom_singleton]

/-- Equation (2.14): one-point conditional order is equivalent to the cross
multiplied two-atom inequality. -/
theorem onePointOpenProb_le_iff_cross (μ ν : FiniteCubeMeasure ι) (e : ι)
    (ξ ζ : Set ι) (hμ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hν : 0 < conditionDenom ν ({e} : Set ι) ζ) :
    onePointOpenProb μ e ξ hμ ≤ onePointOpenProb ν e ζ hν ↔
      μ (forceOpen e ξ) * ν (forceClosed e ζ) ≤
        ν (forceOpen e ζ) * μ (forceClosed e ξ) := by
  have hμ' : 0 < μ (forceClosed e ξ) + μ (forceOpen e ξ) := by
    simpa [conditionDenom_singleton] using hμ
  have hν' : 0 < ν (forceClosed e ζ) + ν (forceOpen e ζ) := by
    simpa [conditionDenom_singleton] using hν
  rw [onePointOpenProb_eq_div, onePointOpenProb_eq_div]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (mul_pos hμ' hν'))
    field_simp [ne_of_gt hμ', ne_of_gt hν'] at hmul
    nlinarith
  · intro h
    have hcross :
        μ (forceOpen e ξ) * (ν (forceClosed e ζ) + ν (forceOpen e ζ)) ≤
          ν (forceOpen e ζ) * (μ (forceClosed e ξ) + μ (forceOpen e ξ)) := by
      nlinarith
    have hden := div_le_div_of_nonneg_right hcross (le_of_lt (mul_pos hμ' hν'))
    have hleft :
        (μ (forceOpen e ξ) * (ν (forceClosed e ζ) + ν (forceOpen e ζ))) /
          ((μ (forceClosed e ξ) + μ (forceOpen e ξ)) *
            (ν (forceClosed e ζ) + ν (forceOpen e ζ))) =
        μ (forceOpen e ξ) /
          (μ (forceClosed e ξ) + μ (forceOpen e ξ)) := by
      field_simp [ne_of_gt hμ', ne_of_gt hν']
    have hright :
        (ν (forceOpen e ζ) * (μ (forceClosed e ξ) + μ (forceOpen e ξ))) /
          ((μ (forceClosed e ξ) + μ (forceOpen e ξ)) *
            (ν (forceClosed e ζ) + ν (forceOpen e ζ))) =
        ν (forceOpen e ζ) /
          (ν (forceClosed e ζ) + ν (forceOpen e ζ)) := by
      field_simp [ne_of_gt hμ', ne_of_gt hν']
    rwa [hleft, hright] at hden

/-- Strong positive association: every positive conditional measure is positively associated. -/
def StronglyPositivelyAssociated (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ (F : Set ι) (ξ : Set ι) (hden : 0 < conditionDenom μ F ξ),
    PositivelyAssociated (conditionOn μ F ξ hden)

/-- Monotonicity of conditionals with respect to the boundary condition. -/
def MonotonicMeasure (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ (F : Set ι) (ξ ζ : Set ι)
    (hξ : 0 < conditionDenom μ F ξ) (hζ : 0 < conditionDenom μ F ζ),
      ξ ⊆ ζ → stochLE (conditionOn μ F ξ hξ) (conditionOn μ F ζ hζ)

/-- One-coordinate monotonicity of conditionals. -/
def OneMonotonicMeasure (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ (e : ι) (ξ ζ : Set ι)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom μ ({e} : Set ι) ζ),
      ξ ⊆ ζ → stochLE (conditionOn μ ({e} : Set ι) ξ hξ)
        (conditionOn μ ({e} : Set ι) ζ hζ)

/-- The one-point conditional domination hypothesis in Theorem 2.6. -/
def OnePointConditionalDomination (μ ν : FiniteCubeMeasure ι) : Prop :=
  ∀ (e : ι) (ξ ζ : Set ι)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom ν ({e} : Set ι) ζ),
      ξ ⊆ ζ → onePointOpenProb μ e ξ hξ ≤ onePointOpenProb ν e ζ hζ

/-- The one-coordinate local Holley inequality (2.4). -/
def LocalHolleyOneCondition (μ ν : FiniteCubeMeasure ι) : Prop :=
  ∀ e : ι, ∀ ω : Set ι,
    μ (forceOpen e ω) * ν (forceClosed e ω) ≤
      μ (forceClosed e ω) * ν (forceOpen e ω)

/-- The two-coordinate local Holley inequality (2.5). -/
def LocalHolleyTwoCondition (μ ν : FiniteCubeMeasure ι) : Prop :=
  ∀ e f : ι, ∀ ω : Set ι,
    μ (forceOpen e (forceClosed f ω)) * ν (forceClosed e (forceOpen f ω)) ≤
      μ (forceClosed e (forceClosed f ω)) * ν (forceOpen e (forceOpen f ω))

/-- The local hypotheses of the finite local Holley criterion, Theorem 2.3. -/
def LocalHolleyCondition (μ ν : FiniteCubeMeasure ι) : Prop :=
  LocalHolleyOneCondition μ ν ∧ LocalHolleyTwoCondition μ ν

/-- The pointwise Holley inequality for a fixed pair of configurations. -/
def HolleyInequalityAt (μ ν : FiniteCubeMeasure ι) (ω η : Set ι) : Prop :=
  μ ω * ν η ≤ μ (ω ∩ η) * ν (ω ∪ η)

/-- Pointwise Holley duality under complementing configurations and swapping measures. -/
theorem holleyInequalityAt_complMeasure_swap_iff (μ ν : FiniteCubeMeasure ι)
    (ω η : Set ι) :
    HolleyInequalityAt (complMeasure ν) (complMeasure μ) ηᶜ ωᶜ ↔
      HolleyInequalityAt μ ν ω η := by
  simp [HolleyInequalityAt, complMeasure, mul_comm, Set.compl_inter, Set.compl_union,
    Set.union_comm, Set.inter_comm]

/-- Global Holley is the assertion of the pointwise Holley inequality for all pairs. -/
theorem holleyCondition_iff_forall_holleyInequalityAt (μ ν : FiniteCubeMeasure ι) :
    HolleyCondition μ ν ↔ ∀ ω η : Set ι, HolleyInequalityAt μ ν ω η :=
  Iff.rfl

/-- Global Holley is invariant under complementing configurations and swapping the two
measures. This is the duality used to cover the second asymmetric case in the local
Holley induction. -/
theorem holleyCondition_complMeasure_swap_iff (μ ν : FiniteCubeMeasure ι) :
    HolleyCondition (complMeasure ν) (complMeasure μ) ↔ HolleyCondition μ ν := by
  constructor
  · intro h ω η
    have hdual := h ηᶜ ωᶜ
    simpa [HolleyCondition, complMeasure, mul_comm, Set.compl_inter, Set.compl_union,
      Set.union_comm, Set.inter_comm] using hdual
  · intro h ω η
    have hbase := h ηᶜ ωᶜ
    simpa [HolleyCondition, complMeasure, mul_comm, Set.compl_inter, Set.compl_union,
      Set.union_comm, Set.inter_comm] using hbase

/-- The one-coordinate local Holley condition is preserved by the complement/swap duality. -/
theorem localHolleyOneCondition_complMeasure_swap (μ ν : FiniteCubeMeasure ι)
    (hlocal : LocalHolleyOneCondition μ ν) :
    LocalHolleyOneCondition (complMeasure ν) (complMeasure μ) := by
  intro e ω
  have h := hlocal e ωᶜ
  simpa [complMeasure, compl_forceOpen, compl_forceClosed, mul_comm] using h

/-- The two-coordinate local Holley condition is preserved by the complement/swap duality. -/
theorem localHolleyTwoCondition_complMeasure_swap (μ ν : FiniteCubeMeasure ι)
    (hlocal : LocalHolleyTwoCondition μ ν) :
    LocalHolleyTwoCondition (complMeasure ν) (complMeasure μ) := by
  intro e f ω
  have h := hlocal e f ωᶜ
  simpa [complMeasure, compl_forceOpen, compl_forceClosed, mul_comm] using h

/-- The local hypotheses of Theorem 2.3 are preserved by the complement/swap duality. -/
theorem localHolleyCondition_complMeasure_swap (μ ν : FiniteCubeMeasure ι)
    (hlocal : LocalHolleyCondition μ ν) :
    LocalHolleyCondition (complMeasure ν) (complMeasure μ) :=
  ⟨localHolleyOneCondition_complMeasure_swap μ ν hlocal.1,
    localHolleyTwoCondition_complMeasure_swap μ ν hlocal.2⟩

/-- The local Hamming-two FKG inequalities appearing in Theorem 2.19, restricted to
opposite corners of coordinate squares. -/
def LocalTwoCoordinateFKG (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ e f : ι, ∀ ω : Set ι,
    μ (forceOpen e (forceClosed f ω)) * μ (forceClosed e (forceOpen f ω)) ≤
      μ (forceOpen e (forceClosed f ω) ∩ forceClosed e (forceOpen f ω)) *
        μ (forceOpen e (forceClosed f ω) ∪ forceClosed e (forceOpen f ω))

theorem fkgLatticeCondition_conditionOn (μ : FiniteCubeMeasure ι)
    (hFKG : FKGLatticeCondition μ) (F : Set ι) (ξ : Set ι)
    (hden : 0 < conditionDenom μ F ξ) :
    FKGLatticeCondition (conditionOn μ F ξ hden) := by
  intro ωF ηF
  have hbase := hFKG (conditionSplice F ξ ωF) (conditionSplice F ξ ηF)
  have hbase' :
      μ (conditionSplice F ξ ωF) * μ (conditionSplice F ξ ηF) ≤
        μ (conditionSplice F ξ (ωF ∩ ηF)) *
          μ (conditionSplice F ξ (ωF ∪ ηF)) := by
    simpa [conditionSplice_inter, conditionSplice_union] using hbase
  have hdiv := div_le_div_of_nonneg_right hbase'
    (mul_nonneg (le_of_lt hden) (le_of_lt hden))
  calc
    conditionOn μ F ξ hden ωF * conditionOn μ F ξ hden ηF =
        (μ (conditionSplice F ξ ωF) * μ (conditionSplice F ξ ηF)) /
          (conditionDenom μ F ξ * conditionDenom μ F ξ) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hden]
    _ ≤ (μ (conditionSplice F ξ (ωF ∩ ηF)) *
          μ (conditionSplice F ξ (ωF ∪ ηF))) /
          (conditionDenom μ F ξ * conditionDenom μ F ξ) := hdiv
    _ = conditionOn μ F ξ hden (ωF ∩ ηF) *
        conditionOn μ F ξ hden (ωF ∪ ηF) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hden]

theorem holleyCondition_conditionOn_pair_of_subset (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) (F : Set ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ F ξ) (hζ : 0 < conditionDenom ν F ζ) :
    HolleyCondition (conditionOn μ F ξ hξ) (conditionOn ν F ζ hζ) := by
  intro ωF ηF
  have hbase := hH (conditionSplice F ξ ωF) (conditionSplice F ζ ηF)
  have hbase' :
      μ (conditionSplice F ξ ωF) * ν (conditionSplice F ζ ηF) ≤
        μ (conditionSplice F ξ (ωF ∩ ηF)) *
          ν (conditionSplice F ζ (ωF ∪ ηF)) := by
    simpa [conditionSplice_inter_of_subset hξζ, conditionSplice_union_of_subset hξζ] using hbase
  have hdiv := div_le_div_of_nonneg_right hbase'
    (mul_nonneg (le_of_lt hξ) (le_of_lt hζ))
  calc
    conditionOn μ F ξ hξ ωF * conditionOn ν F ζ hζ ηF =
        (μ (conditionSplice F ξ ωF) * ν (conditionSplice F ζ ηF)) /
          (conditionDenom μ F ξ * conditionDenom ν F ζ) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hξ, ne_of_gt hζ]
    _ ≤ (μ (conditionSplice F ξ (ωF ∩ ηF)) *
          ν (conditionSplice F ζ (ωF ∪ ηF))) /
          (conditionDenom μ F ξ * conditionDenom ν F ζ) := hdiv
    _ = conditionOn μ F ξ hξ (ωF ∩ ηF) * conditionOn ν F ζ hζ (ωF ∪ ηF) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hξ, ne_of_gt hζ]

theorem holleyCondition_conditionOn_of_subset (μ : FiniteCubeMeasure ι)
    (hFKG : FKGLatticeCondition μ) (F : Set ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ F ξ) (hζ : 0 < conditionDenom μ F ζ) :
    HolleyCondition (conditionOn μ F ξ hξ) (conditionOn μ F ζ hζ) := by
  exact holleyCondition_conditionOn_pair_of_subset μ μ hFKG F hξζ hξ hζ

/-- The easy direction of Theorem 2.6: Holley implies one-point conditional monotonicity. -/
theorem onePointOpenProb_le_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) (e : ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom ν ({e} : Set ι) ζ) :
    onePointOpenProb μ e ξ hξ ≤ onePointOpenProb ν e ζ hζ := by
  have hstoch : stochLE (conditionOn μ ({e} : Set ι) ξ hξ)
      (conditionOn ν ({e} : Set ι) ζ hζ) :=
    stochLE_of_holley _ _
      (holleyCondition_conditionOn_pair_of_subset μ ν hH ({e} : Set ι) hξζ hξ hζ)
  have hInc := isIncreasingEvent_coordOpenEvent (singletonConditionCoord e)
  exact hstoch _ hInc.indicator_isIncreasingRandomVariable

/-- The easy direction of Theorem 2.6 in predicate form. -/
theorem onePointConditionalDomination_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) : OnePointConditionalDomination μ ν := by
  intro e ξ ζ hξ hζ hξζ
  exact onePointOpenProb_le_of_holleyCondition μ ν hH e hξζ hξ hζ

/-- Equation (2.14) as a consequence of Holley's condition. -/
theorem onePointCross_le_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) (e : ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom ν ({e} : Set ι) ζ) :
    μ (forceOpen e ξ) * ν (forceClosed e ζ) ≤
      ν (forceOpen e ζ) * μ (forceClosed e ξ) := by
  exact (onePointOpenProb_le_iff_cross μ ν e ξ ζ hξ hζ).1
    (onePointOpenProb_le_of_holleyCondition μ ν hH e hξζ hξ hζ)

/-- A 1-monotonic measure has nondecreasing one-point conditional open probabilities. -/
theorem onePointOpenProb_le_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hmono : OneMonotonicMeasure μ) (e : ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom μ ({e} : Set ι) ζ) :
    onePointOpenProb μ e ξ hξ ≤ onePointOpenProb μ e ζ hζ := by
  have hstoch := hmono e ξ ζ hξ hζ hξζ
  have hInc := isIncreasingEvent_coordOpenEvent (singletonConditionCoord e)
  exact hstoch _ hInc.indicator_isIncreasingRandomVariable

/-- The cross-multiplied one-point inequality generated by 1-monotonicity. -/
theorem onePointCross_le_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hmono : OneMonotonicMeasure μ) (e : ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ ({e} : Set ι) ξ)
    (hζ : 0 < conditionDenom μ ({e} : Set ι) ζ) :
    μ (forceOpen e ξ) * μ (forceClosed e ζ) ≤
      μ (forceOpen e ζ) * μ (forceClosed e ξ) := by
  exact (onePointOpenProb_le_iff_cross μ μ e ξ ζ hξ hζ).1
    (onePointOpenProb_le_of_oneMonotonicMeasure μ hmono e hξζ hξ hζ)

/-- A two-coordinate local cross inequality generated by 1-monotonicity. -/
theorem twoCoordinateCross_le_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hmono : OneMonotonicMeasure μ) (e f : ι) (ω : Set ι) :
    μ (forceOpen e (forceClosed f ω)) * μ (forceClosed e (forceOpen f ω)) ≤
      μ (forceOpen e (forceOpen f ω)) * μ (forceClosed e (forceClosed f ω)) := by
  have hsub : forceClosed f ω ⊆ forceOpen f ω := by
    intro x hx
    simp [forceClosed, forceOpen] at hx ⊢
    exact Or.inr hx.1
  exact onePointCross_le_of_oneMonotonicMeasure μ hmono e hsub
    (conditionDenom_pos_of_strictPositive μ hμ ({e} : Set ι) (forceClosed f ω))
    (conditionDenom_pos_of_strictPositive μ hμ ({e} : Set ι) (forceOpen f ω))

omit [Fintype ι] in
/-- A forced-open configuration meets the corresponding forced-closed one at the closed corner. -/
theorem forceOpen_inter_forceClosed (e : ι) (ω : Set ι) :
    forceOpen e ω ∩ forceClosed e ω = forceClosed e ω := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

omit [Fintype ι] in
/-- A forced-open configuration joins the corresponding forced-closed one at the open corner. -/
theorem forceOpen_union_forceClosed (e : ι) (ω : Set ι) :
    forceOpen e ω ∪ forceClosed e ω = forceOpen e ω := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

omit [Fintype ι] in
/-- Closing one coordinate of a configuration that contains it is undone by forcing it open. -/
theorem forceOpen_forceClosed_eq_of_mem (e : ι) {ω : Set ι} (he : e ∈ ω) :
    forceOpen e (forceClosed e ω) = ω := by
  ext x
  simp [forceOpen, forceClosed]
  aesop

omit [Fintype ι] in
/-- Closing a coordinate twice is the same as closing it once. -/
theorem forceClosed_forceClosed (e : ι) (ω : Set ι) :
    forceClosed e (forceClosed e ω) = forceClosed e ω := by
  ext x
  simp [forceClosed]

omit [Fintype ι] in
/-- Closing a coordinate not present in a configuration changes nothing. -/
theorem forceClosed_eq_self_of_notMem (e : ι) {ω : Set ι} (he : e ∉ ω) :
    forceClosed e ω = ω := by
  ext x
  simp [forceClosed]
  aesop

/-- Holley's condition implies the one-coordinate local Holley inequality (2.4). -/
theorem localHolleyOneCondition_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) : LocalHolleyOneCondition μ ν := by
  intro e ω
  have h := hH (forceOpen e ω) (forceClosed e ω)
  rwa [forceOpen_inter_forceClosed, forceOpen_union_forceClosed] at h

/-- Iterating the one-coordinate local Holley inequality over a finite set of closed
coordinates. This is the multiplicative path step in the comparable-pair part of
Theorem 2.3. -/
theorem localHolleyOneCondition_closeFinset (μ ν : FiniteCubeMeasure ι)
    (hν : ν.StrictPositive) (hlocal : LocalHolleyOneCondition μ ν) (ω : Set ι) :
    ∀ S : Finset ι, μ ω * ν (ω \ (S : Set ι)) ≤ μ (ω \ (S : Set ι)) * ν ω := by
  classical
  intro S
  refine Finset.induction_on S ?base ?step
  · simp
  · intro e S _ hS
    have hset : ω \ ((insert e S : Finset ι) : Set ι) =
        forceClosed e (ω \ (S : Set ι)) := by
      ext x
      simp [forceClosed]
      aesop
    by_cases heωS : e ∈ ω \ (S : Set ι)
    · have hstep := hlocal e (forceClosed e (ω \ (S : Set ι)))
      have hopen : forceOpen e (forceClosed e (ω \ (S : Set ι))) = ω \ (S : Set ι) :=
        forceOpen_forceClosed_eq_of_mem e heωS
      have hclosed : forceClosed e (forceClosed e (ω \ (S : Set ι))) =
          forceClosed e (ω \ (S : Set ι)) :=
        forceClosed_forceClosed e (ω \ (S : Set ι))
      have hlocal' : μ (ω \ (S : Set ι)) * ν (forceClosed e (ω \ (S : Set ι))) ≤
          μ (forceClosed e (ω \ (S : Set ι))) * ν (ω \ (S : Set ι)) := by
        simpa [hopen, hclosed] using hstep
      have hνmid : 0 < ν (ω \ (S : Set ι)) := hν _
      have hmul1 :=
        mul_le_mul_of_nonneg_right hS (ν.nonneg (forceClosed e (ω \ (S : Set ι))))
      have hmul2 := mul_le_mul_of_nonneg_left hlocal' (ν.nonneg ω)
      have htarget : μ ω * ν (forceClosed e (ω \ (S : Set ι))) ≤
          μ (forceClosed e (ω \ (S : Set ι))) * ν ω := by
        nlinarith [hνmid]
      rw [hset]
      exact htarget
    · have hclosed_self : forceClosed e (ω \ (S : Set ι)) = ω \ (S : Set ι) :=
        forceClosed_eq_self_of_notMem e heωS
      rw [hset, hclosed_self]
      exact hS

/-- The comparable-pair inequality generated by the one-coordinate local Holley condition. -/
theorem localHolleyOneCondition_le_of_subset (μ ν : FiniteCubeMeasure ι)
    (hν : ν.StrictPositive) (hlocal : LocalHolleyOneCondition μ ν)
    {η ω : Set ι} (hηω : η ⊆ ω) :
    μ ω * ν η ≤ μ η * ν ω := by
  classical
  let S : Finset ι := Finset.univ.filter fun e => e ∈ ω ∧ e ∉ η
  have hclose : ω \ (S : Set ι) = η := by
    ext x
    simp [S]
    aesop
  have h := localHolleyOneCondition_closeFinset μ ν hν hlocal ω S
  rwa [hclose] at h

/-- The comparable-pair part of the reverse local Holley criterion proof. -/
theorem holleyCondition_of_localHolleyCondition_of_comparable
    (μ ν : FiniteCubeMeasure ι) (hν : ν.StrictPositive)
    (hlocal : LocalHolleyCondition μ ν) {ω η : Set ι} (hcomp : ω ⊆ η ∨ η ⊆ ω) :
    μ ω * ν η ≤ μ (ω ∩ η) * ν (ω ∪ η) := by
  rcases hcomp with hωη | hηω
  · have hinter : ω ∩ η = ω := by
      ext x
      aesop
    have hunion : ω ∪ η = η := by
      ext x
      aesop
    rw [hinter, hunion]
  · have hinter : ω ∩ η = η := by
      ext x
      aesop
    have hunion : ω ∪ η = ω := by
      ext x
      aesop
    rw [hinter, hunion]
    exact localHolleyOneCondition_le_of_subset μ ν hν hlocal.1 hηω

/-- The algebraic cancellation step in Grimmett's Hamming-distance induction for
Theorem 2.3. The two hypotheses are the two smaller Holley inequalities used in the
displayed multiplication in the proof. -/
theorem holleyInductionStep_mul_cancel (μ ν : FiniteCubeMeasure ι)
    {x y middle bridge bottom top : Set ι}
    (hμmiddle : 0 < μ middle) (hνbridge : 0 < ν bridge)
    (h₁ : μ y * ν bridge ≤ μ middle * ν top)
    (h₂ : μ middle * ν x ≤ μ bottom * ν bridge) :
    μ y * ν x ≤ μ bottom * ν top := by
  have hmul := mul_le_mul h₁ h₂
    (mul_nonneg (μ.nonneg middle) (ν.nonneg x))
    (mul_nonneg (μ.nonneg middle) (ν.nonneg top))
  have hfactor : (μ middle * ν bridge) * (μ y * ν x) ≤
      (μ middle * ν bridge) * (μ bottom * ν top) := by
    calc
      (μ middle * ν bridge) * (μ y * ν x)
          = μ y * ν bridge * (μ middle * ν x) := by ring
      _ ≤ μ middle * ν top * (μ bottom * ν bridge) := hmul
      _ = (μ middle * ν bridge) * (μ bottom * ν top) := by ring
  exact le_of_mul_le_mul_left hfactor (mul_pos hμmiddle hνbridge)

/-- A set-rewriting wrapper around `holleyInductionStep_mul_cancel`: if the two smaller
pointwise Holley inequalities have the meet/join shapes used in the induction, then the
next crossed pair follows. -/
theorem holleyInductionStep_of_holleyInequalityAt (μ ν : FiniteCubeMeasure ι)
    {x y middle bridge bottom top : Set ι}
    (hμmiddle : 0 < μ middle) (hνbridge : 0 < ν bridge)
    (h₁ : HolleyInequalityAt μ ν y bridge)
    (h₂ : HolleyInequalityAt μ ν middle x)
    (hyb_inter : y ∩ bridge = middle) (hyb_union : y ∪ bridge = top)
    (hmx_inter : middle ∩ x = bottom) (hmx_union : middle ∪ x = bridge) :
    μ y * ν x ≤ μ bottom * ν top := by
  have h₁' : μ y * ν bridge ≤ μ middle * ν top := by
    simpa [HolleyInequalityAt, hyb_inter, hyb_union] using h₁
  have h₂' : μ middle * ν x ≤ μ bottom * ν bridge := by
    simpa [HolleyInequalityAt, hmx_inter, hmx_union] using h₂
  exact holleyInductionStep_mul_cancel μ ν hμmiddle hνbridge h₁' h₂'

/-- The set-theoretic Hamming-induction step obtained by deleting one coordinate from the
first configuration. The two Holley hypotheses are the strictly smaller pairs that appear
in the induction once this coordinate is not the only `ω \ η` disagreement. -/
theorem holleyInductionStep_of_openClosed_disagreement (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive) {ω η : Set ι} {e : ι}
    (heω : e ∈ ω) (heη : e ∉ η)
    (h₁ : HolleyInequalityAt μ ν ω (η ∪ forceClosed e ω))
    (h₂ : HolleyInequalityAt μ ν (forceClosed e ω) η) :
    HolleyInequalityAt μ ν ω η := by
  have hyb_inter : ω ∩ (η ∪ forceClosed e ω) = forceClosed e ω := by
    ext x
    by_cases hxe : x = e
    · subst hxe
      simp [forceClosed, heω, heη]
    · simp [forceClosed, hxe]
      tauto
  have hyb_union : ω ∪ (η ∪ forceClosed e ω) = ω ∪ η := by
    ext x
    simp [forceClosed]
    tauto
  have hmx_inter : forceClosed e ω ∩ η = ω ∩ η := by
    ext x
    by_cases hxe : x = e
    · subst hxe
      simp [forceClosed, heη]
    · simp [forceClosed, hxe]
  have hmx_union : forceClosed e ω ∪ η = η ∪ forceClosed e ω := by
    ext x
    simp [Set.mem_union, or_comm]
  exact holleyInductionStep_of_holleyInequalityAt μ ν (hμ _) (hν _) h₁ h₂
    hyb_inter hyb_union hmx_inter hmx_union

/-- The first asymmetric Hamming-induction case for Theorem 2.3: when there are at
least two coordinates open in `ω` and closed in `η`, delete one such coordinate and
invoke the induction hypothesis on the two strictly smaller pairs. -/
theorem holleyInductionStep_of_openClosed_card_two (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive) {ω η : Set ι} {e : ι}
    (he : e ∈ openClosedDisagreeFinset ω η)
    (hmore : 1 < (openClosedDisagreeFinset ω η).card)
    (hIH : ∀ a b : Set ι, hammingDistance a b < hammingDistance ω η →
      HolleyInequalityAt μ ν a b) :
    HolleyInequalityAt μ ν ω η := by
  have he' := (mem_openClosedDisagreeFinset e ω η).1 he
  exact holleyInductionStep_of_openClosed_disagreement μ ν hμ hν he'.1 he'.2
    (hIH ω (η ∪ forceClosed e ω) (hammingDistance_left_bridge_lt he hmore))
    (hIH (forceClosed e ω) η (hammingDistance_forceClosed_left_lt he))

/-- The cross-multiplied one-point inequality generated by one-point conditional
domination. -/
theorem onePointCross_le_of_onePointConditionalDomination (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive)
    (hone : OnePointConditionalDomination μ ν) (e : ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ) :
    μ (forceOpen e ξ) * ν (forceClosed e ζ) ≤
      ν (forceOpen e ζ) * μ (forceClosed e ξ) := by
  have hμden := conditionDenom_pos_of_strictPositive μ hμ ({e} : Set ι) ξ
  have hνden := conditionDenom_pos_of_strictPositive ν hν ({e} : Set ι) ζ
  exact (onePointOpenProb_le_iff_cross μ ν e ξ ζ hμden hνden).1
    (hone e ξ ζ hμden hνden hξζ)

/-- Iterating one-point conditional domination over a finite set of coordinates disjoint
from the upper boundary. This is the product-path proof of Theorem 2.6's converse. -/
theorem onePointConditionalDomination_openFinset_le (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive)
    (hone : OnePointConditionalDomination μ ν) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ) :
    ∀ S : Finset ι, Disjoint (S : Set ι) ζ →
      μ (ξ ∪ (S : Set ι)) * ν ζ ≤ μ ξ * ν (ζ ∪ (S : Set ι)) := by
  classical
  intro S
  refine Finset.induction_on S ?base ?step
  · intro _
    simp
  · intro e S heS ih hdisj
    have hSdisj : Disjoint (S : Set ι) ζ := by
      rw [Set.disjoint_left] at hdisj ⊢
      intro x hxS hxζ
      exact hdisj (by simp [hxS]) hxζ
    have heζ : e ∉ ζ := by
      rw [Set.disjoint_left] at hdisj
      exact fun heζ => hdisj (by simp) heζ
    have heξS : e ∉ ξ ∪ (S : Set ι) := by
      intro heξS
      rcases heξS with heξ | heS'
      · exact heζ (hξζ heξ)
      · exact heS heS'
    have heζS : e ∉ ζ ∪ (S : Set ι) := by
      intro heζS
      rcases heζS with heζ' | heS'
      · exact heζ heζ'
      · exact heS heS'
    have hξSζS : ξ ∪ (S : Set ι) ⊆ ζ ∪ (S : Set ι) :=
      Set.union_subset_union hξζ (fun _ hx => hx)
    have hcross := onePointCross_le_of_onePointConditionalDomination μ ν hμ hν hone e hξSζS
    have hcross' :
        μ (ξ ∪ ((insert e S : Finset ι) : Set ι)) * ν (ζ ∪ (S : Set ι)) ≤
          μ (ξ ∪ (S : Set ι)) * ν (ζ ∪ ((insert e S : Finset ι) : Set ι)) := by
      simpa [forceOpen, forceClosed, heξS, heζS, Set.union_assoc, Set.union_left_comm,
        Set.union_comm, mul_comm, mul_left_comm, mul_assoc] using hcross
    have hih := ih hSdisj
    exact holleyInductionStep_mul_cancel μ ν (hμ _) (hν _) hcross' hih

/-- The converse direction of Theorem 2.6: one-point conditional domination implies
Holley's condition. -/
theorem holleyCondition_of_onePointConditionalDomination (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive)
    (hone : OnePointConditionalDomination μ ν) : HolleyCondition μ ν := by
  intro ω η
  let S : Finset ι := openClosedDisagreeFinset ω η
  have hdisj : Disjoint (S : Set ι) η := by
    rw [Set.disjoint_left]
    intro x hxS hxη
    exact ((mem_openClosedDisagreeFinset x ω η).1 hxS).2 hxη
  have hω : ω ∩ η ∪ (S : Set ι) = ω := by
    ext x
    simp [S, openClosedDisagreeFinset]
    tauto
  have htop : η ∪ (S : Set ι) = ω ∪ η := by
    ext x
    simp [S, openClosedDisagreeFinset]
    tauto
  have h := onePointConditionalDomination_openFinset_le μ ν hμ hν hone
    (Set.inter_subset_right (s := ω) (t := η)) S hdisj
  simpa [S, hω, htop] using h

/-- Theorem 2.6 in predicate form: Holley's condition is equivalent to one-point
conditional domination. -/
theorem holleyCondition_iff_onePointConditionalDomination (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive) :
    HolleyCondition μ ν ↔ OnePointConditionalDomination μ ν := by
  constructor
  · exact onePointConditionalDomination_of_holleyCondition μ ν
  · exact holleyCondition_of_onePointConditionalDomination μ ν hμ hν

/-- The reverse direction of Theorem 2.6, reduced to the local hypotheses of
Theorem 2.3: the one-point conditional inequalities imply (2.4) and (2.5). -/
theorem localHolleyCondition_of_onePointConditionalDomination (μ ν : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hν : ν.StrictPositive)
    (hone : OnePointConditionalDomination μ ν) : LocalHolleyCondition μ ν := by
  constructor
  · intro e ω
    have hμden := conditionDenom_pos_of_strictPositive μ hμ ({e} : Set ι) ω
    have hνden := conditionDenom_pos_of_strictPositive ν hν ({e} : Set ι) ω
    have hprob := hone e ω ω hμden hνden (fun _ hx => hx)
    have hcross := (onePointOpenProb_le_iff_cross μ ν e ω ω hμden hνden).1 hprob
    simpa [mul_comm] using hcross
  · intro e f ω
    have hsub : forceClosed f ω ⊆ forceOpen f ω := by
      intro x hx
      simp [forceClosed, forceOpen] at hx ⊢
      exact Or.inr hx.1
    have hμden := conditionDenom_pos_of_strictPositive μ hμ ({e} : Set ι) (forceClosed f ω)
    have hνden := conditionDenom_pos_of_strictPositive ν hν ({e} : Set ι) (forceOpen f ω)
    have hprob := hone e (forceClosed f ω) (forceOpen f ω) hμden hνden hsub
    have hcross := (onePointOpenProb_le_iff_cross μ ν e (forceClosed f ω)
      (forceOpen f ω) hμden hνden).1 hprob
    simpa [mul_comm] using hcross

omit [Fintype ι] in
/-- The opposite two-coordinate corners meet at the closed-closed corner. -/
theorem forceOpenClosed_inter_forceClosedOpen (e f : ι) (ω : Set ι) :
    forceOpen e (forceClosed f ω) ∩ forceClosed e (forceOpen f ω) =
      forceClosed e (forceClosed f ω) := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

omit [Fintype ι] in
/-- The opposite two-coordinate corners join at the open-open corner. -/
theorem forceOpenClosed_union_forceClosedOpen (e f : ι) (ω : Set ι) :
    forceOpen e (forceClosed f ω) ∪ forceClosed e (forceOpen f ω) =
      forceOpen e (forceOpen f ω) := by
  ext x
  simp [forceOpen, forceClosed]
  tauto

/-- Holley's condition implies the two-coordinate local Holley inequality (2.5). -/
theorem localHolleyTwoCondition_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) : LocalHolleyTwoCondition μ ν := by
  intro e f ω
  have h := hH (forceOpen e (forceClosed f ω)) (forceClosed e (forceOpen f ω))
  rwa [forceOpenClosed_inter_forceClosedOpen, forceOpenClosed_union_forceClosedOpen] at h

/-- The direct opposite-corner part of the reverse local Holley criterion proof. -/
theorem holleyCondition_of_localHolleyCondition_oppositeCorners
    (μ ν : FiniteCubeMeasure ι) (hlocal : LocalHolleyCondition μ ν) (e f : ι)
    (ω : Set ι) :
    μ (forceOpen e (forceClosed f ω)) * ν (forceClosed e (forceOpen f ω)) ≤
      μ (forceOpen e (forceClosed f ω) ∩ forceClosed e (forceOpen f ω)) *
        ν (forceOpen e (forceClosed f ω) ∪ forceClosed e (forceOpen f ω)) := by
  rw [forceOpenClosed_inter_forceClosedOpen, forceOpenClosed_union_forceClosedOpen]
  exact hlocal.2 e f ω

/-- Holley's condition implies the local hypotheses in Theorem 2.3. -/
theorem localHolleyCondition_of_holleyCondition (μ ν : FiniteCubeMeasure ι)
    (hH : HolleyCondition μ ν) : LocalHolleyCondition μ ν :=
  ⟨localHolleyOneCondition_of_holleyCondition μ ν hH,
    localHolleyTwoCondition_of_holleyCondition μ ν hH⟩

/-- The local two-coordinate FKG inequality generated by 1-monotonicity. -/
theorem localTwoCoordinateFKG_le_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hmono : OneMonotonicMeasure μ) (e f : ι) (ω : Set ι) :
    μ (forceOpen e (forceClosed f ω)) * μ (forceClosed e (forceOpen f ω)) ≤
      μ (forceOpen e (forceClosed f ω) ∩ forceClosed e (forceOpen f ω)) *
        μ (forceOpen e (forceClosed f ω) ∪ forceClosed e (forceOpen f ω)) := by
  rw [forceOpenClosed_inter_forceClosedOpen, forceOpenClosed_union_forceClosedOpen]
  simpa [mul_comm] using twoCoordinateCross_le_of_oneMonotonicMeasure μ hμ hmono e f ω

/-- The local FKG predicate is equivalent to the cross form after rewriting meet and join. -/
theorem localTwoCoordinateFKG_iff_cross (μ : FiniteCubeMeasure ι) :
    LocalTwoCoordinateFKG μ ↔
      ∀ e f : ι, ∀ ω : Set ι,
        μ (forceOpen e (forceClosed f ω)) * μ (forceClosed e (forceOpen f ω)) ≤
          μ (forceOpen e (forceOpen f ω)) * μ (forceClosed e (forceClosed f ω)) := by
  constructor
  · intro hlocal e f ω
    have h := hlocal e f ω
    rw [forceOpenClosed_inter_forceClosedOpen, forceOpenClosed_union_forceClosedOpen] at h
    simpa [mul_comm] using h
  · intro hcross e f ω
    rw [forceOpenClosed_inter_forceClosedOpen, forceOpenClosed_union_forceClosedOpen]
    simpa [mul_comm] using hcross e f ω

/-- The self-pair two-coordinate local Holley condition is the local FKG condition. -/
theorem localHolleyTwoCondition_self_iff_localTwoCoordinateFKG (μ : FiniteCubeMeasure ι) :
    LocalHolleyTwoCondition μ μ ↔ LocalTwoCoordinateFKG μ := by
  rw [localTwoCoordinateFKG_iff_cross]
  constructor
  · intro h e f ω
    simpa [mul_comm] using h e f ω
  · intro h e f ω
    simpa [mul_comm] using h e f ω

/-- Full FKG lattice condition implies the local two-coordinate FKG condition. -/
theorem localTwoCoordinateFKG_of_fkgLatticeCondition (μ : FiniteCubeMeasure ι)
    (hFKG : FKGLatticeCondition μ) : LocalTwoCoordinateFKG μ := by
  intro e f ω
  exact hFKG (forceOpen e (forceClosed f ω)) (forceClosed e (forceOpen f ω))

/-- A strictly positive 1-monotonic measure satisfies the local two-coordinate FKG condition. -/
theorem localTwoCoordinateFKG_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hmono : OneMonotonicMeasure μ) :
    LocalTwoCoordinateFKG μ := by
  intro e f ω
  exact localTwoCoordinateFKG_le_of_oneMonotonicMeasure μ hμ hmono e f ω

/-- The `(b) => (a)` implication in Theorem 2.24. -/
theorem stronglyPositivelyAssociated_of_fkgLatticeCondition (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hFKG : FKGLatticeCondition μ) :
    StronglyPositivelyAssociated μ := by
  intro F ξ hden
  exact positivelyAssociated_of_fkg (conditionOn μ F ξ hden)
    (conditionOn_strictPositive μ hμ F ξ hden)
    (fkgLatticeCondition_conditionOn μ hFKG F ξ hden)

/-- The `(b) => (c)` implication in Theorem 2.24. -/
theorem monotonicMeasure_of_fkgLatticeCondition (μ : FiniteCubeMeasure ι)
    (hFKG : FKGLatticeCondition μ) :
    MonotonicMeasure μ := by
  intro F ξ ζ hξ hζ hξζ
  exact stochLE_of_holley (conditionOn μ F ξ hξ) (conditionOn μ F ζ hζ)
    (holleyCondition_conditionOn_of_subset μ hFKG F hξζ hξ hζ)

/-- The `(c) => (d)` implication in Theorem 2.24. -/
theorem oneMonotonicMeasure_of_monotonicMeasure (μ : FiniteCubeMeasure ι)
    (hmono : MonotonicMeasure μ) :
    OneMonotonicMeasure μ := by
  intro e ξ ζ hξ hζ hξζ
  exact hmono ({e} : Set ι) ξ ζ hξ hζ hξζ

/-- The `(d) => (b)` implication in Theorem 2.24. -/
theorem fkgLatticeCondition_of_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) (hmono : OneMonotonicMeasure μ) :
    FKGLatticeCondition μ := by
  exact holleyCondition_of_onePointConditionalDomination μ μ hμ hμ
    (fun e ξ ζ hξ hζ hξζ =>
      onePointOpenProb_le_of_oneMonotonicMeasure μ hmono e hξζ hξ hζ)

/-- For strictly positive finite cube measures, FKG lattice condition and 1-monotonicity
are equivalent. This packages the `(b) => (c) => (d)` and `(d) => (b)` parts of
Theorem 2.24. -/
theorem fkgLatticeCondition_iff_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) :
    FKGLatticeCondition μ ↔ OneMonotonicMeasure μ := by
  constructor
  · intro hFKG
    exact oneMonotonicMeasure_of_monotonicMeasure μ
      (monotonicMeasure_of_fkgLatticeCondition μ hFKG)
  · exact fkgLatticeCondition_of_oneMonotonicMeasure μ hμ

/-- For strictly positive finite cube measures, monotonicity and 1-monotonicity are
equivalent. -/
theorem monotonicMeasure_iff_oneMonotonicMeasure (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) :
    MonotonicMeasure μ ↔ OneMonotonicMeasure μ := by
  constructor
  · exact oneMonotonicMeasure_of_monotonicMeasure μ
  · intro hmono
    exact monotonicMeasure_of_fkgLatticeCondition μ
      (fkgLatticeCondition_of_oneMonotonicMeasure μ hμ hmono)

end FiniteCubeMeasure

end Percolation
