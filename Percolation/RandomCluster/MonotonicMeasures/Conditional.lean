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

end FiniteCubeMeasure

end Percolation
