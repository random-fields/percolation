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

theorem holleyCondition_conditionOn_of_subset (μ : FiniteCubeMeasure ι)
    (hFKG : FKGLatticeCondition μ) (F : Set ι) {ξ ζ : Set ι} (hξζ : ξ ⊆ ζ)
    (hξ : 0 < conditionDenom μ F ξ) (hζ : 0 < conditionDenom μ F ζ) :
    HolleyCondition (conditionOn μ F ξ hξ) (conditionOn μ F ζ hζ) := by
  intro ωF ηF
  have hbase := hFKG (conditionSplice F ξ ωF) (conditionSplice F ζ ηF)
  have hbase' :
      μ (conditionSplice F ξ ωF) * μ (conditionSplice F ζ ηF) ≤
        μ (conditionSplice F ξ (ωF ∩ ηF)) *
          μ (conditionSplice F ζ (ωF ∪ ηF)) := by
    simpa [conditionSplice_inter_of_subset hξζ, conditionSplice_union_of_subset hξζ] using hbase
  have hdiv := div_le_div_of_nonneg_right hbase'
    (mul_nonneg (le_of_lt hξ) (le_of_lt hζ))
  calc
    conditionOn μ F ξ hξ ωF * conditionOn μ F ζ hζ ηF =
        (μ (conditionSplice F ξ ωF) * μ (conditionSplice F ζ ηF)) /
          (conditionDenom μ F ξ * conditionDenom μ F ζ) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hξ, ne_of_gt hζ]
    _ ≤ (μ (conditionSplice F ξ (ωF ∩ ηF)) *
          μ (conditionSplice F ζ (ωF ∪ ηF))) /
          (conditionDenom μ F ξ * conditionDenom μ F ζ) := hdiv
    _ = conditionOn μ F ξ hξ (ωF ∩ ηF) * conditionOn μ F ζ hζ (ωF ∪ ηF) := by
      dsimp [conditionOn]
      field_simp [ne_of_gt hξ, ne_of_gt hζ]

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
