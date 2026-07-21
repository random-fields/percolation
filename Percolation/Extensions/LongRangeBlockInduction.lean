import Percolation.Extensions.LongRangeBlockCrossing

/-!
# Deterministic induction for Newman--Schulman blocks

The probability estimates are useful only after a literal graph-theoretic induction: enough
large child components, linked by cross bonds, lie in one large parent component.  This file
proves that implication with all finite-block subtype maps explicit.
-/

namespace Percolation

open scoped BigOperators

/-- Inclusion of one induced open graph into a larger induced open graph. -/
def longRangeInduceInclusionHom (ω : LongRangeConfiguration)
    {A B : Finset ℤ} (hAB : A ⊆ B) :
    (longRangeOpenGraph ω).induce (A : Set ℤ) →g
      (longRangeOpenGraph ω).induce (B : Set ℤ) where
  toFun := fun x ↦ ⟨x.val, hAB x.property⟩
  map_rel' := by
    intro x y hxy
    change (longRangeOpenGraph ω).Adj x.val y.val
    exact hxy

theorem reachable_parent_of_reachable_child
    (ω : LongRangeConfiguration) {A B : Finset ℤ} (hAB : A ⊆ B)
    {x y : A}
    (hxy : ((longRangeOpenGraph ω).induce (A : Set ℤ)).Reachable x y) :
    ((longRangeOpenGraph ω).induce (B : Set ℤ)).Reachable
      ⟨x.val, hAB x.property⟩ ⟨y.val, hAB y.property⟩ := by
  simpa [longRangeInduceInclusionHom] using
    hxy.map (longRangeInduceInclusionHom ω hAB)

/-- Any two vertices returned by the canonical selector are connected inside their block. -/
theorem reachable_of_mem_longRangeSelectedComponent
    {ω : LongRangeConfiguration} {B : Finset ℤ} {m : ℕ}
    {x y : B} (hx : x ∈ longRangeSelectedComponent ω B m)
    (hy : y ∈ longRangeSelectedComponent ω B m) :
    ((longRangeOpenGraph ω).induce (B : Set ℤ)).Reachable x y := by
  classical
  unfold longRangeSelectedComponent at hx hy
  dsimp only at hx hy
  split_ifs at hx hy with hQ
  · have hx' := mem_longRangeComponentInFinset_iff.mp hx
    have hy' := mem_longRangeComponentInFinset_iff.mp hy
    exact hx'.symm.trans hy'
  · simp at hx

/-- Selected vertices in different child blocks are disjoint. -/
theorem disjoint_selectedChildVertexFinsets
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) (ω : LongRangeConfiguration) {i j : Fin arity} (hij : i ≠ j) :
    Disjoint
      (longRangeComponentVertexFinset
        (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + i.val)) m))
      (longRangeComponentVertexFinset
        (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + j.val)) m)) := by
  exact Disjoint.mono
    (longRangeComponentVertexFinset_subset _)
    (longRangeComponentVertexFinset_subset _)
    (longRangeBlockVertices_children_disjoint hbase harity z
      (fun h ↦ hij (Fin.ext h)))

/-- Union of canonical selected components over a finite set of children. -/
noncomputable def longRangeSelectedChildrenUnion
    (base arity k m : ℕ) (z : ℤ) (ω : LongRangeConfiguration)
    (J : Finset (Fin arity)) : Finset ℤ :=
  J.biUnion fun i ↦ longRangeComponentVertexFinset
    (longRangeSelectedComponent ω
      (longRangeBlockVertices base arity k (z * arity + i.val)) m)

theorem card_longRangeSelectedChildrenUnion
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) (ω : LongRangeConfiguration) (J : Finset (Fin arity)) :
    (longRangeSelectedChildrenUnion base arity k m z ω J).card =
      ∑ i ∈ J, (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + i.val)) m).card := by
  classical
  rw [longRangeSelectedChildrenUnion, Finset.card_biUnion]
  · simp
  · intro i _hi j _hj hij
    exact disjoint_selectedChildVertexFinsets hbase harity z ω hij

theorem longRangeSelectedChildrenUnion_subset_parent
    {base arity k m : ℕ} (z : ℤ) (ω : LongRangeConfiguration)
    (J : Finset (Fin arity)) :
    longRangeSelectedChildrenUnion base arity k m z ω J ⊆
      longRangeBlockVertices base arity (k + 1) z := by
  classical
  intro x hx
  rw [longRangeSelectedChildrenUnion, Finset.mem_biUnion] at hx
  rcases hx with ⟨i, hiJ, hxi⟩
  exact (longRangeComponentVertexFinset_subset _ hxi) |>
    longRangeBlockVertices_child_subset base arity k z i.isLt

/-- A cross bond between selected child components is an edge of the parent induced graph. -/
theorem parent_adj_of_selectedChildren_linked
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) (ω : LongRangeConfiguration)
    {i j : Fin arity} (hij : i ≠ j)
    (hlink : longRangeSetsLinked ω
      (longRangeComponentVertexFinset
        (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + i.val)) m))
      (longRangeComponentVertexFinset
        (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + j.val)) m))) :
    ∃ a : longRangeBlockVertices base arity k (z * arity + i.val),
      ∃ b : longRangeBlockVertices base arity k (z * arity + j.val),
        ((longRangeOpenGraph ω).induce
          (longRangeBlockVertices base arity (k + 1) z : Set ℤ)).Adj
            ⟨a.val, longRangeBlockVertices_child_subset base arity k z i.isLt a.property⟩
            ⟨b.val, longRangeBlockVertices_child_subset base arity k z j.isLt b.property⟩ ∧
        a ∈ longRangeSelectedComponent ω _ m ∧
        b ∈ longRangeSelectedComponent ω _ m := by
  rcases hlink with ⟨a, ha, b, hb, hab⟩
  rw [longRangeComponentVertexFinset, Finset.mem_map] at ha hb
  rcases ha with ⟨aC, haC, haEq⟩
  rcases hb with ⟨bC, hbC, hbEq⟩
  change aC.val = a at haEq
  change bC.val = b at hbEq
  subst a
  subst b
  refine ⟨aC, bC, ?_, haC, hbC⟩
  change (longRangeOpenGraph ω).Adj aC.val bC.val
  rw [longRangeOpenGraph_adj]
  refine ⟨hab, ?_⟩
  intro habEq
  change aC.val = bC.val at habEq
  exact Finset.disjoint_left.mp
    (longRangeBlockVertices_children_disjoint hbase harity z
      (fun h ↦ hij (Fin.ext h))) aC.property (habEq ▸ bC.property)

/-- If child `i₀` and child `i` have large selected components and are linked, every selected
vertex of `i` is reachable from every selected vertex of `i₀` inside the parent. -/
theorem reachable_parent_between_selectedChildren
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) (ω : LongRangeConfiguration)
    {i₀ i : Fin arity} (hi₀i : i₀ ≠ i)
    {x : longRangeBlockVertices base arity k (z * arity + i₀.val)}
    {y : longRangeBlockVertices base arity k (z * arity + i.val)}
    (hx : x ∈ longRangeSelectedComponent ω _ m)
    (hy : y ∈ longRangeSelectedComponent ω _ m)
    (hlink : longRangeSetsLinked ω
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + i₀.val)) m))
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + i.val)) m))) :
    ((longRangeOpenGraph ω).induce
      (longRangeBlockVertices base arity (k + 1) z : Set ℤ)).Reachable
        ⟨x.val, longRangeBlockVertices_child_subset base arity k z i₀.isLt x.property⟩
        ⟨y.val, longRangeBlockVertices_child_subset base arity k z i.isLt y.property⟩ := by
  obtain ⟨aC, bC, hab, ha, hb⟩ :=
    parent_adj_of_selectedChildren_linked hbase harity z ω hi₀i hlink
  have hxaChild := reachable_of_mem_longRangeSelectedComponent hx ha
  have hbyChild := reachable_of_mem_longRangeSelectedComponent hb hy
  have hxa := reachable_parent_of_reachable_child ω
    (longRangeBlockVertices_child_subset base arity k z i₀.isLt) hxaChild
  have hby := reachable_parent_of_reachable_child ω
    (longRangeBlockVertices_child_subset base arity k z i.isLt) hbyChild
  exact hxa.trans (hab.reachable.trans hby)

/-- Quantitative deterministic induction: `quota` pairwise-linked selected child components of
size at least `m` produce a parent component of size at least `quota*m`. -/
theorem exists_parent_component_card_ge_of_selectedChildren
    {base arity quota k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (hquota : 0 < quota) (hm : 0 < m)
    (z : ℤ) (ω : LongRangeConfiguration) (J : Finset (Fin arity))
    (hJcard : quota ≤ J.card)
    (hlarge : ∀ i ∈ J, m ≤ (longRangeSelectedComponent ω
      (longRangeBlockVertices base arity k (z * arity + i.val)) m).card)
    (hlink : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → longRangeSetsLinked ω
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + i.val)) m))
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + j.val)) m))) :
    ∃ x : longRangeBlockVertices base arity (k + 1) z,
      quota * m ≤ (longRangeComponentInFinset ω
        (longRangeBlockVertices base arity (k + 1) z) x).card := by
  classical
  have hJnonempty : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    subst J
    simp at hJcard
    omega
  let i₀ : Fin arity := hJnonempty.choose
  have hi₀J : i₀ ∈ J := hJnonempty.choose_spec
  let C₀ := longRangeSelectedComponent ω
    (longRangeBlockVertices base arity k (z * arity + i₀.val)) m
  have hC₀pos : 0 < C₀.card := hm.trans_le (hlarge i₀ hi₀J)
  have hC₀nonempty : C₀.Nonempty := Finset.card_pos.mp hC₀pos
  let x₀ : longRangeBlockVertices base arity k (z * arity + i₀.val) :=
    hC₀nonempty.choose
  have hx₀ : x₀ ∈ C₀ := hC₀nonempty.choose_spec
  let xP : longRangeBlockVertices base arity (k + 1) z :=
    ⟨x₀.val, longRangeBlockVertices_child_subset base arity k z i₀.isLt x₀.property⟩
  let U := longRangeSelectedChildrenUnion base arity k m z ω J
  have hUparent : U ⊆ longRangeBlockVertices base arity (k + 1) z :=
    longRangeSelectedChildrenUnion_subset_parent z ω J
  let e : U ↪ longRangeBlockVertices base arity (k + 1) z :=
  { toFun := fun u ↦ ⟨u.val, hUparent u.property⟩
    inj' := by
      intro u v h
      apply Subtype.ext
      change u.val = v.val
      exact congrArg (fun w : longRangeBlockVertices base arity (k + 1) z ↦ w.val) h }
  let UP : Finset (longRangeBlockVertices base arity (k + 1) z) := U.attach.map e
  have hUPcard : UP.card = U.card := by simp [UP]
  have hUPsubset : UP ⊆ longRangeComponentInFinset ω
      (longRangeBlockVertices base arity (k + 1) z) xP := by
    intro u hu
    change u ∈ U.attach.map e at hu
    rw [Finset.mem_map] at hu
    rcases hu with ⟨uU, _huAttach, rfl⟩
    rw [mem_longRangeComponentInFinset_iff]
    have huU : uU.val ∈ U := uU.property
    change uU.val ∈ longRangeSelectedChildrenUnion base arity k m z ω J at huU
    rw [longRangeSelectedChildrenUnion, Finset.mem_biUnion] at huU
    rcases huU with ⟨i, hiJ, hui⟩
    rw [longRangeComponentVertexFinset, Finset.mem_map] at hui
    rcases hui with ⟨y, hy, hyval⟩
    change y.val = uU.val at hyval
    have heu : e uU =
        (⟨y.val, longRangeBlockVertices_child_subset base arity k z i.isLt y.property⟩ :
          longRangeBlockVertices base arity (k + 1) z) := by
      apply Subtype.ext
      exact hyval.symm
    rw [heu]
    by_cases hi : i₀ = i
    · subst i
      have hxyChild := reachable_of_mem_longRangeSelectedComponent hx₀ hy
      simpa [xP, e] using reachable_parent_of_reachable_child ω
        (longRangeBlockVertices_child_subset base arity k z i₀.isLt) hxyChild
    · simpa [xP, e] using reachable_parent_between_selectedChildren
        hbase harity z ω hi hx₀ hy (hlink i₀ hi₀J i hiJ hi)
  refine ⟨xP, ?_⟩
  calc
    quota * m ≤ J.card * m := Nat.mul_le_mul_right m hJcard
    _ = ∑ _i ∈ J, m := by simp
    _ ≤ ∑ i ∈ J, (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + i.val)) m).card := by
      exact Finset.sum_le_sum fun i hi ↦ hlarge i hi
    _ = U.card := (card_longRangeSelectedChildrenUnion hbase harity z ω J).symm
    _ = UP.card := hUPcard.symm
    _ ≤ (longRangeComponentInFinset ω
        (longRangeBlockVertices base arity (k + 1) z) xP).card :=
      Finset.card_le_card hUPsubset

/-- Source-level good-block induction using the recursive target sizes. -/
theorem mem_longRangeGeometricBlockGoodEvent_succ_of_children
    {base arity quota k : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (hquota : 0 < quota) (z : ℤ) (ω : LongRangeConfiguration)
    (J : Finset (Fin arity)) (hJcard : quota ≤ J.card)
    (hgood : ∀ i ∈ J, ω ∈ longRangeGeometricBlockGoodEvent
      base arity quota k (z * arity + i.val))
    (hlink : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → longRangeSetsLinked ω
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + i.val))
        (longRangeBlockTargetSize base quota k)))
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k (z * arity + j.val))
        (longRangeBlockTargetSize base quota k)))) :
    ω ∈ longRangeGeometricBlockGoodEvent base arity quota (k + 1) z := by
  let m := longRangeBlockTargetSize base quota k
  have hm : 0 < m := by simp [m, longRangeBlockTargetSize, hbase, hquota]
  have hlarge : ∀ i ∈ J, m ≤ (longRangeSelectedComponent ω
      (longRangeBlockVertices base arity k (z * arity + i.val)) m).card := by
    intro i hi
    exact longRangeSelectedComponent_spec (hgood i hi)
  obtain ⟨x, hx⟩ := exists_parent_component_card_ge_of_selectedChildren
    hbase harity hquota hm z ω J hJcard hlarge hlink
  refine ⟨x, ?_⟩
  rw [longRangeBlockTargetSize_succ]
  exact hx

end Percolation
