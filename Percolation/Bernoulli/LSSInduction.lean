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

/-- The independently diluted field has the prescribed values `z` on the finite set `C`. -/
def dilutedConstraintEvent {ι : Type*} (C : Finset ι) (z : Set ι) :
    Set (Set ι × Set ι) :=
  {yz | ∀ x ∈ C, (x ∈ yz.1 ∧ x ∈ yz.2) ↔ x ∈ z}

/-- All sites in `C` are open in the original field. -/
def originalOpenOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | (C : Set ι) ⊆ yz.1}

/-- All sites in `C` are retained by the auxiliary iid field. -/
def retentionOpenOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | (C : Set ι) ⊆ yz.2}

/-- Every retention bit in `C` is closed.  This is Grimmett's event `B⁰`. -/
def retentionClosedOnProductEvent {ι : Type*} (C : Finset ι) :
    Set (Set ι × Set ι) :=
  {yz | Disjoint (C : Set ι) yz.2}

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

end Percolation
