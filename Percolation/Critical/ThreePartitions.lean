import Mathlib.Order.Partition.Finpartition

/-!
# Compatible three-partitions

This file formalizes the finite partition language used in Grimmett Lemma 8.5.
-/

namespace Percolation

/-- A partition of a finite set into exactly three nonempty parts. -/
def ThreePartition {alpha : Type*} [DecidableEq alpha] (s : Finset alpha) :=
  {P : Finpartition s // P.parts.card = 3}

namespace ThreePartition

variable {alpha : Type*} [DecidableEq alpha] {s : Finset alpha}

instance : DecidableEq (ThreePartition s) := by
  unfold ThreePartition
  infer_instance

instance [Fintype alpha] : Fintype (ThreePartition s) := by
  unfold ThreePartition
  infer_instance

/-- The underlying finite partition. -/
def partition (P : ThreePartition s) : Finpartition s := P.1

/-- The three parts of a three-partition. -/
def parts (P : ThreePartition s) : Finset (Finset alpha) := P.1.parts

@[simp]
theorem card_parts (P : ThreePartition s) : P.parts.card = 3 :=
  P.2

theorem three_le_card (P : ThreePartition s) : 3 ≤ s.card := by
  rw [← P.card_parts]
  exact P.partition.card_parts_le_card

theorem part_subset (P : ThreePartition s) {A : Finset alpha} (hA : A ∈ P.parts) : A ⊆ s :=
  P.partition.subset hA

theorem part_nonempty (P : ThreePartition s) {A : Finset alpha} (hA : A ∈ P.parts) :
    A.Nonempty :=
  P.partition.nonempty_of_mem_parts hA

theorem exists_part_ne_two (P : ThreePartition s) {A B : Finset alpha} :
    ∃ C ∈ P.parts, C ≠ A ∧ C ≠ B := by
  have hpair : ({A, B} : Finset (Finset alpha)).card ≤ 2 := by
    exact (Finset.card_insert_le A {B}).trans_eq (by simp)
  have hlt : ({A, B} : Finset (Finset alpha)).card < P.parts.card := by
    rw [P.card_parts]
    omega
  obtain ⟨C, hC⟩ := Finset.sdiff_nonempty_of_card_lt_card hlt
  refine ⟨C, (Finset.mem_sdiff.mp hC).1, ?_, ?_⟩
  · intro hCA
    subst C
    exact (Finset.mem_sdiff.mp hC).2 (by simp)
  · intro hCB
    subst C
    exact (Finset.mem_sdiff.mp hC).2 (by simp)

/-- Restriction of a three-partition after deleting one point. -/
def erasePartition (P : ThreePartition s) (y : alpha) : Finpartition (s.erase y) :=
  P.partition.restrict (Finset.erase_subset y s)

@[simp]
theorem parts_erasePartition (P : ThreePartition s) (y : alpha) :
    (P.erasePartition y).parts =
      (P.parts.image fun A ↦ A ∩ s.erase y).erase ∅ := by
  change (P.1.parts.image (fun A ↦ A ∩ s.erase y)).erase ∅ =
    (P.1.parts.image fun A ↦ A ∩ s.erase y).erase ∅
  rfl

theorem inter_erase_nonempty_of_singleton_not_mem (P : ThreePartition s) {A : Finset alpha}
    {y : alpha} (hA : A ∈ P.parts) (hsingle : {y} ∉ P.parts) :
    (A ∩ s.erase y).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hzero
  have hAs : A ⊆ s := P.part_subset hA
  have herase : A.erase y = ∅ := by
    have heq : A ∩ s.erase y = A.erase y := by
      rw [Finset.inter_erase, Finset.inter_eq_left.mpr hAs]
    rw [← heq]
    exact hzero
  rcases (Finset.erase_eq_empty_iff A y).mp herase with hAempty | hAy
  · exact P.partition.ne_empty hA hAempty
  · exact hsingle (hAy ▸ hA)

/-- Deleting `y` preserves all three parts exactly when `{y}` was not a part. -/
theorem card_parts_erasePartition_eq_three_iff (P : ThreePartition s) {y : alpha} :
    (P.erasePartition y).parts.card = 3 ↔ {y} ∉ P.parts := by
  constructor
  · intro hcard hsingle
    have hsub : (P.erasePartition y).parts ⊆
        (P.parts.erase {y}).image fun A ↦ A ∩ s.erase y := by
      intro U hU
      rw [parts_erasePartition, Finset.mem_erase] at hU
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hU.2
      refine Finset.mem_image.mpr ⟨A, Finset.mem_erase.mpr ⟨?_, hA⟩, rfl⟩
      intro hAy
      subst A
      simp at hU
    have hle : (P.erasePartition y).parts.card ≤ (P.parts.erase {y}).card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_erase_of_mem hsingle, P.card_parts, hcard] at hle
    omega
  · intro hsingle
    rw [parts_erasePartition]
    have hnonempty : ∀ A ∈ P.parts, A ∩ s.erase y ≠ ∅ := by
      exact fun A hA ↦ Finset.nonempty_iff_ne_empty.mp
        (P.inter_erase_nonempty_of_singleton_not_mem hA hsingle)
    have hinj : Set.InjOn (fun A ↦ A ∩ s.erase y) P.parts := by
      intro A hA B hB hEq
      by_contra hAB
      obtain ⟨x, hx⟩ : (A ∩ s.erase y).Nonempty := Finset.nonempty_iff_ne_empty.mpr
        (hnonempty A hA)
      have hxBInter : x ∈ B ∩ s.erase y := by
        change x ∈ (fun C ↦ C ∩ s.erase y) B
        rw [← hEq]
        exact hx
      exact Finset.disjoint_left.mp (P.partition.disjoint hA hB hAB)
        (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hxBInter).1
    rw [Finset.erase_eq_of_notMem]
    · rw [Finset.card_image_of_injOn hinj, P.card_parts]
    · simpa only [Finset.mem_image, not_exists, not_and] using hnonempty

/-- A point deletion which is known to retain three parts. -/
def eraseThreePartition (P : ThreePartition s) (y : alpha)
    (h : (P.erasePartition y).parts.card = 3) : ThreePartition (s.erase y) :=
  ⟨P.erasePartition y, h⟩

/-- Two three-partitions are compatible when complementary parts can be nested as in
Grimmett's definition preceding Lemma 8.5. -/
def Compatible (P Q : ThreePartition s) : Prop :=
  ∃ A ∈ P.parts, ∃ B ∈ Q.parts, s \ A ⊆ B ∧ s \ B ⊆ A

theorem compatible_comm {P Q : ThreePartition s} : P.Compatible Q ↔ Q.Compatible P := by
  constructor <;> rintro ⟨A, hA, B, hB, hAB, hBA⟩
  · exact ⟨B, hB, A, hA, hBA, hAB⟩
  · exact ⟨B, hB, A, hA, hBA, hAB⟩

theorem not_compatible_of_singleton_mem {P Q : ThreePartition s} {y : alpha} (hy : y ∈ s)
    (hP : {y} ∈ P.parts) (hQ : {y} ∈ Q.parts) : ¬P.Compatible Q := by
  rintro ⟨A, hA, B, hB, hAB, hBA⟩
  by_cases hyA : y ∈ A
  · have hAy : A = {y} := P.partition.eq_of_mem_parts hA hP hyA (by simp)
    obtain ⟨C, hC, hCB, hCy⟩ := Q.exists_part_ne_two (A := B) (B := {y})
    obtain ⟨x, hxC⟩ := Q.part_nonempty hC
    have hxS : x ∈ s := Q.part_subset hC hxC
    have hxB : x ∉ B := Finset.disjoint_left.mp (Q.partition.disjoint hC hB hCB) hxC
    have hxy : x ≠ y := by
      intro hxy
      subst x
      exact Finset.disjoint_left.mp (Q.partition.disjoint hC hQ hCy) hxC (by simp)
    have hxA : x ∈ A := hBA (Finset.mem_sdiff.mpr ⟨hxS, hxB⟩)
    exact hxy (by simpa [hAy] using hxA)
  · have hyB : y ∈ B := hAB (Finset.mem_sdiff.mpr ⟨hy, hyA⟩)
    have hBy : B = {y} := Q.partition.eq_of_mem_parts hB hQ hyB (by simp)
    obtain ⟨C, hC, hCA, hCy⟩ := P.exists_part_ne_two (A := A) (B := {y})
    obtain ⟨x, hxC⟩ := P.part_nonempty hC
    have hxS : x ∈ s := P.part_subset hC hxC
    have hxA : x ∉ A := Finset.disjoint_left.mp (P.partition.disjoint hC hA hCA) hxC
    have hxy : x ≠ y := by
      intro hxy
      subst x
      exact Finset.disjoint_left.mp (P.partition.disjoint hC hP hCy) hxC (by simp)
    have hxB : x ∈ B := hAB (Finset.mem_sdiff.mpr ⟨hxS, hxA⟩)
    exact hxy (by simpa [hBy] using hxB)

theorem compatible_eraseThreePartition {P Q : ThreePartition s} {y : alpha}
    (hPQ : P.Compatible Q) (hP : (P.erasePartition y).parts.card = 3)
    (hQ : (Q.erasePartition y).parts.card = 3) :
    (P.eraseThreePartition y hP).Compatible (Q.eraseThreePartition y hQ) := by
  obtain ⟨A, hA, B, hB, hAB, hBA⟩ := hPQ
  have hPsingle : {y} ∉ P.parts := P.card_parts_erasePartition_eq_three_iff.mp hP
  have hQsingle : {y} ∉ Q.parts := Q.card_parts_erasePartition_eq_three_iff.mp hQ
  have hAmem : A ∩ s.erase y ∈ (P.eraseThreePartition y hP).parts := by
    rw [parts, eraseThreePartition, parts_erasePartition, Finset.mem_erase]
    exact ⟨Finset.nonempty_iff_ne_empty.mp
      (P.inter_erase_nonempty_of_singleton_not_mem hA hPsingle), Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
  have hBmem : B ∩ s.erase y ∈ (Q.eraseThreePartition y hQ).parts := by
    rw [parts, eraseThreePartition, parts_erasePartition, Finset.mem_erase]
    exact ⟨Finset.nonempty_iff_ne_empty.mp
      (Q.inter_erase_nonempty_of_singleton_not_mem hB hQsingle), Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩
  refine ⟨A ∩ s.erase y, hAmem, B ∩ s.erase y, hBmem, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxt, hxA⟩ := Finset.mem_sdiff.mp hx
    have hxs : x ∈ s := Finset.mem_of_mem_erase hxt
    have hxnotA : x ∉ A := fun hxa ↦ hxA (Finset.mem_inter.mpr ⟨hxa, hxt⟩)
    exact Finset.mem_inter.mpr ⟨hAB (Finset.mem_sdiff.mpr ⟨hxs, hxnotA⟩), hxt⟩
  · intro x hx
    obtain ⟨hxt, hxB⟩ := Finset.mem_sdiff.mp hx
    have hxs : x ∈ s := Finset.mem_of_mem_erase hxt
    have hxnotB : x ∉ B := fun hxb ↦ hxB (Finset.mem_inter.mpr ⟨hxb, hxt⟩)
    exact Finset.mem_inter.mpr ⟨hBA (Finset.mem_sdiff.mpr ⟨hxs, hxnotB⟩), hxt⟩

theorem not_compatible_self (P : ThreePartition s) : ¬P.Compatible P := by
  rintro ⟨A, hA, B, hB, hAB, _hBA⟩
  obtain ⟨C, hC, hCA, hCB⟩ := P.exists_part_ne_two (A := A) (B := B)
  obtain ⟨x, hxC⟩ := P.part_nonempty hC
  have hxS : x ∈ s := P.part_subset hC hxC
  have hxA : x ∉ A := Finset.disjoint_left.mp (P.partition.disjoint hC hA hCA) hxC
  have hxB : x ∉ B := Finset.disjoint_left.mp (P.partition.disjoint hC hB hCB) hxC
  exact hxB (hAB (Finset.mem_sdiff.mpr ⟨hxS, hxA⟩))

theorem eraseThreePartition_ne_of_compatible {P Q : ThreePartition s} {y : alpha}
    (hPQ : P.Compatible Q) (hP : (P.erasePartition y).parts.card = 3)
    (hQ : (Q.erasePartition y).parts.card = 3) :
    P.eraseThreePartition y hP ≠ Q.eraseThreePartition y hQ := by
  intro hEq
  have hcompat := compatible_eraseThreePartition hPQ hP hQ
  rw [hEq] at hcompat
  exact (not_compatible_self _ hcompat)

/-- Grimmett Lemma 8.5: a pairwise compatible family of distinct three-partitions of `s`
has at most `|s| - 2` members. -/
theorem compatibleThreePartitions_card_le (F : Finset (ThreePartition s))
    (hF : (F : Set (ThreePartition s)).Pairwise Compatible) : F.card ≤ s.card - 2 := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s F with
  | h n ih =>
      by_cases hFempty : F = ∅
      · simp [hFempty]
      · obtain ⟨P₀, hP₀F⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
        have hthree : 3 ≤ s.card := (P₀ : ThreePartition s).three_le_card
        obtain ⟨y, hy⟩ := s.nonempty_of_ne_empty fun hs ↦ by simp [hs] at hthree
        let good := F.filter fun P ↦ {y} ∉ P.parts
        let bad := F.filter fun P ↦ {y} ∈ P.parts
        have hbad : bad.card ≤ 1 := Finset.card_le_one.mpr fun P hP Q hQ ↦ by
          have hPdata := Finset.mem_filter.mp hP
          have hQdata := Finset.mem_filter.mp hQ
          by_contra hPQ
          exact not_compatible_of_singleton_mem hy hPdata.2 hQdata.2
            (hF hPdata.1 hQdata.1 hPQ)
        let eraseGood : {P // P ∈ good} → ThreePartition (s.erase y) := fun P ↦
          P.1.eraseThreePartition y <|
            P.1.card_parts_erasePartition_eq_three_iff.mpr (Finset.mem_filter.mp P.2).2
        have heraseGoodInj : Function.Injective eraseGood := by
          intro P Q hEq
          apply Subtype.ext
          by_contra hPQ
          have hPdata := Finset.mem_filter.mp P.2
          have hQdata := Finset.mem_filter.mp Q.2
          have hcompat : P.1.Compatible Q.1 := hF hPdata.1 hQdata.1 hPQ
          have hne := eraseThreePartition_ne_of_compatible hcompat
            (P.1.card_parts_erasePartition_eq_three_iff.mpr hPdata.2)
            (Q.1.card_parts_erasePartition_eq_three_iff.mpr hQdata.2)
          exact hne (by simpa [eraseGood] using hEq)
        let eraseGoodEmbedding : {P // P ∈ good} ↪ ThreePartition (s.erase y) :=
          ⟨eraseGood, heraseGoodInj⟩
        let G : Finset (ThreePartition (s.erase y)) := good.attach.map eraseGoodEmbedding
        have hGcard : G.card = good.card := by simp [G]
        have hGpair : (G : Set (ThreePartition (s.erase y))).Pairwise Compatible := by
          intro R hR S hS hRS
          obtain ⟨P, _hP, rfl⟩ := Finset.mem_map.mp hR
          obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_map.mp hS
          have hPQ : P.1 ≠ Q.1 := by
            intro hEq
            exact hRS (congrArg eraseGoodEmbedding (Subtype.ext hEq))
          have hPdata := Finset.mem_filter.mp P.2
          have hQdata := Finset.mem_filter.mp Q.2
          simpa [eraseGoodEmbedding, eraseGood] using
            compatible_eraseThreePartition (hF hPdata.1 hQdata.1 hPQ)
              (P.1.card_parts_erasePartition_eq_three_iff.mpr hPdata.2)
              (Q.1.card_parts_erasePartition_eq_three_iff.mpr hQdata.2)
        have heraseCard : (s.erase y).card < n := by
          rw [Finset.card_erase_of_mem hy, hn]
          omega
        have hgood : good.card ≤ (s.erase y).card - 2 := by
          rw [← hGcard]
          exact ih (s.erase y).card heraseCard G hGpair rfl
        have hsplit : good.card + bad.card = F.card := by
          simpa [good, bad] using
            F.card_filter_add_card_filter_not (fun P : ThreePartition s ↦ {y} ∉ P.parts)
        rw [← hsplit]
        calc
          good.card + bad.card ≤ ((s.erase y).card - 2) + 1 := Nat.add_le_add hgood hbad
          _ ≤ s.card - 2 := by rw [Finset.card_erase_of_mem hy]; omega
          _ = n - 2 := by rw [hn]

end ThreePartition

end Percolation
