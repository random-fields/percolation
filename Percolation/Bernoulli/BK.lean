import Percolation.Bernoulli.Increasing

/-!
# BK/Reimer disjoint-occurrence infrastructure

This file starts the deterministic event-level API for Grimmett's BK inequality section.  It
defines finite witness sets that force events and the disjoint-occurrence event `A ∘ B`.  The
deep BK/Reimer probability inequalities are intentionally not asserted here.
-/

namespace Percolation

open scoped Finset

/-- A finite coordinate set `K` forces event `A` at configuration `ω` if every configuration
agreeing with `ω` on `K` belongs to `A`. This is the witness relation used in BK disjoint
occurrence. -/
def Forces {ι : Type*} (K : Finset ι) (ω : Set ι) (A : Set (Set ι)) : Prop :=
  ∀ η : Set ι, (∀ e ∈ K, (e ∈ η ↔ e ∈ ω)) → η ∈ A

theorem Forces.mem {ι : Type*} {K : Finset ι} {ω : Set ι} {A : Set (Set ι)}
    (hK : Forces K ω A) :
    ω ∈ A :=
  hK ω (fun _ _ ↦ Iff.rfl)

theorem Forces.mono_event {ι : Type*} {K : Finset ι} {ω : Set ι}
    {A B : Set (Set ι)} (hK : Forces K ω A) (hAB : A ⊆ B) :
    Forces K ω B := by
  intro η hagree
  exact hAB (hK η hagree)

theorem Forces.mono_support {ι : Type*} {K L : Finset ι} {ω : Set ι}
    {A : Set (Set ι)} (hK : Forces K ω A) (hKL : K ⊆ L) :
    Forces L ω A := by
  intro η hagree
  exact hK η fun e heK ↦ hagree e (hKL heK)

theorem forces_empty_iff {ι : Type*} {ω : Set ι} {A : Set (Set ι)} :
    Forces (∅ : Finset ι) ω A ↔ A = Set.univ := by
  constructor
  · intro hA
    ext η
    constructor
    · intro _hη
      exact Set.mem_univ η
    · intro _hη
      exact hA η (by simp)
  · intro hA η _hagree
    rw [hA]
    exact Set.mem_univ η

theorem DependsOn.forces {ι : Type*} {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) {ω : Set ι} (hω : ω ∈ A) :
    Forces E ω A := by
  intro η hagree
  exact (hA fun e he ↦ (hagree e he).symm).mp hω

theorem Forces.congr_config {ι : Type*} {K : Finset ι} {ω η : Set ι}
    {A : Set (Set ι)} (hK : Forces K ω A)
    (hωη : ∀ e ∈ K, (e ∈ η ↔ e ∈ ω)) :
    Forces K η A := by
  intro ξ hξ
  exact hK ξ fun e he ↦ (hξ e he).trans (hωη e he)

theorem Forces.restrict_of_dependsOn {ι : Type*} [DecidableEq ι]
    {K E : Finset ι} {ω : Set ι} {A : Set (Set ι)}
    (hK : Forces K ω A) (hA : DependsOn E A) :
    Forces (K ∩ E) ω A := by
  intro η hagree
  let ξ : Set ι := (ω ∩ (K : Set ι)) ∪ (η \ (K : Set ι))
  have hξK : ∀ e ∈ K, (e ∈ ξ ↔ e ∈ ω) := by
    intro e heK
    constructor
    · intro heξ
      rcases heξ with heωK | heηK
      · exact heωK.1
      · exact (heηK.2 heK).elim
    · intro heω
      exact Or.inl ⟨heω, heK⟩
  have hξA : ξ ∈ A := hK ξ hξK
  have hξη : ∀ e ∈ E, (e ∈ ξ ↔ e ∈ η) := by
    intro e heE
    by_cases heK : e ∈ K
    · have heKE : e ∈ K ∩ E := Finset.mem_inter.mpr ⟨heK, heE⟩
      have hηω : e ∈ η ↔ e ∈ ω := hagree e heKE
      constructor
      · intro heξ
        rcases heξ with heωK | heηK
        · exact hηω.mpr heωK.1
        · exact heηK.1
      · intro heη
        exact Or.inl ⟨hηω.mp heη, heK⟩
    · constructor
      · intro heξ
        rcases heξ with heωK | heηK
        · exact (heK heωK.2).elim
        · exact heηK.1
      · intro heη
        exact Or.inr ⟨heη, heK⟩
  exact (hA hξη).mp hξA

theorem Forces.inter {ι : Type*} [DecidableEq ι] {K L : Finset ι} {ω : Set ι}
    {A B : Set (Set ι)} (hK : Forces K ω A) (hL : Forces L ω B) :
    Forces (K ∪ L) ω (A ∩ B) := by
  intro η hagree
  exact ⟨hK η (fun e he ↦ hagree e (Finset.mem_union_left L he)),
    hL η (fun e he ↦ hagree e (Finset.mem_union_right K he))⟩

/-- If `A` is increasing and `K` forces `A` at `ω`, then `K` also forces `A` at any larger
configuration. -/
theorem Forces.mono_config_of_increasing {ι : Type*} {K : Finset ι} {ω η : Set ι}
    {A : Set (Set ι)} (hK : Forces K ω A) (hA : IsIncreasingEvent A) (hωη : ω ⊆ η) :
    Forces K η A := by
  intro ξ hξ
  let ζ : Set ι := (ξ \ (K : Set ι)) ∪ (ω ∩ (K : Set ι))
  have hζagree : ∀ e ∈ K, (e ∈ ζ ↔ e ∈ ω) := by
    intro e heK
    constructor
    · intro heζ
      rcases heζ with heξ | heωK
      · exact (heξ.2 heK).elim
      · exact heωK.1
    · intro heω
      exact Or.inr ⟨heω, heK⟩
  have hζA : ζ ∈ A := hK ζ hζagree
  have hζξ : ζ ⊆ ξ := by
    intro e heζ
    rcases heζ with heξ | heωK
    · exact heξ.1
    · exact (hξ e heωK.2).mpr (hωη heωK.1)
  exact hA hζξ hζA

/-- BK disjoint occurrence: `A ∘ B` occurs at `ω` if disjoint finite coordinate sets force
`A` and `B` at `ω`. -/
def DisjointOccurrence {ι : Type*} (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧ Forces K ω A ∧ Forces L ω B}

theorem mem_disjointOccurrence_iff {ι : Type*} {A B : Set (Set ι)} {ω : Set ι} :
    ω ∈ DisjointOccurrence A B ↔
      ∃ K L : Finset ι, Disjoint K L ∧ Forces K ω A ∧ Forces L ω B :=
  Iff.rfl

theorem disjointOccurrence_subset_inter {ι : Type*} {A B : Set (Set ι)} :
    DisjointOccurrence A B ⊆ A ∩ B := by
  intro ω hω
  rcases hω with ⟨K, L, _hdis, hK, hL⟩
  exact ⟨hK.mem, hL.mem⟩

theorem disjointOccurrence_mono {ι : Type*} {A B A' B' : Set (Set ι)}
    (hAA' : A ⊆ A') (hBB' : B ⊆ B') :
    DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  intro ω hω
  rcases hω with ⟨K, L, hdis, hK, hL⟩
  exact ⟨K, L, hdis, hK.mono_event hAA', hL.mono_event hBB'⟩

theorem disjointOccurrence_comm {ι : Type*} (A B : Set (Set ι)) :
    DisjointOccurrence A B = DisjointOccurrence B A := by
  ext ω
  constructor
  · rintro ⟨K, L, hdis, hK, hL⟩
    exact ⟨L, K, hdis.symm, hL, hK⟩
  · rintro ⟨K, L, hdis, hK, hL⟩
    exact ⟨L, K, hdis.symm, hL, hK⟩

theorem inter_subset_disjointOccurrence_of_dependsOn_disjoint {ι : Type*}
    {E F : Finset ι} {A B : Set (Set ι)}
    (hdis : Disjoint E F) (hA : DependsOn E A) (hB : DependsOn F B) :
    A ∩ B ⊆ DisjointOccurrence A B := by
  intro ω hω
  exact ⟨E, F, hdis, hA.forces hω.1, hB.forces hω.2⟩

theorem DependsOn.disjointOccurrence {ι : Type*} [DecidableEq ι]
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    DependsOn (E ∪ F) (DisjointOccurrence A B) := by
  intro ω η hcoord
  constructor
  · rintro ⟨K, L, hdis, hK, hL⟩
    let K' : Finset ι := K ∩ E
    let L' : Finset ι := L ∩ F
    have hK'ω : Forces K' ω A := by
      simpa [K'] using hK.restrict_of_dependsOn hA
    have hL'ω : Forces L' ω B := by
      simpa [L'] using hL.restrict_of_dependsOn hB
    have hK'η : Forces K' η A := hK'ω.congr_config (by
      intro e he
      have heE : e ∈ E := (Finset.mem_inter.mp he).2
      exact (hcoord e (Finset.mem_union_left F heE)).symm)
    have hL'η : Forces L' η B := hL'ω.congr_config (by
      intro e he
      have heF : e ∈ F := (Finset.mem_inter.mp he).2
      exact (hcoord e (Finset.mem_union_right E heF)).symm)
    have hdis' : Disjoint K' L' := by
      exact hdis.mono (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    exact ⟨K', L', hdis', hK'η, hL'η⟩
  · rintro ⟨K, L, hdis, hK, hL⟩
    let K' : Finset ι := K ∩ E
    let L' : Finset ι := L ∩ F
    have hK'η : Forces K' η A := by
      simpa [K'] using hK.restrict_of_dependsOn hA
    have hL'η : Forces L' η B := by
      simpa [L'] using hL.restrict_of_dependsOn hB
    have hK'ω : Forces K' ω A := hK'η.congr_config (by
      intro e he
      have heE : e ∈ E := (Finset.mem_inter.mp he).2
      exact hcoord e (Finset.mem_union_left F heE))
    have hL'ω : Forces L' ω B := hL'η.congr_config (by
      intro e he
      have heF : e ∈ F := (Finset.mem_inter.mp he).2
      exact hcoord e (Finset.mem_union_right E heF))
    have hdis' : Disjoint K' L' := by
      exact hdis.mono (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    exact ⟨K', L', hdis', hK'ω, hL'ω⟩

theorem measurableSet_disjointOccurrence_of_dependsOn {ι : Type*} [DecidableEq ι]
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    MeasurableSet (DisjointOccurrence A B) :=
  (hA.disjointOccurrence hB).measurableSet

theorem IsIncreasingEvent.disjointOccurrence {ι : Type*} {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (DisjointOccurrence A B) := by
  intro ω η hωη hω
  rcases hω with ⟨K, L, hdis, hK, hL⟩
  exact ⟨K, L, hdis, hK.mono_config_of_increasing hA hωη,
    hL.mono_config_of_increasing hB hωη⟩

/-- Pairwise disjoint finite forcing witnesses indexed by a finite family. -/
def PairwiseDisjointWitnesses {ι κ : Type*} (J : Finset κ) (K : κ → Finset ι) :
    Prop :=
  ∀ ⦃i j : κ⦄, i ∈ J → j ∈ J → i ≠ j → Disjoint (K i) (K j)

theorem pairwiseDisjointWitnesses_empty {ι κ : Type*} (K : κ → Finset ι) :
    PairwiseDisjointWitnesses (∅ : Finset κ) K := by
  intro i _j hi _hj _hij
  simp at hi

theorem PairwiseDisjointWitnesses.mono {ι κ : Type*} {J J' : Finset κ}
    {K : κ → Finset ι} (hK : PairwiseDisjointWitnesses J' K) (hJJ' : J ⊆ J') :
    PairwiseDisjointWitnesses J K := by
  intro i j hi hj hij
  exact hK (hJJ' hi) (hJJ' hj) hij

/-- Finite-family disjoint occurrence: every event has a finite forcing witness, and the
witnesses are pairwise disjoint. This is the deterministic event underlying Grimmett's repeated
BK inequality (2.14). -/
def FiniteDisjointOccurrence {ι κ : Type*}
    (J : Finset κ) (A : κ → Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ K : κ → Finset ι,
    (∀ i, i ∈ J → Forces (K i) ω (A i)) ∧ PairwiseDisjointWitnesses J K}

theorem mem_finiteDisjointOccurrence_iff {ι κ : Type*} {J : Finset κ}
    {A : κ → Set (Set ι)} {ω : Set ι} :
    ω ∈ FiniteDisjointOccurrence J A ↔
      ∃ K : κ → Finset ι,
        (∀ i, i ∈ J → Forces (K i) ω (A i)) ∧ PairwiseDisjointWitnesses J K :=
  Iff.rfl

@[simp]
theorem finiteDisjointOccurrence_empty {ι κ : Type*} (A : κ → Set (Set ι)) :
    FiniteDisjointOccurrence (∅ : Finset κ) A = Set.univ := by
  ext ω
  constructor
  · intro _hω
    exact Set.mem_univ ω
  · intro _hω
    refine ⟨fun _ ↦ ∅, ?_, pairwiseDisjointWitnesses_empty _⟩
    intro i hi
    simp at hi

theorem finiteDisjointOccurrence_subset_finiteEventInter {ι κ : Type*}
    {J : Finset κ} {A : κ → Set (Set ι)} :
    FiniteDisjointOccurrence J A ⊆ finiteEventInter J A := by
  intro ω hω i hi
  rcases hω with ⟨K, hK, _hpair⟩
  exact (hK i hi).mem

theorem finiteDisjointOccurrence_mono {ι κ : Type*} {J : Finset κ}
    {A B : κ → Set (Set ι)} (hAB : ∀ i ∈ J, A i ⊆ B i) :
    FiniteDisjointOccurrence J A ⊆ FiniteDisjointOccurrence J B := by
  intro ω hω
  rcases hω with ⟨K, hK, hpair⟩
  exact ⟨K, (fun i hi ↦ (hK i hi).mono_event (hAB i hi)), hpair⟩

theorem isIncreasingEvent_finiteDisjointOccurrence {ι κ : Type*} {J : Finset κ}
    {A : κ → Set (Set ι)} (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    IsIncreasingEvent (FiniteDisjointOccurrence J A) := by
  intro ω η hωη hω
  rcases hω with ⟨K, hK, hpair⟩
  refine ⟨K, ?_, hpair⟩
  intro i hi
  exact (hK i hi).mono_config_of_increasing (hA i hi) hωη

/-- Removing one event from a finite-family disjoint occurrence yields a binary disjoint
occurrence between that event and the disjoint occurrence of the remaining family. This is the
deterministic induction step needed for repeated BK. -/
theorem finiteDisjointOccurrence_insert_subset_disjointOccurrence {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] {J : Finset κ} {a : κ} (ha : a ∉ J)
    {A : κ → Set (Set ι)} :
    FiniteDisjointOccurrence (insert a J) A ⊆
      DisjointOccurrence (A a) (FiniteDisjointOccurrence J A) := by
  intro ω hω
  rcases hω with ⟨K, hK, hpair⟩
  let L : Finset ι := J.biUnion K
  have hpairJ : PairwiseDisjointWitnesses J K := hpair.mono (by
    intro i hi
    exact Finset.mem_insert.mpr (Or.inr hi))
  have hdis : Disjoint (K a) L := by
    change Disjoint (K a) (J.biUnion K)
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hpair (Finset.mem_insert_self a J) (Finset.mem_insert.mpr (Or.inr hi)) (by
      intro hai
      exact ha (by simpa [hai] using hi))
  have hLforces : Forces L ω (FiniteDisjointOccurrence J A) := by
    intro η hagree
    refine ⟨K, ?_, hpairJ⟩
    intro i hi
    exact (hK i (Finset.mem_insert.mpr (Or.inr hi))).congr_config (by
      intro e he
      exact hagree e (by
        change e ∈ J.biUnion K
        exact Finset.mem_biUnion.mpr ⟨i, hi, he⟩))
  exact ⟨K a, L, hdis, hK a (Finset.mem_insert_self a J), hLforces⟩

theorem dependsOn_finiteDisjointOccurrence {ι κ : Type*} [DecidableEq ι]
    {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) := by
  intro ω η hcoord
  constructor
  · rintro ⟨K, hK, hpair⟩
    let K' : κ → Finset ι := fun i ↦ K i ∩ E i
    have hforcesω : ∀ i, i ∈ J → Forces (K' i) ω (A i) := by
      intro i hi
      simpa [K'] using (hK i hi).restrict_of_dependsOn (hA i hi)
    have hforcesη : ∀ i, i ∈ J → Forces (K' i) η (A i) := by
      intro i hi
      exact (hforcesω i hi).congr_config (by
        intro e he
        have heE : e ∈ E i := (Finset.mem_inter.mp he).2
        exact (hcoord e (Finset.mem_biUnion.mpr ⟨i, hi, heE⟩)).symm)
    have hpair' : PairwiseDisjointWitnesses J K' := by
      intro i j hi hj hij
      exact (hpair hi hj hij).mono
        (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    exact ⟨K', hforcesη, hpair'⟩
  · rintro ⟨K, hK, hpair⟩
    let K' : κ → Finset ι := fun i ↦ K i ∩ E i
    have hforcesη : ∀ i, i ∈ J → Forces (K' i) η (A i) := by
      intro i hi
      simpa [K'] using (hK i hi).restrict_of_dependsOn (hA i hi)
    have hforcesω : ∀ i, i ∈ J → Forces (K' i) ω (A i) := by
      intro i hi
      exact (hforcesη i hi).congr_config (by
        intro e he
        have heE : e ∈ E i := (Finset.mem_inter.mp he).2
        exact hcoord e (Finset.mem_biUnion.mpr ⟨i, hi, heE⟩))
    have hpair' : PairwiseDisjointWitnesses J K' := by
      intro i j hi hj hij
      exact (hpair hi hj hij).mono
        (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    exact ⟨K', hforcesω, hpair'⟩

theorem measurableSet_finiteDisjointOccurrence_of_dependsOn {ι κ : Type*}
    [DecidableEq ι] {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    MeasurableSet (FiniteDisjointOccurrence J A) :=
  (dependsOn_finiteDisjointOccurrence hA).measurableSet

end Percolation
