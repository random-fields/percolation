import Percolation.Bernoulli.Increasing

/-!
# BK/Reimer disjoint-occurrence infrastructure

This file starts the deterministic event-level API for Grimmett's BK inequality section.  It
defines finite witness sets that force events and the disjoint-occurrence event `A ∘ B`.  The
deep Reimer probability inequality is intentionally not asserted here; BK consequences are proved
only conditionally from an explicit `ReimerBoundOn` hypothesis.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Finset unitInterval
open scoped Classical

universe u v

/-- The Bernoulli parameter `1/2`, packaged as a point of the unit interval. -/
noncomputable def unitIntervalHalf : I :=
  ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

@[simp]
theorem coe_unitIntervalHalf :
    (unitIntervalHalf : ℝ) = 1 / 2 :=
  rfl

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

theorem Forces.restrict_of_dependsOn {ι : Type*} {K E : Finset ι} {ω : Set ι}
    {A : Set (Set ι)}
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

theorem Forces.inter {ι : Type*} {K L : Finset ι} {ω : Set ι}
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

/-- BK open disjoint occurrence for increasing events: the forcing witnesses are finite sets of
coordinates that are actually open in the ambient configuration. For increasing events this is
equivalent to `DisjointOccurrence`, but this definition matches the textbook "disjoint open edge
sets" wording. -/
def OpenDisjointOccurrence {ι : Type*} (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧ (K : Set ι) ⊆ ω ∧ (L : Set ι) ⊆ ω ∧
    Forces K ω A ∧ Forces L ω B}

theorem mem_disjointOccurrence_iff {ι : Type*} {A B : Set (Set ι)} {ω : Set ι} :
    ω ∈ DisjointOccurrence A B ↔
      ∃ K L : Finset ι, Disjoint K L ∧ Forces K ω A ∧ Forces L ω B :=
  Iff.rfl

theorem mem_openDisjointOccurrence_iff {ι : Type*} {A B : Set (Set ι)} {ω : Set ι} :
    ω ∈ OpenDisjointOccurrence A B ↔
      ∃ K L : Finset ι, Disjoint K L ∧ (K : Set ι) ⊆ ω ∧ (L : Set ι) ⊆ ω ∧
        Forces K ω A ∧ Forces L ω B :=
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

theorem openDisjointOccurrence_subset_disjointOccurrence {ι : Type*}
    {A B : Set (Set ι)} :
    OpenDisjointOccurrence A B ⊆ DisjointOccurrence A B := by
  intro ω hω
  rcases hω with ⟨K, L, hdis, _hKopen, _hLopen, hK, hL⟩
  exact ⟨K, L, hdis, hK, hL⟩

theorem Forces.restrict_to_open_of_increasing {ι : Type*} {K : Finset ι} {ω : Set ι}
    {A : Set (Set ι)} (hK : Forces K ω A) (hA : IsIncreasingEvent A) :
    Forces (K.filter fun e ↦ e ∈ ω) ω A := by
  classical
  intro η hagree
  let ζ : Set ι := (η \ (K : Set ι)) ∪ (ω ∩ (K : Set ι))
  have hζagree : ∀ e ∈ K, (e ∈ ζ ↔ e ∈ ω) := by
    intro e heK
    constructor
    · intro heζ
      rcases heζ with heηK | heωK
      · exact (heηK.2 heK).elim
      · exact heωK.1
    · intro heω
      exact Or.inr ⟨heω, heK⟩
  have hζA : ζ ∈ A := hK ζ hζagree
  have hζη : ζ ⊆ η := by
    intro e heζ
    rcases heζ with heηK | heωK
    · exact heηK.1
    · have heFilter : e ∈ K.filter fun e ↦ e ∈ ω :=
        Finset.mem_filter.mpr ⟨heωK.2, heωK.1⟩
      exact (hagree e heFilter).mpr heωK.1
  exact hA hζη hζA

theorem disjointOccurrence_subset_openDisjointOccurrence_of_increasing {ι : Type*}
    {A B : Set (Set ι)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    DisjointOccurrence A B ⊆ OpenDisjointOccurrence A B := by
  classical
  intro ω hω
  rcases hω with ⟨K, L, hdis, hK, hL⟩
  let K' : Finset ι := K.filter fun e ↦ e ∈ ω
  let L' : Finset ι := L.filter fun e ↦ e ∈ ω
  have hdis' : Disjoint K' L' := by
    exact hdis.mono
      (by intro e he; exact (Finset.mem_filter.mp he).1)
      (by intro e he; exact (Finset.mem_filter.mp he).1)
  have hKopen : (K' : Set ι) ⊆ ω := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hLopen : (L' : Set ι) ⊆ ω := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  exact ⟨K', L', hdis', hKopen, hLopen,
    by simpa [K'] using hK.restrict_to_open_of_increasing hA,
    by simpa [L'] using hL.restrict_to_open_of_increasing hB⟩

theorem openDisjointOccurrence_eq_disjointOccurrence_of_increasing {ι : Type*}
    {A B : Set (Set ι)} (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    OpenDisjointOccurrence A B = DisjointOccurrence A B :=
  Set.Subset.antisymm openDisjointOccurrence_subset_disjointOccurrence
    (disjointOccurrence_subset_openDisjointOccurrence_of_increasing hA hB)

/-- Reimer's finite box occurrence on a support `E`: there is a witness set `K ⊆ E`
forcing `A`, while the complementary coordinates `E \ K` force `B`. This is Grimmett's
finite-product `A □ B` operation, parametrized by the finite set of relevant coordinates. -/
def ReimerOccurrenceOn {ι : Type*} (E : Finset ι) (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ K : Finset ι, K ⊆ E ∧ Forces K ω A ∧ Forces (E \ K) ω B}

theorem mem_reimerOccurrenceOn_iff {ι : Type*} {E : Finset ι} {A B : Set (Set ι)}
    {ω : Set ι} :
    ω ∈ ReimerOccurrenceOn E A B ↔
      ∃ K : Finset ι, K ⊆ E ∧ Forces K ω A ∧ Forces (E \ K) ω B :=
  Iff.rfl

theorem reimerOccurrenceOn_subset_disjointOccurrence {ι : Type*}
    {E : Finset ι} {A B : Set (Set ι)} :
    ReimerOccurrenceOn E A B ⊆ DisjointOccurrence A B := by
  intro ω hω
  rcases hω with ⟨K, _hKE, hK, hEK⟩
  refine ⟨K, E \ K, ?_, hK, hEK⟩
  rw [Finset.disjoint_left]
  intro e heK heEK
  exact (Finset.mem_sdiff.mp heEK).2 heK

theorem reimerOccurrenceOn_mono_support {ι : Type*} {E G : Finset ι}
    {A B : Set (Set ι)} (hEG : E ⊆ G) :
    ReimerOccurrenceOn E A B ⊆ ReimerOccurrenceOn G A B := by
  intro ω hω
  rcases hω with ⟨K, hKE, hK, hEK⟩
  refine ⟨K, fun e he ↦ hEG (hKE he), hK, hEK.mono_support ?_⟩
  intro e he
  rw [Finset.mem_sdiff] at he ⊢
  exact ⟨hEG he.1, he.2⟩

theorem disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn {ι : Type*}
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    DisjointOccurrence A B ⊆ ReimerOccurrenceOn (E ∪ F) A B := by
  intro ω hω
  rcases hω with ⟨K, L, hdis, hK, hL⟩
  let K' : Finset ι := K ∩ E
  let L' : Finset ι := L ∩ F
  have hK' : Forces K' ω A := by
    simpa [K'] using hK.restrict_of_dependsOn hA
  have hL' : Forces L' ω B := by
    simpa [L'] using hL.restrict_of_dependsOn hB
  refine ⟨K', ?_, hK', hL'.mono_support ?_⟩
  · intro e he
    exact Finset.mem_union_left F (Finset.mem_inter.mp he).2
  · intro e he
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_union_right E (Finset.mem_inter.mp he).2
    · intro heK'
      exact (Finset.disjoint_left.mp hdis) (Finset.mem_inter.mp heK').1
        (Finset.mem_inter.mp he).1

theorem disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn_of_subset {ι : Type*}
    {E F G : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G) :
    DisjointOccurrence A B ⊆ ReimerOccurrenceOn G A B := by
  refine Set.Subset.trans (disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn hA hB) ?_
  refine reimerOccurrenceOn_mono_support ?_
  intro e he
  rcases Finset.mem_union.mp he with heE | heF
  · exact hEG heE
  · exact hFG heF

theorem disjointOccurrence_eq_reimerOccurrenceOn_of_dependsOn {ι : Type*}
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    DisjointOccurrence A B = ReimerOccurrenceOn (E ∪ F) A B :=
  Set.Subset.antisymm (disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn hA hB)
    reimerOccurrenceOn_subset_disjointOccurrence

theorem inter_subset_disjointOccurrence_of_dependsOn_disjoint {ι : Type*}
    {E F : Finset ι} {A B : Set (Set ι)}
    (hdis : Disjoint E F) (hA : DependsOn E A) (hB : DependsOn F B) :
    A ∩ B ⊆ DisjointOccurrence A B := by
  intro ω hω
  exact ⟨E, F, hdis, hA.forces hω.1, hB.forces hω.2⟩

theorem DependsOn.disjointOccurrence {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
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

theorem measurableSet_disjointOccurrence_of_dependsOn {ι : Type*} {E F : Finset ι}
    {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    MeasurableSet (DisjointOccurrence A B) :=
  (hA.disjointOccurrence hB).measurableSet

theorem dependsOn_reimerOccurrenceOn {ι : Type*} {E : Finset ι} {A B : Set (Set ι)} :
    DependsOn E (ReimerOccurrenceOn E A B) := by
  intro ω η hcoord
  constructor
  · rintro ⟨K, hKE, hK, hEK⟩
    refine ⟨K, hKE, ?_, ?_⟩
    · exact hK.congr_config fun e he ↦ (hcoord e (hKE he)).symm
    · exact hEK.congr_config fun e he ↦ (hcoord e (Finset.mem_sdiff.mp he).1).symm
  · rintro ⟨K, hKE, hK, hEK⟩
    refine ⟨K, hKE, ?_, ?_⟩
    · exact hK.congr_config fun e he ↦ hcoord e (hKE he)
    · exact hEK.congr_config fun e he ↦ hcoord e (Finset.mem_sdiff.mp he).1

theorem measurableSet_reimerOccurrenceOn_of_dependsOn {ι : Type*}
    {E : Finset ι} {A B : Set (Set ι)} :
    MeasurableSet (ReimerOccurrenceOn E A B) :=
  (dependsOn_reimerOccurrenceOn (E := E) (A := A) (B := B)).measurableSet

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

/-- Finite-family open disjoint occurrence: every event has a finite forcing witness, the
witnesses are pairwise disjoint, and all witness coordinates are open in the ambient
configuration. For increasing events this agrees with `FiniteDisjointOccurrence` and matches the
open-witness reading of Grimmett's repeated BK inequality (2.14). -/
def FiniteOpenDisjointOccurrence {ι κ : Type*}
    (J : Finset κ) (A : κ → Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ K : κ → Finset ι,
    (∀ i, i ∈ J → (K i : Set ι) ⊆ ω ∧ Forces (K i) ω (A i)) ∧
      PairwiseDisjointWitnesses J K}

theorem mem_finiteDisjointOccurrence_iff {ι κ : Type*} {J : Finset κ}
    {A : κ → Set (Set ι)} {ω : Set ι} :
    ω ∈ FiniteDisjointOccurrence J A ↔
      ∃ K : κ → Finset ι,
        (∀ i, i ∈ J → Forces (K i) ω (A i)) ∧ PairwiseDisjointWitnesses J K :=
  Iff.rfl

theorem mem_finiteOpenDisjointOccurrence_iff {ι κ : Type*} {J : Finset κ}
    {A : κ → Set (Set ι)} {ω : Set ι} :
    ω ∈ FiniteOpenDisjointOccurrence J A ↔
      ∃ K : κ → Finset ι,
        (∀ i, i ∈ J → (K i : Set ι) ⊆ ω ∧ Forces (K i) ω (A i)) ∧
          PairwiseDisjointWitnesses J K :=
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

@[simp]
theorem finiteOpenDisjointOccurrence_empty {ι κ : Type*} (A : κ → Set (Set ι)) :
    FiniteOpenDisjointOccurrence (∅ : Finset κ) A = Set.univ := by
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

theorem finiteOpenDisjointOccurrence_subset_finiteDisjointOccurrence {ι κ : Type*}
    {J : Finset κ} {A : κ → Set (Set ι)} :
    FiniteOpenDisjointOccurrence J A ⊆ FiniteDisjointOccurrence J A := by
  intro ω hω
  rcases hω with ⟨K, hK, hpair⟩
  exact ⟨K, (fun i hi ↦ (hK i hi).2), hpair⟩

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

theorem finiteDisjointOccurrence_subset_finiteOpenDisjointOccurrence_of_increasing
    {ι κ : Type*} {J : Finset κ} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    FiniteDisjointOccurrence J A ⊆ FiniteOpenDisjointOccurrence J A := by
  classical
  intro ω hω
  rcases hω with ⟨K, hK, hpair⟩
  let K' : κ → Finset ι := fun i ↦ (K i).filter fun e ↦ e ∈ ω
  have hforces :
      ∀ i, i ∈ J → (K' i : Set ι) ⊆ ω ∧ Forces (K' i) ω (A i) := by
    intro i hi
    constructor
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · simpa [K'] using (hK i hi).restrict_to_open_of_increasing (hA i hi)
  have hpair' : PairwiseDisjointWitnesses J K' := by
    intro i j hi hj hij
    exact (hpair hi hj hij).mono
      (by intro e he; exact (Finset.mem_filter.mp he).1)
      (by intro e he; exact (Finset.mem_filter.mp he).1)
  exact ⟨K', hforces, hpair'⟩

theorem finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing
    {ι κ : Type*} {J : Finset κ} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    FiniteOpenDisjointOccurrence J A = FiniteDisjointOccurrence J A :=
  Set.Subset.antisymm finiteOpenDisjointOccurrence_subset_finiteDisjointOccurrence
    (finiteDisjointOccurrence_subset_finiteOpenDisjointOccurrence_of_increasing hA)

/-- Removing one event from a finite-family disjoint occurrence yields a binary disjoint
occurrence between that event and the disjoint occurrence of the remaining family. This is the
deterministic induction step needed for repeated BK. -/
theorem finiteDisjointOccurrence_insert_subset_disjointOccurrence {ι κ : Type*}
    {J : Finset κ} {a : κ} (ha : a ∉ J) {A : κ → Set (Set ι)} :
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

theorem dependsOn_finiteDisjointOccurrence {ι κ : Type*} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
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
    {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    MeasurableSet (FiniteDisjointOccurrence J A) :=
  (dependsOn_finiteDisjointOccurrence hA).measurableSet

/-- Finite-trace forcing: inside the cube of traces contained in `E`, the trace coordinates in
`K` force membership in the finite trace event `T`. -/
def TraceForces {ι : Type*} (E K s : Finset ι) (T : Set (Finset ι)) : Prop :=
  ∀ t : Finset ι, t ⊆ E → (∀ e ∈ K, (e ∈ t ↔ e ∈ s)) → t ∈ T

/-- Reimer's box occurrence on the finite trace cube over `E`. -/
def ReimerTraceOccurrence {ι : Type*} (E : Finset ι)
    (T U : Set (Finset ι)) : Set (Finset ι) :=
  {s | s ⊆ E ∧ ∃ K : Finset ι, K ⊆ E ∧ TraceForces E K s T ∧
    TraceForces E (E \ K) s U}

/-- The bitwise-complement image of a trace event inside the finite cube over `E`. -/
def TraceComplement {ι : Type*} (E : Finset ι) (U : Set (Finset ι)) : Set (Finset ι) :=
  {s | E \ s ∈ U}

theorem mem_traceComplement_iff {ι : Type*} {E s : Finset ι} {U : Set (Finset ι)} :
    s ∈ TraceComplement E U ↔ E \ s ∈ U :=
  Iff.rfl

theorem IsIncreasingTrace.traceComplement {ι : Type*} {E : Finset ι}
    {U : Set (Finset ι)} (hU : IsIncreasingTrace E U) :
    IsDecreasingTrace E (TraceComplement E U) := by
  intro s t hst _htE ht
  exact hU (by
    intro e he
    rw [Finset.mem_sdiff] at he ⊢
    exact ⟨he.1, fun hes ↦ he.2 (hst hes)⟩) (by
      intro e he
      exact (Finset.mem_sdiff.mp he).1) ht

/-- Reimer's standard uniform finite-cube complement form: under the uniform measure on the
finite cube over `E`, `T □ U` is bounded by `T ∩ \bar U`. -/
def FiniteTraceUniformReimerBound {ι : Type*} (E : Finset ι) : Prop :=
  ∀ T U : Set (Finset ι),
    finiteBernoulliEventProbability E (1 / 2)
        (ReimerTraceOccurrence E T U) ≤
      finiteBernoulliEventProbability E (1 / 2) (T ∩ TraceComplement E U)

/-- The finite family of traces inside `E` that lie in the trace event `T`. -/
noncomputable def finiteTraceEventFamily {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) : Finset (Finset ι) := by
  classical
  exact E.powerset.filter fun s ↦ s ∈ T

theorem mem_finiteTraceEventFamily_iff {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) (s : Finset ι) :
    s ∈ finiteTraceEventFamily E T ↔ s ⊆ E ∧ s ∈ T := by
  classical
  simp [finiteTraceEventFamily]

/-- Heterogeneous Bernoulli product weight of one finite trace inside support `E`. -/
noncomputable def finiteBernoulliHeteroTraceWeight {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (s : Finset ι) : ℝ := by
  classical
  exact E.prod (fun e ↦ if e ∈ s then q e else 1 - q e)

/-- The traces in an event whose number of open coordinates is exactly `k`. -/
noncomputable def finiteTraceLevelFamily {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) (k : ℕ) : Finset (Finset ι) := by
  classical
  exact (finiteTraceEventFamily E T).filter fun s ↦ s.card = k

/-- The number of traces in an event with exactly `k` open coordinates. -/
noncomputable def finiteTraceLevelCount {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) (k : ℕ) : ℕ :=
  (finiteTraceLevelFamily E T k).card

theorem mem_finiteTraceLevelFamily_iff {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) (k : ℕ) (s : Finset ι) :
    s ∈ finiteTraceLevelFamily E T k ↔ s ⊆ E ∧ s ∈ T ∧ s.card = k := by
  classical
  simp [finiteTraceLevelFamily, mem_finiteTraceEventFamily_iff]
  tauto

/-- Finite Bernoulli event probability as a weighted sum over the finite trace family. -/
theorem finiteBernoulliEventProbability_eq_sum_traceFamily {ι : Type*}
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability E p T =
      (finiteTraceEventFamily E T).sum
        (fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card)) := by
  classical
  unfold finiteBernoulliEventProbability finiteBernoulliExpectation finiteTraceEventFamily
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  by_cases hsT : s ∈ T <;> simp [Set.indicator, hsT]

/-- Heterogeneous finite Bernoulli event probability as a weighted sum over the finite trace
family. -/
theorem finiteBernoulliHeteroEventProbability_eq_sum_traceFamily {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability E q T =
      (finiteTraceEventFamily E T).sum (finiteBernoulliHeteroTraceWeight E q) := by
  classical
  unfold finiteBernoulliHeteroEventProbability finiteBernoulliHeteroExpectation
    finiteTraceEventFamily finiteBernoulliHeteroTraceWeight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  by_cases hsT : s ∈ T <;> simp [Set.indicator, hsT]

/-- Heterogeneous finite Bernoulli event probability only depends on traces inside the finite
support. -/
theorem finiteBernoulliHeteroEventProbability_congr {ι : Type*}
    {E : Finset ι} {q : ι → ℝ} {T U : Set (Finset ι)}
    (hTU : ∀ ⦃s : Finset ι⦄, s ⊆ E → (s ∈ T ↔ s ∈ U)) :
    finiteBernoulliHeteroEventProbability E q T =
      finiteBernoulliHeteroEventProbability E q U := by
  unfold finiteBernoulliHeteroEventProbability
  apply finiteBernoulliHeteroExpectation_congr
  · intro _e _he
    rfl
  · intro s hsE
    by_cases hT : s ∈ T
    · have hU : s ∈ U := (hTU hsE).1 hT
      simp [hT, hU]
    · have hU : s ∉ U := by
        intro h
        exact hT ((hTU hsE).2 h)
      simp [hT, hU]

@[simp]
theorem finiteBernoulliHeteroEventProbability_univ {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) :
    finiteBernoulliHeteroEventProbability E q (Set.univ : Set (Finset ι)) = 1 := by
  unfold finiteBernoulliHeteroEventProbability
  induction E using Finset.induction with
  | empty =>
      simp [finiteBernoulliHeteroExpectation]
  | insert a E ha ih =>
      rw [finiteBernoulliHeteroExpectation_insert ha]
      calc
        finiteBernoulliHeteroExpectation E q
            (fun s ↦ (1 - q a) * (Set.univ : Set (Finset ι)).indicator
                (fun _ ↦ (1 : ℝ)) s +
              q a * (Set.univ : Set (Finset ι)).indicator
                (fun _ ↦ (1 : ℝ)) (insert a s)) =
            finiteBernoulliHeteroExpectation E q (fun _ ↦ (1 : ℝ)) := by
          apply finiteBernoulliHeteroExpectation_congr
          · intro _e _he
            rfl
          · intro s _hsE
            simp
        _ = 1 := by
          simpa [finiteBernoulliHeteroEventProbability] using ih

/-- Finite Bernoulli event probability grouped by the number of open coordinates. This is the
Bernstein-basis form used for weighted finite-cube Reimer checks. -/
theorem finiteBernoulliEventProbability_eq_sum_levelCount {ι : Type*}
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability E p T =
      ∑ k ∈ Finset.range (E.card + 1),
        (finiteTraceLevelCount E T k : ℝ) * p ^ k * (1 - p) ^ (E.card - k) := by
  classical
  rw [finiteBernoulliEventProbability_eq_sum_traceFamily]
  have hmap : ∀ s ∈ finiteTraceEventFamily E T, s.card ∈ Finset.range (E.card + 1) := by
    intro s hs
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.card_le_card ((mem_finiteTraceEventFamily_iff E T s).mp hs).1
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card))]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hconst :
      ∀ s ∈ finiteTraceLevelFamily E T k,
        p ^ s.card * (1 - p) ^ (E.card - s.card) =
          p ^ k * (1 - p) ^ (E.card - k) := by
    intro s hs
    have hcard := (mem_finiteTraceLevelFamily_iff E T k s).mp hs |>.2.2
    rw [hcard]
  calc
    (∑ s ∈ finiteTraceEventFamily E T with s.card = k,
        p ^ s.card * (1 - p) ^ (E.card - s.card)) =
        ∑ s ∈ finiteTraceLevelFamily E T k,
          p ^ s.card * (1 - p) ^ (E.card - s.card) := by
      rfl
    _ = ∑ _s ∈ finiteTraceLevelFamily E T k,
          p ^ k * (1 - p) ^ (E.card - k) := by
      exact Finset.sum_congr rfl hconst
    _ = (finiteTraceLevelCount E T k : ℝ) * p ^ k * (1 - p) ^ (E.card - k) := by
      simp [finiteTraceLevelCount, mul_assoc]

/-- Pull a finite trace event on `ι` back to the canonical cube whose coordinates are the
members of the support `E`. -/
def traceEventOnSupport {ι : Type*} (E : Finset ι)
    (T : Set (Finset ι)) : Set (Finset E) :=
  {t | t.map (Function.Embedding.subtype fun x ↦ x ∈ E) ∈ T}

theorem mem_map_subtype_iff {ι : Type*} {E : Finset ι} (s : Finset E)
    {x : ι} (hx : x ∈ E) :
    x ∈ s.map (Function.Embedding.subtype fun x ↦ x ∈ E) ↔
      (⟨x, hx⟩ : E) ∈ s := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    cases y with
    | mk y hyE =>
      dsimp at hyx
      subst x
      simpa using hy
  · intro hxmem
    exact ⟨⟨x, hx⟩, hxmem, rfl⟩

theorem map_subtype_subtype {ι : Type*} {E : Finset ι} (s : Finset E) :
    (s.map (Function.Embedding.subtype fun x ↦ x ∈ E)).subtype (fun x ↦ x ∈ E) =
      s := by
  ext x
  simp

theorem traceForces_toSupport {ι : Type*} (E K s : Finset ι)
    (T : Set (Finset ι)) (hK : K ⊆ E) :
    TraceForces E K s T →
      TraceForces (Finset.univ : Finset E) (K.subtype fun x ↦ x ∈ E)
        (s.subtype fun x ↦ x ∈ E) (traceEventOnSupport E T) := by
  intro h t _ht hagree
  exact h (t.map (Function.Embedding.subtype fun x ↦ x ∈ E))
    (by
      intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.2)
    (by
      intro e heK
      have heE : e ∈ E := hK heK
      have hsub : (⟨e, heE⟩ : E) ∈ K.subtype (fun x ↦ x ∈ E) := by
        simpa [Finset.mem_subtype] using heK
      specialize hagree (⟨e, heE⟩ : E) hsub
      rw [mem_map_subtype_iff t heE]
      simpa [Finset.mem_subtype] using hagree)

theorem traceForces_ofSupport {ι : Type*} (E : Finset ι) (K s : Finset E)
    (T : Set (Finset ι)) :
    TraceForces (Finset.univ : Finset E) K s (traceEventOnSupport E T) →
      TraceForces E (K.map (Function.Embedding.subtype fun x ↦ x ∈ E))
        (s.map (Function.Embedding.subtype fun x ↦ x ∈ E)) T := by
  intro h t htE hagree
  have ht : t.subtype (fun x ↦ x ∈ E) ∈ traceEventOnSupport E T :=
    h (t.subtype fun x ↦ x ∈ E) (by intro x hx; simp) (by
      intro x hxK
      have hxmap : (x : ι) ∈ K.map (Function.Embedding.subtype fun x ↦ x ∈ E) := by
        rw [mem_map_subtype_iff K x.2]
        exact hxK
      specialize hagree (x : ι) hxmap
      rw [mem_map_subtype_iff s x.2] at hagree
      simpa [Finset.mem_subtype] using hagree)
  simpa [traceEventOnSupport, Finset.subtype_map_of_mem htE] using ht

theorem finiteTraceEventFamily_support_card {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) :
    (finiteTraceEventFamily (Finset.univ : Finset E) (traceEventOnSupport E T)).card =
      (finiteTraceEventFamily E T).card := by
  classical
  symm
  refine Finset.card_bij'
    (fun s _hs ↦ s.subtype fun x ↦ x ∈ E)
    (fun t _ht ↦ t.map (Function.Embedding.subtype fun x ↦ x ∈ E)) ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_finiteTraceEventFamily_iff] at hs ⊢
    constructor
    · intro x _hx
      simp
    · simp [traceEventOnSupport, Finset.subtype_map_of_mem hs.1, hs.2]
  · intro t ht
    rw [mem_finiteTraceEventFamily_iff] at ht ⊢
    constructor
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.2
    · exact ht.2
  · intro s hs
    rw [mem_finiteTraceEventFamily_iff] at hs
    exact Finset.subtype_map_of_mem hs.1
  · intro t _ht
    ext x
    simp [Finset.mem_subtype]

theorem finiteBernoulliExpectation_support_eq {ι : Type*}
    (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (Finset.univ : Finset E) p
        (fun s ↦ X (s.map (Function.Embedding.subtype fun x ↦ x ∈ E))) =
      finiteBernoulliExpectation E p X := by
  classical
  unfold finiteBernoulliExpectation
  symm
  refine Finset.sum_bij'
    (fun s _hs ↦ s.subtype fun x ↦ x ∈ E)
    (fun t _ht ↦ t.map (Function.Embedding.subtype fun x ↦ x ∈ E)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs ⊢
    intro x _hx
    simp
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    intro x hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro s hs
    rw [Finset.mem_powerset] at hs
    exact Finset.subtype_map_of_mem hs
  · intro t _ht
    ext x
    simp [Finset.mem_subtype]
  · intro s hs
    rw [Finset.mem_powerset] at hs
    have hmap : (s.subtype fun x ↦ x ∈ E).map
        (Function.Embedding.subtype fun x ↦ x ∈ E) = s :=
      Finset.subtype_map_of_mem hs
    have hcard : (s.subtype fun x ↦ x ∈ E).card = s.card := by
      rw [← (Finset.card_map (s := s.subtype fun x ↦ x ∈ E)
        (Function.Embedding.subtype fun x ↦ x ∈ E)), hmap]
    simp [hmap, hcard]

theorem finiteBernoulliEventProbability_support_eq {ι : Type*}
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (Finset.univ : Finset E) p (traceEventOnSupport E T) =
      finiteBernoulliEventProbability E p T := by
  unfold finiteBernoulliEventProbability
  simpa [traceEventOnSupport] using
    finiteBernoulliExpectation_support_eq E p
      (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)

theorem traceEventOnSupport_inter {ι : Type*} (E : Finset ι)
    (T U : Set (Finset ι)) :
    traceEventOnSupport E (T ∩ U) = traceEventOnSupport E T ∩ traceEventOnSupport E U := by
  ext s
  rfl

theorem traceEventOnSupport_traceComplement {ι : Type*} (E : Finset ι)
    (U : Set (Finset ι)) :
    traceEventOnSupport E (TraceComplement E U) =
      TraceComplement (Finset.univ : Finset E) (traceEventOnSupport E U) := by
  ext s
  simp only [traceEventOnSupport, TraceComplement, Set.mem_setOf_eq]
  have hmap :
      E \ s.map (Function.Embedding.subtype fun x ↦ x ∈ E) =
        ((@sdiff (Finset E) (@Finset.instSDiff E (Classical.decEq E))
          (Finset.univ : Finset E) s).map
          (Function.Embedding.subtype fun x ↦ x ∈ E)) := by
    ext x
    by_cases hxE : x ∈ E
    · simp [Finset.mem_sdiff, hxE]
    · simp [Finset.mem_map, Finset.mem_sdiff, hxE]
  rw [hmap]

/-- Reimer's standard finite-cube cardinality form. This is the combinatorial theorem whose
normalized-counting version gives the uniform probability form. -/
def FiniteTraceCardinalityReimerBound {ι : Type*} (E : Finset ι) : Prop :=
  ∀ T U : Set (Finset ι),
    (finiteTraceEventFamily E (ReimerTraceOccurrence E T U)).card ≤
      (finiteTraceEventFamily E (T ∩ TraceComplement E U)).card

theorem mem_reimerTraceOccurrence_iff {ι : Type*} {E s : Finset ι}
    {T U : Set (Finset ι)} :
    s ∈ ReimerTraceOccurrence E T U ↔
      s ⊆ E ∧ ∃ K : Finset ι, K ⊆ E ∧ TraceForces E K s T ∧
        TraceForces E (E \ K) s U :=
  Iff.rfl

/-- Finite-trace forcing is monotone in the event being forced. -/
theorem TraceForces.mono_event {ι : Type*} {E K s : Finset ι}
    {T U : Set (Finset ι)} (hTU : T ⊆ U) :
    TraceForces E K s T → TraceForces E K s U := by
  intro h t htE hagree
  exact hTU (h t htE hagree)

/-- If two finite trace events are forced by coordinate sets `K` and `L`, then their
intersection is forced by `K ∪ L`. -/
theorem TraceForces.inter {ι : Type*} {E K L s : Finset ι}
    {T U : Set (Finset ι)}
    (hT : TraceForces E K s T) (hU : TraceForces E L s U) :
    TraceForces E (K ∪ L) s (T ∩ U) := by
  intro t htE hagree
  exact ⟨hT t htE (by
      intro e he
      exact hagree e (Finset.mem_union_left L he)),
    hU t htE (by
      intro e he
      exact hagree e (Finset.mem_union_right K he))⟩

/-- A trace forced at `s` actually contains `s`, provided `s` lies in the ambient cube. -/
theorem TraceForces.mem {ι : Type*} {E K s : Finset ι}
    {T : Set (Finset ι)} (hK : TraceForces E K s T) (hsE : s ⊆ E) :
    s ∈ T :=
  hK s hsE fun _ _ ↦ Iff.rfl

/-- Trace forcing is monotone in the witness set: knowing more coordinates preserves forcing. -/
theorem TraceForces.mono_witness {ι : Type*} {E K L s : Finset ι}
    {T : Set (Finset ι)} (hK : TraceForces E K s T) (hKL : K ⊆ L) :
    TraceForces E L s T := by
  intro t htE hagree
  exact hK t htE fun e heK ↦ hagree e (hKL heK)

/-- Trace forcing is unchanged if the base trace agrees with the original one on the witness. -/
theorem TraceForces.congr_trace {ι : Type*} {E K s t : Finset ι}
    {T : Set (Finset ι)} (hK : TraceForces E K s T)
    (hst : ∀ e ∈ K, (e ∈ t ↔ e ∈ s)) :
    TraceForces E K t T := by
  intro u huE hagree
  exact hK u huE fun e heK ↦ (hagree e heK).trans (hst e heK)

/-- If all ambient coordinates are fixed, forcing is the same as membership of the trace. -/
theorem traceForces_full_iff {ι : Type*} {E s : Finset ι}
    {T : Set (Finset ι)} (hsE : s ⊆ E) :
    TraceForces E E s T ↔ s ∈ T := by
  constructor
  · intro h
    exact h.mem hsE
  · intro hs t htE hagree
    have hts : t = s := by
      ext e
      by_cases heE : e ∈ E
      · exact hagree e heE
      · have het : e ∉ t := fun het ↦ heE (htE het)
        have hes : e ∉ s := fun hes ↦ heE (hsE hes)
        simp [het, hes]
    simpa [hts] using hs

/-- For increasing trace events, closed coordinates in a forcing witness may be discarded:
only the coordinates open in the ambient trace are needed. This is the finite-trace analogue of
`Forces.restrict_to_open_of_increasing`. -/
theorem TraceForces.restrict_to_open_of_increasing {ι : Type*} {E K s : Finset ι}
    {T : Set (Finset ι)} (hK : TraceForces E K s T)
    (hT : IsIncreasingTrace E T) (hsE : s ⊆ E) :
    TraceForces E (K.filter fun e ↦ e ∈ s) s T := by
  classical
  intro t htE hagree
  let u : Finset ι := (t \ K) ∪ (s.filter fun e ↦ e ∈ K)
  have huE : u ⊆ E := by
    intro e he
    rcases Finset.mem_union.mp he with hetK | hesK
    · exact htE (Finset.mem_sdiff.mp hetK).1
    · exact hsE (Finset.mem_filter.mp hesK).1
  have huagree : ∀ e ∈ K, (e ∈ u ↔ e ∈ s) := by
    intro e heK
    constructor
    · intro heu
      rcases Finset.mem_union.mp heu with hetK | hesK
      · exact (Finset.mem_sdiff.mp hetK).2 heK |>.elim
      · exact (Finset.mem_filter.mp hesK).1
    · intro hes
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hes, heK⟩)
  have huT : u ∈ T := hK u huE huagree
  have hut : u ⊆ t := by
    intro e he
    rcases Finset.mem_union.mp he with hetK | hesK
    · exact (Finset.mem_sdiff.mp hetK).1
    · have hes : e ∈ s := (Finset.mem_filter.mp hesK).1
      have heK : e ∈ K := (Finset.mem_filter.mp hesK).2
      have heopen : e ∈ K.filter fun e ↦ e ∈ s := Finset.mem_filter.mpr ⟨heK, hes⟩
      exact (hagree e heopen).mpr hes
  exact hT hut htE huT

/-- Trace forcing on `E` gives ordinary forcing of the cylinder event obtained by reading the
finite trace on `E`. -/
theorem TraceForces.forces_eventOfTrace {ι : Type*} {E K : Finset ι}
    {ω : Set ι} {T : Set (Finset ι)}
    (hK : TraceForces E K (restrictTo E ω) T) (hKE : K ⊆ E) :
    Forces K ω (eventOfTrace E T) := by
  intro η hagree
  change restrictTo E η ∈ T
  exact hK (restrictTo E η) (restrictTo_subset E η) (by
    intro e heK
    have heE : e ∈ E := hKE heK
    have hη : e ∈ restrictTo E η ↔ e ∈ η := by
      simp [mem_restrictTo_iff, heE]
    have hω : e ∈ restrictTo E ω ↔ e ∈ ω := by
      simp [mem_restrictTo_iff, heE]
    exact hη.trans ((hagree e heK).trans hω.symm))

/-- Ordinary forcing of a finite-trace cylinder event descends to trace forcing after restricting
the witness to the trace support. -/
theorem Forces.traceForces_eventOfTrace {ι : Type*} {E K : Finset ι}
    {ω : Set ι} {T : Set (Finset ι)}
    (hK : Forces K ω (eventOfTrace E T)) :
    TraceForces E (K ∩ E) (restrictTo E ω) T := by
  classical
  intro t htE hagree
  let η : Set ι := (t : Set ι) ∪ (ω \ (E : Set ι))
  have hηagree : ∀ e ∈ K, (e ∈ η ↔ e ∈ ω) := by
    intro e heK
    by_cases heE : e ∈ E
    · have heKE : e ∈ K ∩ E := Finset.mem_inter.mpr ⟨heK, heE⟩
      have htω : e ∈ t ↔ e ∈ restrictTo E ω := hagree e heKE
      have hω : e ∈ restrictTo E ω ↔ e ∈ ω := by
        simp [mem_restrictTo_iff, heE]
      have hηt : e ∈ η ↔ e ∈ t := by
        constructor
        · intro heη
          rcases heη with het | heout
          · exact het
          · exact (heout.2 heE).elim
        · intro het
          exact Or.inl het
      exact hηt.trans (htω.trans hω)
    · constructor
      · intro heη
        rcases heη with het | heout
        · exact (heE (htE het)).elim
        · exact heout.1
      · intro heω
        exact Or.inr ⟨heω, heE⟩
  have hηT : η ∈ eventOfTrace E T := hK η hηagree
  change restrictTo E η ∈ T at hηT
  have hrestrict : restrictTo E η = t := by
    ext e
    rw [mem_restrictTo_iff]
    constructor
    · rintro ⟨heE, heη⟩
      rcases heη with het | heout
      · exact het
      · exact (heout.2 heE).elim
    · intro het
      exact ⟨htE het, Or.inl het⟩
  simpa [hrestrict] using hηT

/-- Trace-level open disjoint occurrence: two disjoint finite sets of open coordinates force the
two trace events. For increasing traces this is equal to Reimer trace occurrence. -/
def OpenTraceDisjointOccurrence {ι : Type*} (E : Finset ι)
    (T U : Set (Finset ι)) : Set (Finset ι) :=
  {s | s ⊆ E ∧ ∃ K L : Finset ι, Disjoint K L ∧ K ⊆ s ∧ L ⊆ s ∧
    TraceForces E K s T ∧ TraceForces E L s U}

theorem mem_openTraceDisjointOccurrence_iff {ι : Type*} {E s : Finset ι}
    {T U : Set (Finset ι)} :
    s ∈ OpenTraceDisjointOccurrence E T U ↔
      s ⊆ E ∧ ∃ K L : Finset ι, Disjoint K L ∧ K ⊆ s ∧ L ⊆ s ∧
        TraceForces E K s T ∧ TraceForces E L s U :=
  Iff.rfl

/-- Finite-family open trace disjoint occurrence: every trace event has a forcing witness, the
witnesses are pairwise disjoint, and every witness coordinate is open in the trace. This is the
finite-trace version of Grimmett's repeated BK occurrence. -/
def FiniteOpenTraceDisjointOccurrence {ι κ : Type*}
    (E : Finset ι) (J : Finset κ) (T : κ → Set (Finset ι)) : Set (Finset ι) :=
  {s | s ⊆ E ∧ ∃ K : κ → Finset ι,
    (∀ i, i ∈ J → K i ⊆ s ∧ TraceForces E (K i) s (T i)) ∧
      PairwiseDisjointWitnesses J K}

theorem mem_finiteOpenTraceDisjointOccurrence_iff {ι κ : Type*}
    {E s : Finset ι} {J : Finset κ} {T : κ → Set (Finset ι)} :
    s ∈ FiniteOpenTraceDisjointOccurrence E J T ↔
      s ⊆ E ∧ ∃ K : κ → Finset ι,
        (∀ i, i ∈ J → K i ⊆ s ∧ TraceForces E (K i) s (T i)) ∧
          PairwiseDisjointWitnesses J K :=
  Iff.rfl

@[simp]
theorem finiteOpenTraceDisjointOccurrence_empty {ι κ : Type*}
    (E : Finset ι) (T : κ → Set (Finset ι)) :
    FiniteOpenTraceDisjointOccurrence E (∅ : Finset κ) T = {s | s ⊆ E} := by
  ext s
  constructor
  · intro hs
    exact hs.1
  · intro hs
    refine ⟨hs, fun _ ↦ ∅, ?_, pairwiseDisjointWitnesses_empty _⟩
    intro i hi
    simp at hi

/-- Repeated open trace occurrence of increasing traces is itself increasing. -/
theorem isIncreasingTrace_finiteOpenTraceDisjointOccurrence {ι κ : Type*}
    {E : Finset ι} {J : Finset κ} {T : κ → Set (Finset ι)} :
    IsIncreasingTrace E (FiniteOpenTraceDisjointOccurrence E J T) := by
  intro s t hst htE hs
  rcases hs with ⟨_hsE, K, hK, hpair⟩
  refine ⟨htE, K, ?_, hpair⟩
  intro i hi
  rcases hK i hi with ⟨hKopen, hKforces⟩
  have hKt : K i ⊆ t := hKopen.trans hst
  refine ⟨hKt, ?_⟩
  exact (hKforces.congr_trace fun e heK ↦ by
    constructor
    · intro _het
      exact hKopen heK
    · intro _hes
      exact hKt heK)

/-- Removing one trace event from a finite-family open occurrence yields binary open occurrence
between that event and the open occurrence of the remaining family. -/
theorem finiteOpenTraceDisjointOccurrence_insert_subset_openTraceDisjointOccurrence
    {ι κ : Type*} {E : Finset ι} {J : Finset κ} {a : κ}
    (ha : a ∉ J) {T : κ → Set (Finset ι)} :
    FiniteOpenTraceDisjointOccurrence E (insert a J) T ⊆
      OpenTraceDisjointOccurrence E (T a) (FiniteOpenTraceDisjointOccurrence E J T) := by
  classical
  intro s hs
  rcases hs with ⟨hsE, K, hK, hpair⟩
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
  have hLopen : L ⊆ s := by
    intro e he
    change e ∈ J.biUnion K at he
    rw [Finset.mem_biUnion] at he
    rcases he with ⟨i, hi, hei⟩
    exact (hK i (Finset.mem_insert.mpr (Or.inr hi))).1 hei
  have hLforces : TraceForces E L s (FiniteOpenTraceDisjointOccurrence E J T) := by
    intro t htE hagree
    refine ⟨htE, K, ?_, hpairJ⟩
    intro i hi
    have hKi := hK i (Finset.mem_insert.mpr (Or.inr hi))
    have hKiL : K i ⊆ L := by
      intro e he
      change e ∈ J.biUnion K
      rw [Finset.mem_biUnion]
      exact ⟨i, hi, he⟩
    have hKit : K i ⊆ t := by
      intro e he
      exact (hagree e (hKiL he)).mpr (hKi.1 he)
    refine ⟨hKit, ?_⟩
    exact hKi.2.congr_trace fun e he ↦ hagree e (hKiL he)
  exact ⟨hsE, K a, L, hdis, (hK a (Finset.mem_insert_self a J)).1, hLopen,
    (hK a (Finset.mem_insert_self a J)).2, hLforces⟩

/-- Open trace disjoint occurrence is contained in Reimer trace occurrence: enlarge the second
open witness to the complement of the first one inside the ambient support. -/
theorem openTraceDisjointOccurrence_subset_reimerTraceOccurrence {ι : Type*}
    {E : Finset ι} {T U : Set (Finset ι)} :
    OpenTraceDisjointOccurrence E T U ⊆ ReimerTraceOccurrence E T U := by
  rintro s ⟨hsE, K, L, hdis, hKs, hLs, hKT, hLU⟩
  refine ⟨hsE, K, hKs.trans hsE, hKT, hLU.mono_witness ?_⟩
  intro e heL
  rw [Finset.mem_sdiff]
  exact ⟨hsE (hLs heL), fun heK ↦ (Finset.disjoint_left.mp hdis heK heL)⟩

/-- For increasing trace events, every Reimer trace witness can be converted to disjoint open
witnesses. -/
theorem reimerTraceOccurrence_subset_openTraceDisjointOccurrence_of_increasing {ι : Type*}
    {E : Finset ι} {T U : Set (Finset ι)}
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    ReimerTraceOccurrence E T U ⊆ OpenTraceDisjointOccurrence E T U := by
  classical
  rintro s ⟨hsE, K, hKE, hKT, hEU⟩
  let K' : Finset ι := K.filter fun e ↦ e ∈ s
  let L' : Finset ι := (E \ K).filter fun e ↦ e ∈ s
  have hdis : Disjoint K' L' := by
    refine Finset.disjoint_left.mpr ?_
    intro e heK heL
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp heL).1).2
      (Finset.mem_filter.mp heK).1
  have hKs : K' ⊆ s := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hLs : L' ⊆ s := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  exact ⟨hsE, K', L', hdis, hKs, hLs,
    by simpa [K'] using hKT.restrict_to_open_of_increasing hT hsE,
    by simpa [L'] using hEU.restrict_to_open_of_increasing hU hsE⟩

/-- For increasing traces, Reimer trace occurrence is exactly open trace disjoint occurrence. -/
theorem reimerTraceOccurrence_eq_openTraceDisjointOccurrence_of_increasing {ι : Type*}
    {E : Finset ι} {T U : Set (Finset ι)}
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    ReimerTraceOccurrence E T U = OpenTraceDisjointOccurrence E T U :=
  Set.Subset.antisymm
    (reimerTraceOccurrence_subset_openTraceDisjointOccurrence_of_increasing hT hU)
    openTraceDisjointOccurrence_subset_reimerTraceOccurrence

/-- Open trace disjoint occurrence is exactly open disjoint occurrence of the corresponding
finite-trace cylinder events. -/
theorem eventOfTrace_openTraceDisjointOccurrence {ι : Type*}
    (E : Finset ι) (T U : Set (Finset ι)) :
    eventOfTrace E (OpenTraceDisjointOccurrence E T U) =
      OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U) := by
  classical
  ext ω
  constructor
  · intro hω
    change restrictTo E ω ∈ OpenTraceDisjointOccurrence E T U at hω
    rcases hω with ⟨hsE, K, L, hdis, hKs, hLs, hKT, hLU⟩
    have hKE : K ⊆ E := hKs.trans hsE
    have hLE : L ⊆ E := hLs.trans hsE
    refine ⟨K, L, hdis, ?_, ?_, hKT.forces_eventOfTrace hKE, hLU.forces_eventOfTrace hLE⟩
    · intro e heK
      exact restrictTo_subset_configuration E ω (hKs heK)
    · intro e heL
      exact restrictTo_subset_configuration E ω (hLs heL)
  · intro hω
    rcases hω with ⟨K, L, hdis, hKopen, hLopen, hK, hL⟩
    change restrictTo E ω ∈ OpenTraceDisjointOccurrence E T U
    let K' : Finset ι := K ∩ E
    let L' : Finset ι := L ∩ E
    have hdis' : Disjoint K' L' :=
      hdis.mono
        (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    have hK's : K' ⊆ restrictTo E ω := by
      intro e he
      exact (mem_restrictTo_iff E ω e).mpr
        ⟨(Finset.mem_inter.mp he).2, hKopen (Finset.mem_inter.mp he).1⟩
    have hL's : L' ⊆ restrictTo E ω := by
      intro e he
      exact (mem_restrictTo_iff E ω e).mpr
        ⟨(Finset.mem_inter.mp he).2, hLopen (Finset.mem_inter.mp he).1⟩
    exact ⟨restrictTo_subset E ω, K', L', hdis', hK's, hL's,
      by simpa [K'] using hK.traceForces_eventOfTrace,
      by simpa [L'] using hL.traceForces_eventOfTrace⟩

/-- Finite-family open trace disjoint occurrence is exactly finite-family open disjoint occurrence
of the corresponding finite-trace cylinder events. -/
theorem eventOfTrace_finiteOpenTraceDisjointOccurrence {ι κ : Type*}
    (E : Finset ι) (J : Finset κ) (T : κ → Set (Finset ι)) :
    eventOfTrace E (FiniteOpenTraceDisjointOccurrence E J T) =
      FiniteOpenDisjointOccurrence J (fun i ↦ eventOfTrace E (T i)) := by
  classical
  ext ω
  constructor
  · intro hω
    change restrictTo E ω ∈ FiniteOpenTraceDisjointOccurrence E J T at hω
    rcases hω with ⟨hsE, K, hK, hpair⟩
    refine ⟨K, ?_, hpair⟩
    intro i hi
    rcases hK i hi with ⟨hKopen, hKforces⟩
    have hKE : K i ⊆ E := hKopen.trans hsE
    exact ⟨by
      intro e he
      exact restrictTo_subset_configuration E ω (hKopen he),
      hKforces.forces_eventOfTrace hKE⟩
  · intro hω
    rcases hω with ⟨K, hK, hpair⟩
    change restrictTo E ω ∈ FiniteOpenTraceDisjointOccurrence E J T
    let K' : κ → Finset ι := fun i ↦ K i ∩ E
    have hpair' : PairwiseDisjointWitnesses J K' := by
      intro i j hi hj hij
      exact (hpair hi hj hij).mono
        (by intro e he; exact (Finset.mem_inter.mp he).1)
        (by intro e he; exact (Finset.mem_inter.mp he).1)
    refine ⟨restrictTo_subset E ω, K', ?_, hpair'⟩
    intro i hi
    rcases hK i hi with ⟨hKopen, hKforces⟩
    have hK's : K' i ⊆ restrictTo E ω := by
      intro e he
      exact (mem_restrictTo_iff E ω e).mpr
        ⟨(Finset.mem_inter.mp he).2, hKopen (Finset.mem_inter.mp he).1⟩
    exact ⟨hK's, by simpa [K'] using hKforces.traceForces_eventOfTrace⟩

/-- The finite support for Grimmett's two-copy proof of the BK inequality. The left copy
contains `Sum.inl e`, and the right copy contains `Sum.inr e`, for `e ∈ E`. -/
noncomputable def bkTwoCopySupport {ι : Type*} (E : Finset ι) : Finset (Sum ι ι) := by
  classical
  exact E.map ⟨Sum.inl, fun _ _ h ↦ Sum.inl.inj h⟩ ∪
    E.map ⟨Sum.inr, fun _ _ h ↦ Sum.inr.inj h⟩

@[simp]
theorem inl_mem_bkTwoCopySupport_iff {ι : Type*} (E : Finset ι) (e : ι) :
    Sum.inl e ∈ bkTwoCopySupport E ↔ e ∈ E := by
  classical
  simp [bkTwoCopySupport]

@[simp]
theorem inr_mem_bkTwoCopySupport_iff {ι : Type*} (E : Finset ι) (e : ι) :
    Sum.inr e ∈ bkTwoCopySupport E ↔ e ∈ E := by
  classical
  simp [bkTwoCopySupport]

@[simp]
theorem bkTwoCopySupport_card {ι : Type*} (E : Finset ι) :
    (bkTwoCopySupport E).card = E.card + E.card := by
  classical
  simp only [bkTwoCopySupport]
  rw [Finset.card_union_of_disjoint]
  · simp
  · refine Finset.disjoint_left.mpr ?_
    intro z hzLeft hzRight
    rw [Finset.mem_map] at hzLeft hzRight
    rcases hzLeft with ⟨e, _he, heq⟩
    rcases hzRight with ⟨f, _hf, hfq⟩
    cases heq.trans hfq.symm

/-- Products over the two-copy support split into independent left and right products. -/
theorem bkTwoCopySupport_prod {ι M : Type*} [CommMonoid M]
    (E : Finset ι) (f : Sum ι ι → M) :
    (bkTwoCopySupport E).prod f =
      E.prod (fun e ↦ f (Sum.inl e)) * E.prod (fun e ↦ f (Sum.inr e)) := by
  classical
  simp only [bkTwoCopySupport]
  rw [Finset.prod_union]
  · rw [Finset.prod_map, Finset.prod_map]
    rfl
  · refine Finset.disjoint_left.mpr ?_
    intro z hzLeft hzRight
    rw [Finset.mem_map] at hzLeft hzRight
    rcases hzLeft with ⟨e, _he, heq⟩
    rcases hzRight with ⟨f, _hf, hfq⟩
    cases heq.trans hfq.symm

/-- The left finite trace of a two-copy configuration. -/
noncomputable def bkLeftTrace {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) : Finset ι := by
  classical
  exact E.filter fun e ↦ Sum.inl e ∈ ω

/-- The right finite trace of a two-copy configuration. -/
noncomputable def bkRightTrace {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) : Finset ι := by
  classical
  exact E.filter fun e ↦ Sum.inr e ∈ ω

@[simp]
theorem mem_bkLeftTrace_iff {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) (e : ι) :
    e ∈ bkLeftTrace E ω ↔ e ∈ E ∧ Sum.inl e ∈ ω := by
  classical
  simp [bkLeftTrace]

@[simp]
theorem mem_bkRightTrace_iff {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) (e : ι) :
    e ∈ bkRightTrace E ω ↔ e ∈ E ∧ Sum.inr e ∈ ω := by
  classical
  simp [bkRightTrace]

theorem bkLeftTrace_subset {ι : Type*} (E : Finset ι) (ω : Finset (Sum ι ι)) :
    bkLeftTrace E ω ⊆ E := by
  intro e he
  exact (mem_bkLeftTrace_iff E ω e).mp he |>.1

theorem bkRightTrace_subset {ι : Type*} (E : Finset ι) (ω : Finset (Sum ι ι)) :
    bkRightTrace E ω ⊆ E := by
  intro e he
  exact (mem_bkRightTrace_iff E ω e).mp he |>.1

/-- Reassemble a two-copy finite trace from its left and right traces. -/
noncomputable def bkTracePairSet {ι : Type*}
    (s t : Finset ι) : Finset (Sum ι ι) := by
  classical
  exact s.map ⟨Sum.inl, fun _ _ h ↦ Sum.inl.inj h⟩ ∪
    t.map ⟨Sum.inr, fun _ _ h ↦ Sum.inr.inj h⟩

@[simp]
theorem inl_mem_bkTracePairSet_iff {ι : Type*} (s t : Finset ι) (e : ι) :
    Sum.inl e ∈ bkTracePairSet s t ↔ e ∈ s := by
  classical
  simp [bkTracePairSet]

@[simp]
theorem inr_mem_bkTracePairSet_iff {ι : Type*} (s t : Finset ι) (e : ι) :
    Sum.inr e ∈ bkTracePairSet s t ↔ e ∈ t := by
  classical
  simp [bkTracePairSet]

theorem bkTracePairSet_subset_twoCopySupport {ι : Type*} {E s t : Finset ι}
    (hsE : s ⊆ E) (htE : t ⊆ E) :
    bkTracePairSet s t ⊆ bkTwoCopySupport E := by
  classical
  intro z hz
  cases z with
  | inl e =>
      rw [inl_mem_bkTracePairSet_iff] at hz
      exact inl_mem_bkTwoCopySupport_iff E e |>.mpr (hsE hz)
  | inr e =>
      rw [inr_mem_bkTracePairSet_iff] at hz
      exact inr_mem_bkTwoCopySupport_iff E e |>.mpr (htE hz)

@[simp]
theorem bkLeftTrace_bkTracePairSet {ι : Type*} {E s t : Finset ι} (hsE : s ⊆ E) :
    bkLeftTrace E (bkTracePairSet s t) = s := by
  classical
  ext e
  rw [mem_bkLeftTrace_iff, inl_mem_bkTracePairSet_iff]
  constructor
  · exact fun h ↦ h.2
  · intro hes
    exact ⟨hsE hes, hes⟩

@[simp]
theorem bkRightTrace_bkTracePairSet {ι : Type*} {E s t : Finset ι} (htE : t ⊆ E) :
    bkRightTrace E (bkTracePairSet s t) = t := by
  classical
  ext e
  rw [mem_bkRightTrace_iff, inr_mem_bkTracePairSet_iff]
  constructor
  · exact fun h ↦ h.2
  · intro het
    exact ⟨htE het, het⟩

theorem bkTracePairSet_left_right {ι : Type*} {E : Finset ι}
    {ω : Finset (Sum ι ι)} (hω : ω ⊆ bkTwoCopySupport E) :
    bkTracePairSet (bkLeftTrace E ω) (bkRightTrace E ω) = ω := by
  classical
  ext z
  cases z with
  | inl e =>
      rw [inl_mem_bkTracePairSet_iff, mem_bkLeftTrace_iff]
      constructor
      · exact fun h ↦ h.2
      · intro h
        exact ⟨by simpa using hω h, h⟩
  | inr e =>
      rw [inr_mem_bkTracePairSet_iff, mem_bkRightTrace_iff]
      constructor
      · exact fun h ↦ h.2
      · intro h
        exact ⟨by simpa using hω h, h⟩

@[simp]
theorem bkTracePairSet_card {ι : Type*} (s t : Finset ι) :
    (bkTracePairSet s t).card = s.card + t.card := by
  classical
  simp only [bkTracePairSet]
  rw [Finset.card_union_of_disjoint]
  · simp
  · refine Finset.disjoint_left.mpr ?_
    intro z hzLeft hzRight
    rw [Finset.mem_map] at hzLeft hzRight
    rcases hzLeft with ⟨e, _he, heq⟩
    rcases hzRight with ⟨f, _hf, hfq⟩
    cases heq.trans hfq.symm

@[simp]
theorem bkLeftTrace_twoCopySupport_sdiff {ι : Type*}
    (E : Finset ι) (K : Finset (Sum ι ι)) :
    bkLeftTrace E (bkTwoCopySupport E \ K) = E \ bkLeftTrace E K := by
  classical
  ext e
  rw [mem_bkLeftTrace_iff, Finset.mem_sdiff, Finset.mem_sdiff,
    inl_mem_bkTwoCopySupport_iff, mem_bkLeftTrace_iff]
  by_cases heE : e ∈ E <;> simp [heE]

theorem bkLeftTrace_mono {ι : Type*} {E : Finset ι} {ω η : Finset (Sum ι ι)}
    (hωη : ω ⊆ η) :
    bkLeftTrace E ω ⊆ bkLeftTrace E η := by
  intro e he
  rw [mem_bkLeftTrace_iff] at he ⊢
  exact ⟨he.1, hωη he.2⟩

theorem bkRightTrace_mono {ι : Type*} {E : Finset ι} {ω η : Finset (Sum ι ι)}
    (hωη : ω ⊆ η) :
    bkRightTrace E ω ⊆ bkRightTrace E η := by
  intro e he
  rw [mem_bkRightTrace_iff] at he ⊢
  exact ⟨he.1, hωη he.2⟩

@[simp]
theorem bkLeftTrace_insert_inr {ι : Type*} (E : Finset ι) (a : ι)
    (ω : Finset (Sum ι ι)) :
    bkLeftTrace E (insert (Sum.inr a) ω) = bkLeftTrace E ω := by
  classical
  ext e
  by_cases hea : e = a <;> simp [hea]

@[simp]
theorem bkLeftTrace_erase_inr {ι : Type*} (E : Finset ι) (a : ι)
    (ω : Finset (Sum ι ι)) :
    bkLeftTrace E (ω.erase (Sum.inr a)) = bkLeftTrace E ω := by
  classical
  ext e
  by_cases hea : e = a <;> simp [hea]

/-- Grimmett's composite trace used in the two-copy BK proof. Coordinates in `S` are read from
the right copy, and coordinates in `E \ S` are read from the left copy. -/
noncomputable def bkSplitTrace {ι : Type*} (E S : Finset ι)
    (ω : Finset (Sum ι ι)) : Finset ι := by
  classical
  exact (bkRightTrace E ω ∩ S) ∪ (bkLeftTrace E ω ∩ (E \ S))

@[simp]
theorem mem_bkSplitTrace_iff {ι : Type*} (E S : Finset ι)
    (ω : Finset (Sum ι ι)) (e : ι) :
    e ∈ bkSplitTrace E S ω ↔
      e ∈ E ∧ ((e ∈ S ∧ Sum.inr e ∈ ω) ∨ (e ∉ S ∧ Sum.inl e ∈ ω)) := by
  classical
  by_cases heS : e ∈ S <;>
    simp [bkSplitTrace, heS, and_comm]

theorem bkSplitTrace_subset {ι : Type*} (E S : Finset ι)
    (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S ω ⊆ E := by
  intro e he
  exact (mem_bkSplitTrace_iff E S ω e).mp he |>.1

theorem bkSplitTrace_mono {ι : Type*} {E S : Finset ι} {ω η : Finset (Sum ι ι)}
    (hωη : ω ⊆ η) :
    bkSplitTrace E S ω ⊆ bkSplitTrace E S η := by
  intro e he
  rw [mem_bkSplitTrace_iff] at he ⊢
  exact ⟨he.1, he.2.imp (fun h ↦ ⟨h.1, hωη h.2⟩) (fun h ↦ ⟨h.1, hωη h.2⟩)⟩

@[simp]
theorem bkSplitTrace_insert_inr_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (insert (Sum.inr a) ω) = bkSplitTrace E S ω := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp [haS]
  · by_cases heS : e ∈ S <;> simp [hea, heS]

@[simp]
theorem bkSplitTrace_erase_inr_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (ω.erase (Sum.inr a)) = bkSplitTrace E S ω := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp [haS]
  · by_cases heS : e ∈ S <;> simp [hea, heS]

@[simp]
theorem bkSplitTrace_empty {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) :
    bkSplitTrace E ∅ ω = bkLeftTrace E ω := by
  classical
  ext e
  rw [mem_bkSplitTrace_iff, mem_bkLeftTrace_iff]
  by_cases heE : e ∈ E <;> simp [heE]

@[simp]
theorem bkSplitTrace_self {ι : Type*} (E : Finset ι)
    (ω : Finset (Sum ι ι)) :
    bkSplitTrace E E ω = bkRightTrace E ω := by
  classical
  ext e
  rw [mem_bkSplitTrace_iff, mem_bkRightTrace_iff]
  by_cases heE : e ∈ E <;> simp [heE]

/-- The event `A'` in Grimmett's two-copy proof: the left copy lies in `T`. -/
def bkLeftEvent {ι : Type*} (E : Finset ι) (T : Set (Finset ι)) :
    Set (Finset (Sum ι ι)) :=
  {ω | bkLeftTrace E ω ∈ T}

/-- The event `B_S` in Grimmett's two-copy proof. -/
def bkSplitEvent {ι : Type*} (E S : Finset ι) (U : Set (Finset ι)) :
    Set (Finset (Sum ι ι)) :=
  {ω | bkSplitTrace E S ω ∈ U}

@[simp]
theorem mem_bkLeftEvent_iff {ι : Type*} {E : Finset ι} {T : Set (Finset ι)}
    {ω : Finset (Sum ι ι)} :
    ω ∈ bkLeftEvent E T ↔ bkLeftTrace E ω ∈ T :=
  Iff.rfl

@[simp]
theorem mem_bkSplitEvent_iff {ι : Type*} {E S : Finset ι} {U : Set (Finset ι)}
    {ω : Finset (Sum ι ι)} :
    ω ∈ bkSplitEvent E S U ↔ bkSplitTrace E S ω ∈ U :=
  Iff.rfl

theorem isIncreasingTrace_bkLeftEvent {ι : Type*} {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace E T) :
    IsIncreasingTrace (bkTwoCopySupport E) (bkLeftEvent E T) := by
  intro s t hst _ht hTmem
  exact hT (bkLeftTrace_mono hst) (bkLeftTrace_subset E t) hTmem

theorem isIncreasingTrace_bkSplitEvent {ι : Type*} {E S : Finset ι}
    {U : Set (Finset ι)} (hU : IsIncreasingTrace E U) :
    IsIncreasingTrace (bkTwoCopySupport E) (bkSplitEvent E S U) := by
  intro s t hst _ht hUmem
  exact hU (bkSplitTrace_mono hst) (bkSplitTrace_subset E S t) hUmem

/-- A two-copy forcing witness for an event depending only on the left copy projects to a
one-copy forcing witness. -/
theorem TraceForces.bkLeftEvent_to_leftTrace {ι : Type*}
    {E : Finset ι} {K ω : Finset (Sum ι ι)} {T : Set (Finset ι)}
    (hKF : K ⊆ bkTwoCopySupport E)
    (hK : TraceForces (bkTwoCopySupport E) K ω (bkLeftEvent E T)) :
    TraceForces E (bkLeftTrace E K) (bkLeftTrace E ω) T := by
  classical
  intro t htE hagree
  have hpairF : bkTracePairSet t (bkRightTrace E ω) ⊆ bkTwoCopySupport E :=
    bkTracePairSet_subset_twoCopySupport htE (bkRightTrace_subset E ω)
  have hagreeF :
      ∀ z ∈ K, (z ∈ bkTracePairSet t (bkRightTrace E ω) ↔ z ∈ ω) := by
    intro z hzK
    cases z with
    | inl e =>
        have heE : e ∈ E := by
          simpa using hKF hzK
        have heLeftK : e ∈ bkLeftTrace E K := by
          simp [heE, hzK]
        have heagree := hagree e heLeftK
        simpa [heE] using heagree
    | inr e =>
        have heE : e ∈ E := by
          simpa using hKF hzK
        simp [heE]
  have hmem := hK (bkTracePairSet t (bkRightTrace E ω)) hpairF hagreeF
  change bkLeftTrace E (bkTracePairSet t (bkRightTrace E ω)) ∈ T at hmem
  simpa [bkLeftTrace_bkTracePairSet htE] using hmem

/-- A one-copy forcing witness lifts to a two-copy witness for the corresponding left-copy
event. -/
theorem TraceForces.leftTrace_to_bkLeftEvent {ι : Type*}
    {E K : Finset ι} {ω : Finset (Sum ι ι)} {T : Set (Finset ι)}
    (hKE : K ⊆ E) (hK : TraceForces E K (bkLeftTrace E ω) T) :
    TraceForces (bkTwoCopySupport E) (bkTracePairSet K ∅) ω (bkLeftEvent E T) := by
  classical
  intro η _hηF hagree
  change bkLeftTrace E η ∈ T
  exact hK (bkLeftTrace E η) (bkLeftTrace_subset E η) (by
    intro e heK
    have hePair : Sum.inl e ∈ bkTracePairSet K (∅ : Finset ι) := by
      simp [heK]
    have heagree := hagree (Sum.inl e) hePair
    have heE : e ∈ E := hKE heK
    simpa [mem_bkLeftTrace_iff, heE] using heagree)

/-- Complementary one-copy forcing lifts to the complement of the corresponding left-copy
witness in the two-copy support. -/
theorem TraceForces.leftTraceComplement_to_bkLeftEvent {ι : Type*}
    {E K : Finset ι} {ω : Finset (Sum ι ι)} {T : Set (Finset ι)}
    (hK : TraceForces E (E \ K) (bkLeftTrace E ω) T) :
    TraceForces (bkTwoCopySupport E) (bkTwoCopySupport E \ bkTracePairSet K ∅) ω
      (bkLeftEvent E T) := by
  classical
  intro η _hηF hagree
  change bkLeftTrace E η ∈ T
  exact hK (bkLeftTrace E η) (bkLeftTrace_subset E η) (by
    intro e heEK
    have heE : e ∈ E := (Finset.mem_sdiff.mp heEK).1
    have heK : e ∉ K := (Finset.mem_sdiff.mp heEK).2
    have hePair : Sum.inl e ∈ bkTwoCopySupport E \ bkTracePairSet K (∅ : Finset ι) := by
      rw [Finset.mem_sdiff]
      exact ⟨by simpa using heE, by simp [heK]⟩
    have heagree := hagree (Sum.inl e) hePair
    simpa [mem_bkLeftTrace_iff, heE] using heagree)

@[simp]
theorem bkSplitEvent_empty {ι : Type*} (E : Finset ι) (U : Set (Finset ι)) :
    bkSplitEvent E ∅ U = bkLeftEvent E U := by
  ext ω
  simp [bkSplitEvent, bkLeftEvent]

@[simp]
theorem bkSplitEvent_self {ι : Type*} (E : Finset ι) (U : Set (Finset ι)) :
    bkSplitEvent E E U = {ω | bkRightTrace E ω ∈ U} := by
  ext ω
  simp [bkSplitEvent]

/-- Swap the two copies of one coordinate in Grimmett's two-copy BK proof. -/
noncomputable def bkSwapIndex {ι : Type*} (a : ι) : Sum ι ι ≃ Sum ι ι := by
  classical
  refine
    { toFun := fun z ↦
        match z with
        | Sum.inl e => if e = a then Sum.inr e else Sum.inl e
        | Sum.inr e => if e = a then Sum.inl e else Sum.inr e
      invFun := fun z ↦
        match z with
        | Sum.inl e => if e = a then Sum.inr e else Sum.inl e
        | Sum.inr e => if e = a then Sum.inl e else Sum.inr e
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    cases z with
    | inl e => by_cases h : e = a <;> simp [h]
    | inr e => by_cases h : e = a <;> simp [h]
  · intro z
    cases z with
    | inl e => by_cases h : e = a <;> simp [h]
    | inr e => by_cases h : e = a <;> simp [h]

@[simp]
theorem bkSwapIndex_bkSwapIndex {ι : Type*} (a : ι) (z : Sum ι ι) :
    bkSwapIndex a (bkSwapIndex a z) = z := by
  classical
  cases z with
  | inl e => by_cases h : e = a <;> simp [bkSwapIndex, h]
  | inr e => by_cases h : e = a <;> simp [bkSwapIndex, h]

@[simp]
theorem bkSwapIndex_mem_twoCopySupport_iff {ι : Type*}
    (E : Finset ι) (a : ι) (z : Sum ι ι) :
    bkSwapIndex a z ∈ bkTwoCopySupport E ↔ z ∈ bkTwoCopySupport E := by
  classical
  cases z with
  | inl e => by_cases h : e = a <;> simp [bkSwapIndex, h]
  | inr e => by_cases h : e = a <;> simp [bkSwapIndex, h]

@[simp]
theorem sumElim_bkSwapIndex {ι : Type*} (q : ι → ℝ) (a : ι) (z : Sum ι ι) :
    Sum.elim q q (bkSwapIndex a z) = Sum.elim q q z := by
  classical
  cases z with
  | inl e => by_cases h : e = a <;> simp [bkSwapIndex, h]
  | inr e => by_cases h : e = a <;> simp [bkSwapIndex, h]

/-- Apply the coordinate swap to a two-copy finite trace. -/
noncomputable def bkSwapTrace {ι : Type*} (a : ι)
    (ω : Finset (Sum ι ι)) : Finset (Sum ι ι) :=
  ω.map (bkSwapIndex a).toEmbedding

@[simp]
theorem inl_mem_bkSwapTrace_iff {ι : Type*} (a e : ι)
    (ω : Finset (Sum ι ι)) :
    Sum.inl e ∈ bkSwapTrace a ω ↔
      if e = a then Sum.inr e ∈ ω else Sum.inl e ∈ ω := by
  classical
  by_cases h : e = a <;> simp [bkSwapTrace, bkSwapIndex, h]

@[simp]
theorem inr_mem_bkSwapTrace_iff {ι : Type*} (a e : ι)
    (ω : Finset (Sum ι ι)) :
    Sum.inr e ∈ bkSwapTrace a ω ↔
      if e = a then Sum.inl e ∈ ω else Sum.inr e ∈ ω := by
  classical
  by_cases h : e = a <;> simp [bkSwapTrace, bkSwapIndex, h]

theorem mem_bkSwapTrace_iff_bkSwapIndex_mem {ι : Type*} (a : ι)
    (z : Sum ι ι) (ω : Finset (Sum ι ι)) :
    z ∈ bkSwapTrace a ω ↔ bkSwapIndex a z ∈ ω := by
  classical
  cases z with
  | inl e => by_cases h : e = a <;> simp [bkSwapIndex, h]
  | inr e => by_cases h : e = a <;> simp [bkSwapIndex, h]

@[simp]
theorem bkSwapTrace_bkSwapTrace {ι : Type*} (a : ι) (ω : Finset (Sum ι ι)) :
    bkSwapTrace a (bkSwapTrace a ω) = ω := by
  classical
  ext z
  cases z with
  | inl e =>
      by_cases h : e = a <;> simp [bkSwapTrace, bkSwapIndex, h]
  | inr e =>
      by_cases h : e = a <;> simp [bkSwapTrace, bkSwapIndex, h]

theorem bkSwapTrace_eq_self_of_mem_inl_of_mem_inr {ι : Type*}
    (a : ι) (ω : Finset (Sum ι ι))
    (hl : Sum.inl a ∈ ω) (hr : Sum.inr a ∈ ω) :
    bkSwapTrace a ω = ω := by
  classical
  ext z
  cases z with
  | inl e =>
      by_cases hea : e = a
      · subst e
        simp [hr, hl]
      · simp [hea]
  | inr e =>
      by_cases hea : e = a
      · subst e
        simp [hr, hl]
      · simp [hea]

/-- Swapping coordinate `a` converts the split that still reads `a` from the left copy into the
split that reads `a` from the right copy. This is the trace-level form of Grimmett's transition
from `B_{k-1}` to `B_k`. -/
theorem bkSplitTrace_insert_eq_splitTrace_swap {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E (insert a S) ω = bkSplitTrace E S (bkSwapTrace a ω) := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp [haS]
  · by_cases heS : e ∈ S <;>
      simp [hea, heS]

/-- Event-level version of `bkSplitTrace_insert_eq_splitTrace_swap`. -/
theorem bkSplitEvent_insert_eq_preimage_swap {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (U : Set (Finset ι)) :
    bkSplitEvent E (insert a S) U =
      {ω | bkSwapTrace a ω ∈ bkSplitEvent E S U} := by
  ext ω
  simp [bkSplitEvent, bkSplitTrace_insert_eq_splitTrace_swap E S haS ω]

@[simp]
theorem bkLeftTrace_erase_inl {ι : Type*} (E : Finset ι) (a : ι)
    (ω : Finset (Sum ι ι)) :
    bkLeftTrace E (ω.erase (Sum.inl a)) = (bkLeftTrace E ω).erase a := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp
  · simp [hea]

theorem bkSplitTrace_erase_inl_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (ω.erase (Sum.inl a)) = (bkSplitTrace E S ω).erase a := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp [haS]
  · by_cases heS : e ∈ S <;> simp [hea, heS]

@[simp]
theorem bkSplitTrace_insert_erase_inl_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E (insert a S) (ω.erase (Sum.inl a)) =
      bkSplitTrace E (insert a S) ω := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    simp [haS]
  · by_cases heS : e ∈ S <;> simp [hea, heS]

/-- The one-coordinate swap preserves the ambient two-copy support. -/
theorem bkSwapTrace_subset_twoCopySupport {ι : Type*} {E : Finset ι} {a : ι}
    {ω : Finset (Sum ι ι)} (hω : ω ⊆ bkTwoCopySupport E) :
    bkSwapTrace a ω ⊆ bkTwoCopySupport E := by
  classical
  intro z hz
  cases z with
  | inl e =>
      rw [inl_mem_bkSwapTrace_iff] at hz
      by_cases hea : e = a
      · have hmem : Sum.inr e ∈ ω := by simpa [hea] using hz
        have hsup : Sum.inr e ∈ bkTwoCopySupport E := hω hmem
        simpa using hsup
      · have hmem : Sum.inl e ∈ ω := by simpa [hea] using hz
        exact hω hmem
  | inr e =>
      rw [inr_mem_bkSwapTrace_iff] at hz
      by_cases hea : e = a
      · have hmem : Sum.inl e ∈ ω := by simpa [hea] using hz
        have hsup : Sum.inl e ∈ bkTwoCopySupport E := hω hmem
        simpa using hsup
      · have hmem : Sum.inr e ∈ ω := by simpa [hea] using hz
        exact hω hmem

theorem bkSwapTrace_mem_twoCopyPowerset {ι : Type*} {E : Finset ι} {a : ι}
    {ω : Finset (Sum ι ι)} (hω : ω ∈ (bkTwoCopySupport E).powerset) :
    bkSwapTrace a ω ∈ (bkTwoCopySupport E).powerset :=
  Finset.mem_powerset.mpr (bkSwapTrace_subset_twoCopySupport (Finset.mem_powerset.mp hω))

@[simp]
theorem bkSwapTrace_card {ι : Type*} (a : ι) (ω : Finset (Sum ι ι)) :
    (bkSwapTrace a ω).card = ω.card := by
  classical
  simp [bkSwapTrace]

/-- Swapping one coordinate preserves the heterogeneous two-copy product weight when the left
and right copies use the same coordinate probability. -/
theorem bkSwapTrace_heteroWeight_prod {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (a : ι) (ω : Finset (Sum ι ι)) :
    finiteBernoulliHeteroTraceWeight (bkTwoCopySupport E) (Sum.elim q q)
        (bkSwapTrace a ω) =
      finiteBernoulliHeteroTraceWeight (bkTwoCopySupport E) (Sum.elim q q) ω := by
  classical
  unfold finiteBernoulliHeteroTraceWeight
  refine Finset.prod_bij'
    (fun z _hz ↦ bkSwapIndex a z)
    (fun z _hz ↦ bkSwapIndex a z)
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact (bkSwapIndex_mem_twoCopySupport_iff E a z).mpr hz
  · intro z hz
    exact (bkSwapIndex_mem_twoCopySupport_iff E a z).mpr hz
  · intro z _hz
    exact bkSwapIndex_bkSwapIndex a z
  · intro z _hz
    exact bkSwapIndex_bkSwapIndex a z
  · intro z _hz
    have hq : Sum.elim q q (bkSwapIndex a z) = Sum.elim q q z := by
      simp
    by_cases hzω : z ∈ bkSwapTrace a ω
    · have hswapω : bkSwapIndex a z ∈ ω :=
        (mem_bkSwapTrace_iff_bkSwapIndex_mem a z ω).mp hzω
      simp [hzω, hswapω, hq]
    · have hswapω : bkSwapIndex a z ∉ ω := by
        intro hmem
        exact hzω ((mem_bkSwapTrace_iff_bkSwapIndex_mem a z ω).mpr hmem)
      simp [hzω, hswapω, hq]

/-- The one-coordinate swap is measure-preserving for the finite two-copy Bernoulli cube. This
is the finite-sum version of the measure-preserving swap in Grimmett's proof of (2.21). -/
theorem finiteBernoulliExpectation_bkSwapTrace {ι : Type*}
    (E : Finset ι) (a : ι) (p : ℝ) (X : Finset (Sum ι ι) → ℝ) :
    finiteBernoulliExpectation (bkTwoCopySupport E) p (fun s ↦ X (bkSwapTrace a s)) =
      finiteBernoulliExpectation (bkTwoCopySupport E) p X := by
  classical
  unfold finiteBernoulliExpectation
  refine Finset.sum_bij'
    (fun s _hs ↦ bkSwapTrace a s)
    (fun s _hs ↦ bkSwapTrace a s)
    (fun _ hs ↦ bkSwapTrace_mem_twoCopyPowerset hs)
    (fun _ hs ↦ bkSwapTrace_mem_twoCopyPowerset hs) ?_ ?_ ?_
  · intro s _hs
    exact bkSwapTrace_bkSwapTrace a s
  · intro s _hs
    exact bkSwapTrace_bkSwapTrace a s
  · intro s _hs
    simp

theorem finiteBernoulliEventProbability_bkSwapTrace_preimage {ι : Type*}
    (E : Finset ι) (a : ι) (p : ℝ) (V : Set (Finset (Sum ι ι))) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p
        {ω | bkSwapTrace a ω ∈ V} =
      finiteBernoulliEventProbability (bkTwoCopySupport E) p V := by
  unfold finiteBernoulliEventProbability
  simpa using
    finiteBernoulliExpectation_bkSwapTrace E a p
      (fun s ↦ V.indicator (fun _ ↦ (1 : ℝ)) s)

/-- Compare two finite-cube event probabilities by an injective, level-preserving map from the
first trace family into the second. This is the finite weighted-counting wrapper used by
Grimmett's BK injection. -/
theorem finiteBernoulliEventProbability_le_of_injOn_card_eq {ι : Type*}
    {E : Finset ι} {p : ℝ} {A B : Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Finset ι → Finset ι)
    (hmap : ∀ ⦃s : Finset ι⦄, s ⊆ E → s ∈ A → f s ⊆ E ∧ f s ∈ B)
    (hinj : Set.InjOn f {s | s ⊆ E ∧ s ∈ A})
    (hcard : ∀ ⦃s : Finset ι⦄, s ⊆ E → s ∈ A → (f s).card = s.card) :
    finiteBernoulliEventProbability E p A ≤ finiteBernoulliEventProbability E p B := by
  classical
  rw [finiteBernoulliEventProbability_eq_sum_traceFamily,
    finiteBernoulliEventProbability_eq_sum_traceFamily]
  let SA := finiteTraceEventFamily E A
  let SB := finiteTraceEventFamily E B
  let w : Finset ι → ℝ := fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card)
  have hinjSA : Set.InjOn f (↑SA : Set (Finset ι)) := by
    intro s hs t ht hst
    apply hinj
    · simpa [SA, mem_finiteTraceEventFamily_iff] using hs
    · simpa [SA, mem_finiteTraceEventFamily_iff] using ht
    · exact hst
  calc
    SA.sum w = (SA.image f).sum w := by
      rw [Finset.sum_image hinjSA]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ⊆ E ∧ s ∈ A := by
        simpa [SA, mem_finiteTraceEventFamily_iff] using hs
      have hc := hcard hs'.1 hs'.2
      simp [w, hc]
    _ ≤ SB.sum w := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro t ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨s, hs, rfl⟩
        have hs' : s ⊆ E ∧ s ∈ A := by
          simpa [SA, mem_finiteTraceEventFamily_iff] using hs
        have hfs := hmap hs'.1 hs'.2
        simpa [SB, mem_finiteTraceEventFamily_iff] using hfs
      · intro _s _hsSB _hsnot
        have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
        exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hq0 _)

/-- Compare two heterogeneous finite-cube event probabilities by an injective map that preserves
the product weight of every source trace. This is the weighted form of the counting wrapper used
by Grimmett's BK injection. -/
theorem finiteBernoulliHeteroEventProbability_le_of_injOn_weight_eq {ι : Type*}
    {E : Finset ι} {q : ι → ℝ} {A B : Set (Finset ι)}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (f : Finset ι → Finset ι)
    (hmap : ∀ ⦃s : Finset ι⦄, s ⊆ E → s ∈ A → f s ⊆ E ∧ f s ∈ B)
    (hinj : Set.InjOn f {s | s ⊆ E ∧ s ∈ A})
    (hweight : ∀ ⦃s : Finset ι⦄, s ⊆ E → s ∈ A →
      finiteBernoulliHeteroTraceWeight E q (f s) =
        finiteBernoulliHeteroTraceWeight E q s) :
    finiteBernoulliHeteroEventProbability E q A ≤
      finiteBernoulliHeteroEventProbability E q B := by
  classical
  rw [finiteBernoulliHeteroEventProbability_eq_sum_traceFamily,
    finiteBernoulliHeteroEventProbability_eq_sum_traceFamily]
  let SA := finiteTraceEventFamily E A
  let SB := finiteTraceEventFamily E B
  let w : Finset ι → ℝ := finiteBernoulliHeteroTraceWeight E q
  have hinjSA : Set.InjOn f (↑SA : Set (Finset ι)) := by
    intro s hs t ht hst
    apply hinj
    · simpa [SA, mem_finiteTraceEventFamily_iff] using hs
    · simpa [SA, mem_finiteTraceEventFamily_iff] using ht
    · exact hst
  calc
    SA.sum w = (SA.image f).sum w := by
      rw [Finset.sum_image hinjSA]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ⊆ E ∧ s ∈ A := by
        simpa [SA, mem_finiteTraceEventFamily_iff] using hs
      exact (hweight hs'.1 hs'.2).symm
    _ ≤ SB.sum w := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro t ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨s, hs, rfl⟩
        have hs' : s ⊆ E ∧ s ∈ A := by
          simpa [SA, mem_finiteTraceEventFamily_iff] using hs
        have hfs := hmap hs'.1 hs'.2
        simpa [SB, mem_finiteTraceEventFamily_iff] using hfs
      · intro s _hsSB _hsnot
        unfold finiteBernoulliHeteroTraceWeight
        exact Finset.prod_nonneg (by
          intro e heE
          by_cases hes : e ∈ s
          · simp [hes, hq0 e heE]
          · simpa [hes] using sub_nonneg.mpr (hq1 e heE))

/-- Heterogeneous finite Bernoulli event probabilities are monotone under event inclusion. -/
theorem finiteBernoulliHeteroEventProbability_mono {ι : Type*}
    {E : Finset ι} {q : ι → ℝ} {A B : Set (Finset ι)}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1) (hAB : A ⊆ B) :
    finiteBernoulliHeteroEventProbability E q A ≤
      finiteBernoulliHeteroEventProbability E q B := by
  classical
  refine finiteBernoulliHeteroEventProbability_le_of_injOn_weight_eq hq0 hq1
    (fun s ↦ s) ?_ ?_ ?_
  · intro s hsE hsA
    exact ⟨hsE, hAB hsA⟩
  · intro _s _hs _t _ht hst
    exact hst
  · intro _s _hsE _hsA
    rfl

/-- Heterogeneous finite Bernoulli event probabilities are nonnegative when all coordinate
probabilities lie in `[0,1]`. -/
theorem finiteBernoulliHeteroEventProbability_nonneg {ι : Type*}
    (E : Finset ι) {q : ι → ℝ} (T : Set (Finset ι))
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1) :
    0 ≤ finiteBernoulliHeteroEventProbability E q T := by
  classical
  rw [finiteBernoulliHeteroEventProbability_eq_sum_traceFamily]
  refine Finset.sum_nonneg ?_
  intro s _hs
  unfold finiteBernoulliHeteroTraceWeight
  exact Finset.prod_nonneg (by
    intro e heE
    by_cases hes : e ∈ s
    · simp [hes, hq0 e heE]
    · simpa [hes] using sub_nonneg.mpr (hq1 e heE))

/-- The source event `A' □ B_S` in one step of Grimmett's two-copy proof. -/
def bkStepSource {ι : Type*} (E S : Finset ι)
    (T U : Set (Finset ι)) : Set (Finset (Sum ι ι)) :=
  ReimerTraceOccurrence (bkTwoCopySupport E) (bkLeftEvent E T) (bkSplitEvent E S U)

/-- The target event `A' □ B_{S ∪ {a}}` in one step of Grimmett's two-copy proof. -/
def bkStepTarget {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) : Set (Finset (Sum ι ι)) :=
  bkStepSource E (insert a S) T U

/-- Set the left-copy coordinate `a` to closed. This is Grimmett's operation of changing
`x_k` to `0`. -/
noncomputable def bkCloseLeft {ι : Type*} (a : ι)
    (ω : Finset (Sum ι ι)) : Finset (Sum ι ι) := by
  classical
  exact ω.erase (Sum.inl a)

@[simp]
theorem bkCloseLeft_subset_twoCopySupport {ι : Type*} {E : Finset ι} {a : ι}
    {ω : Finset (Sum ι ι)} (hω : ω ⊆ bkTwoCopySupport E) :
    bkCloseLeft a ω ⊆ bkTwoCopySupport E :=
  (Finset.erase_subset _ _).trans hω

@[simp]
theorem bkLeftTrace_bkCloseLeft {ι : Type*} (E : Finset ι) (a : ι)
    (ω : Finset (Sum ι ι)) :
    bkLeftTrace E (bkCloseLeft a ω) = (bkLeftTrace E ω).erase a := by
  simp [bkCloseLeft]

theorem bkSwapTrace_erase_inr_eq_closeLeft_of_not_mem_inr {ι : Type*}
    (a : ι) (ω : Finset (Sum ι ι)) (hr : Sum.inr a ∉ ω) :
    (bkSwapTrace a ω).erase (Sum.inr a) = bkCloseLeft a ω := by
  classical
  ext z
  cases z with
  | inl e =>
      by_cases hea : e = a
      · subst e
        simp [bkCloseLeft, hr]
      · simp [bkCloseLeft, hea]
  | inr e =>
      by_cases hea : e = a
      · subst e
        simp [bkCloseLeft, hr]
      · simp [bkCloseLeft, hea]

theorem bkSplitTrace_bkCloseLeft_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (bkCloseLeft a ω) = (bkSplitTrace E S ω).erase a := by
  simp [bkCloseLeft, bkSplitTrace_erase_inl_of_not_mem E S haS]

@[simp]
theorem bkSplitTrace_insert_bkCloseLeft_of_not_mem {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E (insert a S) (bkCloseLeft a ω) =
      bkSplitTrace E (insert a S) ω := by
  simp [bkCloseLeft, bkSplitTrace_insert_erase_inl_of_not_mem E S haS]

theorem bkSplitTrace_bkCloseLeft_subset_insert {ι : Type*} (E S : Finset ι) {a : ι}
    (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (bkCloseLeft a ω) ⊆ bkSplitTrace E (insert a S) ω := by
  classical
  intro e he
  rw [mem_bkSplitTrace_iff] at he ⊢
  rcases he with ⟨heE, hecase⟩
  refine ⟨heE, ?_⟩
  by_cases hea : e = a
  · subst e
    simp [bkCloseLeft, haS] at hecase
  · rcases hecase with ⟨heS, her⟩ | ⟨hneS, hel⟩
    · left
      exact ⟨Finset.mem_insert_of_mem heS, by simpa [bkCloseLeft, hea] using her⟩
    · right
      constructor
      · intro heIns
        rw [Finset.mem_insert] at heIns
        exact heIns.elim (fun h ↦ hea h) hneS
      · simpa [bkCloseLeft, hea] using hel

/-- Copy the right-copy value of coordinate `a` into the left copy. This auxiliary trace is used
to compare forcing for `B_S` with forcing for `B_{S ∪ {a}}`. -/
noncomputable def bkSetLeftFromRight {ι : Type*} (a : ι)
    (ω : Finset (Sum ι ι)) : Finset (Sum ι ι) := by
  classical
  exact if Sum.inr a ∈ ω then insert (Sum.inl a) ω else ω.erase (Sum.inl a)

theorem bkSetLeftFromRight_subset_twoCopySupport {ι : Type*} {E : Finset ι} {a : ι}
    {ω : Finset (Sum ι ι)} (hω : ω ⊆ bkTwoCopySupport E) :
    bkSetLeftFromRight a ω ⊆ bkTwoCopySupport E := by
  classical
  intro z hz
  by_cases hra : Sum.inr a ∈ ω
  · simp [bkSetLeftFromRight, hra] at hz
    rcases hz with rfl | hzω
    · have haE : a ∈ E := by simpa using hω hra
      simp [haE]
    · exact hω hzω
  · simp [bkSetLeftFromRight, hra] at hz
    exact hω hz.2

theorem bkSplitTrace_setLeftFromRight_eq_insert_of_not_mem {ι : Type*}
    (E S : Finset ι) {a : ι} (haS : a ∉ S) (ω : Finset (Sum ι ι)) :
    bkSplitTrace E S (bkSetLeftFromRight a ω) =
      bkSplitTrace E (insert a S) ω := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    by_cases hra : Sum.inr a ∈ ω <;> simp [bkSetLeftFromRight, haS, hra]
  · by_cases heS : e ∈ S <;>
      by_cases hra : Sum.inr a ∈ ω <;>
      simp [bkSetLeftFromRight, hea, heS, hra]

/-- Auxiliary configuration for the swapped `C₂''` branch. It makes the old split `B_S` see the
new split `B_{S ∪ {a}}` while preserving the original right-copy value for agreement with old
complement witnesses. -/
noncomputable def bkSwapBackForSplit {ι : Type*} (a : ι)
    (ω t : Finset (Sum ι ι)) : Finset (Sum ι ι) := by
  classical
  let t1 := bkSetLeftFromRight a t
  exact if Sum.inr a ∈ ω then insert (Sum.inr a) t1 else t1.erase (Sum.inr a)

theorem bkSwapBackForSplit_subset_twoCopySupport {ι : Type*} {E : Finset ι} {a : ι}
    {ω t : Finset (Sum ι ι)}
    (hω : ω ⊆ bkTwoCopySupport E) (ht : t ⊆ bkTwoCopySupport E) :
    bkSwapBackForSplit a ω t ⊆ bkTwoCopySupport E := by
  classical
  intro z hz
  by_cases hrω : Sum.inr a ∈ ω
  · simp [bkSwapBackForSplit, hrω] at hz
    rcases hz with rfl | hz
    · exact hω hrω
    · exact bkSetLeftFromRight_subset_twoCopySupport ht hz
  · simp [bkSwapBackForSplit, hrω] at hz
    exact bkSetLeftFromRight_subset_twoCopySupport ht hz.2

theorem bkSplitTrace_swapBackForSplit_eq_insert_of_not_mem {ι : Type*}
    (E S : Finset ι) {a : ι} (haS : a ∉ S)
    (ω t : Finset (Sum ι ι)) :
    bkSplitTrace E S (bkSwapBackForSplit a ω t) =
      bkSplitTrace E (insert a S) t := by
  classical
  ext e
  by_cases hea : e = a
  · subst e
    by_cases hrt : Sum.inr a ∈ t <;>
      by_cases hrω : Sum.inr a ∈ ω <;>
      simp [bkSwapBackForSplit, bkSetLeftFromRight, haS, hrt, hrω]
  · by_cases heS : e ∈ S <;>
      by_cases hrt : Sum.inr a ∈ t <;>
      by_cases hrω : Sum.inr a ∈ ω <;>
      simp [bkSwapBackForSplit, bkSetLeftFromRight, hea, heS, hrt, hrω]

/-- The part `C₂` of Grimmett's partition: `A' □ B_S` occurs with `x_a = 1`, but closing
`x_a` destroys that occurrence. -/
def bkStepC2 {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) : Set (Finset (Sum ι ι)) :=
  {ω | ω ∈ bkStepSource E S T U ∧ Sum.inl a ∈ ω ∧
    bkCloseLeft a ω ∉ bkStepSource E S T U}

/-- The subcase `C₂'`: in an essential-left configuration, some complement-form witness forcing
`A'` contains the left-copy coordinate `a`. -/
def bkStepC2Prime {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) : Set (Finset (Sum ι ι)) :=
  {ω | ω ∈ bkStepC2 E S a T U ∧
    ∃ K : Finset (Sum ι ι),
      K ⊆ bkTwoCopySupport E ∧ Sum.inl a ∈ K ∧
        TraceForces (bkTwoCopySupport E) K ω (bkLeftEvent E T) ∧
          TraceForces (bkTwoCopySupport E) (bkTwoCopySupport E \ K) ω
            (bkSplitEvent E S U)}

/-- The subcase `C₂''`: the essential-left configurations on which Grimmett swaps `x_a`
and `y_a`. -/
def bkStepC2DoublePrime {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) : Set (Finset (Sum ι ι)) :=
  bkStepC2 E S a T U \ bkStepC2Prime E S a T U

/-- Grimmett's page-40 map: identity off `C₂''`, and the one-coordinate swap on `C₂''`. -/
noncomputable def bkStepMap {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) (ω : Finset (Sum ι ι)) : Finset (Sum ι ι) := by
  classical
  exact if ω ∈ bkStepC2DoublePrime E S a T U then bkSwapTrace a ω else ω

theorem bkStepMap_eq_swap_of_mem {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} {ω : Finset (Sum ι ι)}
    (hω : ω ∈ bkStepC2DoublePrime E S a T U) :
    bkStepMap E S a T U ω = bkSwapTrace a ω := by
  classical
  simp [bkStepMap, hω]

theorem bkStepMap_eq_self_of_not_mem {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} {ω : Finset (Sum ι ι)}
    (hω : ω ∉ bkStepC2DoublePrime E S a T U) :
    bkStepMap E S a T U ω = ω := by
  classical
  simp [bkStepMap, hω]

theorem bkStepMap_subset_twoCopySupport {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} {ω : Finset (Sum ι ι)}
    (hω : ω ⊆ bkTwoCopySupport E) :
    bkStepMap E S a T U ω ⊆ bkTwoCopySupport E := by
  classical
  by_cases hswap : ω ∈ bkStepC2DoublePrime E S a T U
  · rw [bkStepMap_eq_swap_of_mem hswap]
    exact bkSwapTrace_subset_twoCopySupport hω
  · rw [bkStepMap_eq_self_of_not_mem hswap]
    exact hω

@[simp]
theorem bkStepMap_card {ι : Type*} (E S : Finset ι) (a : ι)
    (T U : Set (Finset ι)) (ω : Finset (Sum ι ι)) :
    (bkStepMap E S a T U ω).card = ω.card := by
  classical
  by_cases hswap : ω ∈ bkStepC2DoublePrime E S a T U
  · simp [bkStepMap_eq_swap_of_mem hswap]
  · simp [bkStepMap_eq_self_of_not_mem hswap]

/-- A right-copy coordinate is irrelevant to forcing `A'`, which only reads the left copy. -/
theorem TraceForces.erase_inr_of_bkLeftEvent {ι : Type*} {E : Finset ι}
    {K ω : Finset (Sum ι ι)}
    {a : ι} {T : Set (Finset ι)} (hω : ω ⊆ bkTwoCopySupport E)
    (hK : TraceForces (bkTwoCopySupport E) K ω (bkLeftEvent E T)) :
    TraceForces (bkTwoCopySupport E) (K.erase (Sum.inr a)) ω (bkLeftEvent E T) := by
  classical
  intro t htF hagree
  let t' : Finset (Sum ι ι) :=
    if Sum.inr a ∈ ω then insert (Sum.inr a) t else t.erase (Sum.inr a)
  have ht'F : t' ⊆ bkTwoCopySupport E := by
    intro z hz
    by_cases hωa : Sum.inr a ∈ ω
    · simp [t', hωa] at hz
      rcases hz with rfl | hzt
      · exact hω hωa
      · exact htF hzt
    · simp [t', hωa] at hz
      exact htF hz.2
  have hagree' : ∀ z ∈ K, (z ∈ t' ↔ z ∈ ω) := by
    intro z hzK
    by_cases hza : z = Sum.inr a
    · subst z
      by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa]
    · have hzErase : z ∈ K.erase (Sum.inr a) := by
        rw [Finset.mem_erase]
        exact ⟨hza, hzK⟩
      have htz := hagree z hzErase
      by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa, hza, htz]
  have ht' : t' ∈ bkLeftEvent E T := hK t' ht'F hagree'
  have hleft : bkLeftTrace E t' = bkLeftTrace E t := by
    by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa]
  simpa [bkLeftEvent, hleft] using ht'

/-- A right-copy coordinate not yet selected by the split is irrelevant to forcing `B_S`. -/
theorem TraceForces.erase_inr_of_bkSplitEvent_not_mem {ι : Type*}
    {E S : Finset ι} {K ω : Finset (Sum ι ι)} {a : ι}
    {U : Set (Finset ι)} (haS : a ∉ S) (hω : ω ⊆ bkTwoCopySupport E)
    (hK : TraceForces (bkTwoCopySupport E) K ω (bkSplitEvent E S U)) :
    TraceForces (bkTwoCopySupport E) (K.erase (Sum.inr a)) ω (bkSplitEvent E S U) := by
  classical
  intro t htF hagree
  let t' : Finset (Sum ι ι) :=
    if Sum.inr a ∈ ω then insert (Sum.inr a) t else t.erase (Sum.inr a)
  have ht'F : t' ⊆ bkTwoCopySupport E := by
    intro z hz
    by_cases hωa : Sum.inr a ∈ ω
    · simp [t', hωa] at hz
      rcases hz with rfl | hzt
      · exact hω hωa
      · exact htF hzt
    · simp [t', hωa] at hz
      exact htF hz.2
  have hagree' : ∀ z ∈ K, (z ∈ t' ↔ z ∈ ω) := by
    intro z hzK
    by_cases hza : z = Sum.inr a
    · subst z
      by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa]
    · have hzErase : z ∈ K.erase (Sum.inr a) := by
        rw [Finset.mem_erase]
        exact ⟨hza, hzK⟩
      have htz := hagree z hzErase
      by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa, hza, htz]
  have ht' : t' ∈ bkSplitEvent E S U := hK t' ht'F hagree'
  have hsplit : bkSplitTrace E S t' = bkSplitTrace E S t := by
    by_cases hωa : Sum.inr a ∈ ω <;> simp [t', hωa, haS]
  simpa [bkSplitEvent, hsplit] using ht'

/-- Before coordinate `a` is selected by the split, the source event `A' □ B_S` is insensitive
to the right-copy coordinate `a`. This is the formal ingredient used in Grimmett's injectivity
argument for the swapped `C₂''` branch. -/
theorem bkStepSource_erase_inr_of_not_mem {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S) {ω : Finset (Sum ι ι)}
    (hsrc : ω ∈ bkStepSource E S T U) :
    ω.erase (Sum.inr a) ∈ bkStepSource E S T U := by
  classical
  rw [bkStepSource] at hsrc ⊢
  rcases (mem_reimerTraceOccurrence_iff.mp hsrc) with ⟨hωF, K, hKF, hKA, hKB⟩
  let F : Finset (Sum ι ι) := bkTwoCopySupport E
  let r : Sum ι ι := Sum.inr a
  let ω0 : Finset (Sum ι ι) := ω.erase r
  let K0 : Finset (Sum ι ι) := K.erase r
  have hω0F : ω0 ⊆ F := (Finset.erase_subset _ _).trans hωF
  have hK0F : K0 ⊆ F := by
    intro z hz
    exact hKF (Finset.mem_erase.mp hz).2
  refine ⟨hω0F, K0, hK0F, ?_, ?_⟩
  · have hA0 : TraceForces F K0 ω (bkLeftEvent E T) := by
      simpa [F, K0, r] using hKA.erase_inr_of_bkLeftEvent hωF
    apply hA0.congr_trace
    intro z hz
    have hzneq : z ≠ r := (Finset.mem_erase.mp hz).1
    simp [r, hzneq]
  · have hKB' : TraceForces F (F \ K) ω (bkSplitEvent E S U) := by
      convert hKB using 1
      ext z
      simp [F, Finset.mem_sdiff]
    have hB0 : TraceForces F ((F \ K).erase r) ω (bkSplitEvent E S U) := by
      simpa [F, r] using hKB'.erase_inr_of_bkSplitEvent_not_mem haS hωF
    have hBω0 : TraceForces F ((F \ K).erase r) ω0 (bkSplitEvent E S U) := by
      apply hB0.congr_trace
      intro z hz
      have hzneq : z ≠ r := (Finset.mem_erase.mp hz).1
      simp [ω0, r, hzneq]
    apply hBω0.mono_witness
    intro z hz
    rw [Finset.mem_erase] at hz
    rcases hz with ⟨hzneq, hzFK⟩
    rw [Finset.mem_sdiff] at hzFK
    simpa [Finset.mem_sdiff, K0] using
      (show z ∈ F ∧ z ∉ K.erase r from ⟨hzFK.1, by
      intro hzK0
      exact hzFK.2 (Finset.mem_erase.mp hzK0).2⟩)

/-- The `C₁` part of Grimmett's page-40 map lands in the next split event: if the source
occurrence survives closing `x_a`, then the original configuration already lies in
`A' □ B_{S ∪ {a}}`. -/
theorem bkStepTarget_of_closeLeft_mem_source {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U)
    {ω : Finset (Sum ι ι)} (hωF : ω ⊆ bkTwoCopySupport E)
    (hclose : bkCloseLeft a ω ∈ bkStepSource E S T U) :
    ω ∈ bkStepTarget E S a T U := by
  classical
  rw [bkStepTarget, bkStepSource]
  rw [bkStepSource] at hclose
  rcases (mem_reimerTraceOccurrence_iff.mp hclose) with ⟨_hcloseF, K, hKF, hKA, hKB⟩
  let F : Finset (Sum ι ι) := bkTwoCopySupport E
  let closed : Finset (Sum ι ι) := bkCloseLeft a ω
  let K0 : Finset (Sum ι ι) := K.filter fun z ↦ z ∈ closed
  have hK0F : K0 ⊆ F := by
    intro z hz
    exact hKF (Finset.mem_filter.mp hz).1
  have hK0closed : ∀ z ∈ K0, (z ∈ ω ↔ z ∈ closed) := by
    intro z hz
    have hzclosed : z ∈ closed := (Finset.mem_filter.mp hz).2
    constructor
    · intro _
      exact hzclosed
    · intro h
      exact (Finset.erase_subset _ _) h
  refine ⟨hωF, K0, hK0F, ?_, ?_⟩
  · have hAinc : IsIncreasingTrace F (bkLeftEvent E T) :=
      isIncreasingTrace_bkLeftEvent hT
    have hKA0 : TraceForces F K0 closed (bkLeftEvent E T) := by
      convert hKA.restrict_to_open_of_increasing hAinc (by simpa [F, closed] using hclose.1)
        using 1
      ext z
      simp [K0, closed]
    exact hKA0.congr_trace hK0closed
  · have hKB0 : TraceForces F (F \ K0) closed (bkSplitEvent E S U) := by
      have hKB' : TraceForces F (F \ K) closed (bkSplitEvent E S U) := by
        convert hKB using 1
        ext z
        simp [F, Finset.mem_sdiff]
      apply hKB'.mono_witness
      intro z hz
      rw [Finset.mem_sdiff] at hz ⊢
      exact ⟨hz.1, by
        intro hzK0
        exact hz.2 (Finset.mem_filter.mp hzK0).1⟩
    intro t htF hagree
    have hclosed_t_subset : bkCloseLeft a t ⊆ F :=
      bkCloseLeft_subset_twoCopySupport htF
    have hagreeClosed : ∀ z ∈ F \ K0, (z ∈ bkCloseLeft a t ↔ z ∈ closed) := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      by_cases hza : z = Sum.inl a
      · subst z
        simp [bkCloseLeft, closed]
      · have hag := hagree z (by simpa [Finset.mem_sdiff] using hz)
        simpa [bkCloseLeft, closed, hza] using hag
    have hBS : bkCloseLeft a t ∈ bkSplitEvent E S U :=
      hKB0 (bkCloseLeft a t) hclosed_t_subset hagreeClosed
    have hsubset := bkSplitTrace_bkCloseLeft_subset_insert E S haS t
    exact hU hsubset (bkSplitTrace_subset E (insert a S) t) hBS

/-- The `C₂'` part of Grimmett's page-40 map also lands in the next split event without
swapping: the witness for `A'` contains `x_a`, so the complementary witness for `B_S` may
freely replace the left value by the right value. -/
theorem bkStepTarget_of_mem_c2Prime {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S) {ω : Finset (Sum ι ι)}
    (hω : ω ∈ bkStepC2Prime E S a T U) :
    ω ∈ bkStepTarget E S a T U := by
  classical
  rw [bkStepTarget, bkStepSource]
  rw [bkStepC2Prime] at hω
  rcases hω with ⟨hC2, K, hKF, haK, hKA, hKB⟩
  rw [bkStepC2] at hC2
  rcases hC2 with ⟨hsrc, _haopen, _hclose⟩
  rw [bkStepSource] at hsrc
  have hωF : ω ⊆ bkTwoCopySupport E := (mem_reimerTraceOccurrence_iff.mp hsrc).1
  refine ⟨hωF, K, hKF, hKA, ?_⟩
  intro t htF hagree
  have hsetF : bkSetLeftFromRight a t ⊆ bkTwoCopySupport E :=
    bkSetLeftFromRight_subset_twoCopySupport htF
  have hagreeSet : ∀ z ∈ bkTwoCopySupport E \ K,
      (z ∈ bkSetLeftFromRight a t ↔ z ∈ ω) := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    by_cases hza : z = Sum.inl a
    · subst z
      exact (hz.2 haK).elim
    · have hag := hagree z (by simpa [Finset.mem_sdiff] using hz)
      by_cases hra : Sum.inr a ∈ t <;> simp [bkSetLeftFromRight, hra, hza, hag]
  have hBS : bkSetLeftFromRight a t ∈ bkSplitEvent E S U :=
    hKB (bkSetLeftFromRight a t) hsetF hagreeSet
  simpa [bkSplitEvent, bkSplitTrace_setLeftFromRight_eq_insert_of_not_mem E S haS t]
    using hBS

/-- The swapped `C₂''` branch of Grimmett's page-40 map lands in the next split event. -/
theorem bkStepTarget_swap_of_mem_c2DoublePrime {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S) {ω : Finset (Sum ι ι)}
    (hω : ω ∈ bkStepC2DoublePrime E S a T U) :
    bkSwapTrace a ω ∈ bkStepTarget E S a T U := by
  classical
  rw [bkStepC2DoublePrime] at hω
  rcases hω with ⟨hC2, hnotPrime⟩
  rw [bkStepC2] at hC2
  rcases hC2 with ⟨hsrc, haopen, hclose⟩
  rw [bkStepSource] at hsrc
  rcases (mem_reimerTraceOccurrence_iff.mp hsrc) with ⟨hωF, K, hKF, hKA, hKB⟩
  have hKB' : TraceForces (bkTwoCopySupport E) (bkTwoCopySupport E \ K) ω
      (bkSplitEvent E S U) := by
    convert hKB using 1
    ext z
    simp [Finset.mem_sdiff]
  have hnotInlK : Sum.inl a ∉ K := by
    intro haK
    exact hnotPrime ⟨by
      rw [bkStepC2]
      exact ⟨by simpa [bkStepSource] using hsrc, haopen, hclose⟩,
      K, hKF, haK, hKA, hKB'⟩
  let Kt : Finset (Sum ι ι) := K.erase (Sum.inr a)
  have hKtF : Kt ⊆ bkTwoCopySupport E := by
    intro z hz
    exact hKF (Finset.mem_erase.mp hz).2
  rw [bkStepTarget, bkStepSource]
  refine ⟨bkSwapTrace_subset_twoCopySupport hωF, Kt, hKtF, ?_, ?_⟩
  · have hKAerase : TraceForces (bkTwoCopySupport E) Kt ω (bkLeftEvent E T) := by
      simpa [Kt] using hKA.erase_inr_of_bkLeftEvent hωF
    apply hKAerase.congr_trace
    intro z hz
    rw [Finset.mem_erase] at hz
    rcases hz with ⟨hzneInr, hzK⟩
    cases z with
    | inl e =>
        by_cases hea : e = a
        · subst e
          exact (hnotInlK hzK).elim
        · simp [hea]
    | inr e =>
        by_cases hea : e = a
        · subst e
          exact (hzneInr rfl).elim
        · simp [hea]
  · intro t htF hagree
    have hbackF : bkSwapBackForSplit a ω t ⊆ bkTwoCopySupport E :=
      bkSwapBackForSplit_subset_twoCopySupport hωF htF
    have hagreeBack : ∀ z ∈ bkTwoCopySupport E \ K,
        (z ∈ bkSwapBackForSplit a ω t ↔ z ∈ ω) := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      cases z with
      | inl e =>
          by_cases hea : e = a
          · subst e
            have haE : a ∈ E := by simpa using hz.1
            have hag := hagree (Sum.inr a) (by
              simp [Finset.mem_sdiff, Kt, haE])
            rw [inr_mem_bkSwapTrace_iff] at hag
            simp [haopen] at hag
            by_cases hrω : Sum.inr a ∈ ω <;>
              simp [bkSwapBackForSplit, bkSetLeftFromRight, hrω, hag, haopen]
          · have hag := hagree (Sum.inl e) (by
              simpa [Finset.mem_sdiff, Kt] using
                (show Sum.inl e ∈ bkTwoCopySupport E ∧ Sum.inl e ∉ K.erase (Sum.inr a)
                  from ⟨hz.1, by
                intro hmem
                exact hz.2 (Finset.mem_erase.mp hmem).2⟩))
            rw [inl_mem_bkSwapTrace_iff] at hag
            simp [hea] at hag
            by_cases hrω : Sum.inr a ∈ ω <;>
              by_cases hrt : Sum.inr a ∈ t <;>
              simpa [bkSwapBackForSplit, bkSetLeftFromRight, hea, hrω, hrt] using hag
      | inr e =>
          by_cases hea : e = a
          · subst e
            by_cases hrω : Sum.inr a ∈ ω <;>
              simp [bkSwapBackForSplit, bkSetLeftFromRight, hrω]
          · have hag := hagree (Sum.inr e) (by
              simpa [Finset.mem_sdiff, Kt] using
                (show Sum.inr e ∈ bkTwoCopySupport E ∧ Sum.inr e ∉ K.erase (Sum.inr a)
                  from ⟨hz.1, by
                intro hmem
                exact hz.2 (Finset.mem_erase.mp hmem).2⟩))
            rw [inr_mem_bkSwapTrace_iff] at hag
            simp [hea] at hag
            by_cases hrω : Sum.inr a ∈ ω <;>
              by_cases hrt : Sum.inr a ∈ t <;>
              simpa [bkSwapBackForSplit, bkSetLeftFromRight, hea, hrω, hrt] using hag
    have hBS : bkSwapBackForSplit a ω t ∈ bkSplitEvent E S U :=
      hKB' (bkSwapBackForSplit a ω t) hbackF hagreeBack
    simpa [bkSplitEvent, bkSplitTrace_swapBackForSplit_eq_insert_of_not_mem E S haS ω t]
      using hBS

/-- Grimmett's page-40 map sends every source configuration into the next split target. -/
theorem bkStepMap_mem_target {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U)
    {ω : Finset (Sum ι ι)} (hsrc : ω ∈ bkStepSource E S T U) :
    bkStepMap E S a T U ω ∈ bkStepTarget E S a T U := by
  classical
  have hωF : ω ⊆ bkTwoCopySupport E := by
    rw [bkStepSource] at hsrc
    exact (mem_reimerTraceOccurrence_iff.mp hsrc).1
  by_cases hswap : ω ∈ bkStepC2DoublePrime E S a T U
  · rw [bkStepMap_eq_swap_of_mem hswap]
    exact bkStepTarget_swap_of_mem_c2DoublePrime haS hswap
  · rw [bkStepMap_eq_self_of_not_mem hswap]
    by_cases hclose : bkCloseLeft a ω ∈ bkStepSource E S T U
    · exact bkStepTarget_of_closeLeft_mem_source haS hT hU hωF hclose
    · by_cases haopen : Sum.inl a ∈ ω
      · have hC2 : ω ∈ bkStepC2 E S a T U := by
          rw [bkStepC2]
          exact ⟨hsrc, haopen, hclose⟩
        have hPrime : ω ∈ bkStepC2Prime E S a T U := by
          by_contra hnotPrime
          exact hswap ⟨hC2, hnotPrime⟩
        exact bkStepTarget_of_mem_c2Prime haS hPrime
      · have hclose' : bkCloseLeft a ω ∈ bkStepSource E S T U := by
          simpa [bkCloseLeft, Finset.erase_eq_of_notMem haopen] using hsrc
        exact (hclose hclose').elim

/-- A swapped `C₂''` source point cannot collide with an identity-branch source point. This is
the formal version of Grimmett's injectivity paragraph after (2.22). -/
theorem bkStepMap_cross_collision_false {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S) {ω η : Finset (Sum ι ι)}
    (hωswap : ω ∈ bkStepC2DoublePrime E S a T U)
    (hηsrc : η ∈ bkStepSource E S T U)
    (hηnot : η ∉ bkStepC2DoublePrime E S a T U)
    (heq : bkSwapTrace a ω = η) : False := by
  classical
  rw [bkStepC2DoublePrime] at hωswap
  rcases hωswap with ⟨hωC2, hωnotPrime⟩
  rw [bkStepC2] at hωC2
  rcases hωC2 with ⟨hωsrc, haopen, hclose⟩
  by_cases hr : Sum.inr a ∈ ω
  · have hfix := bkSwapTrace_eq_self_of_mem_inl_of_mem_inr a ω haopen hr
    have hηeq : η = ω := by
      rw [← heq, hfix]
    exact hηnot (by
      simpa [hηeq] using
        (show ω ∈ bkStepC2DoublePrime E S a T U from
          ⟨by rw [bkStepC2]; exact ⟨hωsrc, haopen, hclose⟩, hωnotPrime⟩))
  · have hswapSrc : bkSwapTrace a ω ∈ bkStepSource E S T U := by
      simpa [heq] using hηsrc
    have heraseSrc := bkStepSource_erase_inr_of_not_mem (E := E) (S := S) (a := a)
      (T := T) (U := U) haS hswapSrc
    have hclosedEq :=
      bkSwapTrace_erase_inr_eq_closeLeft_of_not_mem_inr a ω hr
    exact hclose (by simpa [hclosedEq] using heraseSrc)

/-- Grimmett's page-40 map is injective on the source event `A' □ B_S`. -/
theorem bkStepMap_injOn_source {ι : Type*} {E S : Finset ι} {a : ι}
    {T U : Set (Finset ι)} (haS : a ∉ S) :
    Set.InjOn (bkStepMap E S a T U) (bkStepSource E S T U) := by
  classical
  intro ω hω η hη hmap
  by_cases hωswap : ω ∈ bkStepC2DoublePrime E S a T U
  · by_cases hηswap : η ∈ bkStepC2DoublePrime E S a T U
    · rw [bkStepMap_eq_swap_of_mem hωswap, bkStepMap_eq_swap_of_mem hηswap] at hmap
      have h := congrArg (bkSwapTrace a) hmap
      simpa using h
    · rw [bkStepMap_eq_swap_of_mem hωswap, bkStepMap_eq_self_of_not_mem hηswap] at hmap
      exact (bkStepMap_cross_collision_false haS hωswap hη hηswap hmap).elim
  · by_cases hηswap : η ∈ bkStepC2DoublePrime E S a T U
    · rw [bkStepMap_eq_self_of_not_mem hωswap, bkStepMap_eq_swap_of_mem hηswap] at hmap
      exact (bkStepMap_cross_collision_false haS hηswap hω hωswap hmap.symm).elim
    · rw [bkStepMap_eq_self_of_not_mem hωswap, bkStepMap_eq_self_of_not_mem hηswap] at hmap
      exact hmap

/-- Grimmett equation (2.21), the one-coordinate split step in the BK proof. -/
theorem finiteBernoulliEventProbability_bkStepSource_le_target {ι : Type*}
    {E S : Finset ι} {a : ι} {T U : Set (Finset ι)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (haS : a ∉ S)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E S T U) ≤
      finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepTarget E S a T U) := by
  classical
  refine finiteBernoulliEventProbability_le_of_injOn_card_eq hp0 hp1
    (bkStepMap E S a T U) ?_ ?_ ?_
  · intro s hsF hsrc
    exact ⟨bkStepMap_subset_twoCopySupport hsF, bkStepMap_mem_target haS hT hU hsrc⟩
  · intro s hs t ht hst
    exact bkStepMap_injOn_source haS hs.2 ht.2 hst
  · intro s _hsF _hsrc
    exact bkStepMap_card E S a T U s

/-- Heterogeneous form of Grimmett equation (2.21), the one-coordinate split step in the BK
proof. The two copies use the same coordinate probability `q e`, so the swap branch preserves
the product weight. -/
theorem finiteBernoulliHeteroEventProbability_bkStepSource_le_target {ι : Type*}
    {E S : Finset ι} {a : ι} {T U : Set (Finset ι)} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1) (haS : a ∉ S)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E S T U) ≤
      finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepTarget E S a T U) := by
  classical
  refine finiteBernoulliHeteroEventProbability_le_of_injOn_weight_eq ?_ ?_
    (bkStepMap E S a T U) ?_ ?_ ?_
  · intro z hz
    cases z with
    | inl e =>
        exact hq0 e ((inl_mem_bkTwoCopySupport_iff E e).mp hz)
    | inr e =>
        exact hq0 e ((inr_mem_bkTwoCopySupport_iff E e).mp hz)
  · intro z hz
    cases z with
    | inl e =>
        exact hq1 e ((inl_mem_bkTwoCopySupport_iff E e).mp hz)
    | inr e =>
        exact hq1 e ((inr_mem_bkTwoCopySupport_iff E e).mp hz)
  · intro s hsF hsrc
    exact ⟨bkStepMap_subset_twoCopySupport hsF, bkStepMap_mem_target haS hT hU hsrc⟩
  · intro s hs t ht hst
    exact bkStepMap_injOn_source haS hs.2 ht.2 hst
  · intro s _hsF _hsrc
    by_cases hswap : s ∈ bkStepC2DoublePrime E S a T U
    · rw [bkStepMap_eq_swap_of_mem hswap]
      exact bkSwapTrace_heteroWeight_prod E q a s
    · rw [bkStepMap_eq_self_of_not_mem hswap]

/-- Telescoping Grimmett's one-coordinate step from `B_0` to `B_S`. -/
theorem finiteBernoulliEventProbability_bkStepSource_empty_le {ι : Type*}
    (E S : Finset ι) {T U : Set (Finset ι)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) (hS : S ⊆ E) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) ≤
      finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E S T U) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rfl
  | insert a S ha ih =>
      have hSE : S ⊆ E := by
        intro e he
        exact hS (Finset.mem_insert_of_mem he)
      have hstep := finiteBernoulliEventProbability_bkStepSource_le_target
        (E := E) (S := S) (a := a) (T := T) (U := U) (p := p) hp0 hp1 ha hT hU
      calc
        finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) ≤
            finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E S T U) :=
          ih hSE
        _ ≤ finiteBernoulliEventProbability (bkTwoCopySupport E) p
            (bkStepSource E (insert a S) T U) := by
          simpa [bkStepTarget] using hstep

/-- Grimmett's telescoped split inequality `P(A' □ B_0) ≤ P(A' □ B_m)`. -/
theorem finiteBernoulliEventProbability_bkStepSource_empty_le_self {ι : Type*}
    (E : Finset ι) {T U : Set (Finset ι)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) ≤
      finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E E T U) :=
  finiteBernoulliEventProbability_bkStepSource_empty_le E E hp0 hp1 hT hU
    (by intro e he; exact he)

/-- Heterogeneous telescoping form `P(A' □ B_0) ≤ P(A' □ B_S)`. -/
theorem finiteBernoulliHeteroEventProbability_bkStepSource_empty_le {ι : Type*}
    (E S : Finset ι) {T U : Set (Finset ι)} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) (hS : S ⊆ E) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E ∅ T U) ≤
      finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E S T U) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rfl
  | insert a S ha ih =>
      have hSE : S ⊆ E := by
        intro e he
        exact hS (Finset.mem_insert_of_mem he)
      have hstep := finiteBernoulliHeteroEventProbability_bkStepSource_le_target
        (E := E) (S := S) (a := a) (T := T) (U := U) (q := q)
        hq0 hq1 ha hT hU
      calc
        finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
            (bkStepSource E ∅ T U) ≤
          finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
            (bkStepSource E S T U) :=
          ih hSE
        _ ≤ finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
            (bkStepSource E (insert a S) T U) := by
          simpa [bkStepTarget] using hstep

/-- Heterogeneous telescoped split inequality `P(A' □ B_0) ≤ P(A' □ B_m)`. -/
theorem finiteBernoulliHeteroEventProbability_bkStepSource_empty_le_self {ι : Type*}
    (E : Finset ι) {T U : Set (Finset ι)} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E ∅ T U) ≤
      finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E E T U) :=
  finiteBernoulliHeteroEventProbability_bkStepSource_empty_le E E hq0 hq1 hT hU
    (by intro e he; exact he)

/-- The endpoint `A' ∩ B_m` in Grimmett's two-copy proof factors into the product of the
one-copy probabilities. -/
theorem finiteBernoulliEventProbability_twoCopy_left_right {ι : Type*}
    (E : Finset ι) (p : ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U} =
      finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U := by
  classical
  rw [finiteBernoulliEventProbability_eq_sum_traceFamily,
    finiteBernoulliEventProbability_eq_sum_traceFamily,
    finiteBernoulliEventProbability_eq_sum_traceFamily]
  let F : Finset (Sum ι ι) := bkTwoCopySupport E
  let A : Set (Finset (Sum ι ι)) :=
    {ω | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U}
  let SF : Finset (Finset (Sum ι ι)) := finiteTraceEventFamily F A
  let ST : Finset (Finset ι) := finiteTraceEventFamily E T
  let SU : Finset (Finset ι) := finiteTraceEventFamily E U
  let wF : Finset (Sum ι ι) → ℝ := fun ω ↦ p ^ ω.card * (1 - p) ^ (F.card - ω.card)
  let wE : Finset ι → ℝ := fun s ↦ p ^ s.card * (1 - p) ^ (E.card - s.card)
  change SF.sum wF = ST.sum wE * SU.sum wE
  have hbij :
      SF.sum wF = (ST.product SU).sum (fun st ↦ wF (bkTracePairSet st.1 st.2)) := by
    refine Finset.sum_bij'
      (fun ω _hω ↦ (bkLeftTrace E ω, bkRightTrace E ω))
      (fun st _hst ↦ bkTracePairSet st.1 st.2) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      change (bkLeftTrace E ω, bkRightTrace E ω) ∈ ST ×ˢ SU
      exact Finset.mem_product.mpr ⟨
        (mem_finiteTraceEventFamily_iff E T (bkLeftTrace E ω)).mpr
          ⟨bkLeftTrace_subset E ω, hω'.2.1⟩,
        (mem_finiteTraceEventFamily_iff E U (bkRightTrace E ω)).mpr
          ⟨bkRightTrace_subset E ω, hω'.2.2⟩⟩
    · intro st hst
      have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
        change st ∈ ST ×ˢ SU at hst
        exact Finset.mem_product.mp hst
      have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
      have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
      have hpairF : bkTracePairSet st.1 st.2 ⊆ F := by
        simpa [F] using bkTracePairSet_subset_twoCopySupport hs.1 ht.1
      have hleft : bkLeftTrace E (bkTracePairSet st.1 st.2) ∈ T := by
        simpa [bkLeftTrace_bkTracePairSet hs.1] using hs.2
      have hright : bkRightTrace E (bkTracePairSet st.1 st.2) ∈ U := by
        simpa [bkRightTrace_bkTracePairSet ht.1] using ht.2
      exact (mem_finiteTraceEventFamily_iff F A (bkTracePairSet st.1 st.2)).mpr
        ⟨hpairF, hleft, hright⟩
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      exact bkTracePairSet_left_right (E := E) (ω := ω) (by simpa [F] using hω'.1)
    · intro st hst
      have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
        change st ∈ ST ×ˢ SU at hst
        exact Finset.mem_product.mp hst
      have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
      have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
      ext <;> simp [bkLeftTrace_bkTracePairSet hs.1, bkRightTrace_bkTracePairSet ht.1]
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      change wF ω = wF (bkTracePairSet (bkLeftTrace E ω) (bkRightTrace E ω))
      rw [bkTracePairSet_left_right (E := E) (ω := ω) (by simpa [F] using hω'.1)]
  rw [hbij]
  have hweight : ∀ st ∈ ST.product SU,
      wF (bkTracePairSet st.1 st.2) = wE st.1 * wE st.2 := by
    intro st hst
    have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
      change st ∈ ST ×ˢ SU at hst
      exact Finset.mem_product.mp hst
    have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
    have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
    have hsle : st.1.card ≤ E.card := Finset.card_le_card hs.1
    have htle : st.2.card ≤ E.card := Finset.card_le_card ht.1
    have hcardSub : E.card + E.card - (st.1.card + st.2.card) =
        (E.card - st.1.card) + (E.card - st.2.card) := by
      omega
    simp only [wF, wE, F, bkTracePairSet_card, bkTwoCopySupport_card]
    rw [hcardSub, pow_add, pow_add]
    ring
  calc
    (ST.product SU).sum (fun st ↦ wF (bkTracePairSet st.1 st.2)) =
        (ST.product SU).sum (fun st ↦ wE st.1 * wE st.2) := by
      apply Finset.sum_congr rfl
      intro st hst
      exact hweight st hst
    _ = ST.sum wE * SU.sum wE := by
      change (∑ st ∈ ST ×ˢ SU, wE st.1 * wE st.2) = ST.sum wE * SU.sum wE
      rw [Finset.sum_product]
      rw [← Finset.sum_mul_sum]

/-- Heterogeneous form of the `B_m` endpoint in Grimmett's two-copy proof: the left and
right-copy coordinates are independent and use the same coordinate probabilities. -/
theorem finiteBernoulliHeteroEventProbability_twoCopy_left_right {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U} =
      finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q U := by
  classical
  rw [finiteBernoulliHeteroEventProbability_eq_sum_traceFamily,
    finiteBernoulliHeteroEventProbability_eq_sum_traceFamily,
    finiteBernoulliHeteroEventProbability_eq_sum_traceFamily]
  let F : Finset (Sum ι ι) := bkTwoCopySupport E
  let A : Set (Finset (Sum ι ι)) :=
    {ω | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U}
  let SF : Finset (Finset (Sum ι ι)) := finiteTraceEventFamily F A
  let ST : Finset (Finset ι) := finiteTraceEventFamily E T
  let SU : Finset (Finset ι) := finiteTraceEventFamily E U
  let wF : Finset (Sum ι ι) → ℝ :=
    finiteBernoulliHeteroTraceWeight F (Sum.elim q q)
  let wE : Finset ι → ℝ := finiteBernoulliHeteroTraceWeight E q
  change SF.sum wF = ST.sum wE * SU.sum wE
  have hbij :
      SF.sum wF = (ST.product SU).sum (fun st ↦ wF (bkTracePairSet st.1 st.2)) := by
    refine Finset.sum_bij'
      (fun ω _hω ↦ (bkLeftTrace E ω, bkRightTrace E ω))
      (fun st _hst ↦ bkTracePairSet st.1 st.2) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      change (bkLeftTrace E ω, bkRightTrace E ω) ∈ ST ×ˢ SU
      exact Finset.mem_product.mpr ⟨
        (mem_finiteTraceEventFamily_iff E T (bkLeftTrace E ω)).mpr
          ⟨bkLeftTrace_subset E ω, hω'.2.1⟩,
        (mem_finiteTraceEventFamily_iff E U (bkRightTrace E ω)).mpr
          ⟨bkRightTrace_subset E ω, hω'.2.2⟩⟩
    · intro st hst
      have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
        change st ∈ ST ×ˢ SU at hst
        exact Finset.mem_product.mp hst
      have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
      have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
      have hpairF : bkTracePairSet st.1 st.2 ⊆ F := by
        simpa [F] using bkTracePairSet_subset_twoCopySupport hs.1 ht.1
      have hleft : bkLeftTrace E (bkTracePairSet st.1 st.2) ∈ T := by
        simpa [bkLeftTrace_bkTracePairSet hs.1] using hs.2
      have hright : bkRightTrace E (bkTracePairSet st.1 st.2) ∈ U := by
        simpa [bkRightTrace_bkTracePairSet ht.1] using ht.2
      exact (mem_finiteTraceEventFamily_iff F A (bkTracePairSet st.1 st.2)).mpr
        ⟨hpairF, hleft, hright⟩
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      exact bkTracePairSet_left_right (E := E) (ω := ω) (by simpa [F] using hω'.1)
    · intro st hst
      have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
        change st ∈ ST ×ˢ SU at hst
        exact Finset.mem_product.mp hst
      have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
      have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
      ext <;> simp [bkLeftTrace_bkTracePairSet hs.1, bkRightTrace_bkTracePairSet ht.1]
    · intro ω hω
      have hω' : ω ⊆ F ∧ ω ∈ A := by
        simpa [SF, mem_finiteTraceEventFamily_iff] using hω
      change wF ω = wF (bkTracePairSet (bkLeftTrace E ω) (bkRightTrace E ω))
      rw [bkTracePairSet_left_right (E := E) (ω := ω) (by simpa [F] using hω'.1)]
  rw [hbij]
  have hweight : ∀ st ∈ ST.product SU,
      wF (bkTracePairSet st.1 st.2) = wE st.1 * wE st.2 := by
    intro st hst
    have hst' : st.1 ∈ ST ∧ st.2 ∈ SU := by
      change st ∈ ST ×ˢ SU at hst
      exact Finset.mem_product.mp hst
    have hs := (mem_finiteTraceEventFamily_iff E T st.1).mp hst'.1
    have ht := (mem_finiteTraceEventFamily_iff E U st.2).mp hst'.2
    unfold wF wE finiteBernoulliHeteroTraceWeight
    rw [bkTwoCopySupport_prod]
    simp [inl_mem_bkTracePairSet_iff, inr_mem_bkTracePairSet_iff]
  calc
    (ST.product SU).sum (fun st ↦ wF (bkTracePairSet st.1 st.2)) =
        (ST.product SU).sum (fun st ↦ wE st.1 * wE st.2) := by
      apply Finset.sum_congr rfl
      intro st hst
      exact hweight st hst
    _ = ST.sum wE * SU.sum wE := by
      change (∑ st ∈ ST ×ˢ SU, wE st.1 * wE st.2) = ST.sum wE * SU.sum wE
      rw [Finset.sum_product]
      rw [← Finset.sum_mul_sum]

/-- The `B_0` endpoint in Grimmett's proof: if both two-copy events read the left copy, their
box occurrence is exactly the original one-copy box occurrence read from the left trace. -/
theorem mem_bkStepSource_empty_iff {ι : Type*} {E : Finset ι}
    {ω : Finset (Sum ι ι)} {T U : Set (Finset ι)}
    (hωF : ω ⊆ bkTwoCopySupport E) :
    ω ∈ bkStepSource E ∅ T U ↔ bkLeftTrace E ω ∈ ReimerTraceOccurrence E T U := by
  classical
  constructor
  · intro hsrc
    rw [bkStepSource] at hsrc
    rcases (mem_reimerTraceOccurrence_iff.mp hsrc) with ⟨_hωF, K, hKF, hKT, hKU⟩
    refine mem_reimerTraceOccurrence_iff.mpr ?_
    refine ⟨bkLeftTrace_subset E ω, bkLeftTrace E K, bkLeftTrace_subset E K,
      hKT.bkLeftEvent_to_leftTrace hKF, ?_⟩
    intro t htE hagree
    have hpairF : bkTracePairSet t (bkRightTrace E ω) ⊆ bkTwoCopySupport E :=
      bkTracePairSet_subset_twoCopySupport htE (bkRightTrace_subset E ω)
    have hagreeF :
        ∀ z ∈ @sdiff (Finset (Sum ι ι))
          (@Finset.instSDiff (Sum ι ι) (Classical.decEq (Sum ι ι)))
          (bkTwoCopySupport E) K,
          (z ∈ bkTracePairSet t (bkRightTrace E ω) ↔ z ∈ ω) := by
      intro z hz
      cases z with
      | inl e =>
          have hz' := (@Finset.mem_sdiff (Sum ι ι)
            (Classical.decEq (Sum ι ι)) (bkTwoCopySupport E) K
            (Sum.inl e)).mp hz
          have heE : e ∈ E := by
            exact (inl_mem_bkTwoCopySupport_iff E e).mp hz'.1
          have hnotK : Sum.inl e ∉ K := hz'.2
          have heLeft : e ∈ E \ bkLeftTrace E K := by
            rw [Finset.mem_sdiff, mem_bkLeftTrace_iff]
            exact ⟨heE, by simpa [heE] using hnotK⟩
          have heagree := hagree e heLeft
          simpa [mem_bkLeftTrace_iff, heE] using heagree
      | inr e =>
          have hz' := (@Finset.mem_sdiff (Sum ι ι)
            (Classical.decEq (Sum ι ι)) (bkTwoCopySupport E) K
            (Sum.inr e)).mp hz
          have heE : e ∈ E := by
            exact (inr_mem_bkTwoCopySupport_iff E e).mp hz'.1
          simp [mem_bkRightTrace_iff, heE]
    have hmem := hKU (bkTracePairSet t (bkRightTrace E ω)) hpairF hagreeF
    change bkSplitTrace E ∅ (bkTracePairSet t (bkRightTrace E ω)) ∈ U at hmem
    simpa [bkSplitTrace_empty, bkLeftTrace_bkTracePairSet htE] using hmem
  · intro hleft
    rw [bkStepSource]
    rcases (mem_reimerTraceOccurrence_iff.mp hleft) with ⟨_hsE, K, hKE, hKT, hKU⟩
    refine mem_reimerTraceOccurrence_iff.mpr ?_
    refine ⟨hωF, bkTracePairSet K ∅, ?_, ?_, ?_⟩
    · exact bkTracePairSet_subset_twoCopySupport hKE (Finset.empty_subset E)
    · exact hKT.leftTrace_to_bkLeftEvent hKE
    · intro η _hηF hagree
      change bkSplitTrace E ∅ η ∈ U
      rw [bkSplitTrace_empty]
      exact hKU (bkLeftTrace E η) (bkLeftTrace_subset E η) (by
        intro e heEK
        have heE : e ∈ E := (Finset.mem_sdiff.mp heEK).1
        have heK : e ∉ K := (Finset.mem_sdiff.mp heEK).2
        have heagree := hagree (Sum.inl e)
          ((@Finset.mem_sdiff (Sum ι ι)
            (Classical.decEq (Sum ι ι)) (bkTwoCopySupport E)
            (bkTracePairSet K ∅) (Sum.inl e)).mpr
            ⟨by simpa using heE, by simp [heK]⟩)
        simpa [mem_bkLeftTrace_iff, heE] using heagree)

/-- A left-copy cylinder in the two-copy cube has the same finite Bernoulli probability as its
one-copy marginal. -/
theorem finiteBernoulliEventProbability_twoCopy_left {ι : Type*}
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T} =
      finiteBernoulliEventProbability E p T := by
  calc
    finiteBernoulliEventProbability (bkTwoCopySupport E) p
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T} =
        finiteBernoulliEventProbability (bkTwoCopySupport E) p
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧
            bkRightTrace E ω ∈ (Set.univ : Set (Finset ι))} := by
      refine finiteBernoulliEventProbability_congr ?_
      intro ω _hωF
      simp
    _ = finiteBernoulliEventProbability E p T *
        finiteBernoulliEventProbability E p (Set.univ : Set (Finset ι)) := by
      exact finiteBernoulliEventProbability_twoCopy_left_right E p T Set.univ
    _ = finiteBernoulliEventProbability E p T := by
      simp

/-- Heterogeneous left-copy cylinder marginal in the two-copy cube. -/
theorem finiteBernoulliHeteroEventProbability_twoCopy_left {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T} =
      finiteBernoulliHeteroEventProbability E q T := by
  calc
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T} =
        finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧
            bkRightTrace E ω ∈ (Set.univ : Set (Finset ι))} := by
      refine finiteBernoulliHeteroEventProbability_congr ?_
      intro ω _hωF
      simp
    _ = finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q (Set.univ : Set (Finset ι)) := by
      exact finiteBernoulliHeteroEventProbability_twoCopy_left_right E q T Set.univ
    _ = finiteBernoulliHeteroEventProbability E q T := by
      simp

/-- Probability form of Grimmett's `B_0` endpoint. -/
theorem finiteBernoulliEventProbability_bkStepSource_empty {ι : Type*}
    (E : Finset ι) (p : ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) =
      finiteBernoulliEventProbability E p (ReimerTraceOccurrence E T U) := by
  calc
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) =
        finiteBernoulliEventProbability (bkTwoCopySupport E) p
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ ReimerTraceOccurrence E T U} := by
      refine finiteBernoulliEventProbability_congr ?_
      intro ω hωF
      exact mem_bkStepSource_empty_iff hωF
    _ = finiteBernoulliEventProbability E p (ReimerTraceOccurrence E T U) :=
      finiteBernoulliEventProbability_twoCopy_left E p (ReimerTraceOccurrence E T U)

/-- Heterogeneous probability form of Grimmett's `B_0` endpoint. -/
theorem finiteBernoulliHeteroEventProbability_bkStepSource_empty {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E ∅ T U) =
      finiteBernoulliHeteroEventProbability E q (ReimerTraceOccurrence E T U) := by
  calc
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E ∅ T U) =
        finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ ReimerTraceOccurrence E T U} := by
      refine finiteBernoulliHeteroEventProbability_congr ?_
      intro ω hωF
      exact mem_bkStepSource_empty_iff hωF
    _ = finiteBernoulliHeteroEventProbability E q (ReimerTraceOccurrence E T U) :=
      finiteBernoulliHeteroEventProbability_twoCopy_left E q (ReimerTraceOccurrence E T U)

/-- The `B_m` endpoint in Grimmett's proof: left-copy and right-copy events use disjoint
coordinates, so box occurrence is ordinary simultaneous occurrence. -/
theorem mem_bkStepSource_self_iff {ι : Type*} {E : Finset ι}
    {ω : Finset (Sum ι ι)} {T U : Set (Finset ι)}
    (hωF : ω ⊆ bkTwoCopySupport E) :
    ω ∈ bkStepSource E E T U ↔ bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U := by
  classical
  constructor
  · intro hsrc
    rw [bkStepSource] at hsrc
    rcases (mem_reimerTraceOccurrence_iff.mp hsrc) with ⟨hωF', _K, _hKF, hKT, hKU⟩
    exact ⟨by simpa [bkLeftEvent] using hKT.mem hωF',
      by simpa [bkSplitEvent] using hKU.mem hωF'⟩
  · rintro ⟨hT, hU⟩
    rw [bkStepSource]
    refine mem_reimerTraceOccurrence_iff.mpr ?_
    refine ⟨hωF, bkTracePairSet E ∅, ?_, ?_, ?_⟩
    · exact bkTracePairSet_subset_twoCopySupport (by intro e he; exact he) (Finset.empty_subset E)
    · have hfull : TraceForces E E (bkLeftTrace E ω) T :=
        (traceForces_full_iff (bkLeftTrace_subset E ω)).mpr hT
      exact hfull.leftTrace_to_bkLeftEvent (by intro e he; exact he)
    · intro η _hηF hagree
      change bkSplitTrace E E η ∈ U
      rw [bkSplitTrace_self]
      have hright : bkRightTrace E η = bkRightTrace E ω := by
        ext e
        by_cases heE : e ∈ E
        · have heagree := hagree (Sum.inr e)
            ((@Finset.mem_sdiff (Sum ι ι)
              (Classical.decEq (Sum ι ι)) (bkTwoCopySupport E)
              (bkTracePairSet E ∅) (Sum.inr e)).mpr
              ⟨by simpa using heE, by simp⟩)
          simpa [mem_bkRightTrace_iff, heE] using heagree
        · simp [mem_bkRightTrace_iff, heE]
      simpa [hright] using hU

/-- Probability form of Grimmett's `B_m` endpoint. -/
theorem finiteBernoulliEventProbability_bkStepSource_self {ι : Type*}
    (E : Finset ι) (p : ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E E T U) =
      finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U := by
  calc
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E E T U) =
        finiteBernoulliEventProbability (bkTwoCopySupport E) p
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U} := by
      refine finiteBernoulliEventProbability_congr ?_
      intro ω hωF
      exact mem_bkStepSource_self_iff hωF
    _ = finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U :=
      finiteBernoulliEventProbability_twoCopy_left_right E p T U

/-- Heterogeneous probability form of Grimmett's `B_m` endpoint. -/
theorem finiteBernoulliHeteroEventProbability_bkStepSource_self {ι : Type*}
    (E : Finset ι) (q : ι → ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E E T U) =
      finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q U := by
  calc
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E E T U) =
        finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
          {ω : Finset (Sum ι ι) | bkLeftTrace E ω ∈ T ∧ bkRightTrace E ω ∈ U} := by
      refine finiteBernoulliHeteroEventProbability_congr ?_
      intro ω hωF
      exact mem_bkStepSource_self_iff hωF
    _ = finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q U :=
      finiteBernoulliHeteroEventProbability_twoCopy_left_right E q T U

/-- Finite-trace BK inequality, proved directly by Grimmett's two-copy split-coordinate proof.
The occurrence operation is the open-disjoint occurrence `A ∘ B`; the internal
`ReimerTraceOccurrence` name denotes only Grimmett's finite `□` occurrence operation, not an
appeal to Reimer's inequality. -/
theorem finiteTraceOpenBK {ι : Type*} {E : Finset ι}
    {T U : Set (Finset ι)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E p (OpenTraceDisjointOccurrence E T U) ≤
      finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U := by
  rw [← reimerTraceOccurrence_eq_openTraceDisjointOccurrence_of_increasing hT hU]
  rw [← finiteBernoulliEventProbability_bkStepSource_empty E p T U]
  calc
    finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E ∅ T U) ≤
        finiteBernoulliEventProbability (bkTwoCopySupport E) p (bkStepSource E E T U) :=
      finiteBernoulliEventProbability_bkStepSource_empty_le_self E hp0 hp1 hT hU
    _ = finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U :=
      finiteBernoulliEventProbability_bkStepSource_self E p T U

/-- Heterogeneous finite-trace BK inequality, proved by Grimmett's two-copy split-coordinate
proof on pages 39--40. -/
theorem finiteTraceOpenBK_heterogeneous {ι : Type*} {E : Finset ι}
    {T U : Set (Finset ι)} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliHeteroEventProbability E q (OpenTraceDisjointOccurrence E T U) ≤
      finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q U := by
  rw [← reimerTraceOccurrence_eq_openTraceDisjointOccurrence_of_increasing hT hU]
  rw [← finiteBernoulliHeteroEventProbability_bkStepSource_empty E q T U]
  calc
    finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
        (bkStepSource E ∅ T U) ≤
        finiteBernoulliHeteroEventProbability (bkTwoCopySupport E) (Sum.elim q q)
          (bkStepSource E E T U) :=
      finiteBernoulliHeteroEventProbability_bkStepSource_empty_le_self E hq0 hq1 hT hU
    _ = finiteBernoulliHeteroEventProbability E q T *
        finiteBernoulliHeteroEventProbability E q U :=
      finiteBernoulliHeteroEventProbability_bkStepSource_self E q T U

/-- Repeated heterogeneous finite-trace BK inequality for pairwise open disjoint occurrence,
obtained by induction from the binary Grimmett two-copy BK theorem. -/
theorem finiteBernoulliHeteroEventProbability_finiteOpenTraceDisjointOccurrence_le_prod
    {ι κ : Type*} {E : Finset ι} {J : Finset κ}
    {T : κ → Set (Finset ι)} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    finiteBernoulliHeteroEventProbability E q (FiniteOpenTraceDisjointOccurrence E J T) ≤
      J.prod fun i ↦ finiteBernoulliHeteroEventProbability E q (T i) := by
  classical
  induction J using Finset.induction with
  | empty =>
      rw [finiteOpenTraceDisjointOccurrence_empty]
      have hbase :
          finiteBernoulliHeteroEventProbability E q {s : Finset ι | s ⊆ E} =
            finiteBernoulliHeteroEventProbability E q (Set.univ : Set (Finset ι)) := by
        refine finiteBernoulliHeteroEventProbability_congr ?_
        intro s hsE
        simp [hsE]
      rw [hbase]
      simp
  | insert a J ha ih =>
      have hTJ : ∀ i ∈ J, IsIncreasingTrace E (T i) := by
        intro i hi
        exact hT i (Finset.mem_insert.mpr (Or.inr hi))
      have hrestInc : IsIncreasingTrace E (FiniteOpenTraceDisjointOccurrence E J T) :=
        isIncreasingTrace_finiteOpenTraceDisjointOccurrence
      have hsubset := finiteOpenTraceDisjointOccurrence_insert_subset_openTraceDisjointOccurrence
        (E := E) (J := J) (a := a) (T := T) ha
      calc
        finiteBernoulliHeteroEventProbability E q
            (FiniteOpenTraceDisjointOccurrence E (insert a J) T) ≤
            finiteBernoulliHeteroEventProbability E q
              (OpenTraceDisjointOccurrence E (T a)
                (FiniteOpenTraceDisjointOccurrence E J T)) :=
          finiteBernoulliHeteroEventProbability_mono hq0 hq1 hsubset
        _ ≤ finiteBernoulliHeteroEventProbability E q (T a) *
              finiteBernoulliHeteroEventProbability E q
                (FiniteOpenTraceDisjointOccurrence E J T) :=
          finiteTraceOpenBK_heterogeneous hq0 hq1
            (hT a (Finset.mem_insert_self a J)) hrestInc
        _ ≤ finiteBernoulliHeteroEventProbability E q (T a) *
              J.prod (fun i ↦ finiteBernoulliHeteroEventProbability E q (T i)) :=
          mul_le_mul_of_nonneg_left (ih hTJ)
            (finiteBernoulliHeteroEventProbability_nonneg E (T a) hq0 hq1)
        _ = (insert a J).prod
              (fun i ↦ finiteBernoulliHeteroEventProbability E q (T i)) := by
          rw [Finset.prod_insert ha]

/-- Repeated homogeneous finite-trace BK inequality for pairwise open disjoint occurrence. -/
theorem finiteBernoulliEventProbability_finiteOpenTraceDisjointOccurrence_le_prod
    {ι κ : Type*} {E : Finset ι} {J : Finset κ}
    {T : κ → Set (Finset ι)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    finiteBernoulliEventProbability E p (FiniteOpenTraceDisjointOccurrence E J T) ≤
      J.prod fun i ↦ finiteBernoulliEventProbability E p (T i) := by
  have h :=
    finiteBernoulliHeteroEventProbability_finiteOpenTraceDisjointOccurrence_le_prod
      (E := E) (J := J) (T := T) (q := fun _ ↦ p)
      (fun _ _ ↦ hp0) (fun _ _ ↦ hp1) hT
  simpa [finiteBernoulliHeteroEventProbability_const] using h

/-- Event-level BK for finite-trace cylinder events, in the textbook open-disjoint-occurrence
form. This is the measure-theoretic lift of `finiteTraceOpenBK`. -/
theorem setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul {ι : Type*}
    {E : Finset ι} {T U : Set (Finset ι)} (p : I)
    (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    (setBer((Set.univ : Set ι), p)).real
        (OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U)) ≤
      (setBer((Set.univ : Set ι), p)).real (eventOfTrace E T) *
        (setBer((Set.univ : Set ι), p)).real (eventOfTrace E U) := by
  rw [← eventOfTrace_openTraceDisjointOccurrence E T U,
    setBernoulli_real_eventOfTrace E (OpenTraceDisjointOccurrence E T U) p,
    setBernoulli_real_eventOfTrace E T p,
    setBernoulli_real_eventOfTrace E U p]
  exact finiteTraceOpenBK p.2.1 p.2.2 hT hU

/-- Event-level repeated BK for finite-trace cylinder events, in finite-family open-witness form.
This is the cylinder-event lift of the repeated finite-trace BK theorem. -/
theorem setBernoulli_real_finiteOpenDisjointOccurrence_eventOfTrace_le_prod
    {ι κ : Type*} {E : Finset ι} {J : Finset κ}
    {T : κ → Set (Finset ι)} (p : I)
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    (setBer((Set.univ : Set ι), p)).real
        (FiniteOpenDisjointOccurrence J (fun i ↦ eventOfTrace E (T i))) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (eventOfTrace E (T i)) := by
  rw [← eventOfTrace_finiteOpenTraceDisjointOccurrence E J T,
    setBernoulli_real_eventOfTrace E (FiniteOpenTraceDisjointOccurrence E J T) p]
  have htrace :=
    finiteBernoulliHeteroEventProbability_finiteOpenTraceDisjointOccurrence_le_prod
      (E := E) (J := J) (T := T) (q := fun _ ↦ (p : ℝ))
      (fun _ _ ↦ p.2.1) (fun _ _ ↦ p.2.2) hT
  have htrace' :
      finiteBernoulliEventProbability E (p : ℝ) (FiniteOpenTraceDisjointOccurrence E J T) ≤
        J.prod fun i ↦ finiteBernoulliEventProbability E (p : ℝ) (T i) := by
    simpa [finiteBernoulliHeteroEventProbability_const] using htrace
  calc
    finiteBernoulliEventProbability E (p : ℝ) (FiniteOpenTraceDisjointOccurrence E J T) ≤
        J.prod (fun i ↦ finiteBernoulliEventProbability E (p : ℝ) (T i)) :=
      htrace'
    _ = J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (eventOfTrace E (T i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [setBernoulli_real_eventOfTrace E (T i) p]

/-- Event-level repeated BK for finite-trace cylinder events, in ordinary finite-family
disjoint-occurrence form. For increasing trace events this is equivalent to the open-witness
version. -/
theorem setBernoulli_real_finiteDisjointOccurrence_eventOfTrace_le_prod
    {ι κ : Type*} {E : Finset ι} {J : Finset κ}
    {T : κ → Set (Finset ι)} (p : I)
    (hT : ∀ i ∈ J, IsIncreasingTrace E (T i)) :
    (setBer((Set.univ : Set ι), p)).real
        (FiniteDisjointOccurrence J (fun i ↦ eventOfTrace E (T i))) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (eventOfTrace E (T i)) := by
  rw [← finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing
    (fun i hi ↦ (hT i hi).eventOfTrace)]
  exact setBernoulli_real_finiteOpenDisjointOccurrence_eventOfTrace_le_prod p hT

/-- Direct finite-support BK inequality for Bernoulli product measure. If two increasing events
depend on finitely many coordinates, then their textbook open disjoint occurrence has
probability at most the product of their probabilities. This is the reusable finite-support
form of Grimmett Theorem 2.12 for the homogeneous `setBer` measure, proved from Grimmett's
two-copy argument rather than from Reimer's inequality. -/
theorem setBernoulli_real_openDisjointOccurrence_le_mul_of_dependsOn_direct
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B := by
  let G : Finset ι := E ∪ F
  have hAdepG : DependsOn G A := hA.mono (by intro e he; exact Finset.mem_union_left F he)
  have hBdepG : DependsOn G B := hB.mono (by intro e he; exact Finset.mem_union_right E he)
  have hAeq : A = eventOfTrace G (eventTrace G A) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hAdepG ω).symm
  have hBeq : B = eventOfTrace G (eventTrace G B) := by
    ext ω
    exact (restrictTo_mem_eventTrace_iff_of_dependsOn hBdepG ω).symm
  rw [hAeq, hBeq]
  exact setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul p
    (IsIncreasingEvent.eventTrace (E := G) hAinc)
    (IsIncreasingEvent.eventTrace (E := G) hBinc)

/-- Direct finite-support BK inequality for ordinary disjoint occurrence. For increasing
events, ordinary disjoint occurrence and textbook open disjoint occurrence agree. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_direct
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B := by
  rw [← openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_openDisjointOccurrence_le_mul_of_dependsOn_direct p hAinc hBinc hA hB

/-- Direct finite-support BK inequality for cubic Bernoulli bond percolation, in textbook
open-disjoint-occurrence form. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_dependsOn_direct
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_openDisjointOccurrence_le_mul_of_dependsOn_direct p
    hAinc hBinc hA hB

/-- Direct finite-support BK inequality for cubic Bernoulli bond percolation, stated with
ordinary disjoint occurrence. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_dependsOn_direct
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_direct p
    hAinc hBinc hA hB

/-- Reimer trace occurrence is monotone in both event arguments. -/
theorem reimerTraceOccurrence_mono {ι : Type*} {E : Finset ι}
    {T U T' U' : Set (Finset ι)}
    (hTT' : T ⊆ T') (hUU' : U ⊆ U') :
    ReimerTraceOccurrence E T U ⊆ ReimerTraceOccurrence E T' U' := by
  rintro s ⟨hsE, K, hKE, hKT, hKU⟩
  exact ⟨hsE, K, hKE, hKT.mono_event hTT', hKU.mono_event hUU'⟩

/-- Reimer trace occurrence is contained in ordinary simultaneous occurrence. -/
theorem reimerTraceOccurrence_subset_inter {ι : Type*} {E : Finset ι}
    {T U : Set (Finset ι)} :
    ReimerTraceOccurrence E T U ⊆ T ∩ U := by
  rintro s ⟨hsE, K, _hKE, hKT, hKU⟩
  exact ⟨hKT s hsE (by intro e _he; rfl), hKU s hsE (by intro e _he; rfl)⟩

/-- Swapping the two forced events in Reimer trace occurrence just replaces the witness `K` by
its complement inside the support. -/
theorem reimerTraceOccurrence_subset_comm {ι : Type*} {E : Finset ι}
    {T U : Set (Finset ι)} :
    ReimerTraceOccurrence E T U ⊆ ReimerTraceOccurrence E U T := by
  classical
  rintro s ⟨hsE, K, hKE, hKT, hKU⟩
  refine ⟨hsE, E \ K, ?_, hKU, ?_⟩
  · intro e he
    exact (Finset.mem_sdiff.mp he).1
  · have hcomp : E \ (E \ K) = K := by
      ext e
      rw [Finset.mem_sdiff, Finset.mem_sdiff]
      constructor
      · rintro ⟨heE, hnot⟩
        by_contra hnotK
        exact hnot ⟨heE, hnotK⟩
      · intro heK
        exact ⟨hKE heK, by
          intro heEK
          exact heEK.2 heK⟩
    simpa [hcomp] using hKT

/-- Reimer trace occurrence is symmetric in its two event arguments. -/
theorem reimerTraceOccurrence_comm {ι : Type*} {E : Finset ι}
    (T U : Set (Finset ι)) :
    ReimerTraceOccurrence E T U = ReimerTraceOccurrence E U T :=
  Set.Subset.antisymm reimerTraceOccurrence_subset_comm reimerTraceOccurrence_subset_comm

theorem traceEventOnSupport_reimerTraceOccurrence {ι : Type*}
    (E : Finset ι) (T U : Set (Finset ι)) :
    traceEventOnSupport E (ReimerTraceOccurrence E T U) =
      ReimerTraceOccurrence (Finset.univ : Finset E)
        (traceEventOnSupport E T) (traceEventOnSupport E U) := by
  classical
  ext s
  constructor
  · intro hs
    rcases (mem_reimerTraceOccurrence_iff.mp hs) with ⟨_hsE, K, hKE, hKT, hKU⟩
    refine ⟨by intro x _hx; simp, K.subtype (fun x ↦ x ∈ E),
      by intro x _hx; simp, ?_, ?_⟩
    · simpa [map_subtype_subtype] using
        (traceForces_toSupport E K
          (s.map (Function.Embedding.subtype fun x ↦ x ∈ E)) T hKE hKT)
    · intro t _ht hagree
      exact hKU (t.map (Function.Embedding.subtype fun x ↦ x ∈ E))
        (by
          intro x hx
          rw [Finset.mem_map] at hx
          rcases hx with ⟨y, _hy, rfl⟩
          exact y.2)
        (by
          intro e heEK
          have heEK' := (Finset.mem_sdiff.mp heEK)
          have heE : e ∈ E := heEK'.1
          have hnotK : e ∉ K := heEK'.2
          have hagree_e := hagree (⟨e, heE⟩ : E) (by
            exact (@Finset.mem_sdiff E (Classical.decEq E) (Finset.univ : Finset E)
              (K.subtype (fun x ↦ x ∈ E)) (⟨e, heE⟩)).mpr ⟨by simp, by
                intro hmem
                exact hnotK (by simpa [Finset.mem_subtype] using hmem)⟩)
          rw [mem_map_subtype_iff t heE]
          simpa [mem_map_subtype_iff s heE] using hagree_e)
  · intro hs
    rcases (mem_reimerTraceOccurrence_iff.mp hs) with ⟨_hsE, K, _hKE, hKT, hKU⟩
    refine ⟨?_, K.map (Function.Embedding.subtype fun x ↦ x ∈ E), ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.2
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.2
    · exact traceForces_ofSupport E K s T hKT
    · intro t htE hagree
      have ht : t.subtype (fun x ↦ x ∈ E) ∈ traceEventOnSupport E U :=
        hKU (t.subtype fun x ↦ x ∈ E) (by intro x hx; simp) (by
          intro x hxK
          have hxK' := (@Finset.mem_sdiff E (Classical.decEq E)
            (Finset.univ : Finset E) K x).mp hxK
          have hxOrig :
              (x : ι) ∈ E \ K.map (Function.Embedding.subtype fun x ↦ x ∈ E) := by
            rw [Finset.mem_sdiff]
            exact ⟨x.2, by
              intro hxmap
              exact hxK'.2 ((mem_map_subtype_iff K x.2).mp hxmap)⟩
          specialize hagree (x : ι) hxOrig
          rw [mem_map_subtype_iff s x.2] at hagree
          simpa [Finset.mem_subtype] using hagree)
      simpa [traceEventOnSupport, Finset.subtype_map_of_mem htE] using ht

/-- Uniform complement-form Reimer on the full finite cube over the subtype support implies the
same uniform Reimer bound on the original finite support. -/
theorem finiteTraceUniformReimerBound_of_univ_subtype {ι : Type*} (E : Finset ι)
    (h : FiniteTraceUniformReimerBound (Finset.univ : Finset E)) :
    FiniteTraceUniformReimerBound E := by
  intro T U
  rw [← finiteBernoulliEventProbability_support_eq E (1 / 2) (ReimerTraceOccurrence E T U),
    traceEventOnSupport_reimerTraceOccurrence,
    ← finiteBernoulliEventProbability_support_eq E (1 / 2) (T ∩ TraceComplement E U),
    traceEventOnSupport_inter, traceEventOnSupport_traceComplement]
  exact h (traceEventOnSupport E T) (traceEventOnSupport E U)

theorem finiteTraceUniformReimerBound_of_forall_univ_fintype {ι : Type u}
    (h : ∀ α : Type u, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α))
    (E : Finset ι) :
    FiniteTraceUniformReimerBound E :=
  finiteTraceUniformReimerBound_of_univ_subtype E (h ↥E)

theorem finiteTraceCardinalityReimerBound_of_univ_subtype {ι : Type*} (E : Finset ι)
    (h : FiniteTraceCardinalityReimerBound (Finset.univ : Finset E)) :
    FiniteTraceCardinalityReimerBound E := by
  intro T U
  rw [← finiteTraceEventFamily_support_card E (ReimerTraceOccurrence E T U),
    traceEventOnSupport_reimerTraceOccurrence,
    ← finiteTraceEventFamily_support_card E (T ∩ TraceComplement E U),
    traceEventOnSupport_inter, traceEventOnSupport_traceComplement]
  exact h (traceEventOnSupport E T) (traceEventOnSupport E U)

theorem finiteTraceCardinalityReimerBound_of_forall_univ_fintype {ι : Type u}
    (h : ∀ α : Type u, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α))
    (E : Finset ι) :
    FiniteTraceCardinalityReimerBound E :=
  finiteTraceCardinalityReimerBound_of_univ_subtype E (h ↥E)

/-- Pull a trace event on `β` back along an equivalence from `α` to `β`. -/
def traceEventMapEquiv {α β : Type*} (e : α ≃ β)
    (T : Set (Finset β)) : Set (Finset α) :=
  {s | s.map e.toEmbedding ∈ T}

theorem map_equiv_symm_map {α β : Type*} (e : α ≃ β) (s : Finset β) :
    (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
  ext x
  simp

theorem map_equiv_map_symm {α β : Type*} (e : α ≃ β) (s : Finset α) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  ext x
  simp

theorem univ_sdiff_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (s : Finset α) :
    (Finset.univ : Finset β) \ s.map e.toEmbedding =
      ((Finset.univ : Finset α) \ s).map e.toEmbedding := by
  ext x
  simp [Finset.mem_sdiff]

theorem traceForces_univ_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (K s : Finset α) (T : Set (Finset β)) :
    TraceForces (Finset.univ : Finset α) K s (traceEventMapEquiv e T) ↔
      TraceForces (Finset.univ : Finset β)
        (K.map e.toEmbedding) (s.map e.toEmbedding) T := by
  constructor
  · intro h t _ht hagree
    have hpre : t.map e.symm.toEmbedding ∈ traceEventMapEquiv e T :=
      h (t.map e.symm.toEmbedding) (by intro x _; simp) (by
        intro a haK
        have haKmap : e a ∈ K.map e.toEmbedding := by
          rw [Finset.mem_map]
          exact ⟨a, haK, by simp⟩
        have hag := hagree (e a) haKmap
        simpa using hag)
    simpa [traceEventMapEquiv, map_equiv_symm_map e t] using hpre
  · intro h t _ht hagree
    exact h (t.map e.toEmbedding) (by intro x _; simp) (by
      intro b hbK
      rcases (Finset.mem_map.mp hbK) with ⟨a, haK, rfl⟩
      have hag := hagree a haK
      simpa using hag)

theorem traceEventMapEquiv_reimerTraceOccurrence_univ
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (T U : Set (Finset β)) :
    traceEventMapEquiv e (ReimerTraceOccurrence (Finset.univ : Finset β) T U) =
      ReimerTraceOccurrence (Finset.univ : Finset α)
        (traceEventMapEquiv e T) (traceEventMapEquiv e U) := by
  ext s
  constructor
  · intro hs
    rcases (mem_reimerTraceOccurrence_iff.mp hs) with ⟨_hsuniv, K, _hK, hKT, hKU⟩
    refine ⟨by intro x _; simp, K.map e.symm.toEmbedding, by intro x _; simp, ?_, ?_⟩
    · rw [traceForces_univ_map_equiv e]
      simpa [map_equiv_symm_map e K] using hKT
    · rw [traceForces_univ_map_equiv e]
      rw [← univ_sdiff_map_equiv e (K.map e.symm.toEmbedding)]
      simpa [map_equiv_symm_map e K] using hKU
  · intro hs
    rcases (mem_reimerTraceOccurrence_iff.mp hs) with ⟨_hsuniv, K, _hK, hKT, hKU⟩
    refine mem_reimerTraceOccurrence_iff.mpr ?_
    refine ⟨by intro x _; simp, K.map e.toEmbedding, by intro x _; simp, ?_, ?_⟩
    · rw [← traceForces_univ_map_equiv e]
      simpa using hKT
    · rw [univ_sdiff_map_equiv e K]
      rw [← traceForces_univ_map_equiv e]
      simpa using hKU

theorem traceEventMapEquiv_inter_traceComplement_univ
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (T U : Set (Finset β)) :
    traceEventMapEquiv e (T ∩ TraceComplement (Finset.univ : Finset β) U) =
      traceEventMapEquiv e T ∩
        TraceComplement (Finset.univ : Finset α) (traceEventMapEquiv e U) := by
  ext s
  simp only [traceEventMapEquiv, Set.mem_setOf_eq, Set.mem_inter_iff, TraceComplement]
  rw [univ_sdiff_map_equiv e s]

theorem finiteTraceEventFamily_univ_card_equiv
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (T : Set (Finset β)) :
    (finiteTraceEventFamily (Finset.univ : Finset α) (traceEventMapEquiv e T)).card =
      (finiteTraceEventFamily (Finset.univ : Finset β) T).card := by
  refine Finset.card_bij'
    (fun s _hs ↦ s.map e.toEmbedding)
    (fun t _ht ↦ t.map e.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_finiteTraceEventFamily_iff] at hs ⊢
    exact ⟨by intro x _; simp, hs.2⟩
  · intro t ht
    rw [mem_finiteTraceEventFamily_iff] at ht ⊢
    refine ⟨by intro x _; simp, ?_⟩
    simpa [traceEventMapEquiv, map_equiv_symm_map e t] using ht.2
  · intro s _hs
    exact map_equiv_map_symm e s
  · intro t _ht
    exact map_equiv_symm_map e t

/-- Cardinal Reimer on a full finite cube is invariant under relabelling the coordinates by an
equivalence. -/
theorem finiteTraceCardinalityReimerBound_univ_equiv
    {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (h : FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    FiniteTraceCardinalityReimerBound (Finset.univ : Finset β) := by
  intro T U
  have hcard := h (traceEventMapEquiv e T) (traceEventMapEquiv e U)
  rw [← traceEventMapEquiv_reimerTraceOccurrence_univ e T U,
    finiteTraceEventFamily_univ_card_equiv e
      (ReimerTraceOccurrence (Finset.univ : Finset β) T U),
    ← traceEventMapEquiv_inter_traceComplement_univ e T U,
    finiteTraceEventFamily_univ_card_equiv e
      (T ∩ TraceComplement (Finset.univ : Finset β) U)] at hcard
  exact hcard

/-- Boolean universal quantification over a finite set, used for reflected finite-cube
checks. -/
def finsetAll {α : Type*} (s : Finset α) (p : α → Bool) : Bool :=
  s.fold (fun x y ↦ x && y) true p

/-- Boolean existential quantification over a finite set, used for reflected finite-cube
checks. -/
def finsetAny {α : Type*} (s : Finset α) (p : α → Bool) : Bool :=
  s.fold (fun x y ↦ x || y) false p

/-- Boolean reflection of `TraceForces` for finite `Fin n` cubes. -/
def traceForcesFinBool {n : ℕ}
    (E K s : Finset (Fin n)) (T : Finset (Finset (Fin n))) : Bool :=
  finsetAll E.powerset fun t ↦
    !(finsetAll K fun e ↦ decide (e ∈ t) == decide (e ∈ s)) || decide (t ∈ T)

/-- Boolean reflection of finite-trace Reimer occurrence for finite `Fin n` cubes. -/
def reimerTraceOccurrenceFinBool {n : ℕ}
    (E : Finset (Fin n)) (T U : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  E.powerset.filter fun s ↦
    finsetAny E.powerset (fun K ↦
      traceForcesFinBool E K s T && traceForcesFinBool E (E \ K) s U) = true

/-- Boolean reflection of `T ∩ TraceComplement E U` for finite `Fin n` cubes. -/
def traceInterComplementFinBool {n : ℕ}
    (E : Finset (Fin n)) (T U : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  E.powerset.filter fun s ↦ (decide (s ∈ T) && decide (E \ s ∈ U)) = true

theorem fin_sdiff_eq_classical {n : ℕ} (s t : Finset (Fin n)) :
    s \ t =
      @sdiff (Finset (Fin n)) (@Finset.instSDiff (Fin n) (Classical.decEq (Fin n))) s t := by
  ext x
  simp [Finset.mem_sdiff]

theorem finsetAll_eq_true_iff_fin {n : ℕ} (s : Finset (Fin n)) (p : Fin n → Bool) :
    finsetAll s p = true ↔ ∀ x ∈ s, p x = true := by
  induction s using Finset.induction with
  | empty => simp [finsetAll]
  | insert a s ha ih =>
      rw [show finsetAll (insert a s) p = (p a && finsetAll s p) by
        simp [finsetAll, Finset.fold_insert, ha]]
      simp [ih, Bool.and_eq_true]

theorem finsetAll_eq_true_iff_finset_fin {n : ℕ}
    (s : Finset (Finset (Fin n))) (p : Finset (Fin n) → Bool) :
    finsetAll s p = true ↔ ∀ x ∈ s, p x = true := by
  induction s using Finset.induction with
  | empty => simp [finsetAll]
  | insert a s ha ih =>
      rw [show finsetAll (insert a s) p = (p a && finsetAll s p) by
        simp [finsetAll, Finset.fold_insert, ha]]
      simp [ih, Bool.and_eq_true]

theorem finsetAny_eq_true_iff_finset_fin {n : ℕ}
    (s : Finset (Finset (Fin n))) (p : Finset (Fin n) → Bool) :
    finsetAny s p = true ↔ ∃ x ∈ s, p x = true := by
  induction s using Finset.induction with
  | empty => simp [finsetAny]
  | insert a s ha ih =>
      rw [show finsetAny (insert a s) p = (p a || finsetAny s p) by
        simp [finsetAny, Finset.fold_insert, ha]]
      simp [ih, Bool.or_eq_true]

theorem traceForcesFinBool_eq_true_iff {n : ℕ}
    (E K s : Finset (Fin n)) (T : Finset (Finset (Fin n))) :
    traceForcesFinBool E K s T = true ↔ TraceForces E K s {t | t ∈ T} := by
  constructor
  · intro h t htE hagree
    rw [traceForcesFinBool] at h
    have hall := (finsetAll_eq_true_iff_finset_fin E.powerset _).mp h
    have htBool := hall t (Finset.mem_powerset.mpr htE)
    have hinner : (finsetAll K fun e ↦ decide (e ∈ t) == decide (e ∈ s)) = true := by
      exact (finsetAll_eq_true_iff_fin K _).mpr fun e he ↦ by
        by_cases het : e ∈ t
        · have hes : e ∈ s := (hagree e he).mp het
          simp [het, hes]
        · have hes : e ∉ s := by
            intro hs
            exact het ((hagree e he).mpr hs)
          simp [het, hes]
    simp [hinner] at htBool
    exact htBool
  · intro h
    rw [traceForcesFinBool]
    rw [finsetAll_eq_true_iff_finset_fin]
    intro t ht
    rw [Bool.or_eq_true]
    by_cases hinner : (finsetAll K fun e ↦ decide (e ∈ t) == decide (e ∈ s)) = true
    · right
      exact decide_eq_true (h t (Finset.mem_powerset.mp ht) (by
        intro e he
        have heq := (finsetAll_eq_true_iff_fin K _).mp hinner e he
        by_cases het : e ∈ t <;> by_cases hes : e ∈ s <;> simp [het, hes] at heq ⊢))
    · left
      cases hfin : (finsetAll K fun e ↦ decide (e ∈ t) == decide (e ∈ s)) <;> simp_all

theorem mem_reimerTraceOccurrenceFinBool_iff {n : ℕ}
    (E s : Finset (Fin n)) (T U : Finset (Finset (Fin n))) :
    s ∈ reimerTraceOccurrenceFinBool E T U ↔
      s ∈ ReimerTraceOccurrence E {t | t ∈ T} {t | t ∈ U} := by
  rw [reimerTraceOccurrenceFinBool, ReimerTraceOccurrence]
  simp only [Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq, Bool.and_eq_true,
    finsetAny_eq_true_iff_finset_fin, traceForcesFinBool_eq_true_iff]
  constructor
  · rintro ⟨hsE, K, hKE, hKT, hKU⟩
    rw [fin_sdiff_eq_classical E K] at hKU
    exact ⟨hsE, K, hKE, hKT, hKU⟩
  · rintro ⟨hsE, K, hKE, hKT, hKU⟩
    rw [← fin_sdiff_eq_classical E K] at hKU
    exact ⟨hsE, K, hKE, hKT, hKU⟩

theorem mem_traceInterComplementFinBool_iff {n : ℕ}
    (E s : Finset (Fin n)) (T U : Finset (Finset (Fin n))) :
    s ∈ traceInterComplementFinBool E T U ↔
      s ⊆ E ∧
        s ∈ ({t | t ∈ T} ∩ TraceComplement E {t | t ∈ U} : Set (Finset (Fin n))) := by
  rw [traceInterComplementFinBool, TraceComplement]
  simp only [Finset.mem_filter, Finset.mem_powerset, Bool.and_eq_true, decide_eq_true_eq,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hsE, hT, hU⟩
    rw [fin_sdiff_eq_classical E s] at hU
    exact ⟨hsE, hT, hU⟩
  · rintro ⟨hsE, hT, hU⟩
    rw [← fin_sdiff_eq_classical E s] at hU
    exact ⟨hsE, hT, hU⟩

/-- Exhaustive reflected proof of Reimer's cardinality inequality on the three-coordinate
finite cube. -/
theorem finiteTraceCardinalityReimerBound_univ_fin_three_reflected :
    ∀ T U : Finset (Finset (Fin 3)),
      (reimerTraceOccurrenceFinBool (Finset.univ : Finset (Fin 3)) T U).card ≤
        (traceInterComplementFinBool (Finset.univ : Finset (Fin 3)) T U).card := by
  native_decide

/-- Reimer's cardinality inequality on the full three-coordinate finite cube. -/
theorem finiteTraceCardinalityReimerBound_univ_fin_three :
    FiniteTraceCardinalityReimerBound (Finset.univ : Finset (Fin 3)) := by
  intro T U
  let E : Finset (Fin 3) := Finset.univ
  let TF : Finset (Finset (Fin 3)) := finiteTraceEventFamily E T
  let UF : Finset (Finset (Fin 3)) := finiteTraceEventFamily E U
  have hleft : finiteTraceEventFamily E (ReimerTraceOccurrence E T U) =
      reimerTraceOccurrenceFinBool E TF UF := by
    ext s
    rw [mem_finiteTraceEventFamily_iff, mem_reimerTraceOccurrenceFinBool_iff]
    constructor
    · rintro ⟨hsE, hocc⟩
      rcases hocc with ⟨_hsE, K, hKE, hKT, hKU⟩
      refine ⟨hsE, K, hKE, ?_, ?_⟩
      · intro t htE hagree
        exact (mem_finiteTraceEventFamily_iff E T t).mpr ⟨htE, hKT t htE hagree⟩
      · intro t htE hagree
        exact (mem_finiteTraceEventFamily_iff E U t).mpr ⟨htE, hKU t htE hagree⟩
    · intro hocc
      rcases hocc with ⟨hsE, K, hKE, hKT, hKU⟩
      refine ⟨hsE, hsE, K, hKE, ?_, ?_⟩
      · intro t htE hagree
        exact (mem_finiteTraceEventFamily_iff E T t).mp (hKT t htE hagree) |>.2
      · intro t htE hagree
        exact (mem_finiteTraceEventFamily_iff E U t).mp (hKU t htE hagree) |>.2
  have hright : finiteTraceEventFamily E (T ∩ TraceComplement E U) =
      traceInterComplementFinBool E TF UF := by
    ext s
    rw [mem_finiteTraceEventFamily_iff, mem_traceInterComplementFinBool_iff]
    constructor
    · rintro ⟨hsE, hT, hU⟩
      refine ⟨hsE, ?_, ?_⟩
      · exact (mem_finiteTraceEventFamily_iff E T s).mpr ⟨hsE, hT⟩
      · let sc : Finset (Fin 3) :=
          @sdiff (Finset (Fin 3)) (@Finset.instSDiff (Fin 3) (Classical.decEq (Fin 3))) E s
        have hUc : sc ∈ U := by
          simpa [sc] using mem_traceComplement_iff.mp hU
        have hscE : sc ⊆ E := by
          intro e he
          have he' : e ∈
              @sdiff (Finset (Fin 3)) (@Finset.instSDiff (Fin 3) (Classical.decEq (Fin 3)))
                E s := by
            simpa [sc] using he
          exact ((@Finset.mem_sdiff (Fin 3) (Classical.decEq (Fin 3)) E s e).mp he').1
        exact mem_traceComplement_iff.mpr
          ((mem_finiteTraceEventFamily_iff E U sc).mpr ⟨hscE, hUc⟩)
    · rintro ⟨hsE, hT, hU⟩
      refine ⟨hsE, ?_, ?_⟩
      · exact (mem_finiteTraceEventFamily_iff E T s).mp hT |>.2
      · let sc : Finset (Fin 3) :=
          @sdiff (Finset (Fin 3)) (@Finset.instSDiff (Fin 3) (Classical.decEq (Fin 3))) E s
        have hUc : sc ∈ UF := by
          simpa [sc] using mem_traceComplement_iff.mp hU
        have hUset : sc ∈ U := (mem_finiteTraceEventFamily_iff E U sc).mp hUc |>.2
        exact mem_traceComplement_iff.mpr (by simpa [sc] using hUset)
  rw [hleft, hright]
  exact finiteTraceCardinalityReimerBound_univ_fin_three_reflected TF UF

/-- Reimer's cardinality inequality for any three-coordinate finite support, obtained by
transporting the full `Fin 3` reflected slice to the subtype support. -/
theorem finiteTraceCardinalityReimerBound_of_card_eq_three {ι : Type*} {E : Finset ι}
    (hE : E.card = 3) :
    FiniteTraceCardinalityReimerBound E := by
  refine finiteTraceCardinalityReimerBound_of_univ_subtype E ?_
  have hcard : Nat.card E = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hE
  exact finiteTraceCardinalityReimerBound_univ_equiv
    (Finite.equivFinOfCardEq hcard).symm finiteTraceCardinalityReimerBound_univ_fin_three

theorem mem_eventTrace_reimerOccurrenceOn_iff_of_dependsOn {ι : Type*}
    {E s : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) :
    s ∈ eventTrace E (ReimerOccurrenceOn E A B) ↔
      s ∈ ReimerTraceOccurrence E (eventTrace E A : Set (Finset ι))
        (eventTrace E B : Set (Finset ι)) := by
  constructor
  · intro hs
    have hs' := (mem_eventTrace_iff E (ReimerOccurrenceOn E A B) s).mp hs
    rcases hs'.2 with ⟨K, hKE, hK, hEK⟩
    refine ⟨hs'.1, K, hKE, ?_, ?_⟩
    · intro t htE hts
      exact (mem_eventTrace_iff E A t).mpr ⟨htE, hK (t : Set ι) hts⟩
    · intro t htE hts
      exact (mem_eventTrace_iff E B t).mpr ⟨htE, hEK (t : Set ι) hts⟩
  · intro hs
    rcases hs with ⟨hsE, K, hKE, hK, hEK⟩
    refine (mem_eventTrace_iff E (ReimerOccurrenceOn E A B) s).mpr ⟨hsE, ?_⟩
    refine ⟨K, hKE, ?_, ?_⟩
    · intro η hη
      have ht : restrictTo E η ∈ eventTrace E A := hK (restrictTo E η)
        (restrictTo_subset E η) (by
          intro e heK
          have heE : e ∈ E := hKE heK
          simpa [restrictTo, heE] using hη e heK)
      exact (restrictTo_mem_eventTrace_iff_of_dependsOn hA η).mp ht
    · intro η hη
      have ht : restrictTo E η ∈ eventTrace E B := hEK (restrictTo E η)
        (restrictTo_subset E η) (by
          intro e heEK
          have heE : e ∈ E := (Finset.mem_sdiff.mp heEK).1
          simpa [restrictTo, heE] using hη e heEK)
      exact (restrictTo_mem_eventTrace_iff_of_dependsOn hB η).mp ht

theorem finiteBernoulliEventProbability_eventTrace_reimerOccurrenceOn
    {ι : Type*} {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) (p : I) :
    finiteBernoulliEventProbability E (p : ℝ)
        (eventTrace E (ReimerOccurrenceOn E A B)) =
      finiteBernoulliEventProbability E (p : ℝ)
        (ReimerTraceOccurrence E (eventTrace E A : Set (Finset ι))
          (eventTrace E B : Set (Finset ι))) := by
  refine finiteBernoulliEventProbability_congr ?_
  intro s _hsE
  exact mem_eventTrace_reimerOccurrenceOn_iff_of_dependsOn hA hB

/-- The weighted finite-cube Reimer inequality on a fixed support. Proving this proposition for
all finite supports is the remaining combinatorial core needed to discharge `ReimerBoundOn`. -/
def FiniteTraceReimerBound {ι : Type*} (E : Finset ι) (p : ℝ) : Prop :=
  ∀ T U : Set (Finset ι),
    finiteBernoulliEventProbability E p (ReimerTraceOccurrence E T U) ≤
      finiteBernoulliEventProbability E p T * finiteBernoulliEventProbability E p U

/-- Weighted finite-trace Reimer rewritten in cardinality-level coordinates. This is the exact
finite polynomial form used by reflected/finite coefficient certificates. -/
theorem finiteTraceReimerBound_iff_levelCount {ι : Type*} (E : Finset ι) (p : ℝ) :
    FiniteTraceReimerBound E p ↔
      ∀ T U : Set (Finset ι),
        (∑ k ∈ Finset.range (E.card + 1),
            (finiteTraceLevelCount E (ReimerTraceOccurrence E T U) k : ℝ) *
              p ^ k * (1 - p) ^ (E.card - k)) ≤
          (∑ k ∈ Finset.range (E.card + 1),
              (finiteTraceLevelCount E T k : ℝ) *
                p ^ k * (1 - p) ^ (E.card - k)) *
            (∑ k ∈ Finset.range (E.card + 1),
              (finiteTraceLevelCount E U k : ℝ) *
                p ^ k * (1 - p) ^ (E.card - k)) := by
  constructor
  · intro h T U
    simpa [finiteBernoulliEventProbability_eq_sum_levelCount] using h T U
  · intro h T U
    simpa [finiteBernoulliEventProbability_eq_sum_levelCount] using h T U

theorem finiteTraceReimerBound_of_univ_subtype {ι : Type*} (E : Finset ι) (p : ℝ)
    (h : FiniteTraceReimerBound (Finset.univ : Finset E) p) :
    FiniteTraceReimerBound E p := by
  intro T U
  rw [← finiteBernoulliEventProbability_support_eq E p (ReimerTraceOccurrence E T U),
    traceEventOnSupport_reimerTraceOccurrence,
    ← finiteBernoulliEventProbability_support_eq E p T,
    ← finiteBernoulliEventProbability_support_eq E p U]
  exact h (traceEventOnSupport E T) (traceEventOnSupport E U)

theorem finiteTraceReimerBound_of_forall_univ_fintype {ι : Type u} (p : ℝ)
    (h : ∀ α : Type u, [Fintype α] → FiniteTraceReimerBound (Finset.univ : Finset α) p)
    (E : Finset ι) :
    FiniteTraceReimerBound E p :=
  finiteTraceReimerBound_of_univ_subtype E p (h ↥E)

theorem finiteBernoulliEventProbability_zero {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability E 0 T =
      if (∅ : Finset ι) ∈ T then 1 else 0 := by
  revert T
  induction E using Finset.induction with
  | empty =>
      intro T
      by_cases hT : (∅ : Finset ι) ∈ T <;>
        simp [finiteBernoulliEventProbability, hT]
  | insert a E ha ih =>
      intro T
      rw [finiteBernoulliEventProbability_insert_split ha]
      simp [ih T]

theorem finiteBernoulliEventProbability_one {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability E 1 T = if E ∈ T then 1 else 0 := by
  revert T
  induction E using Finset.induction with
  | empty =>
      intro T
      by_cases hT : (∅ : Finset ι) ∈ T <;>
        simp [finiteBernoulliEventProbability, hT]
  | insert a E ha ih =>
      intro T
      rw [finiteBernoulliEventProbability_insert_split ha]
      simpa using ih {s : Finset ι | insert a s ∈ T}

theorem finiteTraceReimerBound_zero {ι : Type*} (E : Finset ι) :
    FiniteTraceReimerBound E 0 := by
  intro T U
  rw [finiteBernoulliEventProbability_zero E (ReimerTraceOccurrence E T U),
    finiteBernoulliEventProbability_zero E T, finiteBernoulliEventProbability_zero E U]
  by_cases hbox : (∅ : Finset ι) ∈ ReimerTraceOccurrence E T U
  · rcases (mem_reimerTraceOccurrence_iff.mp hbox).2 with ⟨K, hKE, hK, hEK⟩
    have hT0 : (∅ : Finset ι) ∈ T :=
      hK ∅ (Finset.empty_subset E) (by simp)
    have hU0 : (∅ : Finset ι) ∈ U :=
      hEK ∅ (Finset.empty_subset E) (by simp)
    simp [hbox, hT0, hU0]
  · by_cases hT0 : (∅ : Finset ι) ∈ T <;>
      by_cases hU0 : (∅ : Finset ι) ∈ U <;>
      simp [hbox, hT0, hU0]

theorem finiteTraceReimerBound_one {ι : Type*} (E : Finset ι) :
    FiniteTraceReimerBound E 1 := by
  intro T U
  rw [finiteBernoulliEventProbability_one E (ReimerTraceOccurrence E T U),
    finiteBernoulliEventProbability_one E T, finiteBernoulliEventProbability_one E U]
  by_cases hbox : E ∈ ReimerTraceOccurrence E T U
  · rcases (mem_reimerTraceOccurrence_iff.mp hbox).2 with ⟨K, hKE, hK, hEK⟩
    have hT1 : E ∈ T :=
      hK E (by intro e he; exact he) (by simp)
    have hU1 : E ∈ U :=
      hEK E (by intro e he; exact he) (by simp)
    simp [hbox, hT1, hU1]
  · by_cases hT1 : E ∈ T <;>
      by_cases hU1 : E ∈ U <;>
      simp [hbox, hT1, hU1]

/-- At parameter `p = 1/2`, finite Bernoulli probability is normalized counting measure on the
finite trace cube. -/
theorem finiteBernoulliEventProbability_half_eq_card {ι : Type*}
    (E : Finset ι) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability E (1 / 2) T =
      ((finiteTraceEventFamily E T).card : ℝ) / (2 : ℝ) ^ E.card := by
  classical
  unfold finiteBernoulliEventProbability finiteBernoulliExpectation
  have hweight : ∀ s ∈ E.powerset,
      (1 / 2 : ℝ) ^ s.card * (1 - 1 / 2 : ℝ) ^ (E.card - s.card) =
        (1 / 2 : ℝ) ^ E.card := by
    intro s hs
    have hsE : s ⊆ E := Finset.mem_powerset.mp hs
    have hcard : s.card + (E.card - s.card) = E.card :=
      Nat.add_sub_of_le (Finset.card_le_card hsE)
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
    rw [← pow_add]
    rw [hcard]
  calc
    E.powerset.sum
        (fun s ↦ (1 / 2 : ℝ) ^ s.card * (1 - 1 / 2 : ℝ) ^ (E.card - s.card) *
          T.indicator (fun _ ↦ (1 : ℝ)) s) =
        E.powerset.sum
          (fun s ↦ (1 / 2 : ℝ) ^ E.card * T.indicator (fun _ ↦ (1 : ℝ)) s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hweight s hs]
    _ = (1 / 2 : ℝ) ^ E.card *
        E.powerset.sum (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) := by
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) ^ E.card * ((finiteTraceEventFamily E T).card : ℝ) := by
      congr 1
      unfold finiteTraceEventFamily
      simp only [Set.indicator]
      rw [Finset.sum_boole]
    _ = ((finiteTraceEventFamily E T).card : ℝ) / (2 : ℝ) ^ E.card := by
      rw [one_div_pow]
      ring

theorem finiteBernoulliEventProbability_half_traceComplement {ι : Type*}
    (E : Finset ι) (U : Set (Finset ι)) :
    finiteBernoulliEventProbability E (1 / 2) (TraceComplement E U) =
      finiteBernoulliEventProbability E (1 / 2) U := by
  classical
  revert U
  induction E using Finset.induction with
  | empty =>
      intro U
      by_cases hU : (∅ : Finset ι) ∈ U <;>
        simp [finiteBernoulliEventProbability, TraceComplement, hU]
  | insert a E ha ih =>
      intro U
      rw [finiteBernoulliEventProbability_insert_split ha,
        finiteBernoulliEventProbability_insert_split ha]
      have hclosed :
          finiteBernoulliEventProbability E (1 / 2) (TraceComplement (insert a E) U) =
            finiteBernoulliEventProbability E (1 / 2)
              (TraceComplement E {s : Finset ι | insert a s ∈ U}) := by
        refine finiteBernoulliEventProbability_congr ?_
        intro s hsE
        have hsa : a ∉ s := Finset.notMem_mono hsE ha
        have hdiff : (insert a E) \ s = insert a (E \ s) := by
          ext x
          by_cases hxa : x = a
          · subst x
            simp [hsa]
          · simp [Finset.mem_sdiff, hxa]
        simp [TraceComplement, hdiff]
      have hopen :
          finiteBernoulliEventProbability E (1 / 2)
              {s : Finset ι | insert a s ∈ TraceComplement (insert a E) U} =
            finiteBernoulliEventProbability E (1 / 2) (TraceComplement E U) := by
        refine finiteBernoulliEventProbability_congr ?_
        intro s hsE
        have hdiff : E \ insert a s = E \ s := by
          ext x
          by_cases hxa : x = a
          · subst x
            simp [ha]
          · simp [Finset.mem_sdiff, hxa]
        simp [TraceComplement, hdiff]
      rw [hclosed, hopen, ih {s : Finset ι | insert a s ∈ U}, ih U]
      ring

/-- The uniform-measure finite BK inequality for increasing traces, as a formal corollary of
Reimer's uniform complement-form inequality and finite FKG. -/
theorem finiteTraceBK_half_of_uniformReimerBound {ι : Type*} {E : Finset ι}
    (hReimer : FiniteTraceUniformReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E (1 / 2) (ReimerTraceOccurrence E T U) ≤
      finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) U := by
  calc
    finiteBernoulliEventProbability E (1 / 2) (ReimerTraceOccurrence E T U) ≤
        finiteBernoulliEventProbability E (1 / 2) (T ∩ TraceComplement E U) :=
      hReimer T U
    _ ≤ finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) (TraceComplement E U) :=
      finiteBernoulliEventProbability_le_mul_of_increasing_decreasing
        (by norm_num) (by norm_num) hT hU.traceComplement
    _ = finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) U := by
      rw [finiteBernoulliEventProbability_half_traceComplement]

/-- The BK-shaped open-witness finite trace inequality at `p = 1/2`, as a formal corollary of
Reimer's uniform complement-form inequality. -/
theorem finiteTraceOpenBK_half_of_uniformReimerBound {ι : Type*} {E : Finset ι}
    (hReimer : FiniteTraceUniformReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E (1 / 2) (OpenTraceDisjointOccurrence E T U) ≤
      finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) U := by
  simpa [← reimerTraceOccurrence_eq_openTraceDisjointOccurrence_of_increasing hT hU] using
    finiteTraceBK_half_of_uniformReimerBound hReimer hT hU

/-- Product-measure BK for finite-trace cylinder events at `p = 1/2`, as a direct corollary of
Reimer's uniform complement-form theorem on the finite support. -/
theorem setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_uniformReimerBound
    {ι : Type*} {E : Finset ι} (hReimer : FiniteTraceUniformReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real
        (OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U)) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E T) *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E U) := by
  rw [← eventOfTrace_openTraceDisjointOccurrence E T U,
    setBernoulli_real_eventOfTrace E (OpenTraceDisjointOccurrence E T U) unitIntervalHalf,
    setBernoulli_real_eventOfTrace E T unitIntervalHalf,
    setBernoulli_real_eventOfTrace E U unitIntervalHalf]
  simpa [unitIntervalHalf] using finiteTraceOpenBK_half_of_uniformReimerBound hReimer hT hU

/-- Reimer's cardinality theorem implies the uniform probability form by normalizing both sides
by the size of the finite cube. -/
theorem finiteTraceUniformReimerBound_of_cardinalityReimerBound {ι : Type*}
    {E : Finset ι} (hReimer : FiniteTraceCardinalityReimerBound E) :
    FiniteTraceUniformReimerBound E := by
  intro T U
  rw [finiteBernoulliEventProbability_half_eq_card E (ReimerTraceOccurrence E T U),
    finiteBernoulliEventProbability_half_eq_card E (T ∩ TraceComplement E U)]
  have hcard :
      ((finiteTraceEventFamily E (ReimerTraceOccurrence E T U)).card : ℝ) ≤
        ((finiteTraceEventFamily E (T ∩ TraceComplement E U)).card : ℝ) := by
    exact_mod_cast hReimer T U
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- The finite-trace BK inequality for increasing traces, as a corollary of Reimer's cardinality
theorem on the same finite cube. -/
theorem finiteTraceBK_half_of_cardinalityReimerBound {ι : Type*} {E : Finset ι}
    (hReimer : FiniteTraceCardinalityReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E (1 / 2) (ReimerTraceOccurrence E T U) ≤
      finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) U :=
  finiteTraceBK_half_of_uniformReimerBound
    (finiteTraceUniformReimerBound_of_cardinalityReimerBound hReimer) hT hU

/-- The BK-shaped open-witness finite trace inequality at `p = 1/2`, as a corollary of Reimer's
cardinality theorem on the same finite cube. -/
theorem finiteTraceOpenBK_half_of_cardinalityReimerBound {ι : Type*} {E : Finset ι}
    (hReimer : FiniteTraceCardinalityReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    finiteBernoulliEventProbability E (1 / 2) (OpenTraceDisjointOccurrence E T U) ≤
      finiteBernoulliEventProbability E (1 / 2) T *
        finiteBernoulliEventProbability E (1 / 2) U :=
  finiteTraceOpenBK_half_of_uniformReimerBound
    (finiteTraceUniformReimerBound_of_cardinalityReimerBound hReimer) hT hU

/-- Product-measure BK for finite-trace cylinder events at `p = 1/2`, as a direct corollary of
Reimer's cardinality theorem on the finite support. -/
theorem setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_cardinalityReimerBound
    {ι : Type*} {E : Finset ι} (hReimer : FiniteTraceCardinalityReimerBound E)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real
        (OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U)) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E T) *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E U) :=
  setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_uniformReimerBound
    (finiteTraceUniformReimerBound_of_cardinalityReimerBound hReimer) hT hU

/-- Product-measure BK for finite-trace cylinder events at `p = 1/2`, as a corollary of
Reimer's uniform complement-form theorem stated only on full finite cubes. -/
theorem setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_forall_univ_uniformReimerBound
    {ι : Type u} {E : Finset ι}
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α))
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real
        (OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U)) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E T) *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E U) :=
  setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_uniformReimerBound
    (finiteTraceUniformReimerBound_of_forall_univ_fintype hReimer E) hT hU

/-- Product-measure BK for finite-trace cylinder events at `p = 1/2`, as a corollary of
Reimer's cardinality theorem stated only on full finite cubes. -/
theorem setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_forall_univ_cardinalityReimerBound
    {ι : Type u} {E : Finset ι}
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α))
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace E T) (hU : IsIncreasingTrace E U) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real
        (OpenDisjointOccurrence (eventOfTrace E T) (eventOfTrace E U)) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E T) *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real (eventOfTrace E U) :=
  setBernoulli_real_openDisjointOccurrence_eventOfTrace_le_mul_half_of_cardinalityReimerBound
    (finiteTraceCardinalityReimerBound_of_forall_univ_fintype hReimer E) hT hU

theorem traceForces_empty_iff {ι : Type*} {T : Set (Finset ι)} :
    TraceForces (∅ : Finset ι) ∅ ∅ T ↔ (∅ : Finset ι) ∈ T := by
  constructor
  · intro h
    exact h ∅ (by simp) (by simp)
  · intro h t ht _hagree
    have ht_empty : t = ∅ := by
      exact Finset.eq_empty_iff_forall_notMem.mpr fun e he ↦ by
        simpa using ht he
    simpa [ht_empty] using h

theorem mem_reimerTraceOccurrence_empty_iff {ι : Type*} {s : Finset ι}
    {T U : Set (Finset ι)} :
    s ∈ ReimerTraceOccurrence (∅ : Finset ι) T U ↔
      s = ∅ ∧ (∅ : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U := by
  constructor
  · intro hs
    rcases hs with ⟨hs_empty_subset, K, hK_empty_subset, hK, hEK⟩
    have hs_empty : s = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun e he ↦ by
        simpa using hs_empty_subset he
    have hK_empty : K = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun e he ↦ by
        simpa using hK_empty_subset he
    subst s
    subst K
    exact ⟨rfl, (traceForces_empty_iff.mp hK), (traceForces_empty_iff.mp (by simpa using hEK))⟩
  · rintro ⟨rfl, hT, hU⟩
    refine ⟨by simp, ∅, by simp, traceForces_empty_iff.mpr hT, ?_⟩
    simpa using traceForces_empty_iff.mpr hU

theorem finiteTraceEventFamily_empty_card {ι : Type*} (T : Set (Finset ι)) :
    (finiteTraceEventFamily (∅ : Finset ι) T).card =
      if (∅ : Finset ι) ∈ T then 1 else 0 := by
  by_cases hT : (∅ : Finset ι) ∈ T <;>
    simp [finiteTraceEventFamily, Finset.filter_singleton, hT]

theorem finiteTraceCardinalityReimerBound_empty {ι : Type*} :
    FiniteTraceCardinalityReimerBound (∅ : Finset ι) := by
  intro T U
  rw [finiteTraceEventFamily_empty_card (ReimerTraceOccurrence (∅ : Finset ι) T U),
    finiteTraceEventFamily_empty_card (T ∩ TraceComplement (∅ : Finset ι) U)]
  by_cases hT : (∅ : Finset ι) ∈ T <;>
    by_cases hU : (∅ : Finset ι) ∈ U <;>
    simp [TraceComplement, mem_reimerTraceOccurrence_empty_iff, hT, hU]

theorem finiteTraceReimerBound_empty {ι : Type*} (p : ℝ) :
    FiniteTraceReimerBound (∅ : Finset ι) p := by
  intro T U
  by_cases hT : (∅ : Finset ι) ∈ T
  · by_cases hU : (∅ : Finset ι) ∈ U
    · have hbox : (∅ : Finset ι) ∈ ReimerTraceOccurrence (∅ : Finset ι) T U := by
        exact (mem_reimerTraceOccurrence_empty_iff (s := (∅ : Finset ι))).mpr ⟨rfl, hT, hU⟩
      simp [finiteBernoulliEventProbability, finiteBernoulliExpectation, hT, hU, hbox]
    · have hbox : (∅ : Finset ι) ∉ ReimerTraceOccurrence (∅ : Finset ι) T U := by
        intro h
        exact hU ((mem_reimerTraceOccurrence_empty_iff (s := (∅ : Finset ι))).mp h).2.2
      simp [finiteBernoulliEventProbability, finiteBernoulliExpectation, hT, hU, hbox]
  · have hbox : (∅ : Finset ι) ∉ ReimerTraceOccurrence (∅ : Finset ι) T U := by
      intro h
      exact hT ((mem_reimerTraceOccurrence_empty_iff (s := (∅ : Finset ι))).mp h).2.1
    simp [finiteBernoulliEventProbability, finiteBernoulliExpectation, hT, hbox]

theorem finiteBernoulliEventProbability_singleton {ι : Type*} (a : ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliEventProbability ({a} : Finset ι) p T =
      (if (∅ : Finset ι) ∈ T then 1 - p else 0) +
        (if ({a} : Finset ι) ∈ T then p else 0) := by
  have hpowerset : ({a} : Finset ι).powerset = ({∅, {a}} : Finset (Finset ι)) := by
    ext s
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  by_cases h0 : (∅ : Finset ι) ∈ T <;> by_cases h1 : ({a} : Finset ι) ∈ T <;>
    simp [finiteBernoulliEventProbability, finiteBernoulliExpectation, hpowerset, h0, h1]

theorem finiteTraceEventFamily_singleton_card {ι : Type*} (a : ι)
    (T : Set (Finset ι)) :
    (finiteTraceEventFamily ({a} : Finset ι) T).card =
      (if (∅ : Finset ι) ∈ T then 1 else 0) +
        (if ({a} : Finset ι) ∈ T then 1 else 0) := by
  have hpowerset : ({a} : Finset ι).powerset = ({∅, {a}} : Finset (Finset ι)) := by
    ext s
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  have hne : (∅ : Finset ι) ≠ {a} := by simp
  by_cases h0 : (∅ : Finset ι) ∈ T <;> by_cases h1 : ({a} : Finset ι) ∈ T <;>
    simp [finiteTraceEventFamily, hpowerset, Finset.filter_insert, Finset.filter_singleton,
      h0, h1, hne]

theorem finiteTraceCardinalityReimerBound_singleton {ι : Type*} (a : ι) :
    FiniteTraceCardinalityReimerBound ({a} : Finset ι) := by
  intro T U
  rw [finiteTraceEventFamily_singleton_card a
      (ReimerTraceOccurrence ({a} : Finset ι) T U),
    finiteTraceEventFamily_singleton_card a (T ∩ TraceComplement ({a} : Finset ι) U)]
  by_cases hT0 : (∅ : Finset ι) ∈ T <;>
    by_cases hT1 : ({a} : Finset ι) ∈ T <;>
    by_cases hU0 : (∅ : Finset ι) ∈ U <;>
    by_cases hU1 : ({a} : Finset ι) ∈ U <;>
    simp [ReimerTraceOccurrence, TraceForces, TraceComplement, hT0, hT1, hU0, hU1]

theorem finiteTraceCardinalityReimerBound_of_card_le_one {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 1) :
    FiniteTraceCardinalityReimerBound E := by
  classical
  have hcases : E.card = 0 ∨ E.card = 1 := by omega
  rcases hcases with h0 | h1
  · have hE_empty : E = ∅ := Finset.card_eq_zero.mp h0
    subst E
    exact finiteTraceCardinalityReimerBound_empty
  · rcases Finset.card_eq_one.mp h1 with ⟨a, hE_singleton⟩
    subst E
    exact finiteTraceCardinalityReimerBound_singleton a

theorem finiteTraceReimerBound_singleton {ι : Type*} (a : ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteTraceReimerBound ({a} : Finset ι) p := by
  intro T U
  rw [finiteBernoulliEventProbability_singleton a p
      (ReimerTraceOccurrence ({a} : Finset ι) T U),
    finiteBernoulliEventProbability_singleton a p T,
    finiteBernoulliEventProbability_singleton a p U]
  by_cases hT0 : (∅ : Finset ι) ∈ T <;>
    by_cases hT1 : ({a} : Finset ι) ∈ T <;>
    by_cases hU0 : (∅ : Finset ι) ∈ U <;>
    by_cases hU1 : ({a} : Finset ι) ∈ U <;>
    simp [ReimerTraceOccurrence, TraceForces, hT0, hT1, hU0, hU1] <;>
    nlinarith [hp0, hp1]

theorem subset_pair_iff_eq {ι : Type*} {a b : ι} (hab : a ≠ b) (s : Finset ι) :
    s ⊆ ({a, b} : Finset ι) ↔
      s = ∅ ∨ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  constructor
  · intro hsub
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · right
        right
        right
        ext x
        constructor
        · intro hx
          have hxpair := hsub hx
          simp at hxpair ⊢
          exact hxpair
        · intro hx
          simp at hx
          rcases hx with rfl | rfl
          · exact ha
          · exact hb
      · right
        left
        ext x
        constructor
        · intro hx
          have hxpair := hsub hx
          simp at hxpair
          rcases hxpair with rfl | rfl
          · simp
          · exact (hb hx).elim
        · intro hx
          have hxa : x = a := by
            simpa using hx
          simpa [hxa] using ha
    · by_cases hb : b ∈ s
      · right
        right
        left
        ext x
        constructor
        · intro hx
          have hxpair := hsub hx
          simp at hxpair
          rcases hxpair with rfl | rfl
          · exact (ha hx).elim
          · simp
        · intro hx
          have hxb : x = b := by
            simpa using hx
          simpa [hxb] using hb
      · left
        exact Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
          have hxpair := hsub hx
          simp at hxpair
          rcases hxpair with rfl | rfl
          · exact ha hx
          · exact hb hx
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem powerset_pair {ι : Type*} {a b : ι} (hab : a ≠ b) :
    ({a, b} : Finset ι).powerset =
      ({∅, {a}, {b}, {a, b}} : Finset (Finset ι)) := by
  ext s
  rw [Finset.mem_powerset, subset_pair_iff_eq hab s]
  simp

theorem finiteBernoulliEventProbability_pair {ι : Type*} {a b : ι}
    (hab : a ≠ b) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliEventProbability ({a, b} : Finset ι) p T =
      (if (∅ : Finset ι) ∈ T then (1 - p) ^ 2 else 0) +
        (if ({a} : Finset ι) ∈ T then p * (1 - p) else 0) +
        (if ({b} : Finset ι) ∈ T then p * (1 - p) else 0) +
        (if ({a, b} : Finset ι) ∈ T then p ^ 2 else 0) := by
  have hpowerset := powerset_pair (a := a) (b := b) hab
  have h_empty_ne_a : (∅ : Finset ι) ≠ {a} := by simp
  have h_empty_ne_b : (∅ : Finset ι) ≠ {b} := by simp
  have h_empty_ne_ab : (∅ : Finset ι) ≠ {a, b} :=
    (Finset.insert_ne_empty a ({b} : Finset ι)).symm
  have h_a_ne_b : ({a} : Finset ι) ≠ {b} := by
    intro h
    have ha_mem : a ∈ ({b} : Finset ι) := by
      rw [← h]
      simp
    exact hab (Finset.mem_singleton.mp ha_mem)
  have h_a_ne_ab : ({a} : Finset ι) ≠ {a, b} := by
    intro h
    have hb_mem : b ∈ ({a} : Finset ι) := by
      rw [h]
      simp
    exact hab (Finset.mem_singleton.mp hb_mem).symm
  have h_b_ne_ab : ({b} : Finset ι) ≠ {a, b} := by
    intro h
    have ha_mem : a ∈ ({b} : Finset ι) := by
      rw [h]
      simp
    exact hab (Finset.mem_singleton.mp ha_mem)
  by_cases h0 : (∅ : Finset ι) ∈ T <;>
    by_cases ha : ({a} : Finset ι) ∈ T <;>
    by_cases hb : ({b} : Finset ι) ∈ T <;>
    by_cases habT : ({a, b} : Finset ι) ∈ T <;>
    simp [finiteBernoulliEventProbability, finiteBernoulliExpectation, hpowerset, h0, ha, hb,
      habT, hab, h_empty_ne_a, h_empty_ne_b, h_empty_ne_ab, h_a_ne_b, h_a_ne_ab,
      h_b_ne_ab] <;>
    ring

theorem finiteTraceEventFamily_pair_card {ι : Type*} {a b : ι} (hab : a ≠ b)
    (T : Set (Finset ι)) :
    (finiteTraceEventFamily ({a, b} : Finset ι) T).card =
      (if (∅ : Finset ι) ∈ T then 1 else 0) +
        (if ({a} : Finset ι) ∈ T then 1 else 0) +
          (if ({b} : Finset ι) ∈ T then 1 else 0) +
            (if ({a, b} : Finset ι) ∈ T then 1 else 0) := by
  have hpowerset := powerset_pair (a := a) (b := b) hab
  have h_empty_ne_a : (∅ : Finset ι) ≠ {a} := by simp
  have h_empty_ne_b : (∅ : Finset ι) ≠ {b} := by simp
  have h_empty_ne_ab : (∅ : Finset ι) ≠ {a, b} :=
    (Finset.insert_ne_empty a ({b} : Finset ι)).symm
  have h_a_ne_b : ({a} : Finset ι) ≠ {b} := by
    intro h
    have ha_mem : a ∈ ({b} : Finset ι) := by
      rw [← h]
      simp
    exact hab (Finset.mem_singleton.mp ha_mem)
  have h_a_ne_ab : ({a} : Finset ι) ≠ {a, b} := by
    intro h
    have hb_mem : b ∈ ({a} : Finset ι) := by
      rw [h]
      simp
    exact hab (Finset.mem_singleton.mp hb_mem).symm
  have h_b_ne_ab : ({b} : Finset ι) ≠ {a, b} := by
    intro h
    have ha_mem : a ∈ ({b} : Finset ι) := by
      rw [h]
      simp
    exact hab (Finset.mem_singleton.mp ha_mem)
  by_cases h0 : (∅ : Finset ι) ∈ T <;>
    by_cases ha : ({a} : Finset ι) ∈ T <;>
    by_cases hb : ({b} : Finset ι) ∈ T <;>
    by_cases habT : ({a, b} : Finset ι) ∈ T <;>
    simp [finiteTraceEventFamily, hpowerset, Finset.filter_insert, Finset.filter_singleton,
      h0, ha, hb, habT, h_empty_ne_a, h_empty_ne_b, h_empty_ne_ab, h_a_ne_b,
      h_a_ne_ab, h_b_ne_ab]

theorem traceForces_pair_empty_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {s : Finset ι} {T : Set (Finset ι)} :
    TraceForces ({a, b} : Finset ι) ∅ s T ↔
      (∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧
        ({b} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T := by
  constructor
  · intro h
    exact ⟨h ∅ (by simp) (by simp), h {a} (by simp) (by simp),
      h {b} (by simp) (by simp), h {a, b} (by simp) (by simp)⟩
  · intro h t ht _hagree
    rcases (subset_pair_iff_eq hab t).mp ht with rfl | rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

theorem traceForces_pair_all_iff {ι : Type*} {a b : ι}
    {s : Finset ι} (hs : s ⊆ ({a, b} : Finset ι)) {T : Set (Finset ι)} :
    TraceForces ({a, b} : Finset ι) ({a, b} : Finset ι) s T ↔ s ∈ T := by
  constructor
  · intro h
    exact h s hs (by intro e _he; rfl)
  · intro hsT t ht hagree
    have hts : t = s := by
      ext y
      constructor
      · intro hy
        exact (hagree y (ht hy)).mp hy
      · intro hy
        exact (hagree y (hs hy)).mpr hy
    simpa [hts] using hsT

theorem traceForces_pair_left_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {s : Finset ι} {T : Set (Finset ι)} :
    TraceForces ({a, b} : Finset ι) ({a} : Finset ι) s T ↔
      if a ∈ s then ({a} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T
      else (∅ : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T := by
  by_cases ha : a ∈ s
  · simp [ha]
    constructor
    · intro h
      exact ⟨h {a} (by simp) (by
          intro e he
          have hea : e = a := by
            simpa using he
          subst e
          simp [ha]),
        h {a, b} (by simp) (by
          intro e he
          have hea : e = a := by
            simpa using he
          subst e
          simp [ha])⟩
    · intro h t ht hagree
      rcases (subset_pair_iff_eq hab t).mp ht with rfl | rfl | rfl | rfl
      · have : a ∈ (∅ : Finset ι) := (hagree a (by simp)).mpr ha
        simp at this
      · exact h.1
      · have : a ∈ ({b} : Finset ι) := (hagree a (by simp)).mpr ha
        have hab' : a = b := Finset.mem_singleton.mp this
        exact (hab hab').elim
      · exact h.2
  · simp [ha]
    constructor
    · intro h
      exact ⟨h ∅ (by simp) (by simp [ha]), h {b} (by simp) (by
        intro e he
        have hea : e = a := by
          simpa using he
        subst e
        simp [ha, hab])⟩
    · intro h t ht hagree
      rcases (subset_pair_iff_eq hab t).mp ht with rfl | rfl | rfl | rfl
      · exact h.1
      · have : a ∈ s := (hagree a (by simp)).mp (by simp)
        exact (ha this).elim
      · exact h.2
      · have : a ∈ s := (hagree a (by simp)).mp (by simp)
        exact (ha this).elim

theorem traceForces_pair_right_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {s : Finset ι} {T : Set (Finset ι)} :
    TraceForces ({a, b} : Finset ι) ({b} : Finset ι) s T ↔
      if b ∈ s then ({b} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T
      else (∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T := by
  by_cases hb : b ∈ s
  · simp [hb]
    constructor
    · intro h
      exact ⟨h {b} (by simp) (by
          intro e he
          have heb : e = b := by
            simpa using he
          subst e
          simp [hb]),
        h {a, b} (by simp) (by
          intro e he
          have heb : e = b := by
            simpa using he
          subst e
          simp [hb])⟩
    · intro h t ht hagree
      rcases (subset_pair_iff_eq hab t).mp ht with rfl | rfl | rfl | rfl
      · have : b ∈ (∅ : Finset ι) := (hagree b (by simp)).mpr hb
        simp at this
      · have : b ∈ ({a} : Finset ι) := (hagree b (by simp)).mpr hb
        have hba : b = a := Finset.mem_singleton.mp this
        exact (hab hba.symm).elim
      · exact h.1
      · exact h.2
  · simp [hb]
    constructor
    · intro h
      exact ⟨h ∅ (by simp) (by simp [hb]), h {a} (by simp) (by
        intro e he
        have heb : e = b := by
          simpa using he
        subst e
        simp [hb, hab.symm])⟩
    · intro h t ht hagree
      rcases (subset_pair_iff_eq hab t).mp ht with rfl | rfl | rfl | rfl
      · exact h.1
      · exact h.2
      · have : b ∈ s := (hagree b (by simp)).mp (by simp)
        exact (hb this).elim
      · have : b ∈ s := (hagree b (by simp)).mp (by simp)
        exact (hb this).elim

theorem reimerTraceOccurrence_pair_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {s : Finset ι} {T U : Set (Finset ι)} :
    s ∈ ReimerTraceOccurrence ({a, b} : Finset ι) T U ↔
      s ⊆ ({a, b} : Finset ι) ∧
        ((TraceForces ({a, b} : Finset ι) ∅ s T ∧
            TraceForces ({a, b} : Finset ι) ({a, b} : Finset ι) s U) ∨
          (TraceForces ({a, b} : Finset ι) ({a} : Finset ι) s T ∧
            TraceForces ({a, b} : Finset ι) ({b} : Finset ι) s U) ∨
          (TraceForces ({a, b} : Finset ι) ({b} : Finset ι) s T ∧
            TraceForces ({a, b} : Finset ι) ({a} : Finset ι) s U) ∨
          (TraceForces ({a, b} : Finset ι) ({a, b} : Finset ι) s T ∧
            TraceForces ({a, b} : Finset ι) ∅ s U)) := by
  have hdiff_a : ({a, b} : Finset ι) \ ({a} : Finset ι) = {b} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxpair, hxa⟩
      simp at hxpair ⊢
      rcases hxpair with rfl | rfl
      · exact (hxa (by simp)).elim
      · rfl
    · intro hx
      have hxb : x = b := by
        simpa using hx
      subst x
      exact Finset.mem_sdiff.mpr ⟨by simp, by simp [hab.symm]⟩
  have hdiff_b : ({a, b} : Finset ι) \ ({b} : Finset ι) = {a} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxpair, hxb⟩
      simp at hxpair ⊢
      rcases hxpair with rfl | rfl
      · rfl
      · exact (hxb (by simp)).elim
    · intro hx
      have hxa : x = a := by
        simpa using hx
      subst x
      exact Finset.mem_sdiff.mpr ⟨by simp, by simp [hab]⟩
  constructor
  · intro hs
    rcases hs with ⟨hsE, K, hKE, hKT, hKU⟩
    refine ⟨hsE, ?_⟩
    rcases (subset_pair_iff_eq hab K).mp hKE with rfl | rfl | rfl | rfl
    · left
      exact ⟨by simpa using hKT, by simpa using hKU⟩
    · right
      left
      exact ⟨by simpa using hKT, by simpa [hdiff_a] using hKU⟩
    · right
      right
      left
      exact ⟨by simpa using hKT, by simpa [hdiff_b] using hKU⟩
    · right
      right
      right
      exact ⟨by simpa using hKT, by simpa using hKU⟩
  · rintro ⟨hsE, h⟩
    rcases h with h | h | h | h
    · refine ⟨hsE, ∅, by simp, h.1, ?_⟩
      simpa using h.2
    · refine ⟨hsE, ({a} : Finset ι), by simp, h.1, ?_⟩
      simpa [hdiff_a] using h.2
    · refine ⟨hsE, ({b} : Finset ι), by simp, h.1, ?_⟩
      simpa [hdiff_b] using h.2
    · refine ⟨hsE, ({a, b} : Finset ι), by simp, h.1, ?_⟩
      simpa using h.2

theorem mem_reimerTraceOccurrence_pair_empty_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {T U : Set (Finset ι)} :
    (∅ : Finset ι) ∈ ReimerTraceOccurrence ({a, b} : Finset ι) T U ↔
      ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          ({a, b} : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U) ∨
        ((∅ : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          (∅ : Finset ι) ∈ U ∧ ({a} : Finset ι) ∈ U) ∨
        ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧
          (∅ : Finset ι) ∈ U ∧ ({b} : Finset ι) ∈ U) ∨
        ((∅ : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U ∧ ({a} : Finset ι) ∈ U ∧
          ({b} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) := by
  rw [reimerTraceOccurrence_pair_iff hab]
  simp [traceForces_pair_empty_iff hab, traceForces_pair_all_iff,
    traceForces_pair_left_iff hab, traceForces_pair_right_iff hab]
  tauto

theorem mem_reimerTraceOccurrence_pair_left_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {T U : Set (Finset ι)} :
    ({a} : Finset ι) ∈ ReimerTraceOccurrence ({a, b} : Finset ι) T U ↔
      ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          ({a, b} : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ U) ∨
        (({a} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T ∧
          (∅ : Finset ι) ∈ U ∧ ({a} : Finset ι) ∈ U) ∨
        ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧
          ({a} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) ∨
        (({a} : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U ∧ ({a} : Finset ι) ∈ U ∧
          ({b} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) := by
  rw [reimerTraceOccurrence_pair_iff hab]
  simp [traceForces_pair_empty_iff hab, traceForces_pair_all_iff,
    traceForces_pair_left_iff hab, traceForces_pair_right_iff hab, hab, hab.symm]
  tauto

theorem mem_reimerTraceOccurrence_pair_right_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {T U : Set (Finset ι)} :
    ({b} : Finset ι) ∈ ReimerTraceOccurrence ({a, b} : Finset ι) T U ↔
      ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          ({a, b} : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ U) ∨
        ((∅ : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          ({b} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) ∨
        (({b} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T ∧
          (∅ : Finset ι) ∈ U ∧ ({b} : Finset ι) ∈ U) ∨
        (({b} : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U ∧ ({a} : Finset ι) ∈ U ∧
          ({b} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) := by
  rw [reimerTraceOccurrence_pair_iff hab]
  simp [traceForces_pair_empty_iff hab, traceForces_pair_all_iff,
    traceForces_pair_left_iff hab, traceForces_pair_right_iff hab, hab]
  tauto

theorem mem_reimerTraceOccurrence_pair_all_iff {ι : Type*} {a b : ι} (hab : a ≠ b)
    {T U : Set (Finset ι)} :
    ({a, b} : Finset ι) ∈ ReimerTraceOccurrence ({a, b} : Finset ι) T U ↔
      ((∅ : Finset ι) ∈ T ∧ ({a} : Finset ι) ∈ T ∧ ({b} : Finset ι) ∈ T ∧
          ({a, b} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ U) ∨
        (({a} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T ∧
          ({b} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) ∨
        (({b} : Finset ι) ∈ T ∧ ({a, b} : Finset ι) ∈ T ∧
          ({a} : Finset ι) ∈ U ∧ ({a, b} : Finset ι) ∈ U) ∨
        (({a, b} : Finset ι) ∈ T ∧ (∅ : Finset ι) ∈ U ∧
          ({a} : Finset ι) ∈ U ∧ ({b} : Finset ι) ∈ U ∧
          ({a, b} : Finset ι) ∈ U) := by
  rw [reimerTraceOccurrence_pair_iff hab]
  simp [traceForces_pair_empty_iff hab, traceForces_pair_all_iff,
    traceForces_pair_left_iff hab, traceForces_pair_right_iff hab, hab, hab.symm]
  tauto

set_option maxHeartbeats 3000000 in
theorem finiteTraceCardinalityReimerBound_pair {ι : Type*} {a b : ι} (hab : a ≠ b) :
    FiniteTraceCardinalityReimerBound ({a, b} : Finset ι) := by
  intro T U
  have hdiff_empty : ({a, b} : Finset ι) \ (∅ : Finset ι) = {a, b} := by simp
  have hdiff_a : ({a, b} : Finset ι) \ ({a} : Finset ι) = {b} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxpair, hxa⟩
      simp at hxpair ⊢
      rcases hxpair with rfl | rfl
      · exact (hxa (by simp)).elim
      · rfl
    · intro hx
      have hxb : x = b := by
        simpa using hx
      subst x
      exact Finset.mem_sdiff.mpr ⟨by simp, by simp [hab.symm]⟩
  have hdiff_b : ({a, b} : Finset ι) \ ({b} : Finset ι) = {a} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxpair, hxb⟩
      simp at hxpair ⊢
      rcases hxpair with rfl | rfl
      · rfl
      · exact (hxb (by simp)).elim
    · intro hx
      have hxa : x = a := by
        simpa using hx
      subst x
      exact Finset.mem_sdiff.mpr ⟨by simp, by simp [hab]⟩
  rw [finiteTraceEventFamily_pair_card hab
      (ReimerTraceOccurrence ({a, b} : Finset ι) T U),
    finiteTraceEventFamily_pair_card hab (T ∩ TraceComplement ({a, b} : Finset ι) U)]
  by_cases hT0 : (∅ : Finset ι) ∈ T <;>
    by_cases hTa : ({a} : Finset ι) ∈ T <;>
    by_cases hTb : ({b} : Finset ι) ∈ T <;>
    by_cases hTab : ({a, b} : Finset ι) ∈ T <;>
    by_cases hU0 : (∅ : Finset ι) ∈ U <;>
    by_cases hUa : ({a} : Finset ι) ∈ U <;>
    by_cases hUb : ({b} : Finset ι) ∈ U <;>
    by_cases hUab : ({a, b} : Finset ι) ∈ U <;>
    simp [mem_reimerTraceOccurrence_pair_empty_iff hab,
      mem_reimerTraceOccurrence_pair_left_iff hab,
      mem_reimerTraceOccurrence_pair_right_iff hab,
      mem_reimerTraceOccurrence_pair_all_iff hab, TraceComplement, hdiff_empty, hdiff_a,
      hdiff_b, hT0, hTa, hTb, hTab, hU0, hUa, hUb, hUab]

theorem finiteTraceCardinalityReimerBound_of_card_le_two {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 2) :
    FiniteTraceCardinalityReimerBound E := by
  classical
  have hcases : E.card = 0 ∨ E.card = 1 ∨ E.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hE_empty : E = ∅ := Finset.card_eq_zero.mp h0
    subst E
    exact finiteTraceCardinalityReimerBound_empty
  · rcases Finset.card_eq_one.mp h1 with ⟨a, hE_singleton⟩
    subst E
    exact finiteTraceCardinalityReimerBound_singleton a
  · rcases Finset.card_eq_two.mp h2 with ⟨a, b, hab, hE_pair⟩
    subst E
    exact finiteTraceCardinalityReimerBound_pair hab

/-- Reimer's cardinality inequality for supports of cardinality at most three. The
three-coordinate case is obtained by transporting the full `Fin 3` reflected slice. -/
theorem finiteTraceCardinalityReimerBound_of_card_le_three {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 3) :
    FiniteTraceCardinalityReimerBound E := by
  classical
  have hcases : E.card = 0 ∨ E.card = 1 ∨ E.card = 2 ∨ E.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact finiteTraceCardinalityReimerBound_of_card_le_two (by omega)
  · exact finiteTraceCardinalityReimerBound_of_card_le_two (by omega)
  · exact finiteTraceCardinalityReimerBound_of_card_le_two (by omega)
  · exact finiteTraceCardinalityReimerBound_of_card_eq_three h3

set_option maxHeartbeats 3000000 in
/-- The weighted two-coordinate finite-cube Reimer inequality. This is the first nontrivial
finite-support Reimer endpoint beyond the one-coordinate truth table. -/
theorem finiteTraceReimerBound_pair {ι : Type*} {a b : ι} (hab : a ≠ b) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteTraceReimerBound ({a, b} : Finset ι) p := by
  intro T U
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have b0 : 0 ≤ (1 - p) ^ 4 := pow_nonneg hq0 4
  have b1 : 0 ≤ p * (1 - p) ^ 3 := mul_nonneg hp0 (pow_nonneg hq0 3)
  have b2 : 0 ≤ p ^ 2 * (1 - p) ^ 2 :=
    mul_nonneg (pow_nonneg hp0 2) (pow_nonneg hq0 2)
  have b3 : 0 ≤ p ^ 3 * (1 - p) := mul_nonneg (pow_nonneg hp0 3) hq0
  have b4 : 0 ≤ p ^ 4 := pow_nonneg hp0 4
  ring_nf at b0 b1 b2 b3 b4
  rw [finiteBernoulliEventProbability_pair hab p
      (ReimerTraceOccurrence ({a, b} : Finset ι) T U),
    finiteBernoulliEventProbability_pair hab p T,
    finiteBernoulliEventProbability_pair hab p U]
  by_cases hT0 : (∅ : Finset ι) ∈ T <;>
    by_cases hTa : ({a} : Finset ι) ∈ T <;>
    by_cases hTb : ({b} : Finset ι) ∈ T <;>
    by_cases hTab : ({a, b} : Finset ι) ∈ T <;>
    by_cases hU0 : (∅ : Finset ι) ∈ U <;>
    by_cases hUa : ({a} : Finset ι) ∈ U <;>
    by_cases hUb : ({b} : Finset ι) ∈ U <;>
    by_cases hUab : ({a, b} : Finset ι) ∈ U <;>
    simp [mem_reimerTraceOccurrence_pair_empty_iff hab,
      mem_reimerTraceOccurrence_pair_left_iff hab,
      mem_reimerTraceOccurrence_pair_right_iff hab,
      mem_reimerTraceOccurrence_pair_all_iff hab, hT0, hTa, hTb, hTab, hU0, hUa, hUb,
      hUab] <;>
    ring_nf <;>
    nlinarith [b0, b1, b2, b3, b4]

/-- The weighted finite-cube Reimer inequality for supports of cardinality at most two,
assembled from the empty, singleton, and two-coordinate truth-table proofs. -/
theorem finiteTraceReimerBound_of_card_le_two {ι : Type*} {E : Finset ι} {p : ℝ}
    (hE : E.card ≤ 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteTraceReimerBound E p := by
  classical
  have hcases : E.card = 0 ∨ E.card = 1 ∨ E.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hE_empty : E = ∅ := Finset.card_eq_zero.mp h0
    subst E
    exact finiteTraceReimerBound_empty p
  · rcases Finset.card_eq_one.mp h1 with ⟨a, hE_singleton⟩
    subst E
    exact finiteTraceReimerBound_singleton a hp0 hp1
  · rcases Finset.card_eq_two.mp h2 with ⟨a, b, hab, hE_pair⟩
    subst E
    exact finiteTraceReimerBound_pair hab hp0 hp1

/-- Grimmett Theorem 2.19, proved cardinality slice: the empty finite cube. -/
theorem grimmettTheorem219_cardinality_empty {ι : Type*} :
    FiniteTraceCardinalityReimerBound (∅ : Finset ι) :=
  finiteTraceCardinalityReimerBound_empty

/-- Grimmett Theorem 2.19, proved cardinality slice: one coordinate. -/
theorem grimmettTheorem219_cardinality_singleton {ι : Type*} (a : ι) :
    FiniteTraceCardinalityReimerBound ({a} : Finset ι) :=
  finiteTraceCardinalityReimerBound_singleton a

/-- Grimmett Theorem 2.19, proved cardinality slice: two coordinates. -/
theorem grimmettTheorem219_cardinality_pair {ι : Type*} {a b : ι} (hab : a ≠ b) :
    FiniteTraceCardinalityReimerBound ({a, b} : Finset ι) :=
  finiteTraceCardinalityReimerBound_pair hab

/-- Grimmett Theorem 2.19, proved cardinality slice: supports of size at most two. -/
theorem grimmettTheorem219_cardinality_of_card_le_two {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 2) :
    FiniteTraceCardinalityReimerBound E :=
  finiteTraceCardinalityReimerBound_of_card_le_two hE

/-- Grimmett Theorem 2.19, proved cardinality slice on the full three-coordinate cube. This
currently inherits the native-reflection axiom footprint of
`finiteTraceCardinalityReimerBound_univ_fin_three`. -/
theorem grimmettTheorem219_cardinality_univ_fin_three :
    FiniteTraceCardinalityReimerBound (Finset.univ : Finset (Fin 3)) :=
  finiteTraceCardinalityReimerBound_univ_fin_three

/-- Grimmett Theorem 2.19, proved cardinality slice: any three-coordinate support, transported
from the full `Fin 3` cube. -/
theorem grimmettTheorem219_cardinality_of_card_eq_three {ι : Type*} {E : Finset ι}
    (hE : E.card = 3) :
    FiniteTraceCardinalityReimerBound E :=
  finiteTraceCardinalityReimerBound_of_card_eq_three hE

/-- Grimmett Theorem 2.19, proved cardinality slice: supports of size at most three. The
three-coordinate case currently inherits the native-reflection axiom footprint. -/
theorem grimmettTheorem219_cardinality_of_card_le_three {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 3) :
    FiniteTraceCardinalityReimerBound E :=
  finiteTraceCardinalityReimerBound_of_card_le_three hE

/-- Grimmett Theorem 2.19, uniform complement-form consequence of cardinality Reimer. -/
theorem grimmettTheorem219_uniform_of_cardinality {ι : Type*} {E : Finset ι}
    (hReimer : FiniteTraceCardinalityReimerBound E) :
    FiniteTraceUniformReimerBound E :=
  finiteTraceUniformReimerBound_of_cardinalityReimerBound hReimer

/-- Grimmett Theorem 2.19, proved uniform complement-form slice for supports of size at most
three. The three-coordinate case currently inherits the native-reflection axiom footprint. -/
theorem grimmettTheorem219_uniform_of_card_le_three {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 3) :
    FiniteTraceUniformReimerBound E :=
  grimmettTheorem219_uniform_of_cardinality
    (grimmettTheorem219_cardinality_of_card_le_three hE)

/-- Weighted finite-trace Reimer, proved endpoint slice at `p = 0`. -/
theorem grimmettTheorem219_weighted_zero {ι : Type*} (E : Finset ι) :
    FiniteTraceReimerBound E 0 :=
  finiteTraceReimerBound_zero E

/-- Weighted finite-trace Reimer, proved endpoint slice at `p = 1`. -/
theorem grimmettTheorem219_weighted_one {ι : Type*} (E : Finset ι) :
    FiniteTraceReimerBound E 1 :=
  finiteTraceReimerBound_one E

/-- Weighted finite-trace Reimer, proved slice for supports of size at most two and any
Bernoulli parameter. -/
theorem grimmettTheorem219_weighted_of_card_le_two {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 2) (p : I) :
    FiniteTraceReimerBound E (p : ℝ) :=
  finiteTraceReimerBound_of_card_le_two hE p.2.1 p.2.2

/-- A Reimer bound on the finite support `E`. This is an interface for an actual proof of
Reimer's theorem; it is deliberately a hypothesis rather than a project axiom. -/
def ReimerBoundOn {ι : Type*} (μ : Measure (Set ι)) (E : Finset ι) : Prop :=
  ∀ ⦃A B : Set (Set ι)⦄, DependsOn E A → DependsOn E B →
    μ.real (ReimerOccurrenceOn E A B) ≤ μ.real A * μ.real B

/-- A weighted finite-trace Reimer theorem on `E` discharges the Bernoulli product-measure
`ReimerBoundOn` on the same support. -/
theorem reimerBoundOn_setBernoulli_of_finiteTraceReimerBound {ι : Type*}
    (E : Finset ι) (p : I) (hReimer : FiniteTraceReimerBound E (p : ℝ)) :
    ReimerBoundOn (setBer((Set.univ : Set ι), p)) E := by
  intro A B hA hB
  rw [(dependsOn_reimerOccurrenceOn (E := E) (A := A) (B := B)).setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hA.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    hB.setBernoulli_real_eq_finiteBernoulliEventProbability p,
    finiteBernoulliEventProbability_eventTrace_reimerOccurrenceOn hA hB p]
  exact hReimer (eventTrace E A : Set (Finset ι)) (eventTrace E B : Set (Finset ι))

theorem reimerBoundOn_setBernoulli_empty {ι : Type*} (p : I) :
    ReimerBoundOn (setBer((Set.univ : Set ι), p)) (∅ : Finset ι) :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound (∅ : Finset ι) p
    (finiteTraceReimerBound_empty (p : ℝ))

theorem reimerBoundOn_setBernoulli_singleton {ι : Type*} (a : ι) (p : I) :
    ReimerBoundOn (setBer((Set.univ : Set ι), p)) ({a} : Finset ι) :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound ({a} : Finset ι) p
    (finiteTraceReimerBound_singleton a p.2.1 p.2.2)

theorem reimerBoundOn_setBernoulli_pair {ι : Type*} {a b : ι} (hab : a ≠ b) (p : I) :
    ReimerBoundOn (setBer((Set.univ : Set ι), p)) ({a, b} : Finset ι) :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound ({a, b} : Finset ι) p
    (finiteTraceReimerBound_pair hab p.2.1 p.2.2)

theorem reimerBoundOn_setBernoulli_of_card_le_two {ι : Type*} {E : Finset ι}
    (hE : E.card ≤ 2) (p : I) :
    ReimerBoundOn (setBer((Set.univ : Set ι), p)) E :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound E p
    (finiteTraceReimerBound_of_card_le_two hE p.2.1 p.2.2)

theorem reimerBoundOn_setBernoulli_zero {ι : Type*} (E : Finset ι) :
    ReimerBoundOn (setBer((Set.univ : Set ι), (0 : I))) E :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound E (0 : I) (by
    simpa using finiteTraceReimerBound_zero E)

theorem reimerBoundOn_setBernoulli_one {ι : Type*} (E : Finset ι) :
    ReimerBoundOn (setBer((Set.univ : Set ι), (1 : I))) E :=
  reimerBoundOn_setBernoulli_of_finiteTraceReimerBound E (1 : I) (by
    simpa using finiteTraceReimerBound_one E)

/-- If `G` contains finite supports for `A` and `B`, then Reimer's finite box inequality on
`G` implies the binary BK estimate for `A ∘ B`. -/
theorem measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset {ι : Type*}
    {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    {E F G : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : ReimerBoundOn μ G) :
    μ.real (DisjointOccurrence A B) ≤ μ.real A * μ.real B := by
  calc
    μ.real (DisjointOccurrence A B) ≤ μ.real (ReimerOccurrenceOn G A B) :=
      measureReal_mono
        (disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn_of_subset hA hB hEG hFG)
    _ ≤ μ.real A * μ.real B :=
      hReimer (hA.mono hEG) (hB.mono hFG)

/-- Finite-support BK is a formal corollary of Reimer's finite box inequality. -/
theorem measureReal_disjointOccurrence_le_mul_of_reimerBoundOn {ι : Type*}
    {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ReimerBoundOn μ (E ∪ F)) :
    μ.real (DisjointOccurrence A B) ≤ μ.real A * μ.real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hReimer

/-- Reimer's finite box inequality implies textbook BK for open disjoint occurrence of
increasing events on finite supports. -/
theorem measureReal_openDisjointOccurrence_le_mul_of_reimerBoundOn_of_subset {ι : Type*}
    {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : ReimerBoundOn μ G) :
    μ.real (OpenDisjointOccurrence A B) ≤ μ.real A * μ.real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset hA hB hEG hFG
    hReimer

/-- Finite-support textbook BK for open disjoint occurrence, as a direct corollary of Reimer's
finite box inequality. -/
theorem measureReal_openDisjointOccurrence_le_mul_of_reimerBoundOn {ι : Type*}
    {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ReimerBoundOn μ (E ∪ F)) :
    μ.real (OpenDisjointOccurrence A B) ≤ μ.real A * μ.real B :=
  measureReal_openDisjointOccurrence_le_mul_of_reimerBoundOn_of_subset
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hReimer

theorem setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_singleton
    {ι : Type*} (a : ι) (p : I) {A B : Set (Set ι)}
    (hA : DependsOn ({a} : Finset ι) A) (hB : DependsOn ({a} : Finset ι) B) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset hA hB
    (by intro e he; simpa using he)
    (by intro e he; simpa using he)
    (reimerBoundOn_setBernoulli_singleton a p)

theorem setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_pair
    {ι : Type*} {a b : ι} (hab : a ≠ b) (p : I) {A B : Set (Set ι)}
    (hA : DependsOn ({a, b} : Finset ι) A) (hB : DependsOn ({a, b} : Finset ι) B) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset hA hB
    (by intro e he; simpa using he)
    (by intro e he; simpa using he)
    (reimerBoundOn_setBernoulli_pair hab p)

/-- Unconditional Bernoulli-product BK when both events are supported inside a common support
with at most two coordinates. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_card_le_two_of_subset
    {ι : Type*} (p : I) {E F G : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hEG : E ⊆ G) (hFG : F ⊆ G) (hG : G.card ≤ 2) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn_of_subset hA hB hEG hFG
    (reimerBoundOn_setBernoulli_of_card_le_two hG p)

/-- Unconditional Bernoulli-product BK for events whose combined finite support has at most two
coordinates. This is the largest currently proved finite-support slice of BK in this file. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_union_card_le_two
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 2) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_card_le_two_of_subset p hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hEF

theorem setBernoulli_real_disjointOccurrence_le_mul_zero
    {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (setBer((Set.univ : Set ι), (0 : I))).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), (0 : I))).real A *
        (setBer((Set.univ : Set ι), (0 : I))).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn hA hB
    (reimerBoundOn_setBernoulli_zero (E ∪ F))

theorem setBernoulli_real_disjointOccurrence_le_mul_one
    {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (setBer((Set.univ : Set ι), (1 : I))).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), (1 : I))).real A *
        (setBer((Set.univ : Set ι), (1 : I))).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn hA hB
    (reimerBoundOn_setBernoulli_one (E ∪ F))

/-- Uniform finite-support BK for increasing events, as a direct corollary of Reimer's
uniform complement-form inequality on a common support. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    {ι : Type*} {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceUniformReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  let μ : Measure (Set ι) := setBer((Set.univ : Set ι), unitIntervalHalf)
  have hAdepG : DependsOn G A := hA.mono hEG
  have hBdepG : DependsOn G B := hB.mono hFG
  have hfinite :=
    finiteTraceBK_half_of_uniformReimerBound hReimer
      (hAinc.eventTrace (E := G)) (hBinc.eventTrace (E := G))
  calc
    μ.real (DisjointOccurrence A B) ≤ μ.real (ReimerOccurrenceOn G A B) :=
      measureReal_mono
        (disjointOccurrence_subset_reimerOccurrenceOn_of_dependsOn_of_subset hA hB hEG hFG)
    _ = finiteBernoulliEventProbability G (1 / 2)
        (ReimerTraceOccurrence G (eventTrace G A : Set (Finset ι))
          (eventTrace G B : Set (Finset ι))) := by
      rw [(dependsOn_reimerOccurrenceOn (E := G) (A := A) (B := B)).setBernoulli_real_eq_finiteBernoulliEventProbability unitIntervalHalf,
        finiteBernoulliEventProbability_eventTrace_reimerOccurrenceOn hAdepG hBdepG
          unitIntervalHalf]
      simp
    _ ≤ finiteBernoulliEventProbability G (1 / 2) (eventTrace G A) *
        finiteBernoulliEventProbability G (1 / 2) (eventTrace G B) :=
      hfinite
    _ = μ.real A * μ.real B := by
      rw [hAdepG.setBernoulli_real_eq_finiteBernoulliEventProbability unitIntervalHalf,
        hBdepG.setBernoulli_real_eq_finiteBernoulliEventProbability unitIntervalHalf]
      simp

/-- Uniform finite-support BK for increasing events, as a corollary of Reimer's complement-form
inequality stated only on full finite cubes. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    {ι : Type u} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    (finiteTraceUniformReimerBound_of_forall_univ_fintype hReimer (E ∪ F))

/-- Uniform finite-support BK for textbook open disjoint occurrence, as a corollary of
Reimer's complement-form inequality stated only on full finite cubes. -/
theorem setBernoulli_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    {ι : Type u} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    hAinc hBinc hA hB hReimer

/-- Uniform finite-support BK for increasing events, as a corollary of Reimer's cardinality
theorem on a common support. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    {ι : Type*} {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceCardinalityReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    hAinc hBinc hA hB hEG hFG
    (finiteTraceUniformReimerBound_of_cardinalityReimerBound hReimer)

/-- Uniform Bernoulli-product BK for increasing events supported inside a common support with
at most three coordinates. This is a direct low-support corollary of the cardinal Reimer slice. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_card_le_three_of_subset
    {ι : Type*} {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hEG : E ⊆ G) (hFG : F ⊆ G) (hG : G.card ≤ 3) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    hAinc hBinc hA hB hEG hFG
    (finiteTraceCardinalityReimerBound_of_card_le_three hG)

/-- Uniform Bernoulli-product BK for increasing events whose combined support has at most
three coordinates. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_union_card_le_three
    {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 3) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_card_le_three_of_subset
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hEF

/-- Uniform textbook open-occurrence BK for increasing events whose combined support has at most
three coordinates. -/
theorem setBernoulli_real_openDisjointOccurrence_le_mul_half_of_dependsOn_union_card_le_three
    {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 3) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_union_card_le_three
    hAinc hBinc hA hB hEF

/-- Uniform finite-support BK for increasing events, as a direct all-support corollary of
Reimer's cardinality theorem on every finite cube. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound
    {ι : Type*} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, FiniteTraceCardinalityReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    (hReimer (E ∪ F))

/-- Uniform finite-support BK for increasing events, as a corollary of Reimer's cardinality
theorem stated only on full finite cubes. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound
    {ι : Type u} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound
    hAinc hBinc hA hB
    (fun G ↦ finiteTraceCardinalityReimerBound_of_forall_univ_fintype hReimer G)

/-- The generic Bernoulli-product finite-support BK bound, conditional on Reimer's theorem. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_reimerBoundOn {ι : Type*} (p : I)
    {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, ReimerBoundOn (setBer((Set.univ : Set ι), p)) G) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  measureReal_disjointOccurrence_le_mul_of_reimerBoundOn hA hB (hReimer _)

/-- The generic Bernoulli-product finite-support BK bound as a direct corollary of a
finite-trace Reimer theorem on every finite support. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_of_reimerBoundOn p hA hB fun G ↦
    reimerBoundOn_setBernoulli_of_finiteTraceReimerBound G p (hReimer G)

/-- The generic Bernoulli-product finite-support BK bound as a direct corollary of weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem setBernoulli_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (DisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound p hA hB
    (fun G ↦ finiteTraceReimerBound_of_forall_univ_fintype (p : ℝ) hReimer G)

/-- The generic Bernoulli-product finite-support BK bound for textbook open disjoint occurrence,
as a direct corollary of weighted finite-trace Reimer on every finite support. -/
theorem setBernoulli_real_openDisjointOccurrence_le_mul_of_finiteTraceReimerBound
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound p hA hB
    hReimer

/-- The generic Bernoulli-product finite-support BK bound for textbook open disjoint occurrence,
as a direct corollary of weighted finite-trace Reimer stated only on full finite cubes. -/
theorem setBernoulli_real_openDisjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound p
    hA hB hReimer

/-- Source-facing homogeneous finite-product form of Grimmett Theorem 2.12, proved directly
from Grimmett's two-copy BK argument. Grimmett's printed Theorem 2.12 allows inhomogeneous
product coordinates; this wrapper records the homogeneous `setBer` version used by the
bond-percolation specialization. -/
theorem grimmettTheorem212_homogeneous
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_openDisjointOccurrence_le_mul_of_dependsOn_direct
    p hAinc hBinc hA hB

/-- Source-facing homogeneous finite-product form of Grimmett Theorem 2.12, proved as a
special corollary of Reimer's finite box inequality on every finite support. Grimmett's printed
Theorem 2.12 allows inhomogeneous product coordinates; this wrapper records the homogeneous
`setBer` version used by the bond-percolation specialization. -/
theorem grimmettTheorem212_homogeneous_of_reimerBoundOn
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, ReimerBoundOn (setBer((Set.univ : Set ι), p)) G) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  measureReal_openDisjointOccurrence_le_mul_of_reimerBoundOn
    hAinc hBinc hA hB (hReimer _)

/-- Source-facing homogeneous finite-product form of Grimmett Theorem 2.12, from weighted
finite-trace Reimer on every finite support. -/
theorem grimmettTheorem212_homogeneous_of_finiteTraceReimerBound
    {ι : Type*} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_openDisjointOccurrence_le_mul_of_finiteTraceReimerBound
    p hAinc hBinc hA hB hReimer

/-- Source-facing homogeneous finite-product form of Grimmett Theorem 2.12, from weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem grimmettTheorem212_homogeneous_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), p)).real A *
        (setBer((Set.univ : Set ι), p)).real B :=
  setBernoulli_real_openDisjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    p hAinc hBinc hA hB hReimer

/-- Source-facing homogeneous `p = 1/2` form of Grimmett Theorem 2.12, from Reimer's
uniform complement-form inequality on a common finite support. -/
theorem grimmettTheorem212_homogeneous_half_of_uniformReimerBound
    {ι : Type*} {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceUniformReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    hAinc hBinc hA hB hEG hFG hReimer

/-- Source-facing homogeneous `p = 1/2` form of Grimmett Theorem 2.12, from Reimer's
uniform complement-form inequality on all full finite cubes. -/
theorem grimmettTheorem212_homogeneous_half_of_forall_univ_uniformReimerBound
    {ι : Type u} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B :=
  setBernoulli_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    hAinc hBinc hA hB hReimer

/-- Source-facing homogeneous `p = 1/2` form of Grimmett Theorem 2.12, as a direct corollary
of Reimer's cardinality inequality on a common finite support. -/
theorem grimmettTheorem212_homogeneous_half_of_cardinalityReimerBound
    {ι : Type*} {E F G : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceCardinalityReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    hAinc hBinc hA hB hEG hFG hReimer

/-- Source-facing homogeneous `p = 1/2` form of Grimmett Theorem 2.12, as a direct corollary
of Reimer's cardinality inequality on all full finite cubes. -/
theorem grimmettTheorem212_homogeneous_half_of_forall_univ_cardinalityReimerBound
    {ι : Type u} {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (OpenDisjointOccurrence A B) ≤
      (setBer((Set.univ : Set ι), unitIntervalHalf)).real A *
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound
    hAinc hBinc hA hB hReimer

/-- Grimmett 2.15, in finite-support cubic-bond form, as a corollary of Reimer's finite box
bound. The increasing hypotheses match the textbook statement; the formal implication only uses
finite support plus Reimer. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_reimerBoundOn
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) G) :
    (bernoulliBondMeasure d p).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B :=
  by
    haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
      dsimp [bernoulliBondMeasure]
      infer_instance
    exact measureReal_disjointOccurrence_le_mul_of_reimerBoundOn hA hB (hReimer _)

/-- Grimmett 2.15, in finite-support cubic-bond form, as a direct corollary of finite-trace
Reimer on every finite edge support. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_reimerBoundOn d p
    _hAinc _hBinc hA hB fun G ↦ by
      dsimp [bernoulliBondMeasure]
      exact reimerBoundOn_setBernoulli_of_finiteTraceReimerBound G p (hReimer G)

/-- Grimmett 2.15, in finite-support cubic-bond form, as a direct corollary of weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound p
    hA hB hReimer

/-- Grimmett 2.15 in textbook open-disjoint-occurrence form, as a direct corollary of
finite-trace Reimer on every finite edge support. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound d p
    hAinc hBinc hA hB hReimer

/-- Grimmett 2.15 in textbook open-disjoint-occurrence form, as a direct corollary of weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    d p hAinc hBinc hA hB hReimer

/-- Source-facing Grimmett Theorem 2.15: finite-edge bond-percolation BK, proved directly from
Grimmett's two-copy BK argument. -/
theorem grimmettTheorem215
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_dependsOn_direct
    d p hAinc hBinc hA hB

/-- Source-facing Grimmett Theorem 2.15: finite-edge bond-percolation BK, proved as a direct
corollary of Reimer's finite box inequality on every finite edge support. -/
theorem grimmettTheorem215_of_reimerBoundOn
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) G) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  exact measureReal_openDisjointOccurrence_le_mul_of_reimerBoundOn
    hAinc hBinc hA hB (hReimer _)

/-- Source-facing Grimmett Theorem 2.15 from finite-trace Reimer on every finite edge support. -/
theorem grimmettTheorem215_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_finiteTraceReimerBound
    d p hAinc hBinc hA hB hReimer

/-- Source-facing Grimmett Theorem 2.15 from weighted finite-trace Reimer stated only on full
finite cubes. -/
theorem grimmettTheorem215_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound
    d p hAinc hBinc hA hB hReimer

/-- Unconditional two-coordinate common-support slice of Grimmett 2.15 for cubic bond
percolation. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_card_le_two_of_subset
    (d : ℕ) (p : I) {E F G : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hEG : E ⊆ G) (hFG : F ⊆ G) (hG : G.card ≤ 2) :
    (bernoulliBondMeasure d p).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_card_le_two_of_subset p hA hB
    hEG hFG hG

theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_zero
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d (0 : I)).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d (0 : I)).real A * (bernoulliBondMeasure d (0 : I)).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_zero hA hB

theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_one
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (_hAinc : IsIncreasingEvent A) (_hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d (1 : I)).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d (1 : I)).real A * (bernoulliBondMeasure d (1 : I)).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_one hA hB

/-- Source-facing endpoint slice of Grimmett Theorem 2.15 at `p = 0`. -/
theorem grimmettTheorem215_zero
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d (0 : I)).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d (0 : I)).real A *
        (bernoulliBondMeasure d (0 : I)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_zero d hAinc hBinc hA hB

/-- Source-facing endpoint slice of Grimmett Theorem 2.15 at `p = 1`. -/
theorem grimmettTheorem215_one
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d (1 : I)).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d (1 : I)).real A *
        (bernoulliBondMeasure d (1 : I)).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_one d hAinc hBinc hA hB

/-- Source-facing low-support slice of Grimmett Theorem 2.15: arbitrary `p`, provided the
combined finite edge support has cardinality at most two. -/
theorem grimmettTheorem215_of_union_card_le_two
    (d : ℕ) (p : I) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 2) :
    (bernoulliBondMeasure d p).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_card_le_two_of_subset d p
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hEF

/-- Uniform `p=1/2` common-support slice of Grimmett 2.15, obtained from Reimer's uniform
complement-form inequality on the same finite edge support. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    (d : ℕ) {E F G : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceUniformReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_uniformReimerBound
    hAinc hBinc hA hB hEG hFG hReimer

/-- The `p=1/2` finite-support cubic-bond form of Grimmett 2.15 as a corollary of
Reimer's uniform complement-form inequality stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    hAinc hBinc hA hB hReimer

/-- The textbook open-occurrence `p=1/2` finite-support cubic-bond form of Grimmett 2.15 as a
corollary of Reimer's uniform complement-form inequality stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    hAinc hBinc hA hB hReimer

/-- Source-facing `p = 1/2` Grimmett Theorem 2.15, from Reimer's uniform complement-form
inequality on all full finite cubes. -/
theorem grimmettTheorem215_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound
    d hAinc hBinc hA hB hReimer

/-- Uniform `p=1/2` common-support slice of Grimmett 2.15, obtained from Reimer's cardinality
theorem on the same finite edge support. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    (d : ℕ) {E F G : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound
    hAinc hBinc hA hB hEG hFG hReimer

/-- Source-facing `p = 1/2` Grimmett Theorem 2.15, as a direct corollary of Reimer's
cardinality inequality on a common finite edge support. -/
theorem grimmettTheorem215_half_of_cardinalityReimerBound
    (d : ℕ) {E F G : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEG : E ⊆ G) (hFG : F ⊆ G)
    (hReimer : FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound d
    hAinc hBinc hA hB hEG hFG hReimer

/-- Uniform `p=1/2` common-support slice of Grimmett 2.15 for cubic bond percolation when the
common finite edge support has at most three edges. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_card_le_three_of_subset
    (d : ℕ) {E F G : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hEG : E ⊆ G) (hFG : F ⊆ G) (hG : G.card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_card_le_three_of_subset
    hAinc hBinc hA hB hEG hFG hG

/-- Uniform `p=1/2` finite-support cubic-bond slice of Grimmett 2.15 when the combined finite
edge support has at most three edges. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_union_card_le_three
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_card_le_three_of_subset
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    hEF

/-- Uniform `p=1/2` textbook open-occurrence cubic-bond slice of Grimmett 2.15 when the combined
finite edge support has at most three edges. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_half_of_union_card_le_three
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_union_card_le_three d
    hAinc hBinc hA hB hEF

/-- Source-facing `p = 1/2` low-support slice of Grimmett Theorem 2.15, obtained from the
current transported three-coordinate cardinal-Reimer theorem. -/
theorem grimmettTheorem215_half_of_union_card_le_three
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) (hEF : (E ∪ F).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_half_of_union_card_le_three d
    hAinc hBinc hA hB hEF

/-- The `p=1/2` finite-support cubic-bond form of Grimmett 2.15 as a direct all-support
corollary of Reimer's cardinality theorem on every finite edge cube. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_cardinalityReimerBound d
    hAinc hBinc hA hB
    (by intro e he; exact Finset.mem_union_left F he)
    (by intro e he; exact Finset.mem_union_right E he)
    (hReimer (E ∪ F))

/-- Source-facing `p = 1/2` Grimmett Theorem 2.15, as a direct corollary of Reimer's
cardinality inequality on every finite edge support. -/
theorem grimmettTheorem215_half_of_forall_cardinalityReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound d
    hAinc hBinc hA hB hReimer

/-- The `p=1/2` finite-support cubic-bond form of Grimmett 2.15 as a corollary of
Reimer's cardinality theorem stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (DisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound
    hAinc hBinc hA hB hReimer

/-- Source-facing `p = 1/2` Grimmett Theorem 2.15, as a direct corollary of Reimer's
cardinality inequality stated on all full finite cubes. -/
theorem grimmettTheorem215_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (OpenDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real A *
        (bernoulliBondMeasure d unitIntervalHalf).real B := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing hAinc hBinc]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound
    d hAinc hBinc hA hB hReimer

/-- The finite edge support of a finite indexed family of walks. -/
noncomputable def walkFamilyEdgeFinset {d : ℕ} {u v : Cubic d} {β : Type*}
    (s : Finset β) (walk : β → (cubicGraph d).Walk u v) : Finset (CubicEdge d) :=
  s.biUnion fun b ↦ walkEdgeFinset (walk b)

theorem walkEdgeFinset_subset_walkFamilyEdgeFinset {d : ℕ} {u v : Cubic d}
    {β : Type*} {s : Finset β} {walk : β → (cubicGraph d).Walk u v}
    {b : β} (hb : b ∈ s) :
    walkEdgeFinset (walk b) ⊆ walkFamilyEdgeFinset s walk := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨b, hb, he⟩

theorem dependsOn_existsOpenWalkIn {d : ℕ} {u v : Cubic d}
    {β : Type*} (s : Finset β) (walk : β → (cubicGraph d).Walk u v) :
    DependsOn (walkFamilyEdgeFinset s walk)
      {ω : EdgeConfiguration d | existsOpenWalkIn s walk ω} := by
  intro ω η hcoord
  constructor
  · rintro ⟨b, hb, hopen⟩
    refine ⟨b, hb, ?_⟩
    have hdep := (dependsOn_walkIsOpen (walk b)).mono
      (walkEdgeFinset_subset_walkFamilyEdgeFinset (s := s) (walk := walk) hb)
    exact (hdep hcoord).mp hopen
  · rintro ⟨b, hb, hopen⟩
    refine ⟨b, hb, ?_⟩
    have hdep := (dependsOn_walkIsOpen (walk b)).mono
      (walkEdgeFinset_subset_walkFamilyEdgeFinset (s := s) (walk := walk) hb)
    exact (hdep hcoord).mpr hopen

/-- A source-shaped version of Grimmett's path-family application of BK: for every index in
`J`, choose one walk from the finite family `s i`, all chosen walks are open, and their edge sets
are pairwise disjoint. -/
def ExistsPairwiseDisjointOpenWalksIn {d : ℕ} {κ β : Type*} {J : Finset κ}
    {u v : κ → Cubic d} (s : κ → Finset β)
    (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (ω : EdgeConfiguration d) : Prop :=
  ∃ b : ∀ i, i ∈ J → β,
    (∀ i hi, b i hi ∈ s i ∧ walkIsOpen ω (walk i (b i hi))) ∧
      ∀ ⦃i j : κ⦄, (hi : i ∈ J) → (hj : j ∈ J) → i ≠ j →
        Disjoint (walkEdgeFinset (walk i (b i hi)))
          (walkEdgeFinset (walk j (b j hj)))

theorem Forces.existsOpenWalkIn {d : ℕ} {u v : Cubic d} {β : Type*}
    {K : Finset (CubicEdge d)} {ω : EdgeConfiguration d}
    {s : Finset β} {walk : β → (cubicGraph d).Walk u v}
    (hK : Forces K ω {η : EdgeConfiguration d | existsOpenWalkIn s walk η}) :
    ∃ b ∈ s, walkIsOpen ω (walk b) ∧ walkEdgeFinset (walk b) ⊆ K := by
  let η : EdgeConfiguration d := ω ∩ (K : Set (CubicEdge d))
  have hagree : ∀ e ∈ K, (e ∈ η ↔ e ∈ ω) := by
    intro e he
    simp [η, he]
  rcases hK η hagree with ⟨b, hb, hopenη⟩
  have hηω : η ⊆ ω := by
    intro e he
    exact he.1
  have hopenω : walkIsOpen ω (walk b) :=
    isIncreasingEvent_walkIsOpen (walk b) hηω hopenη
  have hsubη : (walkEdgeFinset (walk b) : Set (CubicEdge d)) ⊆ η := by
    have hmem : η ∈ {ξ : EdgeConfiguration d | walkIsOpen ξ (walk b)} := hopenη
    rwa [walkIsOpen_event_eq_openOn_walkEdgeFinset] at hmem
  refine ⟨b, hb, hopenω, ?_⟩
  intro e he
  exact (hsubη he).2

theorem mem_finiteDisjointOccurrence_existsOpenWalkIn_iff {d : ℕ} {κ β : Type*}
    {J : Finset κ} {u v : κ → Cubic d}
    {s : κ → Finset β} {walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)}
    {ω : EdgeConfiguration d} :
    ω ∈ FiniteDisjointOccurrence J
        (fun i ↦ {η : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) η}) ↔
      ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω := by
  constructor
  · rintro ⟨K, hK, hpair⟩
    let b : ∀ i, i ∈ J → β :=
      fun i hi ↦ Classical.choose ((hK i hi).existsOpenWalkIn (s := s i) (walk := walk i))
    have hb :
        ∀ i hi,
          b i hi ∈ s i ∧ walkIsOpen ω (walk i (b i hi)) ∧
            walkEdgeFinset (walk i (b i hi)) ⊆ K i := by
      intro i hi
      exact Classical.choose_spec ((hK i hi).existsOpenWalkIn (s := s i) (walk := walk i))
    refine ⟨b, ?_, ?_⟩
    · intro i hi
      exact ⟨(hb i hi).1, (hb i hi).2.1⟩
    · intro i j hi hj hij
      exact (hpair hi hj hij).mono (hb i hi).2.2 (hb j hj).2.2
  · rintro ⟨b, hb, hpair⟩
    classical
    let K : κ → Finset (CubicEdge d) :=
      fun i ↦ if hi : i ∈ J then walkEdgeFinset (walk i (b i hi)) else ∅
    refine ⟨K, ?_, ?_⟩
    · intro i hi
      have hKi : K i = walkEdgeFinset (walk i (b i hi)) := by
        simp [K, hi]
      intro η hagree
      refine ⟨b i hi, (hb i hi).1, ?_⟩
      intro e he
      let ce : CubicEdge d := ⟨e, (walk i (b i hi)).edges_subset_edgeSet he⟩
      have hceWalk : ce ∈ walkEdgeFinset (walk i (b i hi)) :=
        (mem_walkEdgeFinset_iff (walk i (b i hi)) ce).mpr he
      have hceK : ce ∈ K i := by
        simpa [hKi] using hceWalk
      have hceω : ce ∈ ω := (hb i hi).2 e he
      exact (hagree ce hceK).mpr hceω
    · intro i j hi hj hij
      have hKi : K i = walkEdgeFinset (walk i (b i hi)) := by
        simp [K, hi]
      have hKj : K j = walkEdgeFinset (walk j (b j hj)) := by
        simp [K, hj]
      simpa [hKi, hKj] using hpair hi hj hij

theorem finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    {d : ℕ} {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    FiniteDisjointOccurrence J
        (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω}) =
      {ω : EdgeConfiguration d |
        ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} := by
  ext ω
  exact mem_finiteDisjointOccurrence_existsOpenWalkIn_iff

theorem mem_finiteOpenDisjointOccurrence_existsOpenWalkIn_iff {d : ℕ} {κ β : Type*}
    {J : Finset κ} {u v : κ → Cubic d}
    {s : κ → Finset β} {walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)}
    {ω : EdgeConfiguration d} :
    ω ∈ FiniteOpenDisjointOccurrence J
        (fun i ↦ {η : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) η}) ↔
      ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω := by
  rw [finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing
    (J := J)
    (A := fun i ↦ {η : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) η})
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))]
  exact mem_finiteDisjointOccurrence_existsOpenWalkIn_iff

theorem finiteOpenDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    {d : ℕ} {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    FiniteOpenDisjointOccurrence J
        (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω}) =
      {ω : EdgeConfiguration d |
        ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} := by
  ext ω
  exact mem_finiteOpenDisjointOccurrence_existsOpenWalkIn_iff

/-- Binary source-shaped path-family BK event: choose one open walk from each finite family,
and require the two chosen walks to use disjoint edge sets. -/
def ExistsDisjointOpenWalksIn {d : ℕ} {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (ω : EdgeConfiguration d) : Prop :=
  ∃ b ∈ s, ∃ c ∈ t,
    walkIsOpen ω (walkA b) ∧ walkIsOpen ω (walkB c) ∧
      Disjoint (walkEdgeFinset (walkA b)) (walkEdgeFinset (walkB c))

theorem mem_disjointOccurrence_existsOpenWalkIn_binary_iff {d : ℕ}
    {u v x y : Cubic d} {β γ : Type*}
    {s : Finset β} {t : Finset γ}
    {walkA : β → (cubicGraph d).Walk u v} {walkB : γ → (cubicGraph d).Walk x y}
    {ω : EdgeConfiguration d} :
    ω ∈ DisjointOccurrence
        {η : EdgeConfiguration d | existsOpenWalkIn s walkA η}
        {η : EdgeConfiguration d | existsOpenWalkIn t walkB η} ↔
      ExistsDisjointOpenWalksIn s t walkA walkB ω := by
  constructor
  · rintro ⟨K, L, hdis, hK, hL⟩
    rcases hK.existsOpenWalkIn (s := s) (walk := walkA) with ⟨b, hb, hbopen, hbsub⟩
    rcases hL.existsOpenWalkIn (s := t) (walk := walkB) with ⟨c, hc, hcopen, hcsub⟩
    exact ⟨b, hb, c, hc, hbopen, hcopen, hdis.mono hbsub hcsub⟩
  · rintro ⟨b, hb, c, hc, hbopen, hcopen, hdis⟩
    refine ⟨walkEdgeFinset (walkA b), walkEdgeFinset (walkB c), hdis, ?_, ?_⟩
    · intro η hagree
      refine ⟨b, hb, ?_⟩
      intro e he
      let ce : CubicEdge d := ⟨e, (walkA b).edges_subset_edgeSet he⟩
      have hceWalk : ce ∈ walkEdgeFinset (walkA b) :=
        (mem_walkEdgeFinset_iff (walkA b) ce).mpr he
      have hceω : ce ∈ ω := hbopen e he
      exact (hagree ce hceWalk).mpr hceω
    · intro η hagree
      refine ⟨c, hc, ?_⟩
      intro e he
      let ce : CubicEdge d := ⟨e, (walkB c).edges_subset_edgeSet he⟩
      have hceWalk : ce ∈ walkEdgeFinset (walkB c) :=
        (mem_walkEdgeFinset_iff (walkB c) ce).mpr he
      have hceω : ce ∈ ω := hcopen e he
      exact (hagree ce hceWalk).mpr hceω

theorem disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn {d : ℕ}
    {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y) :
    DisjointOccurrence
        {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
        {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} =
      {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} := by
  ext ω
  exact mem_disjointOccurrence_existsOpenWalkIn_binary_iff

theorem openDisjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn {d : ℕ}
    {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y) :
    OpenDisjointOccurrence
        {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
        {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} =
      {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} := by
  rw [openDisjointOccurrence_eq_disjointOccurrence_of_increasing
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)]
  exact disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB

/-- Direct binary path-family BK for finite families of open walks. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_direct
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y) :
    (bernoulliBondMeasure d p).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_dependsOn_direct d p
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)

/-- Direct binary path-family BK in textbook open-disjoint-occurrence form. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_existsOpenWalkIn_le_mul_direct
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y) :
    (bernoulliBondMeasure d p).real
        (OpenDisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_of_dependsOn_direct d p
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)

/-- Direct explicit binary path-family BK: the event that the two finite walk families contain
edge-disjoint open walks has probability at most the product of the two one-family
probabilities. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_direct
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_direct
    d p s t walkA walkB

/-- Conditional BK for two finite families of open walks. This is the binary path-family
specialization supplied by the finite-support bond-percolation theorem. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_reimerBoundOn
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ G : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) G) :
    (bernoulliBondMeasure d p).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_reimerBoundOn d p
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK as a direct corollary of finite-trace Reimer on every finite edge
support. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_finiteTraceReimerBound d p
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK as a direct corollary of weighted finite-trace Reimer stated only on
full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_of_forall_univ_finiteTraceReimerBound d p
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK at `p=1/2` as a corollary of Reimer's uniform complement-form
inequality stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound d
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK in textbook open-occurrence form at `p=1/2`, as a corollary of
Reimer's uniform complement-form inequality stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_openDisjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (OpenDisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_openDisjointOccurrence_le_mul_half_of_forall_univ_uniformReimerBound d
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK at `p=1/2` as a direct corollary of Reimer's cardinality theorem on
every finite edge support. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_cardinalityReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound d
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Binary path-family BK at `p=1/2` as a corollary of Reimer's cardinality theorem stated
only on full finite cubes. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (DisjointOccurrence
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω}
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω}) ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} :=
  bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_forall_univ_cardinalityReimerBound d
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hReimer

/-- Conditional binary path-family BK in explicit source form: the event that the two finite
walk families contain edge-disjoint open walks. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_of_reimerBoundOn
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ G : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) G) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_reimerBoundOn
    d p s t walkA walkB hReimer

/-- Explicit binary path-family BK as a direct corollary of finite-trace Reimer on every finite
edge support. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_finiteTraceReimerBound
    d p s t walkA walkB hReimer

/-- Explicit binary path-family BK as a direct corollary of weighted finite-trace Reimer stated
only on full finite cubes. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact
    bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_of_forall_univ_finiteTraceReimerBound
      d p s t walkA walkB hReimer

/-- Explicit binary path-family BK at `p=1/2` from full-cube uniform Reimer. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_half_of_forall_univ_uniformReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceUniformReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact
    bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_univ_uniformReimerBound
      d s t walkA walkB hReimer

/-- Explicit binary path-family BK at `p=1/2` from full-cube cardinal Reimer. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact
    bernoulliBondMeasure_real_disjointOccurrence_existsOpenWalkIn_le_mul_half_of_forall_univ_cardinalityReimerBound
      d s t walkA walkB hReimer

/-- Explicit binary path-family BK at `p=1/2` when the two finite path-family supports use at
most three edges in total. -/
theorem bernoulliBondMeasure_real_existsDisjointOpenWalksIn_le_mul_half_of_union_card_le_three
    (d : ℕ) {u v x y : Cubic d} {β γ : Type*}
    (s : Finset β) (t : Finset γ)
    (walkA : β → (cubicGraph d).Walk u v) (walkB : γ → (cubicGraph d).Walk x y)
    (hE : (walkFamilyEdgeFinset s walkA ∪ walkFamilyEdgeFinset t walkB).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d | ExistsDisjointOpenWalksIn s t walkA walkB ω} ≤
      (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn s walkA ω} *
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn t walkB ω} := by
  rw [← disjointOccurrence_existsOpenWalkIn_binary_eq_existsDisjointOpenWalksIn s t walkA walkB]
  exact bernoulliBondMeasure_real_disjointOccurrence_le_mul_half_of_union_card_le_three d
    (isIncreasingEvent_existsOpenWalkIn s walkA)
    (isIncreasingEvent_existsOpenWalkIn t walkB)
    (dependsOn_existsOpenWalkIn s walkA)
    (dependsOn_existsOpenWalkIn t walkB)
    hE

/-- Direct repeated finite-family BK for Bernoulli product measures. This is the finite-family
extension of `setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_direct`, proved by the
standard induction using the binary BK inequality at each step. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_direct
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) := by
  induction J using Finset.induction with
  | empty =>
      rw [finiteDisjointOccurrence_empty]
      simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  | insert a J ha ih =>
      have hAJinc : ∀ i ∈ J, IsIncreasingEvent (A i) := by
        intro i hi
        exact hAinc i (Finset.mem_insert.mpr (Or.inr hi))
      have hAJ : ∀ i ∈ J, DependsOn (E i) (A i) := by
        intro i hi
        exact hA i (Finset.mem_insert.mpr (Or.inr hi))
      have hincRest : IsIncreasingEvent (FiniteDisjointOccurrence J A) :=
        isIncreasingEvent_finiteDisjointOccurrence hAJinc
      have hrest : DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) :=
        dependsOn_finiteDisjointOccurrence hAJ
      have hsubset := finiteDisjointOccurrence_insert_subset_disjointOccurrence
        (ι := ι) (κ := κ) (J := J) (a := a) (A := A) ha
      calc
        (setBer((Set.univ : Set ι), p)).real (FiniteDisjointOccurrence (insert a J) A) ≤
            (setBer((Set.univ : Set ι), p)).real
              (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono hsubset
        _ ≤ (setBer((Set.univ : Set ι), p)).real (A a) *
              (setBer((Set.univ : Set ι), p)).real (FiniteDisjointOccurrence J A) :=
          setBernoulli_real_disjointOccurrence_le_mul_of_dependsOn_direct p
            (hAinc a (Finset.mem_insert_self a J)) hincRest
            (hA a (Finset.mem_insert_self a J)) hrest
        _ ≤ (setBer((Set.univ : Set ι), p)).real (A a) *
              J.prod (fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i)) :=
          mul_le_mul_of_nonneg_left (ih hAJinc hAJ) measureReal_nonneg
        _ = (insert a J).prod
              (fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i)) := by
          rw [Finset.prod_insert ha]

/-- Direct repeated finite-family BK for Bernoulli product measures in open-witness form. -/
theorem setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_direct
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) := by
  rw [finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing hAinc]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_direct p hAinc hA

/-- Direct repeated finite-family BK for cubic Bernoulli bond percolation. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_direct
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (bernoulliBondMeasure d p).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_direct p hAinc hA

/-- Direct repeated finite-family BK for cubic Bernoulli bond percolation in open-witness form. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_direct
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (bernoulliBondMeasure d p).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_direct p hAinc hA

/-- Direct finite-family path-event BK for finite families of open walks. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_direct
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    (bernoulliBondMeasure d p).real
        (FiniteDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_direct d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))

/-- Direct finite-family path-event BK in open-witness form. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_existsOpenWalkIn_le_prod_direct
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    (bernoulliBondMeasure d p).real
        (FiniteOpenDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_direct d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))

/-- Direct finite-family path BK in explicit pairwise edge-disjoint open-walk form. -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_direct
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} := by
  rw [← finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    (J := J) s walk]
  exact bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_direct
    d p s walk

/-- Repeated BK follows formally from the binary disjoint-occurrence bound. This theorem does
not assert the binary BK/Reimer inequality; it records the finite induction that will be used once
the binary probability estimate is available. -/
theorem measureReal_finiteDisjointOccurrence_le_prod_of_disjointOccurrence_bound
    {ι κ : Type*} {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    (hBK : ∀ {A B : Set (Set ι)}, IsIncreasingEvent A → IsIncreasingEvent B →
      μ.real (DisjointOccurrence A B) ≤ μ.real A * μ.real B)
    {J : Finset κ} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) :
    μ.real (FiniteDisjointOccurrence J A) ≤ J.prod (fun i ↦ μ.real (A i)) := by
  induction J using Finset.induction with
  | empty =>
      rw [finiteDisjointOccurrence_empty]
      simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  | insert a J ha ih =>
      have hAJ : ∀ i ∈ J, IsIncreasingEvent (A i) := by
        intro i hi
        exact hA i (Finset.mem_insert.mpr (Or.inr hi))
      have hincRest : IsIncreasingEvent (FiniteDisjointOccurrence J A) :=
        isIncreasingEvent_finiteDisjointOccurrence hAJ
      have hsubset := finiteDisjointOccurrence_insert_subset_disjointOccurrence
        (ι := ι) (κ := κ) (J := J) (a := a) (A := A) ha
      calc
        μ.real (FiniteDisjointOccurrence (insert a J) A) ≤
            μ.real (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono hsubset
        _ ≤ μ.real (A a) * μ.real (FiniteDisjointOccurrence J A) :=
          hBK (hA a (Finset.mem_insert_self a J)) hincRest
        _ ≤ μ.real (A a) * J.prod (fun i ↦ μ.real (A i)) :=
          mul_le_mul_of_nonneg_left (ih hAJ) measureReal_nonneg
        _ = (insert a J).prod (fun i ↦ μ.real (A i)) := by
          rw [Finset.prod_insert ha]

/-- Reimer's finite box inequality implies the repeated finite-family BK product bound. -/
theorem measureReal_finiteDisjointOccurrence_le_prod_of_reimerBoundOn
    {ι κ : Type*} {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    (hReimer : ∀ E : Finset ι, ReimerBoundOn μ E)
    {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    μ.real (FiniteDisjointOccurrence J A) ≤ J.prod (fun i ↦ μ.real (A i)) := by
  induction J using Finset.induction with
  | empty =>
      rw [finiteDisjointOccurrence_empty]
      simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  | insert a J ha ih =>
      have hAJ : ∀ i ∈ J, DependsOn (E i) (A i) := by
        intro i hi
        exact hA i (Finset.mem_insert.mpr (Or.inr hi))
      have hrest : DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) :=
        dependsOn_finiteDisjointOccurrence hAJ
      have hsubset := finiteDisjointOccurrence_insert_subset_disjointOccurrence
        (ι := ι) (κ := κ) (J := J) (a := a) (A := A) ha
      have hbinary :
          μ.real (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) ≤
            μ.real (A a) * μ.real (FiniteDisjointOccurrence J A) :=
        measureReal_disjointOccurrence_le_mul_of_reimerBoundOn
          (μ := μ) (E := E a) (F := J.biUnion E)
          (hA a (Finset.mem_insert_self a J)) hrest (hReimer (E a ∪ J.biUnion E))
      calc
        μ.real (FiniteDisjointOccurrence (insert a J) A) ≤
            μ.real (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono hsubset
        _ ≤ μ.real (A a) * μ.real (FiniteDisjointOccurrence J A) :=
          hbinary
        _ ≤ μ.real (A a) * J.prod (fun i ↦ μ.real (A i)) :=
          mul_le_mul_of_nonneg_left (ih hAJ) measureReal_nonneg
        _ = (insert a J).prod (fun i ↦ μ.real (A i)) := by
          rw [Finset.prod_insert ha]

/-- Reimer's finite box inequality implies the source-shaped repeated finite-family BK product
bound for open disjoint occurrence of increasing events. -/
theorem measureReal_finiteOpenDisjointOccurrence_le_prod_of_reimerBoundOn
    {ι κ : Type*} {μ : Measure (Set ι)} [IsProbabilityMeasure μ]
    (hReimer : ∀ E : Finset ι, ReimerBoundOn μ E)
    {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    μ.real (FiniteOpenDisjointOccurrence J A) ≤ J.prod (fun i ↦ μ.real (A i)) := by
  rw [finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing hAinc]
  exact measureReal_finiteDisjointOccurrence_le_prod_of_reimerBoundOn hReimer hA

/-- Repeated finite-family BK for Bernoulli product measures as a direct corollary of
finite-trace Reimer on every finite support. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_of_finiteTraceReimerBound
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  measureReal_finiteDisjointOccurrence_le_prod_of_reimerBoundOn
    (μ := setBer((Set.univ : Set ι), p))
    (fun G ↦ reimerBoundOn_setBernoulli_of_finiteTraceReimerBound G p (hReimer G))
    hA

/-- Repeated finite-family BK for Bernoulli product measures as a direct corollary of weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} {κ : Type v} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  setBernoulli_real_finiteDisjointOccurrence_le_prod_of_finiteTraceReimerBound p hA
    (fun G ↦ finiteTraceReimerBound_of_forall_univ_fintype (p : ℝ) hReimer G)

/-- Source-shaped repeated finite-family BK for Bernoulli product measures, as a direct
corollary of finite-trace Reimer on every finite support. -/
theorem setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  measureReal_finiteOpenDisjointOccurrence_le_prod_of_reimerBoundOn
    (μ := setBer((Set.univ : Set ι), p))
    (fun G ↦ reimerBoundOn_setBernoulli_of_finiteTraceReimerBound G p (hReimer G))
    hAinc hA

/-- Source-shaped repeated finite-family BK for Bernoulli product measures, as a direct
corollary of weighted finite-trace Reimer stated only on full finite cubes. -/
theorem setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} {κ : Type v} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound p
    hAinc hA (fun G ↦ finiteTraceReimerBound_of_forall_univ_fintype (p : ℝ) hReimer G)

/-- Source-facing homogeneous finite-product form of Grimmett (2.14), proved by iterating the
direct finite-support BK inequality. -/
theorem grimmettEquation214_homogeneous
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_direct p hAinc hA

/-- Source-facing homogeneous finite-product form of Grimmett (2.14), proved by iterating the
BK consequence of Reimer's finite box inequality. -/
theorem grimmettEquation214_homogeneous_of_reimerBoundOn
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset ι, ReimerBoundOn (setBer((Set.univ : Set ι), p)) G) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  measureReal_finiteOpenDisjointOccurrence_le_prod_of_reimerBoundOn
    (μ := setBer((Set.univ : Set ι), p)) hReimer hAinc hA

/-- Source-facing homogeneous finite-product form of Grimmett (2.14), from weighted
finite-trace Reimer on every finite support. -/
theorem grimmettEquation214_homogeneous_of_finiteTraceReimerBound
    {ι κ : Type*} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset ι, FiniteTraceReimerBound G (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound
    p hAinc hA hReimer

/-- Source-facing homogeneous finite-product form of Grimmett (2.14), from weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem grimmettEquation214_homogeneous_of_forall_univ_finiteTraceReimerBound
    {ι : Type u} {κ : Type v} (p : I) {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (setBer((Set.univ : Set ι), p)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), p)).real (A i) :=
  setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    p hAinc hA hReimer

/-- Repeated finite-family BK at `p=1/2` for Bernoulli product measures, as a direct corollary
of Reimer's cardinality theorem on every finite support. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_forall_cardinalityReimerBound
    {ι κ : Type*} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset ι, FiniteTraceCardinalityReimerBound G) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) := by
  induction J using Finset.induction with
  | empty =>
      rw [finiteDisjointOccurrence_empty]
      simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  | insert a J ha ih =>
      have hAJinc : ∀ i ∈ J, IsIncreasingEvent (A i) := by
        intro i hi
        exact hAinc i (Finset.mem_insert.mpr (Or.inr hi))
      have hAJ : ∀ i ∈ J, DependsOn (E i) (A i) := by
        intro i hi
        exact hA i (Finset.mem_insert.mpr (Or.inr hi))
      have hincRest : IsIncreasingEvent (FiniteDisjointOccurrence J A) :=
        isIncreasingEvent_finiteDisjointOccurrence hAJinc
      have hrest : DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) :=
        dependsOn_finiteDisjointOccurrence hAJ
      have hsubset := finiteDisjointOccurrence_insert_subset_disjointOccurrence
        (ι := ι) (κ := κ) (J := J) (a := a) (A := A) ha
      have hbinary :
          (setBer((Set.univ : Set ι), unitIntervalHalf)).real
              (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) ≤
            (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real
                (FiniteDisjointOccurrence J A) :=
        setBernoulli_real_disjointOccurrence_le_mul_half_of_forall_cardinalityReimerBound
          (hAinc a (Finset.mem_insert_self a J)) hincRest
          (hA a (Finset.mem_insert_self a J)) hrest hReimer
      calc
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real
            (FiniteDisjointOccurrence (insert a J) A) ≤
            (setBer((Set.univ : Set ι), unitIntervalHalf)).real
              (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono hsubset
        _ ≤ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real
                (FiniteDisjointOccurrence J A) :=
          hbinary
        _ ≤ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              J.prod fun i ↦ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) :=
          mul_le_mul_of_nonneg_left (ih hAJinc hAJ) measureReal_nonneg
        _ = (insert a J).prod fun i ↦
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) := by
          rw [Finset.prod_insert ha]

/-- Repeated finite-family BK at `p=1/2` for Bernoulli product measures when the union of the
finite supports has cardinality at most three. This is the repeated-BK analogue of the binary
`card ≤ 3` slice. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    {ι κ : Type*} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) (hE : (J.biUnion E).card ≤ 3) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) := by
  induction J using Finset.induction with
  | empty =>
      rw [finiteDisjointOccurrence_empty]
      simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  | insert a J ha ih =>
      have hAJinc : ∀ i ∈ J, IsIncreasingEvent (A i) := by
        intro i hi
        exact hAinc i (Finset.mem_insert.mpr (Or.inr hi))
      have hAJ : ∀ i ∈ J, DependsOn (E i) (A i) := by
        intro i hi
        exact hA i (Finset.mem_insert.mpr (Or.inr hi))
      have hJsubset : J.biUnion E ⊆ (insert a J).biUnion E := by
        intro e he
        rcases Finset.mem_biUnion.mp he with ⟨i, hi, hei⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert.mpr (Or.inr hi), hei⟩
      have hJcard : (J.biUnion E).card ≤ 3 :=
        le_trans (Finset.card_le_card hJsubset) hE
      have hincRest : IsIncreasingEvent (FiniteDisjointOccurrence J A) :=
        isIncreasingEvent_finiteDisjointOccurrence hAJinc
      have hrest : DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) :=
        dependsOn_finiteDisjointOccurrence hAJ
      have hsubset := finiteDisjointOccurrence_insert_subset_disjointOccurrence
        (ι := ι) (κ := κ) (J := J) (a := a) (A := A) ha
      have hEaSub : E a ⊆ (insert a J).biUnion E := by
        intro e he
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self a J, he⟩
      have hbinary :
          (setBer((Set.univ : Set ι), unitIntervalHalf)).real
              (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) ≤
            (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real
                (FiniteDisjointOccurrence J A) :=
        setBernoulli_real_disjointOccurrence_le_mul_half_of_dependsOn_card_le_three_of_subset
          (hAinc a (Finset.mem_insert_self a J)) hincRest
          (hA a (Finset.mem_insert_self a J)) hrest hEaSub hJsubset hE
      calc
        (setBer((Set.univ : Set ι), unitIntervalHalf)).real
            (FiniteDisjointOccurrence (insert a J) A) ≤
            (setBer((Set.univ : Set ι), unitIntervalHalf)).real
              (DisjointOccurrence (A a) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono hsubset
        _ ≤ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real
                (FiniteDisjointOccurrence J A) :=
          hbinary
        _ ≤ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A a) *
              J.prod fun i ↦
                (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) :=
          mul_le_mul_of_nonneg_left (ih hAJinc hAJ hJcard) measureReal_nonneg
        _ = (insert a J).prod fun i ↦
              (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) := by
          rw [Finset.prod_insert ha]

/-- Source-shaped repeated finite-family BK at `p=1/2` for Bernoulli product measures when the
union of the finite supports has cardinality at most three. -/
theorem setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    {ι κ : Type*} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) (hE : (J.biUnion E).card ≤ 3) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) := by
  rw [finiteOpenDisjointOccurrence_eq_finiteDisjointOccurrence_of_increasing hAinc]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    hAinc hA hE

/-- Repeated finite-family BK at `p=1/2`, as a corollary of Reimer's cardinality theorem
stated only on full finite cubes. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_forall_univ_cardinalityReimerBound
    {ι : Type u} {κ : Type v} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type u, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (setBer((Set.univ : Set ι), unitIntervalHalf)).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (setBer((Set.univ : Set ι), unitIntervalHalf)).real (A i) :=
  setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_forall_cardinalityReimerBound
    hAinc hA
    (fun G ↦ finiteTraceCardinalityReimerBound_of_forall_univ_fintype hReimer G)

/-- Repeated finite-family BK for cubic bond percolation, conditional on Reimer's finite box
inequality. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_of_reimerBoundOn
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (_hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ E : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) E) :
    (bernoulliBondMeasure d p).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) :=
  by
    haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
      dsimp [bernoulliBondMeasure]
      infer_instance
    exact measureReal_finiteDisjointOccurrence_le_prod_of_reimerBoundOn hReimer hA

/-- Repeated finite-family BK for cubic bond percolation as a direct corollary of finite-trace
Reimer on every finite edge support. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (_hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_of_finiteTraceReimerBound p hA
    hReimer

/-- Repeated finite-family BK for cubic bond percolation as a direct corollary of weighted
finite-trace Reimer stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (_hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound p
    hA hReimer

/-- Source-shaped repeated finite-family BK for cubic bond percolation, conditional on Reimer's
finite box inequality. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_of_reimerBoundOn
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ E : Finset (CubicEdge d), ReimerBoundOn (bernoulliBondMeasure d p) E) :
    (bernoulliBondMeasure d p).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) :=
  by
    haveI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
      dsimp [bernoulliBondMeasure]
      infer_instance
    exact measureReal_finiteOpenDisjointOccurrence_le_prod_of_reimerBoundOn hReimer hAinc hA

/-- Source-shaped repeated finite-family BK for cubic bond percolation as a direct corollary of
finite-trace Reimer on every finite edge support. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound p
    hAinc hA hReimer

/-- Source-shaped repeated finite-family BK for cubic bond percolation as a direct corollary of
weighted finite-trace Reimer stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d p).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound p
    hAinc hA hReimer

/-- Repeated finite-family BK at `p=1/2` for cubic bond percolation, as a direct corollary of
Reimer's cardinality theorem on every finite edge support. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_half_of_forall_cardinalityReimerBound
    (d : ℕ) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceCardinalityReimerBound G) :
    (bernoulliBondMeasure d unitIntervalHalf).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d unitIntervalHalf).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_forall_cardinalityReimerBound
    hAinc hA hReimer

/-- Repeated finite-family BK at `p=1/2` for cubic bond percolation, as a corollary of
Reimer's cardinality theorem stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d unitIntervalHalf).real (A i) := by
  dsimp [bernoulliBondMeasure]
  exact setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_forall_univ_cardinalityReimerBound
    hAinc hA hReimer

/-- Repeated finite-family BK at `p=1/2` for cubic bond percolation when the union of the
finite edge supports has cardinality at most three. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    (d : ℕ) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) (hE : (J.biUnion E).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (FiniteDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d unitIntervalHalf).real (A i) := by
  classical
  dsimp [bernoulliBondMeasure]
  refine setBernoulli_real_finiteDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    hAinc hA ?_
  convert hE using 1
  congr 1
  ext e
  simp [Finset.mem_biUnion]

/-- Source-shaped repeated finite-family BK at `p=1/2` for cubic bond percolation when the union
of the finite edge supports has cardinality at most three. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    (d : ℕ) {κ : Type*} {J : Finset κ}
    {E : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i))
    (hA : ∀ i ∈ J, DependsOn (E i) (A i)) (hE : (J.biUnion E).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real (FiniteOpenDisjointOccurrence J A) ≤
      J.prod fun i ↦ (bernoulliBondMeasure d unitIntervalHalf).real (A i) := by
  classical
  dsimp [bernoulliBondMeasure]
  refine setBernoulli_real_finiteOpenDisjointOccurrence_le_prod_half_of_biUnion_card_le_three
    hAinc hA ?_
  convert hE using 1
  congr 1
  ext e
  simp [Finset.mem_biUnion]

/-- Finite-family path-event BK at `p=1/2` as a corollary of Reimer's cardinality theorem
stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (FiniteDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_half_of_forall_univ_cardinalityReimerBound d
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hReimer

/-- Finite-family path-event BK at `p=1/2` when the union of the finite path-family edge
supports has cardinality at most three. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_half_of_biUnion_card_le_three
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hE : (J.biUnion fun i ↦ walkFamilyEdgeFinset (s i) (walk i)).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (FiniteDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_half_of_biUnion_card_le_three d
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hE

/-- Finite-family path-event BK as a direct corollary of weighted finite-trace Reimer stated
only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        (FiniteDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hReimer

/-- Finite-family open-witness path-event BK as a direct corollary of weighted finite-trace
Reimer on every finite edge support. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_existsOpenWalkIn_le_prod_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        (FiniteOpenDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_of_finiteTraceReimerBound d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hReimer

/-- Finite-family open-witness path-event BK at `p=1/2` when the union of the finite
path-family edge supports has cardinality at most three. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_existsOpenWalkIn_le_prod_half_of_biUnion_card_le_three
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hE : (J.biUnion fun i ↦ walkFamilyEdgeFinset (s i) (walk i)).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        (FiniteOpenDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_half_of_biUnion_card_le_three d
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hE

/-- Finite-family open-witness path-event BK as a direct corollary of weighted finite-trace
Reimer stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_existsOpenWalkIn_le_prod_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        (FiniteOpenDisjointOccurrence J
          (fun i ↦ {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω})) ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_finiteOpenDisjointOccurrence_le_prod_of_forall_univ_finiteTraceReimerBound
    d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hReimer

/-- Explicit pairwise edge-disjoint open-walk BK at `p=1/2` when the union of the finite
path-family edge supports has cardinality at most three. -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_half_of_biUnion_card_le_three
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hE : (J.biUnion fun i ↦ walkFamilyEdgeFinset (s i) (walk i)).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} := by
  rw [← finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    (J := J) s walk]
  exact
    bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_half_of_biUnion_card_le_three
      d s walk hE

/-- Source-shaped finite-family path BK: under finite-trace Reimer on every finite edge
support, the probability that the chosen finite walk families contain pairwise edge-disjoint open
walks is at most the product of the individual open-walk probabilities. This is the finite-support
form of Grimmett's path-family application (2.17). -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} := by
  rw [← finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    (J := J) s walk]
  exact bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod_of_finiteTraceReimerBound d p
    (fun i _hi ↦ isIncreasingEvent_existsOpenWalkIn (s i) (walk i))
    (fun i _hi ↦ dependsOn_existsOpenWalkIn (s i) (walk i))
    hReimer

/-- Source-shaped finite-family path BK as a direct corollary of weighted finite-trace Reimer
stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} := by
  rw [← finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    (J := J) s walk]
  exact
    bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_of_forall_univ_finiteTraceReimerBound
      d p s walk hReimer

/-- Source-shaped finite-family path BK at `p=1/2` as a direct corollary of Reimer's
cardinality theorem stated only on full finite cubes. -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} := by
  rw [← finiteDisjointOccurrence_existsOpenWalkIn_eq_existsPairwiseDisjointOpenWalksIn
    (J := J) s walk]
  exact
    bernoulliBondMeasure_real_finiteDisjointOccurrence_existsOpenWalkIn_le_prod_half_of_forall_univ_cardinalityReimerBound
      d s walk hReimer

/-- Source-facing finite-family form of Grimmett (2.17), proved from the direct finite-support
BK inequality. This is the finite-box version before taking path-family limits. -/
theorem grimmettEquation217_finite
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_direct d p s walk

/-- Source-facing finite-family form of Grimmett (2.17), proved from finite-trace Reimer on
every finite edge support. This is the finite-box version before taking path-family limits. -/
theorem grimmettEquation217_finite_of_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ G : Finset (CubicEdge d), FiniteTraceReimerBound G (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_of_finiteTraceReimerBound
    d p s walk hReimer

/-- Source-facing finite-family form of Grimmett (2.17), proved from weighted finite-trace
Reimer stated only on full finite cubes. -/
theorem grimmettEquation217_finite_of_forall_univ_finiteTraceReimerBound
    (d : ℕ) (p : I) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceReimerBound (Finset.univ : Finset α) (p : ℝ)) :
    (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_of_forall_univ_finiteTraceReimerBound
    d p s walk hReimer

/-- Source-facing finite-family form of Grimmett (2.17) at `p=1/2`, from full-cube
cardinality Reimer. -/
theorem grimmettEquation217_finite_half_of_forall_univ_cardinalityReimerBound
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hReimer : ∀ α : Type, [Fintype α] →
      FiniteTraceCardinalityReimerBound (Finset.univ : Finset α)) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_half_of_forall_univ_cardinalityReimerBound
    d s walk hReimer

/-- Source-facing finite-family form of Grimmett (2.17) at `p=1/2` for total edge support of
cardinality at most three. -/
theorem grimmettEquation217_finite_half_of_biUnion_card_le_three
    (d : ℕ) {κ β : Type*} {J : Finset κ} {u v : κ → Cubic d}
    (s : κ → Finset β) (walk : ∀ i, β → (cubicGraph d).Walk (u i) (v i))
    (hE : (J.biUnion fun i ↦ walkFamilyEdgeFinset (s i) (walk i)).card ≤ 3) :
    (bernoulliBondMeasure d unitIntervalHalf).real
        {ω : EdgeConfiguration d |
          ExistsPairwiseDisjointOpenWalksIn (J := J) s walk ω} ≤
      J.prod fun i ↦
        (bernoulliBondMeasure d unitIntervalHalf).real
          {ω : EdgeConfiguration d | existsOpenWalkIn (s i) (walk i) ω} :=
  bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalksIn_le_prod_half_of_biUnion_card_le_three
    d s walk hE

end Percolation
