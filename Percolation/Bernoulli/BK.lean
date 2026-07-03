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

theorem IsIncreasingEvent.disjointOccurrence {ι : Type*} {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (DisjointOccurrence A B) := by
  intro ω η hωη hω
  rcases hω with ⟨K, L, hdis, hK, hL⟩
  exact ⟨K, L, hdis, hK.mono_config_of_increasing hA hωη,
    hL.mono_config_of_increasing hB hωη⟩

end Percolation
