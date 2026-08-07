import Percolation.Bernoulli.FKGInfinite

/-!
# Conditioning on a finite trace which forces the overlap open

This file records a ratio-free finite-trace conditioning lemma for Bernoulli product measure.
If an event `A` is determined by a finite set `E`, an increasing event `B` is determined by a
finite set `F`, and every configuration in `A` has all coordinates in `E ∩ F` open, then
conditioning on `A` cannot decrease the probability of `B`.

The proof partitions by the trace on `E` and uses splice factorization on every cell.  It is the
finite-coordinate form of the `H`/`J` conditioning step in Grimmett's proof of Lemma 11.73.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

variable {ι : Type*}

/-- Ratio-free conditioning in its direct splice form.  On every trace cell compatible with
`A`, it is enough that splicing that trace into a configuration from `B` preserves membership in
`B`.  This formulation is useful when the preservation proof first replaces a witness by a
fresh first-contact witness, rather than proving literal support disjointness. -/
theorem setBernoulli_real_mul_le_inter_of_splice_preserves
    (p : I) {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hBm : MeasurableSet B)
    (hpreserve : ∀ s ⊆ E, (↑s : Set ι) ∈ A →
      B ⊆ (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' B) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  classical
  have hAm : MeasurableSet A := hA.measurableSet
  rw [setBernoulli_real_eq_sum_splice p E hAm,
    setBernoulli_real_eq_sum_splice p E (hAm.inter hBm), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  by_cases hsA : (↑s : Set ι) ∈ A
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).2 hsA
    have hpreInter :
        (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ B) =
          (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' B := by
      simp only [Set.preimage_inter, hpreA, Set.univ_inter]
    rw [hpreA, hpreInter, probReal_univ, mul_one]
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono (hpreserve s hsE hsA))
      (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hsplice
      apply hsA
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).1 hsplice
    have hpreInter :
        (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ B) = ∅ := by
      rw [Set.preimage_inter, hpreA, Set.empty_inter]
    simp [hpreA, hpreInter]

/-- Ratio-free finite-trace conditioning when the event sampled off the trace is mapped into a
possibly different target event.  This is the form needed for geometric gluing: after a trace is
spliced into a configuration carrying the two fresh arms, the arms themselves need not survive
as separately named events, provided their surviving subpaths and the trace-open interface give
the target crossing. -/
theorem setBernoulli_real_mul_le_inter_of_splice_maps
    (p : I) {E : Finset ι} {A B T : Set (Set ι)}
    (hA : DependsOn E A) (hTm : MeasurableSet T)
    (hmap : ∀ s ⊆ E, (↑s : Set ι) ∈ A →
      B ⊆ (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' T) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ T) := by
  classical
  have hAm : MeasurableSet A := hA.measurableSet
  rw [setBernoulli_real_eq_sum_splice p E hAm,
    setBernoulli_real_eq_sum_splice p E (hAm.inter hTm), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  by_cases hsA : (↑s : Set ι) ∈ A
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).2 hsA
    have hsubset : B ⊆
          (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ T) := by
      intro ω hωB
      exact ⟨Set.eq_univ_iff_forall.mp hpreA _, hmap s hsE hsA hωB⟩
    rw [hpreA, probReal_univ, mul_one]
    exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
      (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hsplice
      apply hsA
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).1 hsplice
    have hpreInter :
        (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ T) = ∅ := by
      rw [Set.preimage_inter, hpreA, Set.empty_inter]
    simp [hpreA, hpreInter]

/-- A finite-support event which forces open every coordinate where it overlaps the support of
an increasing event is positively correlated with that event.  Unlike FKG, the first event need
not itself be increasing. -/
theorem setBernoulli_real_mul_le_inter_of_forces_open
    (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn F B)
    (hBinc : IsIncreasingEvent B)
    (hforce : ∀ ω ∈ A, ∀ e ∈ E, e ∈ F → e ∈ ω) :
    setBer((Set.univ : Set ι), p).real A *
        setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  classical
  let μ := setBer((Set.univ : Set ι), p)
  have hAm : MeasurableSet A := hA.measurableSet
  have hBm : MeasurableSet B := hB.measurableSet
  rw [setBernoulli_real_eq_sum_splice p E hAm,
    setBernoulli_real_eq_sum_splice p E (hAm.inter hBm), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  by_cases hsA : (↑s : Set ι) ∈ A
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).2 hsA
    have hopen : ∀ e ∈ E, e ∈ F → e ∈ s := by
      intro e heE heF
      exact hforce (↑s : Set ι) hsA e heE heF
    have hsubset : B ⊆ (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' B := by
      intro ω hωB
      let η : Set ι := ω ∪ (↑s : Set ι)
      have hωη : ω ⊆ η := Set.subset_union_left
      have hηB : η ∈ B := hBinc hωη hωB
      have hagree : ∀ e ∈ F,
          e ∈ spliceOn E s ω ↔ e ∈ η := by
        intro e heF
        by_cases heE : e ∈ E
        · rw [mem_spliceOn_of_mem heE]
          have hes : e ∈ s := hopen e heE heF
          simp [η, hes]
        · rw [mem_spliceOn_of_notMem hsE heE]
          have hes : e ∉ s := fun hes ↦ heE (hsE hes)
          simp [η, hes]
      exact (hB hagree).2 hηB
    have hpreInter :
        (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ B) =
          (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' B := by
      simp only [Set.preimage_inter, hpreA, Set.univ_inter]
    rw [hpreA, hpreInter, probReal_univ, mul_one]
    exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
      (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)
  · have hpreA : (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' A = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hsplice
      apply hsA
      exact (hA fun e heE ↦ by
        rw [mem_spliceOn_of_mem heE]
        simp).1 hsplice
    have hpreInter :
        (fun ω : Set ι ↦ spliceOn E s ω) ⁻¹' (A ∩ B) = ∅ := by
      rw [Set.preimage_inter, hpreA, Set.empty_inter]
    simp [hpreA, hpreInter]

end Percolation
