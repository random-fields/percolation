import Percolation.Critical.DynamicHistoryReplay

/-!
# Replay reveal counters

The concrete Chapter 7 exploration never queries a coarse site twice.  Combining that fact with
the scale-uniform influence-site packing bound gives a finite, history-independent budget for the
number of runtime schedules which can change any fixed physical edge threshold.
-/

namespace Percolation

namespace DynamicBlockHistoryReplay

variable {d : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Coarse sites already queried by the canonical replay whose local reveal region can contain
the physical vertex `z`. -/
noncomputable def replayInfluenceSitesSeen
    (N : ℕ) (z : Cubic d) (root : F) (history : List (F × Bool)) : Finset F :=
  by
    classical
    exact ((canonicalSuffix root history).map Prod.fst).toFinset.filter
      fun v ↦ v.1 ∈ grimmettMarstrandInfluenceSites N z

/-- A newly admitted coarse query is not already counted. -/
theorem not_mem_replayInfluenceSitesSeen_of_admissibleQuery
    (N : ℕ) (z : Cubic d) (root : F) (history : List (F × Bool)) (v : F)
    (hadmissible : AdmissibleQuery root history v) :
    v ∉ replayInfluenceSitesSeen N z root history := by
  classical
  simp only [replayInfluenceSitesSeen, Finset.mem_filter, List.mem_toFinset, not_and_or]
  exact Or.inl (not_mem_canonicalSuffix_map_fst_of_admissibleQuery root history v hadmissible)

/-- Appending a genuine answer increments the local reveal counter exactly when the newly queried
site can influence `z`. -/
theorem replayInfluenceSitesSeen_append_singleton_of_mem
    (N : ℕ) (z : Cubic d) (root : F) (history : List (F × Bool)) (v : F)
    (accepted : Bool) (hadmissible : AdmissibleQuery root history v)
    (hv : v.1 ∈ grimmettMarstrandInfluenceSites N z) :
    replayInfluenceSitesSeen N z root (history ++ [(v, accepted)]) =
      insert v (replayInfluenceSitesSeen N z root history) := by
  classical
  rw [replayInfluenceSitesSeen, canonicalSuffix_append_singleton_of_admissibleQuery
    root history v accepted hadmissible]
  simp [replayInfluenceSitesSeen, Finset.filter_insert, hv]

/-- A query outside the influence set does not change the local reveal counter. -/
theorem replayInfluenceSitesSeen_append_singleton_of_not_mem
    (N : ℕ) (z : Cubic d) (root : F) (history : List (F × Bool)) (v : F)
    (accepted : Bool) (hadmissible : AdmissibleQuery root history v)
    (hv : v.1 ∉ grimmettMarstrandInfluenceSites N z) :
    replayInfluenceSitesSeen N z root (history ++ [(v, accepted)]) =
      replayInfluenceSitesSeen N z root history := by
  classical
  rw [replayInfluenceSitesSeen, canonicalSuffix_append_singleton_of_admissibleQuery
    root history v accepted hadmissible]
  simp [replayInfluenceSitesSeen, Finset.filter_insert, hv]

/-- The number of earlier queries capable of changing an edge incident to `z` is uniformly
bounded by the geometric influence-set cardinality. -/
theorem card_replayInfluenceSitesSeen_le_ncard
    (N : ℕ) (hN : 0 < N) (z : Cubic d) (root : F) (history : List (F × Bool)) :
    (replayInfluenceSitesSeen N z root history).card ≤
      (grimmettMarstrandInfluenceSites N z).ncard := by
  classical
  let seen := replayInfluenceSitesSeen N z root history
  have hsubset : (seen.image Subtype.val : Set (Cubic d)) ⊆
      grimmettMarstrandInfluenceSites N z := by
    intro x hx
    rw [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    change v ∈ replayInfluenceSitesSeen N z root history at hv
    exact (Finset.mem_filter.mp hv).2
  have hncard := Set.ncard_le_ncard hsubset
    (finite_grimmettMarstrandInfluenceSites hN z)
  rw [Set.ncard_coe_finset] at hncard
  calc
    seen.card = (seen.image Subtype.val).card := by
      rw [Finset.card_image_iff.mpr]
      exact Set.injOn_of_injective Subtype.val_injective
    _ ≤ (grimmettMarstrandInfluenceSites N z).ncard := hncard

/-- Explicit scale-uniform bound for the number of earlier influencing queries. -/
theorem card_replayInfluenceSitesSeen_le
    (N : ℕ) (hN : 0 < N) (z : Cubic d) (root : F)
    (history : List (F × Bool)) :
    (replayInfluenceSitesSeen N z root history).card ≤
      (2 ^ d) * (2 * d + 1) := by
  exact (card_replayInfluenceSitesSeen_le_ncard N hN z root history).trans
    (ncard_grimmettMarstrandInfluenceSites_le hN z)

end DynamicBlockHistoryReplay

end Percolation
