import Percolation.Extensions.LongRangeNearOne
import Percolation.Extensions.LongRangeErgodicity

/-!
# Root-cluster tails and the multiscale mass count
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology unitInterval

/-- Translation is a graph isomorphism between a pulled-back configuration and the original
configuration. -/
def longRangeOpenGraphTranslateIso (a : ℤ) (ω : LongRangeConfiguration) :
    longRangeOpenGraph (longRangeConfigurationPullback a ω) ≃g
      longRangeOpenGraph ω where
  toEquiv := Equiv.addRight a
  map_rel_iff' := by
    intro x y
    simp [longRangeOpenGraph_adj, longRangeConfigurationPullback,
      longRangeEdgeTranslateEmbedding_mk]

theorem mem_longRangeConnectionEvent_pullback_iff
    (a : ℤ) (ω : LongRangeConfiguration) (x y : ℤ) :
    longRangeConfigurationPullback a ω ∈ longRangeConnectionEvent x y ↔
      ω ∈ longRangeConnectionEvent (x + a) (y + a) := by
  rw [← longRangeOpenGraph_reachable_iff, ← longRangeOpenGraph_reachable_iff]
  exact (longRangeOpenGraphTranslateIso a ω).reachable_iff.symm

/-- The root cluster contains at least `m` vertices, encoded by a literal finite witness.
This convention remains meaningful for infinite clusters. -/
def longRangeClusterAtLeastEvent (x : ℤ) (m : ℕ) :
    Set LongRangeConfiguration :=
  {ω | ∃ S : Finset ℤ, S.card = m ∧
    ∀ y ∈ S, ω ∈ longRangeConnectionEvent x y}

theorem measurableSet_longRangeClusterAtLeastEvent (x : ℤ) (m : ℕ) :
    MeasurableSet (longRangeClusterAtLeastEvent x m) := by
  rw [show longRangeClusterAtLeastEvent x m =
      ⋃ S : Finset ℤ, if S.card = m then
        ⋂ y : S, longRangeConnectionEvent x y else ∅ by
    ext ω
    simp [longRangeClusterAtLeastEvent]]
  exact MeasurableSet.iUnion fun S ↦ by
    split_ifs
    · exact MeasurableSet.iInter fun y ↦
        measurableSet_longRangeConnectionEvent x y
    · exact MeasurableSet.empty

theorem longRangeClusterAtLeastEvent_mono {x : ℤ} {m n : ℕ} (hmn : m ≤ n) :
    longRangeClusterAtLeastEvent x n ⊆ longRangeClusterAtLeastEvent x m := by
  classical
  rintro ω ⟨S, hScard, hS⟩
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (hScard ▸ hmn)
  exact ⟨T, hTcard, fun y hy ↦ hS y (hTS hy)⟩

theorem mem_longRangeClusterAtLeastEvent_of_infinite
    {ω : LongRangeConfiguration} {x : ℤ}
    (hinf : (longRangeCluster ω x).Infinite) (m : ℕ) :
    ω ∈ longRangeClusterAtLeastEvent x m := by
  classical
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq m
  exact ⟨S, hScard, fun y hy ↦
    mem_longRangeCluster_iff.mp (hSsub (by simpa using hy))⟩

theorem iInter_longRangeClusterAtLeastEvent_eq_percolationEvent (x : ℤ) :
    ⋂ m : ℕ, longRangeClusterAtLeastEvent x m = longRangePercolationEvent x := by
  ext ω
  simp only [Set.mem_iInter]
  rw [mem_longRangePercolationEvent_iff_cluster_infinite]
  constructor
  · intro h hfinite
    have hm := h ((longRangeCluster ω x).ncard + 1)
    rcases hm with ⟨S, hScard, hS⟩
    have hsub : (S : Set ℤ) ⊆ longRangeCluster ω x := by
      intro y hy
      exact mem_longRangeCluster_iff.mpr (hS y (by simpa using hy))
    have hcardle := Set.ncard_le_ncard hsub hfinite
    simpa [hScard] using hcardle
  · intro hinf
    intro m
    exact mem_longRangeClusterAtLeastEvent_of_infinite hinf m

theorem mem_longRangeClusterAtLeastEvent_pullback_iff
    (a : ℤ) (ω : LongRangeConfiguration) (x : ℤ) (m : ℕ) :
    longRangeConfigurationPullback a ω ∈ longRangeClusterAtLeastEvent x m ↔
      ω ∈ longRangeClusterAtLeastEvent (x + a) m := by
  classical
  constructor
  · rintro ⟨S, hScard, hS⟩
    refine ⟨S.image (fun y ↦ y + a), ?_, ?_⟩
    · calc
        (S.image (fun y ↦ y + a)).card = S.card :=
          Finset.card_image_of_injective _ (add_left_injective a)
        _ = m := hScard
    · intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨z, hz, rfl⟩
      exact (mem_longRangeConnectionEvent_pullback_iff a ω x z).mp (hS z hz)
  · rintro ⟨S, hScard, hS⟩
    refine ⟨S.image (fun y ↦ y - a), ?_, ?_⟩
    · calc
        (S.image (fun y ↦ y - a)).card = S.card :=
          Finset.card_image_of_injective _ sub_left_injective
        _ = m := hScard
    · intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨z, hz, rfl⟩
      rw [mem_longRangeConnectionEvent_pullback_iff]
      convert hS z hz using 1 <;> ring

theorem longRangeTranslatedEvent_clusterAtLeast (a x : ℤ) (m : ℕ) :
    longRangeTranslatedEvent a (longRangeClusterAtLeastEvent x m) =
      longRangeClusterAtLeastEvent (x + a) m := by
  ext ω
  exact mem_longRangeClusterAtLeastEvent_pullback_iff a ω x m

theorem longRangeMeasure_real_clusterAtLeast_eq_origin
    (p : LongRangeProfile) (x : ℤ) (m : ℕ) :
    (longRangeMeasure p).real (longRangeClusterAtLeastEvent x m) =
      (longRangeMeasure p).real (longRangeClusterAtLeastEvent 0 m) := by
  calc
    (longRangeMeasure p).real (longRangeClusterAtLeastEvent x m) =
        (longRangeMeasure p).real
          (longRangeTranslatedEvent x (longRangeClusterAtLeastEvent 0 m)) := by
      rw [longRangeTranslatedEvent_clusterAtLeast]
      simp
    _ = (longRangeMeasure p).real (longRangeClusterAtLeastEvent 0 m) :=
      longRangeMeasure_real_translatedEvent p
        (measurableSet_longRangeClusterAtLeastEvent 0 m) x

/-- Number of vertices in an interval whose ambient open cluster has at least `m` vertices. -/
noncomputable def longRangeLargeClusterVertexCount
    (ω : LongRangeConfiguration) (L m : ℕ) (z : ℤ) : ℕ :=
  by
    classical
    exact ((longRangeIntervalBlock L z).filter fun x ↦
      ω ∈ longRangeClusterAtLeastEvent x m).card

theorem largeComponent_implies_largeClusterVertexCount
    {ω : LongRangeConfiguration} {L m : ℕ} {z : ℤ}
    (hgood : ω ∈ longRangeIntervalLargeComponentEvent L m z) :
    m ≤ longRangeLargeClusterVertexCount ω L m z := by
  classical
  rcases hgood with ⟨x, hx⟩
  let B := longRangeIntervalBlock L z
  let C := longRangeComponentInFinset ω B x
  let e : B ↪ ℤ := Function.Embedding.subtype _
  change m ≤ C.card at hx
  obtain ⟨T, hTC, hTcard⟩ := Finset.exists_subset_card_eq hx
  have hmapSub : C.map e ⊆ B.filter fun y ↦
      ω ∈ longRangeClusterAtLeastEvent y m := by
    intro y hy
    rw [Finset.mem_map] at hy
    rcases hy with ⟨yB, hyC, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨yB.property, ?_⟩
    refine ⟨T.map e, ?_, ?_⟩
    · simpa using hTcard
    · intro v hv
      rw [Finset.mem_map] at hv
      rcases hv with ⟨vB, hvT, rfl⟩
      have hvC := hTC hvT
      rw [← longRangeOpenGraph_reachable_iff]
      have hyReach := mem_longRangeComponentInFinset_iff.mp hyC
      have hvReach := mem_longRangeComponentInFinset_iff.mp hvC
      have hInduced : ((longRangeOpenGraph ω).induce (B : Set ℤ)).Reachable yB vB :=
        hyReach.symm.trans hvReach
      let f : (longRangeOpenGraph ω).induce (B : Set ℤ) →g
          longRangeOpenGraph ω :=
        { toFun := Subtype.val
          map_rel' := fun {_ _} h ↦ h }
      exact hInduced.map f
  have hcount : m ≤ (B.filter fun y ↦
      ω ∈ longRangeClusterAtLeastEvent y m).card := by
    calc
      m ≤ C.card := hx
      _ = (C.map e).card := (Finset.card_map e).symm
      _ ≤ _ := Finset.card_le_card hmapSub
  simpa [longRangeLargeClusterVertexCount, B] using hcount

end Percolation
