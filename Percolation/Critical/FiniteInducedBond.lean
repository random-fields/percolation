import Percolation.Critical.IncomingGreenDomination
import Percolation.Critical.RootedSiteShellProbability

/-!
# Finite induced bond-connection probabilities

This file is the bond analogue of `FiniteInducedSite.lean`.  It first removes the dummy
non-edge coordinates from the finite bond-to-site comparison, then embeds the actual edges of a
finite induced cubic-region ball into the ambient cubic edge type.  Consequently the finite
comparison and infinite-volume region percolation use exactly the same Bernoulli bond law.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

namespace IncomingGreenDomination

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The target-hitting event written on the graph's actual edge subtype rather than on all
unordered vertex pairs. -/
def edgeSetBondHitsTargetEvent (root : V) (target : Finset V) :
    Set (Set G.edgeSet) :=
  {omega | ∃ t ∈ target, ∃ w : G.Walk root t,
    ∀ e, ∀ he : e ∈ w.edges, (⟨e, w.edges_subset_edgeSet he⟩ : G.edgeSet) ∈ omega}

/-- Inclusion of the actual graph-edge coordinates into all unordered vertex pairs. -/
def edgeValEmbedding : G.edgeSet ↪ Sym2 V where
  toFun := Subtype.val
  inj' := Subtype.val_injective

theorem measurableSet_edgeSetBondHitsTargetEvent (root : V) (target : Finset V) :
    MeasurableSet (edgeSetBondHitsTargetEvent G root target) := by
  have hdep : DependsOn (Finset.univ : Finset G.edgeSet)
      (edgeSetBondHitsTargetEvent G root target) := by
    intro omega eta hagree
    have homegaEta : omega = eta := by
      ext e
      exact hagree e (Finset.mem_univ e)
    subst eta
    rfl
  exact hdep.measurableSet

/-- Restricting an all-pairs configuration to actual graph edges identifies the two finite bond
target events. -/
theorem bondHitsTargetEvent_eq_preimage_edgeSet (root : V) (target : Finset V) :
    bondHitsTargetEvent G root target =
      (fun omega : Set (Sym2 V) ↦ edgeValEmbedding G ⁻¹' omega) ⁻¹'
        edgeSetBondHitsTargetEvent G root target := by
  ext omega
  constructor
  · rintro ⟨t, ht, w, hw⟩
    exact ⟨t, ht, w, fun e he ↦ hw e he⟩
  · rintro ⟨t, ht, w, hw⟩
    exact ⟨t, ht, w, fun e he ↦ hw e he⟩

/-- Dummy non-edge coordinates in `bondHitsTargetEvent` integrate out exactly. -/
theorem setBernoulli_real_bondHitsTargetEvent_eq_edgeSet
    (p : I) (root : V) (target : Finset V) :
    setBer((Set.univ : Set (Sym2 V)), p).real
        (bondHitsTargetEvent G root target) =
      setBer((Set.univ : Set G.edgeSet), p).real
        (edgeSetBondHitsTargetEvent G root target) := by
  let f : G.edgeSet ↪ Sym2 V := edgeValEmbedding G
  have hmap := setBernoulli_map_preimage_univ f p
  have hmeas := measurableSet_edgeSetBondHitsTargetEvent G root target
  rw [← hmap, map_measureReal_apply (measurable_preimage_embedding f) hmeas]
  exact congrArg (setBer((Set.univ : Set (Sym2 V)), p)).real
    (bondHitsTargetEvent_eq_preimage_edgeSet G root target)

end IncomingGreenDomination

/-- The finite induced ball, abbreviated for the bond restriction map below. -/
abbrev CubicRegionBallGraph
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :=
  (cubicRegionGraph d F).induce (cubicRegionMetricBall d F root n : Set F)

/-- Forget both subtype layers of a finite region-ball vertex. -/
def cubicRegionBallVertexVal
    {d : ℕ} {F : Set (Cubic d)} {root : F} {n : ℕ} :
    {v : F // v ∈ cubicRegionMetricBall d F root n} → Cubic d :=
  fun v ↦ v.1.1

/-- The graph homomorphism from the finite induced region ball to the ambient cubic graph. -/
def cubicRegionBallToCubicHom
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    CubicRegionBallGraph d F root n →g cubicGraph d where
  toFun := cubicRegionBallVertexVal
  map_rel' := by
    intro x y hxy
    exact SimpleGraph.induce_adj.mp (SimpleGraph.induce_adj.mp hxy)

theorem cubicRegionBallToCubicHom_injective
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    Function.Injective (cubicRegionBallToCubicHom d F root n) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- Every actual edge of a finite induced region ball is an ambient cubic edge. -/
def cubicRegionBallEdgeEmbedding
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    (CubicRegionBallGraph d F root n).edgeSet ↪ CubicEdge d where
  toFun e := ⟨Sym2.map (cubicRegionBallToCubicHom d F root n) e.1,
    (cubicRegionBallToCubicHom d F root n).map_mem_edgeSet e.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Sym2.map.injective (cubicRegionBallToCubicHom_injective d F root n)
    exact congrArg Subtype.val hef

@[simp]
theorem cubicRegionBallEdgeEmbedding_val
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ)
    (e : (CubicRegionBallGraph d F root n).edgeSet) :
    ((cubicRegionBallEdgeEmbedding d F root n e : CubicEdge d) : Sym2 (Cubic d)) =
      Sym2.map cubicRegionBallVertexVal e.1 :=
  rfl

/-- Ambient bond event obtained by restricting a cubic configuration to the actual edges of the
finite induced region ball. -/
def cubicRegionBondConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    Set (EdgeConfiguration d) :=
  (fun omega : EdgeConfiguration d ↦
      cubicRegionBallEdgeEmbedding d F root n ⁻¹' omega) ⁻¹'
    IncomingGreenDomination.edgeSetBondHitsTargetEvent
      (CubicRegionBallGraph d F root n)
      (cubicRegionBallRoot d F root n)
      (cubicRegionBallTarget d F root n)

theorem measurableSet_cubicRegionBondConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    MeasurableSet (cubicRegionBondConnectionToSphereEvent d F root n) := by
  exact (IncomingGreenDomination.measurableSet_edgeSetBondHitsTargetEvent
      (CubicRegionBallGraph d F root n)
      (cubicRegionBallRoot d F root n)
      (cubicRegionBallTarget d F root n)).preimage
    (measurable_preimage_embedding (cubicRegionBallEdgeEmbedding d F root n))

/-- The finite all-pairs bond probability used by the incoming-green comparison is exactly the
ambient cubic bond probability of the region-ball shell event. -/
theorem setBernoulli_real_finiteRegionBall_bondHitsTarget_eq_ambient
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) (p : I) :
    setBer((Set.univ : Set (Sym2 {v : F //
        v ∈ cubicRegionMetricBall d F root n})), p).real
        (IncomingGreenDomination.bondHitsTargetEvent
          (CubicRegionBallGraph d F root n)
          (cubicRegionBallRoot d F root n)
          (cubicRegionBallTarget d F root n)) =
      (bernoulliBondMeasure d p).real
        (cubicRegionBondConnectionToSphereEvent d F root n) := by
  let H := CubicRegionBallGraph d F root n
  let f : H.edgeSet ↪ CubicEdge d := cubicRegionBallEdgeEmbedding d F root n
  have hmap := setBernoulli_map_preimage_univ f p
  have hmeas := IncomingGreenDomination.measurableSet_edgeSetBondHitsTargetEvent H
    (cubicRegionBallRoot d F root n) (cubicRegionBallTarget d F root n)
  rw [IncomingGreenDomination.setBernoulli_real_bondHitsTargetEvent_eq_edgeSet]
  rw [bernoulliBondMeasure, ← hmap,
    map_measureReal_apply (measurable_preimage_embedding f) hmeas]
  rfl

/-- An infinite open bond cluster at `root` crosses every finite region sphere through the
corresponding induced ball. -/
theorem regionInfiniteClusterEvent_subset_cubicRegionBondConnectionToSphereEvent
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) :
    {omega | (cubicOpenClusterWithinVertices d F omega (root : Cubic d)).Infinite} ⊆
      cubicRegionBondConnectionToSphereEvent d F root n := by
  intro omega hInfinite
  obtain ⟨y, hyCluster, hyNotBall⟩ :=
    hInfinite.exists_notMem_finset (cubicMetricBall d root n)
  have hyFar : n ≤ cubicL1Dist (root : Cubic d) y := by
    have hyNotLe : ¬ cubicL1Dist (root : Cubic d) y ≤ n := by
      intro hyLe
      exact hyNotBall (mem_cubicMetricBall_iff_l1Dist_le.mpr hyLe)
    omega
  rcases hyCluster with ⟨hyF, w, hwOpen, hwSupport⟩
  let yF : F := ⟨y, hyF⟩
  let wF₀ := w.induce F hwSupport
  let wF : (cubicRegionGraph d F).Walk root yF :=
    wF₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  obtain ⟨z, q, hzSphere, hqBall, _hqSupport, hqPrefix⟩ :=
    exists_cubicRegionWalk_edgePrefix_to_metricSphere wF (by simp) hyFar
  let zBall : {v : F // v ∈ cubicRegionMetricBall d F root n} :=
    ⟨z, mem_cubicRegionMetricBall_iff.mpr
      (mem_cubicRegionMetricSphere_iff.mp hzSphere).le⟩
  let qBall₀ := q.induce (cubicRegionMetricBall d F root n : Set F) hqBall
  let qBall : (CubicRegionBallGraph d F root n).Walk
      (cubicRegionBallRoot d F root n) zBall :=
    qBall₀.copy (Subtype.ext rfl) (Subtype.ext rfl)
  refine ⟨zBall, ?_, qBall, ?_⟩
  · exact mem_finsetTargetSubtype_iff.mpr hzSphere
  · intro e he
    have he₀ : e ∈ qBall₀.edges := by
      simpa [qBall] using he
    have heRegion : Sym2.map (fun v : {v : F //
        v ∈ cubicRegionMetricBall d F root n} ↦ v.1) e ∈ q.edges := by
      have heMap : Sym2.map (fun v : {v : F //
          v ∈ cubicRegionMetricBall d F root n} ↦ v.1) e ∈
          (qBall₀.map (SimpleGraph.Embedding.induce
            (G := cubicRegionGraph d F)
            (cubicRegionMetricBall d F root n : Set F)).toHom).edges := by
        rw [SimpleGraph.Walk.edges_map]
        exact List.mem_map.mpr ⟨e, he₀, rfl⟩
      have hmap := SimpleGraph.Walk.map_induce q hqBall
      simpa [qBall₀] using hmap ▸ heMap
    have heWF : Sym2.map (fun v : {v : F //
        v ∈ cubicRegionMetricBall d F root n} ↦ v.1) e ∈ wF.edges := by
      obtain ⟨tail, htail⟩ := hqPrefix
      rw [← htail]
      exact List.mem_append.mpr (Or.inl heRegion)
    let embF := SimpleGraph.Embedding.induce (G := cubicGraph d) F
    have heAmbient : Sym2.map (fun v : F ↦ v.1)
        (Sym2.map (fun v : {v : F //
          v ∈ cubicRegionMetricBall d F root n} ↦ v.1) e) ∈
        (wF.map embF.toHom).edges := by
      rw [SimpleGraph.Walk.edges_map]
      exact List.mem_map.mpr ⟨_, heWF, rfl⟩
    have hwFmap : wF.map embF.toHom = w := by
      have hmap := SimpleGraph.Walk.map_induce w hwSupport
      simpa [wF, wF₀, embF] using hmap
    rw [hwFmap] at heAmbient
    have hopen := hwOpen _ heAmbient
    simpa [cubicRegionBallEdgeEmbedding_val, cubicRegionBallVertexVal,
      Sym2.map_map] using hopen

end Percolation
