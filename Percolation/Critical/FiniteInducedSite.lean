import Percolation.Critical.FiniteExplorationBellman

/-!
# Finite induced site-connection probabilities

This file identifies a finite induced-graph target event with the corresponding cylinder event
in the ambient iid site configuration.  It is the probability bridge used when the finite
Bellman comparison in Grimmett Lemma 7.24 is applied to successive metric balls.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A site configuration joins `root` to at least one vertex of a finite target. -/
def siteHitsFinsetEvent {V : Type*} (G : SimpleGraph V) (root : V)
    (target : Finset V) : Set (Set V) :=
  {eta | ∃ t ∈ target, eta ∈ siteConnectionEvent G root t}

theorem measurableSet_siteHitsFinsetEvent
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) (target : Finset V) :
    MeasurableSet (siteHitsFinsetEvent G root target) := by
  classical
  have heq : siteHitsFinsetEvent G root target =
      ⋃ t ∈ target, siteConnectionEvent G root t := by
    ext eta
    simp [siteHitsFinsetEvent]
  rw [heq]
  exact target.measurableSet_biUnion fun t _ht ↦
    measurableSet_siteConnectionEvent G root t

theorem isIncreasingEvent_siteHitsFinsetEvent
    {V : Type*} (G : SimpleGraph V) (root : V) (target : Finset V) :
    IsIncreasingEvent (siteHitsFinsetEvent G root target) := by
  intro eta xi hetaXi
  rintro ⟨t, ht, hconn⟩
  exact ⟨t, ht, isIncreasingEvent_siteConnectionEvent G root t hetaXi hconn⟩

theorem eventTrace_siteHitsFinsetEvent
    {V : Type*} (G : SimpleGraph V) (root : V) (target : Finset V) :
    eventTrace (siteHitsFinsetEvent G root target) =
      SiteExploration.finiteSiteHitsTarget G root target := by
  rfl

/-- On a finite vertex type, the ambient iid site probability is the finite-cube probability
used by the Bellman recursion. -/
theorem setBernoulli_real_siteHitsFinsetEvent_eq_finiteBernoulliProbability
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (target : Finset V) (p : I) :
    setBer((Set.univ : Set V), p).real (siteHitsFinsetEvent G root target) =
      finiteBernoulliProbability Finset.univ (p : ℝ)
        (SiteExploration.finiteSiteHitsTarget G root target) := by
  have hdep : DependsOn (Finset.univ : Finset V) (siteHitsFinsetEvent G root target) := by
    intro eta xi hagree
    have hetaXi : eta = xi := by
      ext z
      exact hagree z (Finset.mem_univ z)
    subst xi
    rfl
  rw [hdep.setBernoulli_real_eq_finiteBernoulliProbability p,
    eventTrace_siteHitsFinsetEvent]

/-- The vertices of `target` regarded as vertices of the graph induced by `R`. -/
noncomputable def finsetTargetSubtype
    {V : Type*} [DecidableEq V] (R target : Finset V) : Finset {v : V // v ∈ R} :=
  target.subtype fun v ↦ v ∈ R

@[simp]
theorem mem_finsetTargetSubtype_iff
    {V : Type*} [DecidableEq V] {R target : Finset V} {v : {v : V // v ∈ R}} :
    v ∈ finsetTargetSubtype R target ↔ (v : V) ∈ target := by
  classical
  rw [finsetTargetSubtype]
  exact Finset.mem_subtype

/-- Restricting an ambient configuration to a finite induced subgraph identifies the induced
target event with a connection constrained to the inducing finset. -/
theorem preimage_siteHitsFinsetEvent_induce
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (R target : Finset V)
    (root : V) (hroot : root ∈ R) :
    (fun eta : Set V ↦ (Subtype.val : {v : V // v ∈ R} → V) ⁻¹' eta) ⁻¹'
        siteHitsFinsetEvent (G.induce (R : Set V)) ⟨root, hroot⟩
          (finsetTargetSubtype R target) =
      {eta : Set V | ∃ t ∈ target, eta ∈ siteConnectionEventIn G R root t} := by
  classical
  ext eta
  constructor
  · rintro ⟨t, htTarget, w, hwOpen⟩
    refine ⟨(t : V), mem_finsetTargetSubtype_iff.mp htTarget,
      w.map (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom, ?_, ?_⟩
    · intro z hz
      have hsupp := SimpleGraph.Walk.support_map
        (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom w
      have hz' := (congrArg (fun l => z ∈ l) hsupp).mp hz
      obtain ⟨z', _hz', rfl⟩ := List.mem_map.mp hz'
      exact z'.property
    · intro z hz
      have hsupp := SimpleGraph.Walk.support_map
        (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom w
      have hzMapMem := (congrArg (fun l => z ∈ l) hsupp).mp hz
      obtain ⟨z', hzSupport, hzEq⟩ := List.mem_map.mp hzMapMem
      subst z
      exact hwOpen z' hzSupport
  · rintro ⟨t, htTarget, w, hwR, hwOpen⟩
    let q := w.induce (R : Set V) hwR
    let rootR : {v : V // v ∈ R} := ⟨root, hwR root w.start_mem_support⟩
    let tR : {v : V // v ∈ R} := ⟨t, hwR t w.end_mem_support⟩
    have hrootEq : rootR = ⟨root, hroot⟩ := Subtype.ext rfl
    refine ⟨tR, ?_, q.copy hrootEq ?_, ?_⟩
    · exact mem_finsetTargetSubtype_iff.mpr htTarget
    · exact Subtype.ext rfl
    · intro z hz
      change (z : V) ∈ eta
      apply hwOpen (z : V)
      have hzq : z ∈ q.support := by simpa using hz
      have hzMap : (z : V) ∈
          (q.map (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom).support := by
        rw [SimpleGraph.Walk.support_map
          (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom q]
        exact List.mem_map.mpr ⟨z, hzq, rfl⟩
      have hmap : q.map (SimpleGraph.Embedding.induce (G := G) (R : Set V)).toHom = w := by
        simpa [q] using SimpleGraph.Walk.map_induce w hwR
      rw [hmap] at hzMap
      exact hzMap

/-- Probability form of the finite induced-subgraph restriction identity. -/
theorem finiteBernoulliProbability_induced_siteHitsTarget_eq_ambient
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) (R target : Finset V) (root : V) (hroot : root ∈ R) (p : I) :
    finiteBernoulliProbability Finset.univ (p : ℝ)
        (SiteExploration.finiteSiteHitsTarget (G.induce (R : Set V)) ⟨root, hroot⟩
          (finsetTargetSubtype R target)) =
      setBer((Set.univ : Set V), p).real
        {eta : Set V | ∃ t ∈ target, eta ∈ siteConnectionEventIn G R root t} := by
  let f : {v : V // v ∈ R} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap := setBernoulli_map_preimage_univ f p
  have hmeas := measurableSet_siteHitsFinsetEvent
    (G.induce (R : Set V)) ⟨root, hroot⟩ (finsetTargetSubtype R target)
  rw [← setBernoulli_real_siteHitsFinsetEvent_eq_finiteBernoulliProbability]
  rw [← hmap, map_measureReal_apply (measurable_preimage_embedding f) hmeas]
  change setBer((Set.univ : Set V), p).real
      ((fun eta : Set V ↦
        (Subtype.val : {v : V // v ∈ R} → V) ⁻¹' eta) ⁻¹'
          siteHitsFinsetEvent (G.induce (R : Set V)) ⟨root, hroot⟩
            (finsetTargetSubtype R target)) = _
  rw [preimage_siteHitsFinsetEvent_induce G R target root hroot]

end Percolation
