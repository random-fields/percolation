import Percolation.Critical.Radius
import Percolation.Core.TwoEdgeMenger
import Percolation.Bernoulli.Russo

/-!
# Pivotal sausages for finite radius events

This file formalizes the ordered pivotal-edge and gap variables used in Grimmett §5.2,
especially Lemmas 5.12 and 5.17.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

/-- Regard a dart of the cubic graph as a cubic edge. -/
def cubicEdgeOfDart {d : ℕ} (a : (cubicGraph d).Dart) : CubicEdge d :=
  ⟨a.edge, by
    change s(a.fst, a.snd) ∈ (cubicGraph d).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact a.adj⟩

/-- A path witness for `Aₙ(x)`, including its finite-support certificate. -/
structure RadiusConnectionWitness (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) where
  endpoint : Cubic d
  sphere_mem : endpoint ∈ cubicMetricSphere d x n
  walk : (cubicGraph d).Walk x endpoint
  isPath : walk.IsPath
  isOpen : walkIsOpen ω walk
  edge_subset : walkEdgeFinset walk ⊆ cubicMetricBallEdges d x n

theorem exists_radiusConnectionWitness {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) :
    Nonempty (RadiusConnectionWitness d x n ω) := by
  rcases hω with ⟨y, hy, w, hopen, hsub⟩
  let q : (cubicGraph d).Walk x y := (w.toPath : (cubicGraph d).Walk x y)
  refine ⟨⟨y, hy, q, w.toPath.2, walkIsOpen_toPath w hopen, ?_⟩⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  apply hsub
  rw [mem_walkEdgeFinset_iff]
  exact SimpleGraph.Walk.edges_toPath_subset w he

/-- A fixed witness, used only to turn the source's path-independent pivotal ordering into a
total Lean function. -/
noncomputable def canonicalRadiusWitness {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    RadiusConnectionWitness d x n ω :=
  Classical.choice (exists_radiusConnectionWitness hω)

/-- Ordered pivotal darts along the canonical open path. -/
noncomputable def radiusPivotalDarts {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    List ((cubicGraph d).Dart) := by
  classical
  exact (canonicalRadiusWitness hω).walk.darts.filter fun a ↦
    decide (IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart a) ω)

theorem radiusPivotalDarts_nodup {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    (radiusPivotalDarts hω).Nodup := by
  classical
  exact (SimpleGraph.Walk.darts_nodup_of_support_nodup
    (canonicalRadiusWitness hω).isPath.support_nodup).filter _

/-- The finite set of edges pivotal for `Aₙ(x)`. -/
noncomputable def radiusPivotalEdgeFinset (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBallEdges d x n).filter fun e ↦
    IsPivotal (radiusConnectionEvent d x n) e ω

/-- The number `N(Aₙ)` of pivotal edges. -/
noncomputable def radiusPivotalCount (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : ℕ :=
  (radiusPivotalEdgeFinset d x n ω).card

/-- The `k`-th pivotal sausage gap, indexed from one as in Grimmett.  It is zero when `Aₙ`
does not occur or fewer than `k` pivotal edges exist. -/
noncomputable def sausageGap (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) (k : ℕ) : ℕ := by
  classical
  by_cases hω : ω ∈ radiusConnectionEvent d x n
  · let L := radiusPivotalDarts hω
    by_cases hk : 1 ≤ k ∧ k ≤ L.length
    · let a := L[k - 1]'(by omega)
      by_cases hk1 : k = 1
      · exact cubicL1Dist x a.fst
      · let b := L[k - 2]'(by omega)
        exact cubicL1Dist b.snd a.fst
    · exact n
  · exact n

/-- The profile consisting of the pivotal count and all one-based sausage gaps. -/
structure PivotalSausageProfile where
  pivotalCount : ℕ
  gap : ℕ → ℕ

noncomputable def pivotalSausageProfile (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : PivotalSausageProfile where
  pivotalCount := radiusPivotalCount d x n ω
  gap := sausageGap d x n ω

theorem pivotal_open_of_mem_event {ι : Type*} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {ω : Set ι} (hω : ω ∈ A) {e : ι}
    (he : IsPivotal A e ω) : e ∈ ω := by
  have hpiv := (hA.isPivotal_iff e ω).mp he
  by_contra heω
  apply hpiv.2
  simpa [Set.diff_singleton_eq_self heω] using hω

/-- Every pivotal edge of `Aₙ(x)` occurs on every open path witnessing `Aₙ(x)`. -/
theorem pivotal_mem_witness_walk {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {y : Cubic d} (hy : y ∈ cubicMetricSphere d x n)
    (w : (cubicGraph d).Walk x y) (hopen : walkIsOpen ω w)
    (hsub : walkEdgeFinset w ⊆ cubicMetricBallEdges d x n)
    {e : CubicEdge d} (he : IsPivotal (radiusConnectionEvent d x n) e ω) :
    (e : Sym2 (Cubic d)) ∈ w.edges := by
  have heopen := pivotal_open_of_mem_event
    (isIncreasingEvent_radiusConnectionEvent d x n) hω he
  by_contra hew
  have hopen' : walkIsOpen (ω \ {e}) w := by
    intro f hf
    have hfopen := hopen f hf
    constructor
    · exact hfopen
    · intro hfe
      apply hew
      have hval : f = (e : Sym2 (Cubic d)) := by
        exact congrArg Subtype.val (by simpa using hfe)
      exact hval ▸ hf
  have hclosed : ω \ {e} ∈ radiusConnectionEvent d x n :=
    ⟨y, hy, w, hopen', hsub⟩
  exact ((isIncreasingEvent_radiusConnectionEvent d x n).isPivotal_iff e ω).mp he |>.2 hclosed

/-- The canonical pivotal list contains exactly the pivotal edges of `Aₙ(x)`; in particular,
the pivotal count does not omit any pivotal edge. -/
theorem mem_radiusPivotalDarts_iff {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (a : (cubicGraph d).Dart) :
    a ∈ radiusPivotalDarts hω ↔
      a ∈ (canonicalRadiusWitness hω).walk.darts ∧
        IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart a) ω := by
  classical
  simp [radiusPivotalDarts]

theorem radiusPivotalDarts_length_eq_count {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    (radiusPivotalDarts hω).length = radiusPivotalCount d x n ω := by
  classical
  let w := (canonicalRadiusWitness hω).walk
  let L := radiusPivotalDarts hω
  have hLsub : ∀ a ∈ L, a ∈ w.darts := by
    intro a ha
    exact (mem_radiusPivotalDarts_iff hω a).mp ha |>.1
  have hedge_inj : ∀ a ∈ w.darts, ∀ b ∈ w.darts,
      cubicEdgeOfDart a = cubicEdgeOfDart b → a = b := by
    intro a ha b hb hab
    apply List.inj_on_of_nodup_map (f := SimpleGraph.Dart.edge)
      (l := w.darts) (by
        simpa [SimpleGraph.Walk.edges] using (canonicalRadiusWitness hω).isPath.isTrail.edges_nodup)
      ha hb
    exact congrArg Subtype.val hab
  have hmap_nodup : (L.map cubicEdgeOfDart).Nodup :=
    (radiusPivotalDarts_nodup hω).map_on fun a ha b hb hab ↦
      hedge_inj a (hLsub a ha) b (hLsub b hb) hab
  have hfinset : (L.map cubicEdgeOfDart).toFinset =
      radiusPivotalEdgeFinset d x n ω := by
    ext e
    constructor
    · intro he
      rw [List.mem_toFinset, List.mem_map] at he
      rcases he with ⟨a, ha, rfl⟩
      rw [radiusPivotalEdgeFinset, Finset.mem_filter]
      have ha' := (mem_radiusPivotalDarts_iff hω a).mp ha
      exact ⟨(canonicalRadiusWitness hω).edge_subset <|
        (mem_walkEdgeFinset_iff _ _).mpr <| by
          rw [SimpleGraph.Walk.edges]
          exact List.mem_map.mpr ⟨a, ha'.1, rfl⟩, ha'.2⟩
    · intro he
      rw [radiusPivotalEdgeFinset, Finset.mem_filter] at he
      have hep := pivotal_mem_witness_walk hω
        (canonicalRadiusWitness hω).sphere_mem (canonicalRadiusWitness hω).walk
        (canonicalRadiusWitness hω).isOpen (canonicalRadiusWitness hω).edge_subset he.2
      rw [SimpleGraph.Walk.edges] at hep
      rcases List.mem_map.mp hep with ⟨a, ha, hae⟩
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨a, ?_, ?_⟩
      · rw [mem_radiusPivotalDarts_iff]
        refine ⟨ha, ?_⟩
        have haee : cubicEdgeOfDart a = e := Subtype.ext hae
        rw [haee]
        exact he.2
      · apply Subtype.ext
        exact hae
  rw [radiusPivotalCount, ← hfinset, List.toFinset_card_of_nodup hmap_nodup,
    List.length_map]

end Percolation
