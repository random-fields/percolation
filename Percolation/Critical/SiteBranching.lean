import Percolation.Critical.Regions
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# A bounded-degree branching bound for site percolation

The elementary path-counting argument in this file is deliberately graph-generic.  On a
locally finite graph of maximum degree `D`, the number of walks of length `n` from a fixed
root is at most `D^n`.  A self-avoiding open-site walk of that length uses `n+1` distinct
sites, giving the usual subcritical criterion `D p < 1`.
-/

open Filter MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped BigOperators unitInterval

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- All walks of a prescribed length starting at `x`, with their endpoint sigma-packaged. -/
def rootedWalks (G : SimpleGraph V) [G.LocallyFinite] :
    (n : ℕ) → (x : V) → Finset (Σ y, G.Walk x y)
  | 0, x => {⟨x, .nil⟩}
  | n + 1, x =>
      (Finset.univ : Finset (G.neighborSet x)).biUnion fun y =>
        (rootedWalks G n y).image fun q =>
          ⟨q.1, .cons y.2 q.2⟩

theorem mem_rootedWalks_iff (G : SimpleGraph V) [G.LocallyFinite]
    {n : ℕ} {x : V} {q : Σ y, G.Walk x y} :
    q ∈ G.rootedWalks n x ↔ q.2.length = n := by
  induction n generalizing x q with
  | zero => grind [rootedWalks, SimpleGraph.Walk.length_eq_zero_iff,
      SimpleGraph.Walk.eq_nil_iff_nil, SimpleGraph.Walk.Nil.eq]
  | succ n ih =>
      rcases q with ⟨z, w⟩
      cases w with
      | nil =>
          constructor
          · intro hmem
            rw [rootedWalks] at hmem
            obtain ⟨y, _hy, himage⟩ := Finset.mem_biUnion.mp hmem
            obtain ⟨q, _hq, heq⟩ := Finset.mem_image.mp himage
            have hlen := congrArg
              (fun r : Σ z, G.Walk x z => r.2.length) heq
            simp at hlen
          · intro hlen
            simp at hlen
      | @cons x y z hxy w =>
          simp only [rootedWalks, Finset.mem_biUnion, Finset.mem_univ, true_and,
            Finset.mem_image]
          constructor
          · rintro ⟨a, q, hq, heq⟩
            have hqLen : q.2.length = n := (ih (q := q)).mp hq
            have hlen := congrArg
              (fun r : Σ z, G.Walk x z => r.2.length) heq
            simpa [hqLen] using hlen.symm
          · intro hwLen
            refine ⟨⟨y, hxy⟩, ⟨z, w⟩, ?_, rfl⟩
            apply (ih (q := ⟨z, w⟩)).mpr
            simpa using hwLen

/-- Maximum-degree path count, retaining all walks so no self-avoidance enumeration is needed. -/
theorem card_rootedWalks_le (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D) (n : ℕ) (x : V) :
    (G.rootedWalks n x).card ≤ D ^ n := by
  induction n generalizing x with
  | zero => simp [rootedWalks]
  | succ n ih =>
      calc
        (G.rootedWalks (n + 1) x).card ≤
            ∑ y : G.neighborSet x, (G.rootedWalks n y).card := by
          rw [rootedWalks]
          refine Finset.card_biUnion_le.trans ?_
          exact Finset.sum_le_sum fun y _hy => Finset.card_image_le
        _ ≤ ∑ _y : G.neighborSet x, D ^ n :=
          Finset.sum_le_sum fun y _hy => ih y
        _ = G.degree x * D ^ n := by
          simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
            congrArg (fun k : ℕ => k * D ^ n)
              (SimpleGraph.card_neighborSet_eq_degree G x)
        _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hdegree x)
        _ = D ^ (n + 1) := by rw [pow_succ']

end SimpleGraph

namespace Percolation

/-- Cylinder event that every vertex visited by `w` is open. -/
def siteWalkOpenEvent {V : Type*} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) : Set (Set V) :=
  {eta | ∀ z ∈ w.support, z ∈ eta}

theorem siteWalkOpenEvent_eq_superset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (w : G.Walk x y) :
    siteWalkOpenEvent w = {eta : Set V | (w.support.toFinset : Set V) ⊆ eta} := by
  ext eta
  constructor
  · intro h z hz
    exact h z (List.mem_toFinset.mp hz)
  · intro h z hz
    exact h (List.mem_toFinset.mpr hz)

theorem measurableSet_siteWalkOpenEvent {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (w : G.Walk x y) :
    MeasurableSet (siteWalkOpenEvent w) := by
  rw [siteWalkOpenEvent_eq_superset]
  exact measurableSet_superset_finset _

theorem setBernoulli_real_siteWalkOpenEvent_of_isPath
    {V : Type*} [Countable V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (w : G.Walk x y)
    (hw : w.IsPath) (p : I) :
    (setBernoulli (Set.univ : Set V) p).real (siteWalkOpenEvent w) =
      (p : ℝ) ^ (w.length + 1) := by
  rw [siteWalkOpenEvent_eq_superset,
    setBernoulli_real_superset_finset_univ]
  congr 1
  rw [List.toFinset_card_of_nodup hw.support_nodup, w.length_support]

/-- Finite union of open self-avoiding walks of length `n` from `x`. -/
def siteOpenPathOfLengthEvent {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (x : V) (n : ℕ) : Set (Set V) :=
  ⋃ q ∈ G.rootedWalks n x,
    if q.2.IsPath then siteWalkOpenEvent q.2 else ∅

theorem measurableSet_siteOpenPathOfLengthEvent
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (x : V) (n : ℕ) :
    MeasurableSet (siteOpenPathOfLengthEvent G x n) := by
  apply (G.rootedWalks n x).measurableSet_biUnion
  intro q hq
  split_ifs
  · exact measurableSet_siteWalkOpenEvent q.2
  · exact MeasurableSet.empty

/-- Union bound for an open self-avoiding path in a bounded-degree graph. -/
theorem setBernoulli_real_siteOpenPathOfLengthEvent_le
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (x : V) (n : ℕ) (p : I) :
    (setBernoulli (Set.univ : Set V) p).real
        (siteOpenPathOfLengthEvent G x n) ≤
      (D : ℝ) ^ n * (p : ℝ) ^ (n + 1) := by
  let W := G.rootedWalks n x
  calc
    (setBernoulli (Set.univ : Set V) p).real
        (siteOpenPathOfLengthEvent G x n) ≤
        ∑ q ∈ W,
          (setBernoulli (Set.univ : Set V) p).real
            (if q.2.IsPath then siteWalkOpenEvent q.2 else ∅) := by
      exact measureReal_biUnion_finset_le W _
    _ ≤ ∑ _q ∈ W, (p : ℝ) ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hpath
      · rw [setBernoulli_real_siteWalkOpenEvent_of_isPath q.2 hpath p,
          (SimpleGraph.mem_rootedWalks_iff G).mp hq]
      · simpa using (pow_nonneg p.2.1 (n + 1))
    _ = W.card * (p : ℝ) ^ (n + 1) := by simp
    _ ≤ (D ^ n : ℕ) * (p : ℝ) ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast SimpleGraph.card_rootedWalks_le G hdegree n x
      · exact pow_nonneg p.2.1 _
    _ = (D : ℝ) ^ n * (p : ℝ) ^ (n + 1) := by norm_cast

private theorem finite_siteOpenGraph_neighborSet
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
    (eta : Set V) (x : V) :
    ((siteOpenGraph G eta).neighborSet x).Finite := by
  exact (G.neighborSet x).toFinite.subset fun y hy => (siteOpenGraph_adj.mp hy).1

private theorem finite_siteGraphReachableWithin
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (eta : Set V) : ∀ (n : ℕ) (x : V),
      {y | ∃ w : (siteOpenGraph G eta).Walk x y, w.length ≤ n}.Finite
  | 0, x => by
      apply Set.finite_singleton x |>.subset
      rintro y ⟨w, hw⟩
      have hlen : w.length = 0 := Nat.eq_zero_of_le_zero hw
      simpa using (w.eq_of_length_eq_zero hlen).symm
  | n + 1, x => by
      let T : Set V := {x} ∪ ⋃ v ∈ (siteOpenGraph G eta).neighborSet x,
        {y | ∃ w : (siteOpenGraph G eta).Walk v y, w.length ≤ n}
      have hT : T.Finite := by
        apply Set.Finite.union (Set.finite_singleton x)
        exact (finite_siteOpenGraph_neighborSet eta x).biUnion fun v hv =>
          finite_siteGraphReachableWithin G eta n v
      apply hT.subset
      rintro y ⟨w, hw⟩
      cases w with
      | nil => exact Set.mem_union_left _ (Set.mem_singleton x)
      | @cons _ v y hxv q =>
          refine Set.mem_union_right _ ?_
          refine Set.mem_iUnion.2 ⟨v, ?_⟩
          refine Set.mem_iUnion.2 ⟨hxv, ?_⟩
          exact ⟨q, by simpa using hw⟩

private theorem siteOpenGraph_walk_support_subset
    {V : Type*} {G : SimpleGraph V} {eta : Set V} {x y : V}
    (w : (siteOpenGraph G eta).Walk x y) (hx : x ∈ eta) :
    ∀ z ∈ w.support, z ∈ eta := by
  induction w with
  | nil => simpa using hx
  | @cons u v z huv w ih =>
      intro a ha
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact (siteOpenGraph_adj.mp huv).2.1
      · exact ih (siteOpenGraph_adj.mp huv).2.2 a ha

/-- An infinite site cluster forces an open self-avoiding path of every length. -/
theorem siteOpenPathOfLengthEvent_of_siteOpenCluster_infinite
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {eta : Set V} {x : V} (hinf : (siteOpenCluster G eta x).Infinite)
    (n : ℕ) : eta ∈ siteOpenPathOfLengthEvent G x n := by
  have hx : x ∈ eta := by
    by_contra hx
    apply hinf
    rw [siteOpenCluster_eq_reachable]
    simp [hx]
  have hreach : ({y | (siteOpenGraph G eta).Reachable x y} : Set V).Infinite := by
    rw [siteOpenCluster_eq_reachable] at hinf
    simpa [hx] using hinf
  have hnsub : ¬({y | (siteOpenGraph G eta).Reachable x y} : Set V) ⊆
      {y | ∃ w : (siteOpenGraph G eta).Walk x y, w.length ≤ n} := by
    intro hsub
    exact hreach ((finite_siteGraphReachableWithin G eta n x).subset hsub)
  obtain ⟨y, hyreach, hyn⟩ := Set.not_subset.mp hnsub
  rcases hyreach with ⟨q⟩
  let w := q.toPath
  have hnle : n ≤ w.1.length := by
    by_contra h
    apply hyn
    exact ⟨w.1, Nat.le_of_lt (Nat.lt_of_not_ge h)⟩
  let r := w.1.take n
  let openToBase : siteOpenGraph G eta →g G :=
    { toFun := id
      map_rel' := fun h => (siteOpenGraph_adj.mp h).1 }
  let s := r.map openToBase
  have hsPath : s.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective (fun _ _ h => h) (w.2.take n)
  have hsLength : s.length = n := by simp [s, r, SimpleGraph.Walk.take_length, hnle]
  change eta ∈ ⋃ q ∈ G.rootedWalks n x,
    if q.2.IsPath then siteWalkOpenEvent q.2 else ∅
  let qS : Σ y, G.Walk x y := ⟨_, s⟩
  refine Set.mem_iUnion.2 ⟨qS, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact (SimpleGraph.mem_rootedWalks_iff G).mpr hsLength
  · change eta ∈ if s.IsPath then siteWalkOpenEvent s else ∅
    rw [if_pos hsPath]
    change ∀ z ∈ s.support, z ∈ eta
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact siteOpenGraph_walk_support_subset r hx v hv

/-- Rooted site percolation is null below the elementary branching bound. -/
theorem setBernoulli_siteOpenCluster_infinite_eq_zero_of_mul_lt_one
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (p : I) (hp : (D : ℝ) * (p : ℝ) < 1) (x : V) :
    setBernoulli (Set.univ : Set V) p
      {eta | (siteOpenCluster G eta x).Infinite} = 0 := by
  let mu := setBernoulli (Set.univ : Set V) p
  have hle (n : ℕ) :
      mu.real {eta | (siteOpenCluster G eta x).Infinite} ≤
        (p : ℝ) * ((D : ℝ) * (p : ℝ)) ^ n := by
    calc
      mu.real {eta | (siteOpenCluster G eta x).Infinite} ≤
          mu.real (siteOpenPathOfLengthEvent G x n) :=
        measureReal_mono (fun eta h =>
          siteOpenPathOfLengthEvent_of_siteOpenCluster_infinite G h n)
      _ ≤ (D : ℝ) ^ n * (p : ℝ) ^ (n + 1) :=
        setBernoulli_real_siteOpenPathOfLengthEvent_le G hdegree x n p
      _ = (p : ℝ) * ((D : ℝ) * (p : ℝ)) ^ n := by ring
  have hnonneg : 0 ≤ (D : ℝ) * (p : ℝ) := mul_nonneg (by positivity) p.2.1
  have htend : Tendsto (fun n : ℕ =>
      (p : ℝ) * ((D : ℝ) * (p : ℝ)) ^ n) atTop (nhds 0) := by
    have hpconst : Tendsto (fun _ : ℕ => (p : ℝ)) atTop (nhds (p : ℝ)) :=
      tendsto_const_nhds
    have hpow : Tendsto (fun n : ℕ => ((D : ℝ) * (p : ℝ)) ^ n)
        atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.2 ⟨by linarith, hp⟩)
    convert hpconst.mul hpow using 1 <;> simp
  apply (measureReal_eq_zero_iff (μ := mu)).mp
  apply le_antisymm
  · exact ge_of_tendsto' htend hle
  · exact measureReal_nonneg

/-- Global bounded-degree site percolation criterion. -/
theorem siteTheta_eq_zero_of_degree_mul_lt_one
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (p : I) (hp : (D : ℝ) * (p : ℝ) < 1) :
    siteTheta G p = 0 := by
  unfold siteTheta
  apply (measureReal_eq_zero_iff
    (μ := setBernoulli (Set.univ : Set V) p)).mpr
  rw [show {eta | hasInfiniteSiteCluster G eta} =
      ⋃ x : V, {eta | (siteOpenCluster G eta x).Infinite} by
    ext eta
    simp [hasInfiniteSiteCluster]]
  exact measure_iUnion_null fun x =>
    setBernoulli_siteOpenCluster_infinite_eq_zero_of_mul_lt_one
      G hdegree p hp x

end Percolation
