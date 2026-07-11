import Percolation.Critical.StaticBlocks
import Percolation.Critical.InfiniteClusterDensity

/-!
# Deterministic adapters for the Chapter 7 coalescence estimate

Lemma 7.89 bounds the probability that two macroscopic arms do not merge in a larger box.
This file supplies the pathwise interface: an infinite-cluster vertex in the inner box reaches
the outer surface through the outer box, and hence failure of two such vertices to connect is
literally the previously defined two-arm separation event.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

/-- First hitting of a coordinate-box surface by a walk which starts anywhere inside the box.
This generalizes `exists_open_walk_to_cubicBoxSurface_in_box`, whose starting point is the box
center. -/
theorem exists_open_walk_to_cubicBoxSurface_in_box_of_mem
    {d N : ℕ} {ω : EdgeConfiguration d} {c u y : Cubic d}
    (hu : u ∈ cubicMetricBox d c N) (w : (cubicGraph d).Walk u y)
    (hopen : walkIsOpen ω w) (hy : N ≤ cubicLInfDist c y) :
    ∃ z, z ∈ cubicBoxSurface d c N ∧
      ω ∈ connectionEventIn d (cubicBoxEdges d c N) u z := by
  classical
  have hexit : ∃ k : ℕ,
      k ≤ w.length ∧ N ≤ cubicLInfDist c (w.getVert k) :=
    ⟨w.length, le_rfl, by simpa using hy⟩
  let k := Nat.find hexit
  have hk : k ≤ w.length ∧ N ≤ cubicLInfDist c (w.getVert k) := Nat.find_spec hexit
  have hkdist : cubicLInfDist c (w.getVert k) = N := by
    by_cases hkzero : k = 0
    · have hstart : w.getVert k = u := by simp [hkzero]
      apply le_antisymm
      · rw [hstart]
        exact mem_cubicMetricBox_iff_lInfDist_le.mp hu
      · exact hk.2
    · let j := k - 1
      have hksucc : k = j + 1 := by omega
      have hjfind : j < Nat.find hexit := by change j < k; omega
      have hjlt : cubicLInfDist c (w.getVert j) < N := by
        apply lt_of_not_ge
        intro hj
        exact Nat.find_min hexit hjfind ⟨by omega, hj⟩
      have hjlen : j < w.length := by omega
      have hadj := w.adj_getVert_succ hjlen
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
      have hupper : cubicLInfDist c (w.getVert (j + 1)) ≤ N := by
        calc
          cubicLInfDist c (w.getVert (j + 1)) ≤
              cubicLInfDist c (w.getVert j) +
                cubicLInfDist (w.getVert j) (w.getVert (j + 1)) :=
            cubicLInfDist_triangle _ _ _
          _ ≤ cubicLInfDist c (w.getVert j) + 1 := by
            gcongr
            rw [ha]
            exact cubicLInfDist_stepFrom_le_one _ _
          _ ≤ N := by omega
      rw [hksucc]
      exact le_antisymm hupper (by simpa [hksucc] using hk.2)
  let q := w.take k
  have hqLength : q.length = k := by simp [q, Nat.min_eq_left hk.1]
  have hqSupport : ∀ z ∈ q.support, z ∈ cubicMetricBox d c N := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    rcases hz with ⟨m, hm, hmle⟩
    subst z
    have hmk : m ≤ k := by omega
    have hget : q.getVert m = w.getVert m := by simp [q, Nat.min_eq_right hmk]
    rw [hget, mem_cubicMetricBox_iff_lInfDist_le]
    by_cases hmk' : m = k
    · simpa [hmk'] using hkdist.le
    · have hmlt : m < k := lt_of_le_of_ne hmk hmk'
      apply le_of_lt
      apply lt_of_not_ge
      intro hmge
      exact Nat.find_min hexit hmlt ⟨(hmle.trans_eq hqLength).trans hk.1, hmge⟩
  have hqOpen : walkIsOpen ω q := by
    intro e he
    apply hopen e
    have he' : e ∈ (w.take k).edges := by simpa [q] using he
    rw [SimpleGraph.Walk.edges_take] at he'
    exact List.Sublist.subset (List.take_sublist k w.edges) he'
  refine ⟨w.getVert k, ?_, q, hqOpen, ?_⟩
  · rw [mem_cubicBoxSurface]
    exact hkdist
  · exact walkEdgeFinset_subset_cubicBoxEdges_of_support q hqSupport

/-- An infinite-cluster vertex inside a finite coordinate box has an open connection, using
only internal box edges, to that box's surface. -/
theorem hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent
    {d N : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    (hxBox : x ∈ cubicMetricBox d cubicOrigin N)
    (hxInf : hasInfiniteOpenClusterFrom d ω x) :
    ω ∈ connectionToBoxSurfaceEvent d N x := by
  classical
  have hexists : ∃ y ∈ cubicOpenClusterFrom d ω x,
      y ∉ cubicMetricBox d cubicOrigin N := by
    by_contra hnot
    push Not at hnot
    apply hxInf
    exact (cubicMetricBox d cubicOrigin N).finite_toSet.subset fun y hy ↦ hnot y hy
  obtain ⟨y, ⟨w, hwOpen⟩, hyBox⟩ := hexists
  have hyFar : N ≤ cubicLInfDist cubicOrigin y := by
    exact le_of_not_ge fun hle ↦
      hyBox (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
  obtain ⟨z, hzSurface, hzConn⟩ :=
    exists_open_walk_to_cubicBoxSurface_in_box_of_mem hxBox w hwOpen hyFar
  apply Set.mem_iUnion.mpr
  refine ⟨z, Set.mem_iUnion.mpr ⟨hzSurface, ?_⟩⟩
  exact hzConn

/-- Two infinite-cluster vertices in the inner box which are not connected in the outer box
realize the two-arm separation event. -/
theorem mem_twoArmSeparationEvent_of_infinite_of_not_connected
    {d n N : ℕ} {ω : EdgeConfiguration d} {x y : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n)
    (hy : y ∈ cubicMetricBox d cubicOrigin n)
    (hnN : n ≤ N)
    (hxInf : hasInfiniteOpenClusterFrom d ω x)
    (hyInf : hasInfiniteOpenClusterFrom d ω y)
    (hxy : ω ∉ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y) :
    ω ∈ twoArmSeparationEvent d n N x y := by
  rw [twoArmSeparationEvent, if_pos ⟨hx, hy⟩]
  refine ⟨⟨?_, ?_⟩, hxy⟩
  · exact hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent
      (mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans hnN)) hxInf
  · exact hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent
      (mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((mem_cubicMetricBox_iff_lInfDist_le.mp hy).trans hnN)) hyInf

/-- Outside the two-arm event, any two infinite-cluster vertices of the inner box are connected
inside the outer box. -/
theorem connectionEventIn_of_infinite_of_not_twoArm
    {d n N : ℕ} {ω : EdgeConfiguration d} {x y : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n)
    (hy : y ∈ cubicMetricBox d cubicOrigin n)
    (hnN : n ≤ N)
    (hxInf : hasInfiniteOpenClusterFrom d ω x)
    (hyInf : hasInfiniteOpenClusterFrom d ω y)
    (hnot : ω ∉ twoArmSeparationEvent d n N x y) :
    ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y := by
  by_contra hxy
  exact hnot (mem_twoArmSeparationEvent_of_infinite_of_not_connected
    hx hy hnN hxInf hyInf hxy)

/-- Every pair of infinite-cluster vertices in the inner box is connected inside the outer
box.  The explicit finite intersection makes measurability transparent. -/
def infiniteClusterCoalescenceEvent (d n N : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ x ∈ cubicMetricBox d cubicOrigin n,
    ⋂ y ∈ cubicMetricBox d cubicOrigin n,
      ((infiniteClusterVertexEvent d x ∩ infiniteClusterVertexEvent d y)ᶜ ∪
        connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y)

theorem measurableSet_infiniteClusterCoalescenceEvent (d n N : ℕ) :
    MeasurableSet (infiniteClusterCoalescenceEvent d n N) := by
  apply (cubicMetricBox d cubicOrigin n).measurableSet_biInter
  intro x hx
  apply (cubicMetricBox d cubicOrigin n).measurableSet_biInter
  intro y hy
  exact ((measurableSet_infiniteClusterVertexEvent d x).inter
    (measurableSet_infiniteClusterVertexEvent d y)).compl.union
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y).measurableSet

theorem mem_infiniteClusterCoalescenceEvent_iff {d n N : ℕ}
    {ω : EdgeConfiguration d} :
    ω ∈ infiniteClusterCoalescenceEvent d n N ↔
      ∀ x ∈ cubicMetricBox d cubicOrigin n,
        ∀ y ∈ cubicMetricBox d cubicOrigin n,
          hasInfiniteOpenClusterFrom d ω x →
          hasInfiniteOpenClusterFrom d ω y →
          ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y := by
  simp only [infiniteClusterCoalescenceEvent, Set.mem_iInter, Set.mem_union,
    Set.mem_compl_iff, Set.mem_inter_iff, infiniteClusterVertexEvent, Set.mem_setOf_eq]
  constructor
  · intro h x hx y hy hxInf hyInf
    rcases h x hx y hy with hnot | hconn
    · exact False.elim (hnot ⟨hxInf, hyInf⟩)
    · exact hconn
  · intro h x hx y hy
    by_cases hInf : hasInfiniteOpenClusterFrom d ω x ∧
        hasInfiniteOpenClusterFrom d ω y
    · exact Or.inr (h x hx y hy hInf.1 hInf.2)
    · exact Or.inl hInf

/-- Failure of inner-box infinite-cluster coalescence is covered by the finite union of
two-arm separation events. -/
theorem infiniteClusterCoalescenceEvent_compl_subset_iUnion_twoArm
    {d n N : ℕ} (hnN : n ≤ N) :
    (infiniteClusterCoalescenceEvent d n N)ᶜ ⊆
      ⋃ x ∈ cubicMetricBox d cubicOrigin n,
        ⋃ y ∈ cubicMetricBox d cubicOrigin n,
          twoArmSeparationEvent d n N x y := by
  intro ω hω
  by_contra hnotUnion
  apply hω
  rw [mem_infiniteClusterCoalescenceEvent_iff]
  intro x hx y hy hxInf hyInf
  apply connectionEventIn_of_infinite_of_not_twoArm hx hy hnN hxInf hyInf
  intro hxy
  apply hnotUnion
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
    Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hxy⟩⟩⟩⟩

/-- Finite union bound reducing coalescence failure to pairwise two-arm probabilities. -/
theorem bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_sum
    {d n N : ℕ} (p : I) (hnN : n ≤ N) :
    (bernoulliBondMeasure d p).real (infiniteClusterCoalescenceEvent d n N)ᶜ ≤
      ∑ x ∈ cubicMetricBox d cubicOrigin n,
        ∑ y ∈ cubicMetricBox d cubicOrigin n,
          (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) := by
  let μ := bernoulliBondMeasure d p
  calc
    μ.real (infiniteClusterCoalescenceEvent d n N)ᶜ ≤
        μ.real (⋃ x ∈ cubicMetricBox d cubicOrigin n,
          ⋃ y ∈ cubicMetricBox d cubicOrigin n,
            twoArmSeparationEvent d n N x y) :=
      measureReal_mono
        (infiniteClusterCoalescenceEvent_compl_subset_iUnion_twoArm hnN)
        (measure_ne_top _ _)
    _ ≤ ∑ x ∈ cubicMetricBox d cubicOrigin n,
          μ.real (⋃ y ∈ cubicMetricBox d cubicOrigin n,
            twoArmSeparationEvent d n N x y) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ cubicMetricBox d cubicOrigin n,
          ∑ y ∈ cubicMetricBox d cubicOrigin n,
            μ.real (twoArmSeparationEvent d n N x y) := by
      apply Finset.sum_le_sum
      intro x hx
      exact measureReal_biUnion_finset_le _ _

/-- Uniform two-arm bounds imply the polynomially corrected coalescence estimate. -/
theorem bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_card_sq_mul
    {d n N : ℕ} (p : I) (hnN : n ≤ N) (q : ℝ)
    (hpair : ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n,
        (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) ≤ q) :
    (bernoulliBondMeasure d p).real (infiniteClusterCoalescenceEvent d n N)ᶜ ≤
      ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 * q := by
  calc
    (bernoulliBondMeasure d p).real (infiniteClusterCoalescenceEvent d n N)ᶜ ≤
        ∑ x ∈ cubicMetricBox d cubicOrigin n,
          ∑ y ∈ cubicMetricBox d cubicOrigin n,
            (bernoulliBondMeasure d p).real (twoArmSeparationEvent d n N x y) :=
      bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_sum p hnN
    _ ≤ ∑ _x ∈ cubicMetricBox d cubicOrigin n,
          ∑ _y ∈ cubicMetricBox d cubicOrigin n, q := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact hpair x hx y hy
    _ = ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 * q := by
      simp [pow_two, mul_assoc]

/-- A uniform pairwise two-arm estimate whose polynomially corrected upper bound tends to zero
implies that every pair of inner infinite-cluster vertices coalesces in the outer box with
probability tending to one.  This is the exact analytic interface between Lemma 7.89 and the
probability assembly of Lemma 7.97. -/
theorem infiniteClusterCoalescenceEvent_probability_tendsto_one_of_twoArm_bound
    {d : ℕ} (p : I) (r R : ℕ → ℕ) (q : ℕ → ℝ)
    (hrR : ∀ n, r n ≤ R n)
    (hpair : ∀ n, ∀ x ∈ cubicMetricBox d cubicOrigin (r n),
      ∀ y ∈ cubicMetricBox d cubicOrigin (r n),
        (bernoulliBondMeasure d p).real
          (twoArmSeparationEvent d (r n) (R n) x y) ≤ q n)
    (hdecay : Filter.Tendsto
      (fun n ↦ ((cubicMetricBox d cubicOrigin (r n)).card : ℝ) ^ 2 * q n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterCoalescenceEvent d (r n) (R n)))
      Filter.atTop (nhds 1) := by
  let μ := bernoulliBondMeasure d p
  let C : ℕ → Set (EdgeConfiguration d) := fun n ↦
    infiniteClusterCoalescenceEvent d (r n) (R n)
  have hfailure : Filter.Tendsto (fun n ↦ μ.real (C n)ᶜ)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg)
      (Filter.Eventually.of_forall fun n ↦ ?_) hdecay
    simpa [μ, C] using
      bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_card_sq_mul
        p (hrR n) (q n) (hpair n)
  have hEq : (fun n ↦ μ.real (C n)) = fun n ↦ 1 - μ.real (C n)ᶜ := by
    funext n
    rw [probReal_compl_eq_one_sub
      (measurableSet_infiniteClusterCoalescenceEvent d (r n) (R n))]
    linarith
  rw [hEq]
  simpa [μ, C] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfailure

end Percolation
