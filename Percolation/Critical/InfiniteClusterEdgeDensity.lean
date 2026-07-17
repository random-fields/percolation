import Percolation.Critical.InfiniteClusterZeroOne

/-!
# Edgewise balance at the infinite cluster

This file proves the one-edge probability identity underlying Grimmett's equation (8.101).
The common off-edge event is evaluated after forcing the distinguished edge closed.  The
Bernoulli coordinate factorization then gives the exact open/closed weights `p` and `1 - p`.

The almost-sure spatial-density limit is not asserted in this local-balance file.  It is
discharged later, under the positive finite-cluster radius exponent from Theorem 8.21, by
finite-cylinder approximation and Borel--Cantelli rather than a multiparameter ergodic theorem.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

section DeleteOneEdge

variable {V : Type*} {G : SimpleGraph V} {u v z : V}

/-- If `z` is connected to one endpoint of an edge, then after deleting that edge it remains
connected to at least one endpoint. -/
theorem SimpleGraph.Reachable.reachable_deleteEdges_endpoint_cover
    (huz : G.Reachable u z) (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).Reachable u z ∨
      (G.deleteEdges {s(u, v)}).Reachable v z := by
  classical
  obtain ⟨P, hP⟩ := huz.symm.exists_isPath
  by_cases heP : s(u, v) ∈ P.edges
  · have hvP : v ∈ P.support := P.snd_mem_support_of_mem_edges heP
    let Q := P.takeUntil v hvP
    have huNotQ : u ∉ Q.support := by
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hP hvP huv.ne
    have heNotQ : s(u, v) ∉ Q.edges := by
      intro heQ
      exact huNotQ (Q.fst_mem_support_of_mem_edges heQ)
    right
    exact (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨Q, heNotQ⟩).symm
  · left
    exact (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨P, heP⟩).symm

/-- Deleting an edge incident to the root of an infinite component leaves an infinite component
attached to at least one endpoint. -/
theorem SimpleGraph.infinite_reachable_deleteEdges_endpoint
    (huv : G.Adj u v) (huInf : {z | G.Reachable u z}.Infinite) :
    {z | (G.deleteEdges {s(u, v)}).Reachable u z}.Infinite ∨
      {z | (G.deleteEdges {s(u, v)}).Reachable v z}.Infinite := by
  classical
  let U : Set V := {z | (G.deleteEdges {s(u, v)}).Reachable u z}
  let W : Set V := {z | (G.deleteEdges {s(u, v)}).Reachable v z}
  have hcover : {z | G.Reachable u z} ⊆ U ∪ W := by
    intro z huz
    exact SimpleGraph.Reachable.reachable_deleteEdges_endpoint_cover huz huv
  by_cases hU : U.Infinite
  · exact Or.inl hU
  · right
    by_contra hW
    exact huInf (((Set.not_infinite.mp hU).union (Set.not_infinite.mp hW)).subset hcover)

end DeleteOneEdge

/-- Rooted infinitude expressed directly through reachability in the random open graph. -/
theorem hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite
    {d : ℕ} {omega : EdgeConfiguration d} {x : Cubic d} :
    hasInfiniteOpenClusterFrom d omega x ↔
      {y | (cubicOpenGraph d omega).Reachable x y}.Infinite := by
  have hsupp : ((cubicOpenGraph d omega).connectedComponentMk x).supp =
      {y | (cubicOpenGraph d omega).Reachable x y} := by
    ext y
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact SimpleGraph.reachable_comm
  rw [hasInfiniteOpenClusterFrom, ← cubicOpenGraph_component_supp, hsupp]

/-- Infinitude propagates along reachability in the open graph. -/
theorem hasInfiniteOpenClusterFrom_of_openGraph_reachable
    {d : ℕ} {omega : EdgeConfiguration d} {x y : Cubic d}
    (hxy : (cubicOpenGraph d omega).Reachable x y)
    (hxInf : hasInfiniteOpenClusterFrom d omega x) :
    hasInfiniteOpenClusterFrom d omega y := by
  apply hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite.mpr
  exact (hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite.mp hxInf).mono
    (fun z hxz ↦ hxy.symm.trans hxz)

/-- The endpoints of an open cubic edge are mutually reachable in the open graph. -/
theorem cubicOpenGraph_reachable_of_mem_edge_toFinset
    {d : ℕ} {e : CubicEdge d} {omega : EdgeConfiguration d}
    (heOpen : e ∈ omega) {x y : Cubic d}
    (hxe : x ∈ e.1.toFinset) (hye : y ∈ e.1.toFinset) :
    (cubicOpenGraph d omega).Reachable x y := by
  classical
  rcases e with ⟨edge, heCubic⟩
  induction edge using Sym2.ind with
  | _ u v =>
      have huv : (cubicGraph d).Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using heCubic
      have hOpenAdj : (cubicOpenGraph d omega).Adj u v :=
        cubicOpenGraph_adj.mpr ⟨huv, heOpen⟩
      have hxuv : x = u ∨ x = v := by
        simpa [Sym2.mem_toFinset] using hxe
      have hyuv : y = u ∨ y = v := by
        simpa [Sym2.mem_toFinset] using hye
      rcases hxuv with rfl | rfl <;> rcases hyuv with rfl | rfl
      · exact ⟨SimpleGraph.Walk.nil⟩
      · exact hOpenAdj.reachable
      · exact hOpenAdj.symm.reachable
      · exact ⟨SimpleGraph.Walk.nil⟩

/-- Closing a finite coordinate set after any splice on the same coordinates is independent of
the intermediate trace. -/
@[simp]
theorem spliceOn_empty_spliceOn {ι : Type*} [DecidableEq ι]
    {E s : Finset ι} (hs : s ⊆ E) (omega : Set ι) :
    spliceOn E ∅ (spliceOn E s omega) = spliceOn E ∅ omega := by
  ext a
  by_cases ha : a ∈ E
  · simp only [mem_spliceOn_of_mem ha]
  · rw [mem_spliceOn_of_notMem (by simp) ha,
      mem_spliceOn_of_notMem hs ha,
      mem_spliceOn_of_notMem (by simp) ha]

/-- The event that, after closing `e`, at least one endpoint of `e` lies in an infinite open
cluster.  It is deliberately evaluated in the closed-edge configuration, so it depends only on
coordinates other than `e`. -/
def edgeInfiniteContinuationEvent {d : ℕ} (e : CubicEdge d) :
    Set (EdgeConfiguration d) :=
  ⋃ x ∈ e.1.toFinset,
    (fun omega ↦ spliceOn {e} ∅ omega) ⁻¹'
      {eta | hasInfiniteOpenClusterFrom d eta x}

theorem mem_edgeInfiniteContinuationEvent_iff {d : ℕ} {e : CubicEdge d}
    {omega : EdgeConfiguration d} :
    omega ∈ edgeInfiniteContinuationEvent e ↔
      ∃ x ∈ e.1.toFinset,
        hasInfiniteOpenClusterFrom d (spliceOn {e} ∅ omega) x := by
  simp [edgeInfiniteContinuationEvent]

theorem measurable_edgeInfiniteContinuationEvent {d : ℕ} (e : CubicEdge d) :
    MeasurableSet (edgeInfiniteContinuationEvent e) := by
  classical
  have hclose : Measurable (fun omega : EdgeConfiguration d ↦ spliceOn {e} ∅ omega) := by
    apply (measurable_spliceOn_generateFrom
      (E := {e}) (s := ∅) (by simp)).mono
    · exact generateFrom_coordinateEvents_le _
    · exact le_rfl
  exact Finset.measurableSet_biUnion _ fun x _hx ↦
    hclose (measurableSet_hasInfiniteOpenClusterFrom d x)

/-- Splicing the distinguished edge does not change its off-edge continuation event. -/
theorem preimage_spliceOn_edgeInfiniteContinuationEvent {d : ℕ}
    (e : CubicEdge d) {s : Finset (CubicEdge d)} (hs : s ⊆ {e}) :
    (fun omega ↦ spliceOn {e} s omega) ⁻¹' edgeInfiniteContinuationEvent e =
      edgeInfiniteContinuationEvent e := by
  classical
  ext omega
  simp only [edgeInfiniteContinuationEvent, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rcases hx with ⟨hxe, hxInf⟩
    exact ⟨hxe, by simpa [spliceOn_empty_spliceOn hs] using hxInf⟩
  · rintro ⟨x, hxe, hxInf⟩
    exact ⟨x, hxe, by simpa [spliceOn_empty_spliceOn hs] using hxInf⟩

/-- A distinguished edge is open and its closed-edge remainder has an infinite continuation from
one of its endpoints.  This is the local interior-edge event used in equation (8.101). -/
def infiniteClusterInteriorEdgeEvent {d : ℕ} (e : CubicEdge d) :
    Set (EdgeConfiguration d) :=
  edgeInfiniteContinuationEvent e ∩ finiteCylinder {e} {e}

/-- A distinguished edge is closed and its closed-edge remainder has an infinite continuation
from one of its endpoints.  This is the local boundary-edge event used in equation (8.101). -/
def infiniteClusterBoundaryEdgeEvent {d : ℕ} (e : CubicEdge d) :
    Set (EdgeConfiguration d) :=
  edgeInfiniteContinuationEvent e ∩ finiteCylinder {e} ∅

/-- An infinite continuation survives closing an open edge at one of its two endpoints. -/
theorem exists_endpoint_hasInfiniteOpenClusterFrom_spliceOn_empty_singleton
    {d : ℕ} (e : CubicEdge d) {omega : EdgeConfiguration d}
    (heOpen : e ∈ omega) {x : Cubic d} (hxe : x ∈ e.1.toFinset)
    (hxInf : hasInfiniteOpenClusterFrom d omega x) :
    ∃ y ∈ e.1.toFinset,
      hasInfiniteOpenClusterFrom d (spliceOn {e} ∅ omega) y := by
  classical
  rcases e with ⟨edge, heCubic⟩
  induction edge using Sym2.ind with
  | _ u v =>
      let e : CubicEdge d := ⟨s(u, v), heCubic⟩
      have huv : (cubicGraph d).Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using heCubic
      have hGadj : (cubicOpenGraph d omega).Adj u v := by
        exact cubicOpenGraph_adj.mpr ⟨huv, by simpa [e] using heOpen⟩
      have hxuv : x = u ∨ x = v := by
        simpa [Sym2.mem_toFinset] using hxe
      have hxReachInf :
          {z | (cubicOpenGraph d omega).Reachable x z}.Infinite :=
        hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite.mp hxInf
      have hdeleted :
          {z | ((cubicOpenGraph d omega).deleteEdges {s(u, v)}).Reachable u z}.Infinite ∨
            {z | ((cubicOpenGraph d omega).deleteEdges {s(u, v)}).Reachable v z}.Infinite := by
        rcases hxuv with rfl | rfl
        · exact SimpleGraph.infinite_reachable_deleteEdges_endpoint hGadj hxReachInf
        · rcases SimpleGraph.infinite_reachable_deleteEdges_endpoint hGadj.symm hxReachInf with
            hvInf | huInf
          · exact Or.inr (by simpa [Sym2.eq_swap] using hvInf)
          · exact Or.inl (by simpa [Sym2.eq_swap] using huInf)
      have hgraph :
          cubicOpenGraph d (spliceOn {e} ∅ omega) =
            (cubicOpenGraph d omega).deleteEdges {s(u, v)} := by
        simpa [e, underlyingCubicEdges] using
          (cubicOpenGraph_spliceOn_empty {e} omega)
      rcases hdeleted with huInf | hvInf
      · refine ⟨u, by simp [Sym2.mem_toFinset], ?_⟩
        apply hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite.mpr
        rwa [hgraph]
      · refine ⟨v, by simp [Sym2.mem_toFinset], ?_⟩
        apply hasInfiniteOpenClusterFrom_iff_openGraph_reachable_infinite.mpr
        rwa [hgraph]

theorem measurable_infiniteClusterInteriorEdgeEvent {d : ℕ} (e : CubicEdge d) :
    MeasurableSet (infiniteClusterInteriorEdgeEvent e) :=
  (measurable_edgeInfiniteContinuationEvent e).inter
    (measurableSet_finiteCylinder (by simp))

theorem measurable_infiniteClusterBoundaryEdgeEvent {d : ℕ} (e : CubicEdge d) :
    MeasurableSet (infiniteClusterBoundaryEdgeEvent e) :=
  (measurable_edgeInfiniteContinuationEvent e).inter
    (measurableSet_finiteCylinder (by simp))

/-- Semantic form of the interior-edge event: the edge is open and touches an infinite open
cluster.  Since the edge is open, this is equivalent to both endpoints belonging to that same
infinite cluster. -/
theorem mem_infiniteClusterInteriorEdgeEvent_iff {d : ℕ} {e : CubicEdge d}
    {omega : EdgeConfiguration d} :
    omega ∈ infiniteClusterInteriorEdgeEvent e ↔
      e ∈ omega ∧ ∃ x ∈ e.1.toFinset, hasInfiniteOpenClusterFrom d omega x := by
  classical
  constructor
  · rintro ⟨hcontinuation, hcylinder⟩
    have heOpen : e ∈ omega := by
      exact (mem_finiteCylinder.mp hcylinder e (by simp)).mpr (by simp)
    obtain ⟨x, hxe, hxInf⟩ :=
      mem_edgeInfiniteContinuationEvent_iff.mp hcontinuation
    have hcloseSubset : spliceOn {e} ∅ omega ⊆ omega := by
      intro f hf
      rw [mem_spliceOn] at hf
      exact hf.elim (by simp) And.left
    exact ⟨heOpen, x, hxe,
      isIncreasingEvent_hasInfiniteOpenClusterFrom d x hcloseSubset hxInf⟩
  · rintro ⟨heOpen, x, hxe, hxInf⟩
    refine ⟨mem_edgeInfiniteContinuationEvent_iff.mpr
      (exists_endpoint_hasInfiniteOpenClusterFrom_spliceOn_empty_singleton
        e heOpen hxe hxInf), ?_⟩
    intro f hf
    simp only [Finset.mem_singleton] at hf
    subst f
    simp [heOpen]

/-- Source-facing semantic form: an interior edge is open and both of its endpoints belong to
the infinite-cluster vertex set. -/
theorem mem_infiniteClusterInteriorEdgeEvent_iff_all_endpoints {d : ℕ}
    {e : CubicEdge d} {omega : EdgeConfiguration d} :
    omega ∈ infiniteClusterInteriorEdgeEvent e ↔
      e ∈ omega ∧
        ∀ x ∈ e.1.toFinset, hasInfiniteOpenClusterFrom d omega x := by
  constructor
  · rw [mem_infiniteClusterInteriorEdgeEvent_iff]
    rintro ⟨heOpen, y, hye, hyInf⟩
    refine ⟨heOpen, fun x hxe ↦ ?_⟩
    exact hasInfiniteOpenClusterFrom_of_openGraph_reachable
      (cubicOpenGraph_reachable_of_mem_edge_toFinset heOpen hye hxe) hyInf
  · rintro ⟨heOpen, hall⟩
    rw [mem_infiniteClusterInteriorEdgeEvent_iff]
    have hnonempty : e.1.toFinset.Nonempty := by
      rcases e with ⟨edge, heCubic⟩
      induction edge using Sym2.ind with
      | _ u v => exact ⟨u, by simp [Sym2.mem_toFinset]⟩
    obtain ⟨x, hxe⟩ := hnonempty
    exact ⟨heOpen, x, hxe, hall x hxe⟩

/-- Semantic form of the boundary-edge event: the edge is closed and touches an infinite open
cluster. -/
theorem mem_infiniteClusterBoundaryEdgeEvent_iff {d : ℕ} {e : CubicEdge d}
    {omega : EdgeConfiguration d} :
    omega ∈ infiniteClusterBoundaryEdgeEvent e ↔
      e ∉ omega ∧ ∃ x ∈ e.1.toFinset, hasInfiniteOpenClusterFrom d omega x := by
  classical
  constructor
  · rintro ⟨hcontinuation, hcylinder⟩
    have heClosed : e ∉ omega := by
      intro heOpen
      have : e ∈ (∅ : Finset (CubicEdge d)) :=
        (mem_finiteCylinder.mp hcylinder e (by simp)).mp heOpen
      simp at this
    have hsplice : spliceOn {e} ∅ omega = omega :=
      spliceOn_eq_self_of_mem_finiteCylinder (by simp) hcylinder
    obtain ⟨x, hxe, hxInf⟩ :=
      mem_edgeInfiniteContinuationEvent_iff.mp hcontinuation
    exact ⟨heClosed, x, hxe, by simpa [hsplice] using hxInf⟩
  · rintro ⟨heClosed, x, hxe, hxInf⟩
    have hcylinder : omega ∈ finiteCylinder {e} ∅ := by
      intro f hf
      simp only [Finset.mem_singleton] at hf
      subst f
      simp [heClosed]
    have hsplice : spliceOn {e} ∅ omega = omega :=
      spliceOn_eq_self_of_mem_finiteCylinder (by simp) hcylinder
    refine ⟨mem_edgeInfiniteContinuationEvent_iff.mpr ⟨x, hxe, ?_⟩, hcylinder⟩
    simpa [hsplice] using hxInf

/-- The one-edge interior event has the open-edge Bernoulli factor `p`. -/
theorem infiniteClusterInteriorEdgeEvent_probability {d : ℕ}
    (p : I) (e : CubicEdge d) :
    (bernoulliBondMeasure d p).real (infiniteClusterInteriorEdgeEvent e) =
      (bernoulliBondMeasure d p).real (edgeInfiniteContinuationEvent e) * (p : ℝ) := by
  classical
  change setBer((Set.univ : Set (CubicEdge d)), p).real
      (edgeInfiniteContinuationEvent e ∩ finiteCylinder {e} {e}) =
    setBer((Set.univ : Set (CubicEdge d)), p).real
      (edgeInfiniteContinuationEvent e) * (p : ℝ)
  rw [setBernoulli_real_inter_finiteCylinder p (by simp)
    (measurable_edgeInfiniteContinuationEvent e),
    preimage_spliceOn_edgeInfiniteContinuationEvent e (by simp)]
  simp [finiteBernoulliWeight]

/-- The one-edge boundary event has the closed-edge Bernoulli factor `1 - p`. -/
theorem infiniteClusterBoundaryEdgeEvent_probability {d : ℕ}
    (p : I) (e : CubicEdge d) :
    (bernoulliBondMeasure d p).real (infiniteClusterBoundaryEdgeEvent e) =
      (bernoulliBondMeasure d p).real (edgeInfiniteContinuationEvent e) * (1 - (p : ℝ)) := by
  classical
  change setBer((Set.univ : Set (CubicEdge d)), p).real
      (edgeInfiniteContinuationEvent e ∩ finiteCylinder {e} ∅) =
    setBer((Set.univ : Set (CubicEdge d)), p).real
      (edgeInfiniteContinuationEvent e) * (1 - (p : ℝ))
  rw [setBernoulli_real_inter_finiteCylinder p (by simp)
    (measurable_edgeInfiniteContinuationEvent e),
    preimage_spliceOn_edgeInfiniteContinuationEvent e (by simp)]
  simp [finiteBernoulliWeight]

/-- Exact, endpoint-safe edgewise balance behind Grimmett's equation (8.101).  The
cross-multiplied form avoids dividing by `p` or `1 - p`. -/
theorem one_sub_p_mul_infiniteClusterInteriorEdgeEvent_probability_eq
    {d : ℕ} (p : I) (e : CubicEdge d) :
    (1 - (p : ℝ)) *
        (bernoulliBondMeasure d p).real (infiniteClusterInteriorEdgeEvent e) =
      (p : ℝ) *
        (bernoulliBondMeasure d p).real (infiniteClusterBoundaryEdgeEvent e) := by
  rw [infiniteClusterInteriorEdgeEvent_probability,
    infiniteClusterBoundaryEdgeEvent_probability]
  ring

/-! ### Finite-box counts and the conditional spatial-limit assembly -/

/-- Number of open internal edges of the infinite cluster whose two endpoints lie in the
coordinate box of radius `n`. -/
noncomputable def infiniteClusterInteriorEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((cubicBoxEdges d cubicOrigin n).filter fun e ↦
    omega ∈ infiniteClusterInteriorEdgeEvent e).card

/-- Number of closed boundary edges touching the infinite cluster whose two endpoints lie in
the coordinate box of radius `n`.  This is Grimmett's finite-box version of `|∂I|`. -/
noncomputable def infiniteClusterBoundaryEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((cubicBoxEdges d cubicOrigin n).filter fun e ↦
    omega ∈ infiniteClusterBoundaryEdgeEvent e).card

/-- Box-volume-normalized density of infinite-cluster interior edges. -/
noncomputable def infiniteClusterInteriorEdgeDensity (d n : ℕ)
    (omega : EdgeConfiguration d) : ℝ :=
  (infiniteClusterInteriorEdgeCount d n omega : ℝ) /
    (cubicMetricBox d cubicOrigin n).card

/-- Box-volume-normalized density of infinite-cluster boundary edges. -/
noncomputable def infiniteClusterBoundaryEdgeDensity (d n : ℕ)
    (omega : EdgeConfiguration d) : ℝ :=
  (infiniteClusterBoundaryEdgeCount d n omega : ℝ) /
    (cubicMetricBox d cubicOrigin n).card

/-- Source-facing finite-box ratio in Theorem 8.99.  Division is totalized, but the limiting
denominator is proved positive in the supercritical, positive-density regime. -/
noncomputable def infiniteClusterBoundaryInteriorEdgeRatio (d n : ℕ)
    (omega : EdgeConfiguration d) : ℝ :=
  (infiniteClusterBoundaryEdgeCount d n omega : ℝ) /
    infiniteClusterInteriorEdgeCount d n omega

/-- Infinite-volume intensity of unoriented infinite-cluster interior edges.  Each unoriented
cubic edge is represented once, by its positively oriented endpoint and coordinate direction. -/
noncomputable def infiniteClusterInteriorEdgeIntensity (d : ℕ) (p : I) : ℝ :=
  ∑ i : Fin d,
    (bernoulliBondMeasure d p).real
      (infiniteClusterInteriorEdgeEvent
        (cubicStepEdge cubicOrigin (i, true)))

/-- Infinite-volume intensity of unoriented boundary edges touching the infinite cluster. -/
noncomputable def infiniteClusterBoundaryEdgeIntensity (d : ℕ) (p : I) : ℝ :=
  ∑ i : Fin d,
    (bernoulliBondMeasure d p).real
      (infiniteClusterBoundaryEdgeEvent
        (cubicStepEdge cubicOrigin (i, true)))

/-- Summing the one-edge identity over the `d` positive coordinate directions gives the exact
intensity balance used after the pointwise ergodic theorem in Grimmett's proof of Theorem 8.99. -/
theorem one_sub_p_mul_infiniteClusterInteriorEdgeIntensity_eq
    (d : ℕ) (p : I) :
    (1 - (p : ℝ)) * infiniteClusterInteriorEdgeIntensity d p =
      (p : ℝ) * infiniteClusterBoundaryEdgeIntensity d p := by
  simp only [infiniteClusterInteriorEdgeIntensity,
    infiniteClusterBoundaryEdgeIntensity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact one_sub_p_mul_infiniteClusterInteriorEdgeEvent_probability_eq p
    (cubicStepEdge cubicOrigin (i, true))

/-- The interior-edge intensity is positive whenever `p > 0`, the origin percolates with
positive probability, and the lattice has at least one coordinate direction. -/
theorem infiniteClusterInteriorEdgeIntensity_pos {d : ℕ} (hd : 1 ≤ d)
    (p : I) (hp : 0 < (p : ℝ)) (htheta : 0 < theta d p) :
    0 < infiniteClusterInteriorEdgeIntensity d p := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let e : CubicEdge d := cubicStepEdge cubicOrigin (i, true)
  let A : Set (EdgeConfiguration d) := openEdgeSetEvent d {e}
  let B : Set (EdgeConfiguration d) :=
    {omega | hasInfiniteOpenClusterFrom d omega cubicOrigin}
  have hAinc : IsIncreasingEvent A := by
    intro omega eta homegaeta homega f hf
    exact homegaeta (homega hf)
  have hABsubset : A ∩ B ⊆ infiniteClusterInteriorEdgeEvent e := by
    rintro omega ⟨hopen, hinfinite⟩
    rw [mem_infiniteClusterInteriorEdgeEvent_iff]
    refine ⟨hopen (by simp), cubicOrigin, ?_, hinfinite⟩
    simp [e, cubicStepEdge]
  have hfkg := bernoulliBondMeasure_real_fkg p hAinc
    (isIncreasingEvent_hasInfiniteOpenClusterFrom d cubicOrigin)
    (measurableSet_openEdgeSetEvent d {e})
    (measurableSet_hasInfiniteOpenClusterFrom d cubicOrigin)
  have hterm :
      0 < (bernoulliBondMeasure d p).real
        (infiniteClusterInteriorEdgeEvent e) := by
    apply lt_of_lt_of_le (mul_pos hp htheta)
    calc
      (p : ℝ) * theta d p =
          (bernoulliBondMeasure d p).real A *
            (bernoulliBondMeasure d p).real B := by
        simp [A, B, bernoulliBondMeasure_real_openEdgeSetEvent, theta]
      _ ≤ (bernoulliBondMeasure d p).real (A ∩ B) := hfkg
      _ ≤ (bernoulliBondMeasure d p).real
          (infiniteClusterInteriorEdgeEvent e) :=
        measureReal_mono hABsubset
  apply Finset.sum_pos'
  · intro j _hj
    exact measureReal_nonneg
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [infiniteClusterInteriorEdgeIntensity, e] using hterm

/-- The exact spatial-density input for the almost-sure part of Grimmett's Theorem 8.99:
the two stationary local edge fields obey their pointwise box-average limits.  This proposition
is deliberately specialized to the two fields needed by the theorem.  The later module
`InfiniteClusterEdgeStrongLaw` derives it from a positive finite-cluster radius exponent. -/
def InfiniteClusterEdgeDensityLimits (d : ℕ) (p : I) : Prop :=
  ∀ᵐ omega ∂bernoulliBondMeasure d p,
    Tendsto (fun n ↦ infiniteClusterInteriorEdgeDensity d n omega)
        atTop (nhds (infiniteClusterInteriorEdgeIntensity d p)) ∧
      Tendsto (fun n ↦ infiniteClusterBoundaryEdgeDensity d n omega)
        atTop (nhds (infiniteClusterBoundaryEdgeIntensity d p))

/-- Conditional assembly of Grimmett's Theorem 8.99.  Once the specialized pointwise spatial
limits hold, the finite-box boundary/interior edge ratio converges almost surely to
`(1-p)/p`.  `InfiniteClusterEdgeStrongLaw` supplies the density limits by a summable
finite-cylinder approximation whenever the finite-cluster radius exponent is positive. -/
theorem infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_densityLimits
    {d : ℕ} (hd : 1 ≤ d) (p : I) (hp : 0 < (p : ℝ))
    (htheta : 0 < theta d p) (hlimits : InfiniteClusterEdgeDensityLimits d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ infiniteClusterBoundaryInteriorEdgeRatio d n omega)
        atTop (nhds ((1 - (p : ℝ)) / (p : ℝ))) := by
  have hinteriorPos : 0 < infiniteClusterInteriorEdgeIntensity d p :=
    infiniteClusterInteriorEdgeIntensity_pos hd p hp htheta
  have hratio :
      infiniteClusterBoundaryEdgeIntensity d p /
          infiniteClusterInteriorEdgeIntensity d p =
        (1 - (p : ℝ)) / (p : ℝ) := by
    have hbalance := one_sub_p_mul_infiniteClusterInteriorEdgeIntensity_eq d p
    field_simp [hp.ne', hinteriorPos.ne'] at hbalance ⊢
    nlinarith
  filter_upwards [hlimits] with omega homega
  rcases homega with ⟨hinterior, hboundary⟩
  have hdiv := hboundary.div hinterior hinteriorPos.ne'
  rw [hratio] at hdiv
  rw [show (fun n ↦ infiniteClusterBoundaryInteriorEdgeRatio d n omega) =
      (fun n ↦ infiniteClusterBoundaryEdgeDensity d n omega /
        infiniteClusterInteriorEdgeDensity d n omega) by
    funext n
    rw [infiniteClusterBoundaryInteriorEdgeRatio,
      infiniteClusterBoundaryEdgeDensity, infiniteClusterInteriorEdgeDensity]
    symm
    apply div_div_div_cancel_right₀
    rw [cubicMetricBox_card]
    positivity]
  exact hdiv

end Percolation
