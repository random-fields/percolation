import Percolation.Critical.DynamicSourceEdgeState

/-!
# Connectivity carried by the dynamic source edge state

The source recursion stores the open edge set reached so far.  For the block construction its
essential deterministic invariant is not merely monotonicity of this set: every endpoint of an
explored edge remains connected to one fixed anchor in the final-density configuration.  This
file proves the line-graph induction needed to preserve that invariant under one heterogeneous
source update.
-/

namespace Percolation

open scoped unitInterval

/-- Transitivity of unrestricted open connections. -/
theorem connectionEvent_trans_mem
    {d : ℕ} {omega : EdgeConfiguration d} {x y z : Cubic d}
    (hxy : omega ∈ connectionEvent d x y)
    (hyz : omega ∈ connectionEvent d y z) :
    omega ∈ connectionEvent d x z := by
  rcases hxy with ⟨p, hp⟩
  rcases hyz with ⟨q, hq⟩
  exact ⟨p.append q, walkIsOpen_append hp hq⟩

/-- Symmetry of unrestricted open connections. -/
theorem connectionEvent_symm_mem
    {d : ℕ} {omega : EdgeConfiguration d} {x y : Cubic d}
    (hxy : omega ∈ connectionEvent d x y) :
    omega ∈ connectionEvent d y x := by
  rcases hxy with ⟨p, hp⟩
  exact ⟨p.reverse, walkIsOpen_reverse hp⟩

/-- One open cubic edge connects any two of its endpoints (including the equal-endpoint case). -/
theorem mem_connectionEvent_of_mem_open_edge
    {d : ℕ} {omega : EdgeConfiguration d} {e : CubicEdge d} {x y : Cubic d}
    (heOpen : e ∈ omega) (hx : x ∈ (e : Sym2 (Cubic d)))
    (hy : y ∈ (e : Sym2 (Cubic d))) :
    omega ∈ connectionEvent d x y := by
  by_cases hxy : x = y
  · subst y
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
  · have hedge : s(x, y) = (e : Sym2 (Cubic d)) := by
      rw [← e.1.out_eq, Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact e.1.out_eq
      · exact Sym2.eq_swap.trans e.1.out_eq
      · exact (hxy rfl).elim
    have hadj : (cubicGraph d).Adj x y := by
      rw [← (cubicGraph d).mem_edgeSet, hedge]
      exact e.2
    let step : (cubicGraph d).Walk x y :=
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    refine ⟨step, ?_⟩
    intro f hf
    have hfe : (⟨f, step.edges_subset_edgeSet hf⟩ : CubicEdge d) = e := by
      apply Subtype.ext
      have hfxy : f = s(x, y) := by simpa [step] using hf
      exact hfxy.trans hedge
    simpa [hfe] using heOpen

/-- Both endpoints of an explored edge are connected to the distinguished anchor. -/
def EdgeEndpointsConnected {d : ℕ} (omega : EdgeConfiguration d)
    (anchor : Cubic d) (e : CubicEdge d) : Prop :=
  ∀ x ∈ (e : Sym2 (Cubic d)), omega ∈ connectionEvent d anchor x

/-- Anchor connectivity crosses one further open edge in the cubic line graph. -/
theorem EdgeEndpointsConnected.of_lineAdj
    {d : ℕ} {omega : EdgeConfiguration d} {anchor : Cubic d}
    {e f : CubicEdge d} (he : EdgeEndpointsConnected omega anchor e)
    (hfOpen : f ∈ omega) (hef : (cubicEdgeLineGraph d).Adj e f) :
    EdgeEndpointsConnected omega anchor f := by
  obtain ⟨_hef, x, hxe, hxf⟩ := hef
  intro y hyf
  exact connectionEvent_trans_mem (he x hxe)
    (mem_connectionEvent_of_mem_open_edge hfOpen hxf hyf)

/-- Connectivity propagates along a walk in a finite induced cubic line graph, provided every
edge reached by the walk belongs to a supplied open closure. -/
theorem edgeEndpointsConnected_of_inducedLineWalk
    {d : ℕ} {omega : EdgeConfiguration d} {anchor : Cubic d}
    {allowed closure : Finset (CubicEdge d)}
    {u v : {e : CubicEdge d // e ∈ allowed}}
    (q : (FiniteCubicEdgeLineGraph d allowed).Walk u v)
    (hu : u.1 ∈ closure)
    (hclosed : ∀ e ∈ closure, ∀ f ∈ allowed,
      (cubicEdgeLineGraph d).Adj e f → f ∈ closure)
    (hopen : ∀ e ∈ closure, e ∈ omega)
    (hconnected : EdgeEndpointsConnected omega anchor u.1) :
    EdgeEndpointsConnected omega anchor v.1 := by
  induction q with
  | nil => exact hconnected
  | @cons u v w huv tail ih =>
      have huv' : (cubicEdgeLineGraph d).Adj u.1 v.1 :=
        SimpleGraph.induce_adj.mp huv
      have hv : v.1 ∈ closure := hclosed u.1 hu v.1 v.2 huv'
      exact ih hv (hconnected.of_lineAdj (hopen v.1 hv) huv')

/-- Every edge retained by one source update is open at a final density which dominates the
background density and the literal incremented threshold family. -/
theorem SourceFiniteEdgeRevealState.next_explored_subset_thresholdConfiguration
    {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p pFinal : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (holdOpen : (S.explored : Set (CubicEdge d)) ⊆ thresholdConfiguration pFinal X)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ e, (incremented e : ℝ) ≤ (pFinal : ℝ)) :
    ((S.next stageRegion p incremented X).explored : Set (CubicEdge d)) ⊆
      thresholdConfiguration pFinal X := by
  intro e heNext
  change e ∈ S.nextExplored stageRegion p incremented X at heNext
  change X e < (pFinal : ℝ)
  by_cases heOld : e ∈ S.explored
  · exact holdOpen heOld
  by_cases heBoundary : e ∈ activeCubicEdgeBoundary S.explored stageRegion
  · exact (label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStepFamily
      S.explored (activeCubicEdgeBoundary S.explored stageRegion)
      (sourceStageExterior S.explored stageRegion) p incremented X
      (activeCubicEdgeBoundary_disjoint_explored S.explored stageRegion)
      (activeCubicEdgeBoundary_disjoint_sourceStageExterior S.explored stageRegion)
      heBoundary heNext).trans_le (hincrementedFinal e)
  · exact (label_lt_density_of_mem_exploredEdgeStepFamily_not_old_not_boundary
      S.explored (activeCubicEdgeBoundary S.explored stageRegion)
      (sourceStageExterior S.explored stageRegion) p incremented X
      heNext heOld heBoundary).trans_le hpFinal

/-- Every endpoint of the source state's explored edge set is connected to one fixed anchor. -/
def SourceFiniteEdgeRevealState.EndpointsConnected
    {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (omega : EdgeConfiguration d) (anchor : Cubic d) : Prop :=
  ∀ e ∈ S.explored, EdgeEndpointsConnected omega anchor e

/-- Combined pathwise invariant used by the block runtime: all retained explored edges are open
at the final density, and all of their endpoints are connected to the distinguished anchor. -/
def SourceFiniteEdgeRevealState.RootedOpen
    {d : ℕ} (S : SourceFiniteEdgeRevealState d)
    (omega : EdgeConfiguration d) (anchor : Cubic d) : Prop :=
  (S.explored : Set (CubicEdge d)) ⊆ omega ∧ S.EndpointsConnected omega anchor

/-- One heterogeneous source update preserves anchor connectivity.  New edges are reached in
the line graph from an open old-boundary edge, which shares a vertex with an old explored edge;
the finite reachable closure then propagates the connection to every new endpoint. -/
theorem SourceFiniteEdgeRevealState.endpointsConnected_next
    {d : ℕ} {anchor : Cubic d} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p pFinal : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (holdOpen : (S.explored : Set (CubicEdge d)) ⊆ thresholdConfiguration pFinal X)
    (hconnected : S.EndpointsConnected (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ e, (incremented e : ℝ) ≤ (pFinal : ℝ)) :
    (S.next stageRegion p incremented X).EndpointsConnected
      (thresholdConfiguration pFinal X) anchor := by
  let B := activeCubicEdgeBoundary S.explored stageRegion
  let A := finiteEdgesBelowFamily B incremented X ∪
    finiteEdgesBelow (sourceStageExterior S.explored stageRegion) p X
  let C := finiteEdgeReachableClosure A (finiteEdgesBelowFamily B incremented X)
  have hnextOpen := S.next_explored_subset_thresholdConfiguration stageRegion p pFinal
    incremented X holdOpen hpFinal hincrementedFinal
  intro e heNext
  change e ∈ S.explored ∪ C at heNext
  rw [Finset.mem_union] at heNext
  rcases heNext with heOld | heClosure
  · exact hconnected e heOld
  · obtain ⟨heAllowed, b, hbSource, hbe⟩ :=
      mem_finiteEdgeReachableClosure_iff.mp heClosure
    have hbB : b.1 ∈ B := (mem_finiteEdgesBelowFamily_iff.mp hbSource).1
    obtain ⟨_hbNotOld, f, hfOld, hfb⟩ :=
      mem_cubicEdgeBoundary_iff.mp (Finset.mem_inter.mp hbB).1
    have hbClosure : b.1 ∈ C :=
      (sources_subset_finiteEdgeReachableClosure
        (allowed := A) (sources := finiteEdgesBelowFamily B incremented X)
        Finset.subset_union_left) hbSource
    have hclosed : ∀ g ∈ C, ∀ h ∈ A,
        (cubicEdgeLineGraph d).Adj g h → h ∈ C := by
      intro g hg h hh hgh
      exact mem_finiteEdgeReachableClosure_of_adj hg hh hgh
    have hbConnected : EdgeEndpointsConnected
        (thresholdConfiguration pFinal X) anchor b.1 :=
      (hconnected f hfOld).of_lineAdj
        (hnextOpen (Finset.mem_union_right _ hbClosure)) hfb
    obtain ⟨q⟩ := hbe
    exact edgeEndpointsConnected_of_inducedLineWalk q hbClosure hclosed
      (fun g hg ↦ hnextOpen (Finset.mem_union_right _ hg)) hbConnected

/-- The combined open-and-root-connected invariant is preserved by one source update whenever
the background and incremented thresholds are bounded by the final density. -/
theorem SourceFiniteEdgeRevealState.rootedOpen_next
    {d : ℕ} {anchor : Cubic d} (S : SourceFiniteEdgeRevealState d)
    (stageRegion : Finset (CubicEdge d)) (p pFinal : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hrooted : S.RootedOpen (thresholdConfiguration pFinal X) anchor)
    (hpFinal : (p : ℝ) ≤ (pFinal : ℝ))
    (hincrementedFinal : ∀ e, (incremented e : ℝ) ≤ (pFinal : ℝ)) :
    (S.next stageRegion p incremented X).RootedOpen
      (thresholdConfiguration pFinal X) anchor := by
  exact ⟨S.next_explored_subset_thresholdConfiguration stageRegion p pFinal incremented X
      hrooted.1 hpFinal hincrementedFinal,
    S.endpointsConnected_next stageRegion p pFinal incremented X hrooted.1 hrooted.2
      hpFinal hincrementedFinal⟩

end Percolation
