import Percolation.Critical.DynamicRevealThresholdUpdate
import Percolation.Critical.RestartGeometry

/-!
# Finite edge exploration for dynamic renormalization

Grimmett's sets `E_k` are edge sets, and `Delta E_k` is their boundary in the line graph of the
cubic lattice.  A vertex-component encoding loses this distinction.  This file supplies the
finite line-graph boundary and reachable closure used to construct the literal explored edge
sets in equations (7.27)--(7.32).
-/

namespace Percolation

open scoped unitInterval

/-- Two distinct cubic bonds are adjacent when they share an endpoint.  Since the cubic graph
is simple, distinct bonds cannot share both endpoints, so this is Grimmett's “exactly one common
endvertex” relation. -/
def cubicEdgeLineGraph (d : ℕ) : SimpleGraph (CubicEdge d) where
  Adj e f := e ≠ f ∧ ∃ x : Cubic d, x ∈ (e.1 : Sym2 (Cubic d)) ∧ x ∈ (f.1 : Sym2 (Cubic d))
  symm := by
    rintro e f ⟨hef, x, hxe, hxf⟩
    exact ⟨Ne.symm hef, x, hxf, hxe⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩

@[simp]
theorem cubicEdgeLineGraph_adj_iff {d : ℕ} {e f : CubicEdge d} :
    (cubicEdgeLineGraph d).Adj e f ↔
      e ≠ f ∧ ∃ x : Cubic d, x ∈ (e.1 : Sym2 (Cubic d)) ∧ x ∈ (f.1 : Sym2 (Cubic d)) :=
  Iff.rfl

/-- Endvertices incident to a finite edge set. -/
noncomputable def cubicEdgeEndpointVertices {d : ℕ}
    (E : Finset (CubicEdge d)) : Finset (Cubic d) := by
  classical
  exact E.biUnion fun e ↦ {e.1.out.1, e.1.out.2}

@[simp]
theorem mem_cubicEdgeEndpointVertices_iff {d : ℕ}
    {E : Finset (CubicEdge d)} {x : Cubic d} :
    x ∈ cubicEdgeEndpointVertices E ↔
      ∃ e ∈ E, x ∈ (e.1 : Sym2 (Cubic d)) := by
  classical
  rw [cubicEdgeEndpointVertices, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    refine ⟨e, he, ?_⟩
    rw [← e.1.out_eq, Sym2.mem_iff]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  · rintro ⟨e, he, hx⟩
    refine ⟨e, he, ?_⟩
    rw [← e.1.out_eq, Sym2.mem_iff] at hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

/-- In positive dimension, every vertex of a nontrivial coordinate box is incident to an
internal box edge.  This lets an explored seed edge set recover the whole seed vertex region. -/
theorem cubicMetricBox_subset_cubicEdgeEndpointVertices_cubicBoxEdges
    {d m : ℕ} [NeZero d] (hm : 1 ≤ m) :
    cubicMetricBox d cubicOrigin m ⊆
      cubicEdgeEndpointVertices (cubicBoxEdges d cubicOrigin m) := by
  classical
  intro x hx
  let i : Fin d := 0
  by_cases hpos : x i < cubicOrigin i + (m : ℤ)
  · let a : CubicDirection d := (i, true)
    have hstep : cubicStepFrom x a ∈ cubicMetricBox d cubicOrigin m := by
      rw [mem_cubicMetricBox] at hx ⊢
      intro j
      by_cases hji : j = i
      · subst j
        have hi := hx i
        simp [a, cubicStepFrom, cubicDirectionIncrement]
        omega
      · simpa [a, cubicStepFrom, cubicDirectionIncrement, hji] using hx j
    apply mem_cubicEdgeEndpointVertices_iff.mpr
    refine ⟨cubicStepEdge x a, cubicStepEdge_mem_cubicBoxEdges hx hstep, ?_⟩
    simp [cubicStepEdge]
  · let a : CubicDirection d := (i, false)
    have hstep : cubicStepFrom x a ∈ cubicMetricBox d cubicOrigin m := by
      rw [mem_cubicMetricBox] at hx ⊢
      intro j
      by_cases hji : j = i
      · subst j
        have hi := hx i
        simp [a, cubicStepFrom, cubicDirectionIncrement]
        simp [cubicOrigin] at hpos hi ⊢
        omega
      · simpa [a, cubicStepFrom, cubicDirectionIncrement, hji] using hx j
    apply mem_cubicEdgeEndpointVertices_iff.mpr
    refine ⟨cubicStepEdge x a, cubicStepEdge_mem_cubicBoxEdges hx hstep, ?_⟩
    simp [cubicStepEdge]

/-- Grimmett's literal finite edge boundary `ΔE`: every cubic edge outside `E` sharing an
endvertex with an edge of `E`.  This boundary is global; a restart's finite region `E_Z` is a
separate restriction on which boundary and exterior coordinates are inspected. -/
noncomputable def cubicEdgeBoundary {d : ℕ}
    (E : Finset (CubicEdge d)) : Finset (CubicEdge d) :=
  cubicIncidentEdges d (cubicEdgeEndpointVertices E) \ E

@[simp]
theorem mem_cubicEdgeBoundary_iff {d : ℕ}
    {E : Finset (CubicEdge d)} {f : CubicEdge d} :
    f ∈ cubicEdgeBoundary E ↔
      f ∉ E ∧ ∃ e ∈ E, (cubicEdgeLineGraph d).Adj e f := by
  classical
  rw [cubicEdgeBoundary, Finset.mem_sdiff,
    mem_cubicIncidentEdges_iff_exists_endpoint]
  constructor
  · rintro ⟨⟨x, hxEndpoints, hxf⟩, hfNot⟩
    obtain ⟨e, heE, hxe⟩ := mem_cubicEdgeEndpointVertices_iff.mp hxEndpoints
    exact ⟨hfNot, e, heE, hfNot ∘ fun h ↦ h ▸ heE, x, hxe, hxf⟩
  · rintro ⟨hfNot, e, heE, _hef, x, hxe, hxf⟩
    exact ⟨⟨x, mem_cubicEdgeEndpointVertices_iff.mpr ⟨e, heE, hxe⟩, hxf⟩,
      hfNot⟩

theorem disjoint_cubicEdgeBoundary_left {d : ℕ}
    (E : Finset (CubicEdge d)) : Disjoint (cubicEdgeBoundary E) E := by
  rw [Finset.disjoint_left]
  intro e heBoundary heE
  exact (mem_cubicEdgeBoundary_iff.mp heBoundary).1 heE

theorem disjoint_cubicEdgeBoundary_right {d : ℕ}
    (E : Finset (CubicEdge d)) : Disjoint E (cubicEdgeBoundary E) :=
  (disjoint_cubicEdgeBoundary_left E).symm

/-- `Delta E`, restricted to an advertised finite ambient edge set. -/
noncomputable def cubicEdgeBoundaryWithin {d : ℕ}
    (E ambient : Finset (CubicEdge d)) : Finset (CubicEdge d) := by
  classical
  exact ambient.filter fun f ↦
    f ∉ E ∧ ∃ e ∈ E, (cubicEdgeLineGraph d).Adj e f

@[simp]
theorem mem_cubicEdgeBoundaryWithin_iff {d : ℕ}
    {E ambient : Finset (CubicEdge d)} {f : CubicEdge d} :
    f ∈ cubicEdgeBoundaryWithin E ambient ↔
      f ∈ ambient ∧ f ∉ E ∧ ∃ e ∈ E, (cubicEdgeLineGraph d).Adj e f := by
  classical
  simp [cubicEdgeBoundaryWithin]

/-- Restricting the global boundary to a finite ambient set recovers the older helper. -/
theorem cubicEdgeBoundaryWithin_eq_inter {d : ℕ}
    (E ambient : Finset (CubicEdge d)) :
    cubicEdgeBoundaryWithin E ambient = ambient ∩ cubicEdgeBoundary E := by
  classical
  ext f
  simp only [mem_cubicEdgeBoundaryWithin_iff, Finset.mem_inter,
    mem_cubicEdgeBoundary_iff]

theorem cubicEdgeBoundaryWithin_subset_ambient {d : ℕ}
    (E ambient : Finset (CubicEdge d)) :
    cubicEdgeBoundaryWithin E ambient ⊆ ambient := by
  intro f hf
  exact (mem_cubicEdgeBoundaryWithin_iff.mp hf).1

theorem disjoint_cubicEdgeBoundaryWithin_left {d : ℕ}
    (E ambient : Finset (CubicEdge d)) :
    Disjoint (cubicEdgeBoundaryWithin E ambient) E := by
  rw [Finset.disjoint_left]
  intro f hfBoundary hfE
  exact (mem_cubicEdgeBoundaryWithin_iff.mp hfBoundary).2.1 hfE

theorem disjoint_cubicEdgeBoundaryWithin_right {d : ℕ}
    (E ambient : Finset (CubicEdge d)) :
    Disjoint E (cubicEdgeBoundaryWithin E ambient) :=
  (disjoint_cubicEdgeBoundaryWithin_left E ambient).symm

/-- Enlarging a finite stage region does not change the exposed line boundary when every
newly admitted edge is line-nonadjacent to the explored set. -/
theorem cubicEdgeBoundaryWithin_eq_of_subset_of_no_new_adj {d : ℕ}
    (E oldAmbient newAmbient : Finset (CubicEdge d))
    (hsubset : oldAmbient ⊆ newAmbient)
    (hnew : ∀ e ∈ newAmbient, e ∉ oldAmbient →
      ∀ f ∈ E, ¬ (cubicEdgeLineGraph d).Adj f e) :
    cubicEdgeBoundaryWithin E newAmbient =
      cubicEdgeBoundaryWithin E oldAmbient := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heNew, heNotE, f, hfE, hfe⟩ :=
      mem_cubicEdgeBoundaryWithin_iff.mp he
    have heOld : e ∈ oldAmbient := by
      by_contra heNotOld
      exact hnew e heNew heNotOld f hfE hfe
    exact mem_cubicEdgeBoundaryWithin_iff.mpr
      ⟨heOld, heNotE, f, hfE, hfe⟩
  · intro he
    obtain ⟨heOld, heNotE, f, hfE, hfe⟩ :=
      mem_cubicEdgeBoundaryWithin_iff.mp he
    exact mem_cubicEdgeBoundaryWithin_iff.mpr
      ⟨hsubset heOld, heNotE, f, hfE, hfe⟩

/-- Finite edge-induced graph on an ambient support. -/
abbrev FiniteCubicEdgeLineGraph (d : ℕ) (ambient : Finset (CubicEdge d)) :=
  (cubicEdgeLineGraph d).induce (ambient : Set (CubicEdge d))

/-- Edges in `allowed` connected in the induced line graph to at least one edge in `sources`.
The definition is an actual finite reachable closure, not a cardinality surrogate. -/
noncomputable def finiteEdgeReachableClosure {d : ℕ}
    (allowed sources : Finset (CubicEdge d)) : Finset (CubicEdge d) := by
  classical
  exact (allowed.attach.filter fun e ↦
    ∃ s : {f : CubicEdge d // f ∈ allowed},
      s.1 ∈ sources ∧ (FiniteCubicEdgeLineGraph d allowed).Reachable s e).map
        (Function.Embedding.subtype _)

@[simp]
theorem mem_finiteEdgeReachableClosure_iff {d : ℕ}
    {allowed sources : Finset (CubicEdge d)} {e : CubicEdge d} :
    e ∈ finiteEdgeReachableClosure allowed sources ↔
      ∃ he : e ∈ allowed,
        ∃ s : {f : CubicEdge d // f ∈ allowed},
          s.1 ∈ sources ∧
            (FiniteCubicEdgeLineGraph d allowed).Reachable s ⟨e, he⟩ := by
  classical
  simp [finiteEdgeReachableClosure]

theorem finiteEdgeReachableClosure_subset_allowed {d : ℕ}
    (allowed sources : Finset (CubicEdge d)) :
    finiteEdgeReachableClosure allowed sources ⊆ allowed := by
  intro e he
  exact (mem_finiteEdgeReachableClosure_iff.mp he).choose

/-- Every advertised source edge belongs to its reachable closure when it is allowed. -/
theorem inter_subset_finiteEdgeReachableClosure {d : ℕ}
    (allowed sources : Finset (CubicEdge d)) :
    allowed ∩ sources ⊆ finiteEdgeReachableClosure allowed sources := by
  intro e he
  have heAllowed := (Finset.mem_inter.mp he).1
  have heSource := (Finset.mem_inter.mp he).2
  rw [mem_finiteEdgeReachableClosure_iff]
  exact ⟨heAllowed, ⟨e, heAllowed⟩, heSource, ⟨SimpleGraph.Walk.nil⟩⟩

theorem sources_subset_finiteEdgeReachableClosure {d : ℕ}
    {allowed sources : Finset (CubicEdge d)} (hsource : sources ⊆ allowed) :
    sources ⊆ finiteEdgeReachableClosure allowed sources := by
  intro e he
  exact inter_subset_finiteEdgeReachableClosure allowed sources
    (Finset.mem_inter.mpr ⟨hsource he, he⟩)

/-- Source edges are monotone: enlarging the source set can only enlarge the finite closure. -/
theorem finiteEdgeReachableClosure_mono_sources {d : ℕ}
    {allowed sources targets : Finset (CubicEdge d)}
    (hst : sources ⊆ targets) :
    finiteEdgeReachableClosure allowed sources ⊆
      finiteEdgeReachableClosure allowed targets := by
  intro e he
  obtain ⟨heAllowed, s, hsSource, hse⟩ :=
    mem_finiteEdgeReachableClosure_iff.mp he
  rw [mem_finiteEdgeReachableClosure_iff]
  exact ⟨heAllowed, s, hst hsSource, hse⟩

/-- Enlarging both the allowed edge set and the source set can only enlarge the finite
reachable closure. -/
theorem finiteEdgeReachableClosure_mono {d : ℕ}
    {allowed sources allowed' sources' : Finset (CubicEdge d)}
    (hallowed : allowed ⊆ allowed') (hsources : sources ⊆ sources') :
    finiteEdgeReachableClosure allowed sources ⊆
      finiteEdgeReachableClosure allowed' sources' := by
  intro e he
  obtain ⟨heAllowed, s, hsSource, hse⟩ :=
    mem_finiteEdgeReachableClosure_iff.mp he
  have heAllowed' := hallowed heAllowed
  let f : FiniteCubicEdgeLineGraph d allowed →g
      FiniteCubicEdgeLineGraph d allowed' :=
    { toFun := fun x : {e // e ∈ allowed} ↦
        (⟨x.1, hallowed x.2⟩ : {e // e ∈ allowed'})
      map_rel' := fun hxy ↦ hxy }
  rw [mem_finiteEdgeReachableClosure_iff]
  refine ⟨heAllowed', ⟨s.1, hallowed s.2⟩, hsources hsSource, ?_⟩
  exact hse.map f

/-- A finite set containing every allowed source and closed under allowed line-graph
neighbors contains the complete reachable closure. -/
theorem finiteEdgeReachableClosure_subset_of_closed {d : ℕ}
    {allowed sources target : Finset (CubicEdge d)}
    (hsource : allowed ∩ sources ⊆ target)
    (hclosed : ∀ e ∈ target, ∀ f ∈ allowed,
      (cubicEdgeLineGraph d).Adj e f → f ∈ target) :
    finiteEdgeReachableClosure allowed sources ⊆ target := by
  intro e he
  obtain ⟨heAllowed, s, hsSource, hse⟩ :=
    mem_finiteEdgeReachableClosure_iff.mp he
  have hsTarget : s.1 ∈ target :=
    hsource (Finset.mem_inter.mpr ⟨s.2, hsSource⟩)
  obtain ⟨w⟩ := hse
  have walk_end_mem : ∀ {u v : {f : CubicEdge d // f ∈ allowed}}
      (q : (FiniteCubicEdgeLineGraph d allowed).Walk u v),
      u.1 ∈ target → v.1 ∈ target := by
    intro u v q
    induction q with
    | nil => exact fun hu ↦ hu
    | @cons u v z huv q ih =>
        intro hu
        apply ih
        exact hclosed u.1 hu v.1 v.2 (SimpleGraph.induce_adj.mp huv)
  exact walk_end_mem w hsTarget

/-- A reachable closure is closed under adjoining one allowed line-graph neighbor. -/
theorem mem_finiteEdgeReachableClosure_of_adj
    {d : ℕ} {allowed sources : Finset (CubicEdge d)} {e f : CubicEdge d}
    (he : e ∈ finiteEdgeReachableClosure allowed sources)
    (hf : f ∈ allowed) (hef : (cubicEdgeLineGraph d).Adj e f) :
    f ∈ finiteEdgeReachableClosure allowed sources := by
  obtain ⟨heAllowed, s, hsSource, hse⟩ :=
    mem_finiteEdgeReachableClosure_iff.mp he
  rw [mem_finiteEdgeReachableClosure_iff]
  refine ⟨hf, s, hsSource, hse.trans ?_⟩
  exact ⟨SimpleGraph.Walk.cons (SimpleGraph.induce_adj.mpr hef)
    SimpleGraph.Walk.nil⟩

/-- If one edge of the reachable closure is incident to the start of a cubic walk and every
walk edge is allowed, then the whole walk belongs to the same line-graph closure.  This is the
generic path-transport fact needed when a dynamic restart records only its explored edge set. -/
theorem walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
    {d : ℕ} {allowed sources : Finset (CubicEdge d)}
    {u v : Cubic d} (w : (cubicGraph d).Walk u v) {e : CubicEdge d}
    (he : e ∈ finiteEdgeReachableClosure allowed sources)
    (hue : u ∈ (e.1 : Sym2 (Cubic d)))
    (hw : walkEdgeFinset w ⊆ allowed) :
    walkEdgeFinset w ⊆ finiteEdgeReachableClosure allowed sources := by
  induction w generalizing e with
  | nil => simp [walkEdgeFinset, walkEdgeList]
  | @cons u v z huv w ih =>
      let f : CubicEdge d :=
        ⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huv⟩
      have hfWalk : f ∈ walkEdgeFinset (SimpleGraph.Walk.cons huv w) := by
        rw [mem_walkEdgeFinset_iff]
        simp [f]
      have hfAllowed : f ∈ allowed := hw hfWalk
      have hfClosure : f ∈ finiteEdgeReachableClosure allowed sources := by
        by_cases hfe : f = e
        · simpa [hfe] using he
        · apply mem_finiteEdgeReachableClosure_of_adj he hfAllowed
          rw [cubicEdgeLineGraph_adj_iff]
          refine ⟨Ne.symm hfe, u, hue, ?_⟩
          simp [f]
      have hvf : v ∈ (f.1 : Sym2 (Cubic d)) := by simp [f]
      have hwTail : walkEdgeFinset w ⊆ allowed := by
        intro g hg
        apply hw
        rw [mem_walkEdgeFinset_iff] at hg ⊢
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hg
      have htail := ih hfClosure hvf hwTail
      intro g hg
      rw [mem_walkEdgeFinset_iff] at hg
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hg
      rcases hg with hg | hg
      · have hgf : g = f := by
          apply Subtype.ext
          exact hg
        simpa [hgf] using hfClosure
      · exact htail ((mem_walkEdgeFinset_iff w g).mpr hg)

/-- Once a reachable edge enters a coordinate box through one of its vertices, every allowed
edge internal to that box is in the same line-graph closure.  The proof joins the entry vertex
to an endpoint of the requested edge by a coordinate-monotone cubic walk and then traverses the
requested edge itself. -/
theorem cubicBoxEdges_subset_finiteEdgeReachableClosure_of_incident
    {d m : ℕ} {c x : Cubic d} {allowed sources : Finset (CubicEdge d)}
    {anchor : CubicEdge d}
    (hanchor : anchor ∈ finiteEdgeReachableClosure allowed sources)
    (hxa : x ∈ (anchor.1 : Sym2 (Cubic d)))
    (hx : x ∈ cubicMetricBox d c m)
    (hallowed : cubicBoxEdges d c m ⊆ allowed) :
    cubicBoxEdges d c m ⊆ finiteEdgeReachableClosure allowed sources := by
  classical
  intro f hfBox
  let y : Cubic d := f.1.out.1
  have hy : y ∈ cubicMetricBox d c m :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hfBox
      (Sym2.out_fst_mem f.1)
  obtain ⟨w, hwBetween⟩ := exists_cubicWalk_support_between d x y
  have hwBox : ∀ z ∈ w.support, z ∈ cubicMetricBox d c m := by
    intro z hz
    have hzBetween := hwBetween z hz
    rw [mem_cubicMetricBox] at hx hy ⊢
    intro i
    rcases hzBetween i with hzi | hzi
    · exact ⟨hx i |>.1.trans hzi.1, hzi.2.trans (hy i).2⟩
    · exact ⟨(hy i).1.trans hzi.1, hzi.2.trans (hx i).2⟩
  have hwAllowed : walkEdgeFinset w ⊆ allowed :=
    (walkEdgeFinset_subset_cubicBoxEdges_of_support w hwBox).trans hallowed
  have hwClosure := walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
    w hanchor hxa hwAllowed
  have hab : (cubicGraph d).Adj f.1.out.1 f.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk, f.1.out_eq]
    exact f.2
  let step : (cubicGraph d).Walk f.1.out.1 f.1.out.2 :=
    SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
  let q : (cubicGraph d).Walk x f.1.out.2 := w.append step
  have hqAllowed : walkEdgeFinset q ⊆ allowed := by
    intro g hg
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hwAllowed ((mem_walkEdgeFinset_iff w g).mpr hg)
    · have hgf : g = f := by
        apply Subtype.ext
        have hgs : (g : Sym2 (Cubic d)) = s(f.1.out.1, f.1.out.2) := by
          simpa [step, y] using hg
        exact hgs.trans (by rw [Sym2.mk, f.1.out_eq])
      simpa [hgf] using hallowed hfBox
  have hqClosure := walkEdgeFinset_subset_finiteEdgeReachableClosure_of_incident
    q hanchor hxa hqAllowed
  apply hqClosure
  rw [mem_walkEdgeFinset_iff]
  change (f : Sym2 (Cubic d)) ∈ (w.append step).edges
  rw [SimpleGraph.Walk.edges_append]
  apply List.mem_append_right
  simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.mem_singleton]
  symm
  rw [Sym2.mk, f.1.out_eq]

/-- One finite exploration step: retain the old explored edges and adjoin every allowed edge
line-graph connected to a newly opened boundary exit. -/
noncomputable def nextExploredEdgeSet {d : ℕ}
    (oldExplored allowed openBoundary : Finset (CubicEdge d)) :
    Finset (CubicEdge d) :=
  oldExplored ∪ finiteEdgeReachableClosure allowed openBoundary

theorem oldExplored_subset_nextExploredEdgeSet {d : ℕ}
    (oldExplored allowed openBoundary : Finset (CubicEdge d)) :
    oldExplored ⊆ nextExploredEdgeSet oldExplored allowed openBoundary :=
  Finset.subset_union_left

theorem finiteEdgeReachableClosure_subset_nextExploredEdgeSet {d : ℕ}
    (oldExplored allowed openBoundary : Finset (CubicEdge d)) :
    finiteEdgeReachableClosure allowed openBoundary ⊆
      nextExploredEdgeSet oldExplored allowed openBoundary :=
  Finset.subset_union_right

theorem disjoint_boundary_nextExploredEdgeSet {d : ℕ}
    (oldExplored allowed openBoundary ambient : Finset (CubicEdge d)) :
    Disjoint
      (cubicEdgeBoundaryWithin
        (nextExploredEdgeSet oldExplored allowed openBoundary) ambient)
      (nextExploredEdgeSet oldExplored allowed openBoundary) :=
  disjoint_cubicEdgeBoundaryWithin_left _ _

/-! ### Label-driven one-step exploration -/

/-- Edges in a finite support whose common-uniform labels lie below a certified threshold. -/
noncomputable def finiteEdgesBelow {d : ℕ}
    (E : Finset (CubicEdge d)) (q : I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) := by
  classical
  exact E.filter fun e ↦ X e < (q : ℝ)

@[simp]
theorem mem_finiteEdgesBelow_iff {d : ℕ}
    {E : Finset (CubicEdge d)} {q : I} {X : CubicEdge d → ℝ} {e : CubicEdge d} :
    e ∈ finiteEdgesBelow E q X ↔ e ∈ E ∧ X e < (q : ℝ) := by
  classical
  simp [finiteEdgesBelow]

theorem finiteEdgesBelow_subset {d : ℕ}
    (E : Finset (CubicEdge d)) (q : I) (X : CubicEdge d → ℝ) :
    finiteEdgesBelow E q X ⊆ E := by
  intro e he
  exact (mem_finiteEdgesBelow_iff.mp he).1

/-- Literal finite edge-set update: an exit edge is usable at the incremented boundary
threshold, while every subsequent exterior edge is usable at the background density. -/
noncomputable def exploredEdgeStep {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ) : Finset (CubicEdge d) :=
  let openBoundary := finiteEdgesBelow oldBoundary incremented X
  let openExterior := finiteEdgesBelow exterior p X
  nextExploredEdgeSet oldExplored (openBoundary ∪ openExterior) openBoundary

theorem oldExplored_subset_exploredEdgeStep {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ) :
    oldExplored ⊆ exploredEdgeStep oldExplored oldBoundary exterior p incremented X :=
  oldExplored_subset_nextExploredEdgeSet _ _ _

theorem openBoundary_subset_exploredEdgeStep {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ) :
    finiteEdgesBelow oldBoundary incremented X ⊆
      exploredEdgeStep oldExplored oldBoundary exterior p incremented X := by
  let B := finiteEdgesBelow oldBoundary incremented X
  let A := B ∪ finiteEdgesBelow exterior p X
  change B ⊆ nextExploredEdgeSet oldExplored A B
  exact (sources_subset_finiteEdgeReachableClosure
      (allowed := A) (sources := B) Finset.subset_union_left).trans
    (finiteEdgeReachableClosure_subset_nextExploredEdgeSet oldExplored A B)

theorem exploredEdgeStep_subset {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ) :
    exploredEdgeStep oldExplored oldBoundary exterior p incremented X ⊆
      oldExplored ∪ oldBoundary ∪ exterior := by
  intro e he
  rw [exploredEdgeStep, nextExploredEdgeSet, Finset.mem_union] at he
  rcases he with heOld | heClosure
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ heOld)
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heBoundary | heExterior
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (finiteEdgesBelow_subset _ _ _ heBoundary))
    · exact Finset.mem_union_right _ (finiteEdgesBelow_subset _ _ _ heExterior)

/-- If an old boundary edge is absorbed by the exploration, its label is below the
incremented boundary threshold.  Disjointness from the old explored set and the exterior
support rules out the other two branches of the update. -/
theorem label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStep
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hold : Disjoint oldBoundary oldExplored)
    (hexterior : Disjoint oldBoundary exterior)
    {e : CubicEdge d} (heBoundary : e ∈ oldBoundary)
    (heNext : e ∈ exploredEdgeStep oldExplored oldBoundary exterior p incremented X) :
    X e < (incremented : ℝ) := by
  have heNotOld : e ∉ oldExplored := fun heOld ↦
    Finset.disjoint_left.mp hold heBoundary heOld
  rw [exploredEdgeStep, nextExploredEdgeSet, Finset.mem_union] at heNext
  rcases heNext with heOld | heClosure
  · exact (heNotOld heOld).elim
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heOpenBoundary | heOpenExterior
    · exact (mem_finiteEdgesBelow_iff.mp heOpenBoundary).2
    · exact (Finset.disjoint_left.mp hexterior heBoundary
        (mem_finiteEdgesBelow_iff.mp heOpenExterior).1).elim

/-- A boundary edge not absorbed by the exploration is certified closed at the incremented
threshold.  This is the first nontrivial closed clause of (7.31). -/
theorem incremented_le_label_of_mem_oldBoundary_not_mem_exploredEdgeStep
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ)
    {e : CubicEdge d} (heBoundary : e ∈ oldBoundary)
    (heNotNext : e ∉ exploredEdgeStep oldExplored oldBoundary exterior p incremented X) :
    (incremented : ℝ) ≤ X e := by
  apply le_of_not_gt
  intro heOpen
  apply heNotNext
  exact openBoundary_subset_exploredEdgeStep oldExplored oldBoundary exterior p incremented X
    (mem_finiteEdgesBelow_iff.mpr ⟨heBoundary, heOpen⟩)

/-- Every newly explored edge which is neither old nor an old-boundary exit is open at the
background density. -/
theorem label_lt_density_of_mem_exploredEdgeStep_not_old_not_boundary
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ)
    {e : CubicEdge d}
    (heNext : e ∈ exploredEdgeStep oldExplored oldBoundary exterior p incremented X)
    (heNotOld : e ∉ oldExplored) (heNotBoundary : e ∉ oldBoundary) :
    X e < (p : ℝ) := by
  rw [exploredEdgeStep, nextExploredEdgeSet, Finset.mem_union] at heNext
  rcases heNext with heOld | heClosure
  · exact (heNotOld heOld).elim
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heOpenBoundary | heOpenExterior
    · exact (heNotBoundary (mem_finiteEdgesBelow_iff.mp heOpenBoundary).1).elim
    · exact (mem_finiteEdgesBelow_iff.mp heOpenExterior).2

/-- Every genuinely new boundary edge is closed at the background density.  The hypothesis
`hlineBoundary` says that the advertised old boundary contains the literal line-graph boundary
of the old explored set; `hexterior` identifies the as-yet untouched coordinates. -/
theorem density_le_label_of_mem_newBoundary_not_oldBoundary
    {d : ℕ}
    (oldExplored oldBoundary ambient exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ)
    (hlineBoundary : cubicEdgeBoundaryWithin oldExplored ambient ⊆ oldBoundary)
    (hexterior : exterior = ambient \ (oldExplored ∪ oldBoundary))
    {e : CubicEdge d}
    (heNew : e ∈ cubicEdgeBoundaryWithin
      (exploredEdgeStep oldExplored oldBoundary exterior p incremented X) ambient)
    (heNotOldBoundary : e ∉ oldBoundary) :
    (p : ℝ) ≤ X e := by
  apply le_of_not_gt
  intro heOpen
  obtain ⟨heAmbient, heNotNext, f, hfNext, hfe⟩ :=
    mem_cubicEdgeBoundaryWithin_iff.mp heNew
  have heNotOld : e ∉ oldExplored := fun heOld ↦
    heNotNext (oldExplored_subset_exploredEdgeStep
      oldExplored oldBoundary exterior p incremented X heOld)
  have heExterior : e ∈ exterior := by
    rw [hexterior, Finset.mem_sdiff, Finset.mem_union]
    exact ⟨heAmbient, fun h ↦ h.elim heNotOld heNotOldBoundary⟩
  have heAllowed : e ∈
      finiteEdgesBelow oldBoundary incremented X ∪ finiteEdgesBelow exterior p X :=
    Finset.mem_union_right _ (mem_finiteEdgesBelow_iff.mpr ⟨heExterior, heOpen⟩)
  rw [exploredEdgeStep, nextExploredEdgeSet, Finset.mem_union] at hfNext
  rcases hfNext with hfOld | hfClosure
  · apply heNotOldBoundary
    apply hlineBoundary
    rw [mem_cubicEdgeBoundaryWithin_iff]
    exact ⟨heAmbient, heNotOld, f, hfOld, hfe⟩
  · apply heNotNext
    rw [exploredEdgeStep, nextExploredEdgeSet, Finset.mem_union]
    exact Or.inr (mem_finiteEdgeReachableClosure_of_adj hfClosure heAllowed hfe)

/-- The literal finite line-graph exploration realizes the complete first-update interval
profile.  This is the semantic bridge from the set-valued equations (7.31)--(7.32) to an exact
uniform-label history cell. -/
theorem exploredEdgeStep_mem_firstRadial_updatedProfile
    {d : ℕ}
    (oldExplored oldBoundary ambient : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ)
    (holdBoundary : Disjoint oldBoundary oldExplored)
    (holdBoundaryAmbient : oldBoundary ⊆ ambient)
    (hlineBoundary : cubicEdgeBoundaryWithin oldExplored ambient ⊆ oldBoundary)
    (hseedOpen : ∀ e ∈ oldExplored, X e < (p : ℝ)) :
    let exterior := ambient \ (oldExplored ∪ oldBoundary)
    let nextExplored :=
      exploredEdgeStep oldExplored oldBoundary exterior p incremented X
    let nextBoundary := cubicEdgeBoundaryWithin nextExplored ambient
    X ∈ (firstRadialRevealUpdate oldExplored nextExplored oldBoundary nextBoundary ambient
      p incremented).updatedProfile.event := by
  dsimp only
  let exterior := ambient \ (oldExplored ∪ oldBoundary)
  let nextExplored := exploredEdgeStep oldExplored oldBoundary exterior p incremented X
  let nextBoundary := cubicEdgeBoundaryWithin nextExplored ambient
  let D := firstRadialRevealUpdate oldExplored nextExplored oldBoundary nextBoundary ambient
    p incremented
  rw [RevealThresholdUpdateData.mem_updatedProfile_event_iff]
  constructor
  · intro e heClosed
    rw [RevealThresholdUpdateData.updatedClosedSupport, Finset.mem_union] at heClosed
    rcases heClosed with heOld | heNew
    · have heBoundary := (Finset.mem_sdiff.mp heOld).1
      have heNotNext := (Finset.mem_sdiff.mp heOld).2
      have heAmbient := holdBoundaryAmbient heBoundary
      rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
        D heAmbient heBoundary heNotNext]
      exact incremented_le_label_of_mem_oldBoundary_not_mem_exploredEdgeStep
        oldExplored oldBoundary exterior p incremented X heBoundary heNotNext
    · obtain ⟨heNewBoundary, heNotOldBoundary⟩ :=
        Finset.mem_sdiff.mp (Finset.mem_inter.mp heNew).1
      have heAmbient := (Finset.mem_inter.mp heNew).2
      rw [RevealThresholdUpdateData.updatedLower_eq_density_of_mem_newBoundary
        D heAmbient heNewBoundary heNotOldBoundary]
      exact density_le_label_of_mem_newBoundary_not_oldBoundary
        oldExplored oldBoundary ambient exterior p incremented X hlineBoundary rfl
        heNewBoundary heNotOldBoundary
  · intro e heNext
    by_cases heOld : e ∈ oldExplored
    · rw [RevealThresholdUpdateData.updatedUpper_eq_old_of_mem_oldExplored D heOld]
      simpa [D, firstRadialRevealUpdate, initialRevealUpper, heOld] using
        hseedOpen e heOld
    · by_cases heBoundary : e ∈ oldBoundary
      · rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
          D heOld heBoundary heNext]
        have hboundaryExterior : Disjoint oldBoundary exterior := by
          rw [Finset.disjoint_left]
          intro f hfBoundary hfExterior
          exact (Finset.mem_sdiff.mp hfExterior).2
            (Finset.mem_union_right _ hfBoundary)
        exact label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStep
          oldExplored oldBoundary exterior p incremented X holdBoundary
          hboundaryExterior heBoundary heNext
      · rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
          D heOld heBoundary heNext]
        exact label_lt_density_of_mem_exploredEdgeStep_not_old_not_boundary
          oldExplored oldBoundary exterior p incremented X heNext heOld heBoundary

end Percolation
