import Percolation.Bernoulli.Increasing
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Finite edge-reachability fibers

This module records the stopping-set fact behind finite boundary explorations.  If `R` is the
set of vertices reachable from a finite source set, then the fiber saying that the reachable set
is exactly `R` is determined by the graph edges incident to `R`.  Edges wholly outside `R` are
therefore fresh after conditioning on that fiber.
-/

namespace Percolation

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- All edges of a finite graph incident to a prescribed vertex set. -/
noncomputable def finiteGraphIncidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) : Finset (Sym2 V) :=
  R.biUnion fun v ↦ G.incidenceFinset v

/-- A graph walk is open in a set of unordered edges. -/
def finiteGraphWalkIsOpen {G : SimpleGraph V} (omega : Set (Sym2 V))
    {x y : V} (w : G.Walk x y) : Prop :=
  ∀ e ∈ w.edges, e ∈ omega

/-- Reachability from one of finitely many sources using open graph edges. -/
def finiteGraphReachableFrom (G : SimpleGraph V) (source : Finset V)
    (omega : Set (Sym2 V)) (y : V) : Prop :=
  ∃ x ∈ source, ∃ w : G.Walk x y, finiteGraphWalkIsOpen omega w

/-- The finite set of vertices reachable from the sources through open graph edges. -/
noncomputable def finiteGraphReachableVertices (G : SimpleGraph V) (source : Finset V)
    (omega : Set (Sym2 V)) : Finset V := by
  classical
  exact Finset.univ.filter (finiteGraphReachableFrom G source omega)

omit [DecidableEq V] in
@[simp]
theorem mem_finiteGraphReachableVertices_iff
    (G : SimpleGraph V) (source : Finset V) (omega : Set (Sym2 V)) (y : V) :
    y ∈ finiteGraphReachableVertices G source omega ↔
      finiteGraphReachableFrom G source omega y := by
  classical
  simp [finiteGraphReachableVertices]

omit [Fintype V] [DecidableEq V] in
theorem finiteGraphReachableFrom_source
    {G : SimpleGraph V} {source : Finset V} {omega : Set (Sym2 V)}
    {x : V} (hx : x ∈ source) :
    finiteGraphReachableFrom G source omega x := by
  exact ⟨x, hx, .nil, by simp [finiteGraphWalkIsOpen]⟩

omit [Fintype V] [DecidableEq V] in
theorem finiteGraphReachableFrom_step
    {G : SimpleGraph V} {source : Finset V} {omega : Set (Sym2 V)}
    {x y : V} (hx : finiteGraphReachableFrom G source omega x)
    (hxy : G.Adj x y) (hopen : s(x, y) ∈ omega) :
    finiteGraphReachableFrom G source omega y := by
  rcases hx with ⟨z, hz, w, hw⟩
  refine ⟨z, hz, w.concat hxy, ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
    List.mem_append, List.mem_singleton] at he
  exact he.elim (hw e) (fun h ↦ h ▸ hopen)

private theorem finiteGraphReachableFrom_transport_walk
    (G : SimpleGraph V) [DecidableRel G.Adj] (source R : Finset V)
    {omega eta : Set (Sym2 V)}
    (hmem : ∀ {z}, finiteGraphReachableFrom G source omega z → z ∈ R)
    (hagree : ∀ e ∈ finiteGraphIncidentEdges G R, (e ∈ omega ↔ e ∈ eta))
    {x y : V} (w : G.Walk x y)
    (hw : finiteGraphWalkIsOpen omega w)
    (hxOmega : finiteGraphReachableFrom G source omega x)
    (hxEta : finiteGraphReachableFrom G source eta x) :
    finiteGraphReachableFrom G source eta y := by
  induction w with
  | nil => exact hxEta
  | @cons x z y hxz q ih =>
      have hxR : x ∈ R := hmem hxOmega
      have hedge : s(x, z) ∈ finiteGraphIncidentEdges G R := by
        rw [finiteGraphIncidentEdges, Finset.mem_biUnion]
        refine ⟨x, hxR, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact (G.mk'_mem_incidenceSet_left_iff).mpr hxz
      have hopenOmega : s(x, z) ∈ omega := hw _ (by simp)
      have hopenEta : s(x, z) ∈ eta := (hagree _ hedge).mp hopenOmega
      have hzOmega := finiteGraphReachableFrom_step hxOmega hxz hopenOmega
      have hzEta := finiteGraphReachableFrom_step hxEta hxz hopenEta
      apply ih
      · intro e he
        exact hw e (by simp [he])
      · exact hzOmega
      · exact hzEta

private theorem finiteGraphReachableFrom_transport_walk_rev
    (G : SimpleGraph V) [DecidableRel G.Adj] (source R : Finset V)
    {omega eta : Set (Sym2 V)}
    (hmem : ∀ {z}, finiteGraphReachableFrom G source omega z → z ∈ R)
    (hagree : ∀ e ∈ finiteGraphIncidentEdges G R, (e ∈ omega ↔ e ∈ eta))
    {x y : V} (w : G.Walk x y)
    (hw : finiteGraphWalkIsOpen eta w)
    (hxOmega : finiteGraphReachableFrom G source omega x)
    (hxEta : finiteGraphReachableFrom G source eta x) :
    finiteGraphReachableFrom G source omega y := by
  induction w with
  | nil => exact hxOmega
  | @cons x z y hxz q ih =>
      have hxR : x ∈ R := hmem hxOmega
      have hedge : s(x, z) ∈ finiteGraphIncidentEdges G R := by
        rw [finiteGraphIncidentEdges, Finset.mem_biUnion]
        refine ⟨x, hxR, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact (G.mk'_mem_incidenceSet_left_iff).mpr hxz
      have hopenEta : s(x, z) ∈ eta := hw _ (by simp)
      have hopenOmega : s(x, z) ∈ omega := (hagree _ hedge).mpr hopenEta
      have hzOmega := finiteGraphReachableFrom_step hxOmega hxz hopenOmega
      have hzEta := finiteGraphReachableFrom_step hxEta hxz hopenEta
      apply ih
      · intro e he
        exact hw e (by simp [he])
      · exact hzOmega
      · exact hzEta

/-- A fixed reachable-vertex fiber is determined by the edges incident to that fiber. -/
theorem dependsOn_finiteGraphReachableVertices_fiber
    (G : SimpleGraph V) [DecidableRel G.Adj] (source R : Finset V) :
    DependsOn (finiteGraphIncidentEdges G R)
      {omega | finiteGraphReachableVertices G source omega = R} := by
  classical
  intro omega eta hagree
  have forward : ∀ {omega eta : Set (Sym2 V)},
      (∀ e ∈ finiteGraphIncidentEdges G R, (e ∈ omega ↔ e ∈ eta)) →
      finiteGraphReachableVertices G source omega = R →
      finiteGraphReachableVertices G source eta = R := by
    intro omega eta hagree homega
    have hmem : ∀ {z}, finiteGraphReachableFrom G source omega z → z ∈ R := by
      intro z hz
      rw [← homega]
      exact (mem_finiteGraphReachableVertices_iff G source omega z).mpr hz
    apply Finset.ext
    intro y
    rw [mem_finiteGraphReachableVertices_iff]
    constructor
    · rintro ⟨x, hx, w, hw⟩
      have hxOmega := finiteGraphReachableFrom_source (G := G) (omega := omega) hx
      have hxEta := finiteGraphReachableFrom_source (G := G) (omega := eta) hx
      have hyOmega := finiteGraphReachableFrom_transport_walk_rev
        G source R hmem hagree w hw hxOmega hxEta
      exact hmem hyOmega
    · intro hyR
      have hyOmega : finiteGraphReachableFrom G source omega y := by
        rw [← mem_finiteGraphReachableVertices_iff G source omega y, homega]
        exact hyR
      rcases hyOmega with ⟨x, hx, w, hw⟩
      exact finiteGraphReachableFrom_transport_walk
        G source R hmem hagree w hw
          (finiteGraphReachableFrom_source (G := G) (omega := omega) hx)
          (finiteGraphReachableFrom_source (G := G) (omega := eta) hx)
  exact ⟨forward hagree, forward (fun e he ↦ (hagree e he).symm)⟩

end Percolation
