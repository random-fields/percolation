import Percolation.Bernoulli.Coupling
import Percolation.Critical.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Entanglement of cubic edge sets

This file gives a literal formal version of Grimmett's definitions in Chapter 12, §12.5.
Cubic edges are realized as closed straight segments in Euclidean three-space.  A separating
sphere carries the inside/outside data supplied by Jordan--Brouwer separation; recording that
data in the structure prevents later proofs from silently appealing to an unavailable global
choice of complementary component.
-/

namespace Percolation

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Euclidean three-space used by the entanglement model. -/
abbrev CubicEuclideanPoint3 := EuclideanSpace ℝ (Fin 3)

/-- The standard geometric embedding of a cubic-lattice vertex. -/
noncomputable def cubicEuclideanPoint3 (x : Cubic 3) : CubicEuclideanPoint3 :=
  WithLp.toLp 2 fun i ↦ (x i : ℝ)

theorem cubicEuclideanPoint3_injective : Function.Injective cubicEuclideanPoint3 := by
  intro x y h
  funext i
  have hi := congrArg (fun z : CubicEuclideanPoint3 ↦ WithLp.ofLp z i) h
  change (x i : ℝ) = (y i : ℝ) at hi
  exact_mod_cast hi

/-- The closed straight segment geometrically occupied by a cubic edge. -/
noncomputable def cubicEdgeSegment (e : CubicEdge 3) : Set CubicEuclideanPoint3 :=
  Sym2.lift
    ⟨fun x y ↦ segment ℝ (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y), by
      intro x y
      exact segment_symm ℝ _ _⟩ e.1

@[simp]
theorem cubicEdgeSegment_mk {x y : Cubic 3} (hxy : (cubicGraph 3).Adj x y) :
    cubicEdgeSegment (⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet]⟩ : CubicEdge 3) =
      segment ℝ (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y) := by
  simp [cubicEdgeSegment, Sym2.lift_mk]

/-- Geometric realization of a finite cubic edge set. -/
noncomputable def finiteCubicEdgeRealization (E : Finset (CubicEdge 3)) :
    Set CubicEuclideanPoint3 :=
  ⋃ e ∈ E, cubicEdgeSegment e

/-- Geometric realization of an arbitrary cubic edge set. -/
noncomputable def cubicEdgeRealization (E : Set (CubicEdge 3)) :
    Set CubicEuclideanPoint3 :=
  ⋃ e ∈ E, cubicEdgeSegment e

theorem finiteCubicEdgeRealization_eq (E : Finset (CubicEdge 3)) :
    finiteCubicEdgeRealization E = cubicEdgeRealization (E : Set (CubicEdge 3)) := by
  ext z
  simp [finiteCubicEdgeRealization, cubicEdgeRealization]

theorem finiteCubicEdgeRealization_union (E F : Finset (CubicEdge 3)) :
    finiteCubicEdgeRealization (E ∪ F) =
      finiteCubicEdgeRealization E ∪ finiteCubicEdgeRealization F := by
  ext z
  simp only [finiteCubicEdgeRealization, Finset.mem_union, mem_iUnion, mem_union]
  aesop

theorem cubicEdgeSegment_nonempty (e : CubicEdge 3) :
    (cubicEdgeSegment e).Nonempty := by
  rcases e with ⟨q, hq⟩
  induction q using Sym2.inductionOn with
  | _ x y =>
      exact ⟨cubicEuclideanPoint3 x,
        left_mem_segment ℝ (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y)⟩

theorem cubicEdgeSegment_convex (e : CubicEdge 3) :
    Convex ℝ (cubicEdgeSegment e) := by
  rcases e with ⟨q, hq⟩
  induction q using Sym2.inductionOn with
  | _ x y =>
      exact convex_segment (𝕜 := ℝ)
        (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y)

theorem cubicEdgeRealization_mono {E F : Set (CubicEdge 3)} (hEF : E ⊆ F) :
    cubicEdgeRealization E ⊆ cubicEdgeRealization F := by
  intro z hz
  simp only [cubicEdgeRealization, mem_iUnion] at hz ⊢
  obtain ⟨e, heE, hz⟩ := hz
  exact ⟨e, hEF heE, hz⟩

/-- A topological sphere together with its two complementary components.

The `homeomorphic_to_sphere` field records the source's meaning of "sphere".  The remaining
fields state the Jordan--Brouwer separation data that the definitions use: disjoint open inside
and outside components, a complete cover of the complement, and the bounded/unbounded
distinction. -/
structure SeparatingSphere where
  carrier : Set CubicEuclideanPoint3
  homeomorphic_to_sphere :
    Nonempty (carrier ≃ₜ Metric.sphere (0 : CubicEuclideanPoint3) 1)
  inside : Set CubicEuclideanPoint3
  outside : Set CubicEuclideanPoint3
  isOpen_inside : IsOpen inside
  isOpen_outside : IsOpen outside
  isConnected_inside : IsConnected inside
  isConnected_outside : IsConnected outside
  disjoint_inside_outside : Disjoint inside outside
  compl_carrier : carrierᶜ = inside ∪ outside
  bounded_inside : Bornology.IsBounded inside
  unbounded_outside : ¬Bornology.IsBounded outside

namespace SeparatingSphere

theorem inside_subset_compl (S : SeparatingSphere) : S.inside ⊆ S.carrierᶜ := by
  rw [S.compl_carrier]
  exact subset_union_left

theorem outside_subset_compl (S : SeparatingSphere) : S.outside ⊆ S.carrierᶜ := by
  rw [S.compl_carrier]
  exact subset_union_right

theorem compl_eq_union (S : SeparatingSphere) :
    S.carrierᶜ = S.inside ∪ S.outside :=
  S.compl_carrier

end SeparatingSphere

/-- A finite cubic edge set is entangled when no disjoint sphere separates its realization. -/
def FiniteEntangled (E : Finset (CubicEdge 3)) : Prop :=
  ∀ S : SeparatingSphere,
    Disjoint (finiteCubicEdgeRealization E) S.carrier →
      finiteCubicEdgeRealization E ⊆ S.inside ∨
        finiteCubicEdgeRealization E ⊆ S.outside

/-- Grimmett's exhaustion definition for an arbitrary (possibly infinite) edge set. -/
def Entangled (E : Set (CubicEdge 3)) : Prop :=
  ∀ F : Finset (CubicEdge 3), (F : Set (CubicEdge 3)) ⊆ E →
    ∃ E' : Finset (CubicEdge 3),
      (F : Set (CubicEdge 3)) ⊆ E' ∧
      (E' : Set (CubicEdge 3)) ⊆ E ∧ FiniteEntangled E'

/-- The empty edge set is finite-entangled. -/
theorem finiteEntangled_empty : FiniteEntangled ∅ := by
  intro S hdisj
  left
  simp [finiteCubicEdgeRealization]

/-- A connected realization cannot be split between the two complementary components of a
disjoint separating sphere.  This is the topological core of the source assertion that every
connected graph is entangled. -/
theorem finiteEntangled_of_isConnected (E : Finset (CubicEdge 3))
    (hE : IsConnected (finiteCubicEdgeRealization E)) :
    FiniteEntangled E := by
  intro S hdisj
  have hsubsetCompl : finiteCubicEdgeRealization E ⊆ S.carrierᶜ := by
    exact Set.disjoint_left.1 hdisj
  have hcover : finiteCubicEdgeRealization E ⊆ S.inside ∪ S.outside := by
    rw [← S.compl_carrier]
    exact hsubsetCompl
  exact (isPreconnected_iff_subset_of_disjoint.1 hE.isPreconnected)
    S.inside S.outside S.isOpen_inside S.isOpen_outside hcover <| by
      rw [Set.disjoint_iff_inter_eq_empty.1 S.disjoint_inside_outside,
        inter_empty]

/-- Two finite entanglements whose geometric realizations meet have entangled union. -/
theorem FiniteEntangled.union_of_realization_inter_nonempty
    {E F : Finset (CubicEdge 3)} (hE : FiniteEntangled E)
    (hF : FiniteEntangled F)
    (hinter : (finiteCubicEdgeRealization E ∩
      finiteCubicEdgeRealization F).Nonempty) :
    FiniteEntangled (E ∪ F) := by
  intro S hdisj
  rw [finiteCubicEdgeRealization_union] at hdisj ⊢
  have hdisjE : Disjoint (finiteCubicEdgeRealization E) S.carrier :=
    hdisj.mono_left subset_union_left
  have hdisjF : Disjoint (finiteCubicEdgeRealization F) S.carrier :=
    hdisj.mono_left subset_union_right
  rcases hE S hdisjE with hEin | hEout
  · rcases hF S hdisjF with hFin | hFout
    · exact Or.inl (union_subset hEin hFin)
    · obtain ⟨z, hzE, hzF⟩ := hinter
      exact False.elim <| Set.disjoint_left.1 S.disjoint_inside_outside
        (hEin hzE) (hFout hzF)
  · rcases hF S hdisjF with hFin | hFout
    · obtain ⟨z, hzE, hzF⟩ := hinter
      exact False.elim <| Set.disjoint_left.1 S.disjoint_inside_outside
        (hFin hzF) (hEout hzE)
    · exact Or.inr (union_subset hEout hFout)

@[simp]
theorem walkEdgeFinset_nil_entanglement (x : Cubic 3) :
    walkEdgeFinset (SimpleGraph.Walk.nil : (cubicGraph 3).Walk x x) = ∅ := by
  ext e
  simp [mem_walkEdgeFinset_iff]

@[simp]
theorem walkEdgeFinset_cons_entanglement {x y z : Cubic 3}
    (hxy : (cubicGraph 3).Adj x y) (w : (cubicGraph 3).Walk y z) :
    walkEdgeFinset (SimpleGraph.Walk.cons hxy w) =
      insert (⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet]⟩ : CubicEdge 3)
        (walkEdgeFinset w) := by
  ext e
  rw [mem_walkEdgeFinset_iff]
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, Finset.mem_insert,
    mem_walkEdgeFinset_iff]
  constructor
  · rintro (he | he)
    · left
      exact Subtype.ext he
    · exact Or.inr he
  · rintro (rfl | he)
    · exact Or.inl rfl
    · exact Or.inr he

/-- The edges traversed by any finite cubic walk form a finite entanglement.  This supplies the
precise geometric bridge from ordinary open connectivity to entanglement. -/
theorem finiteEntangled_walkEdgeFinset {x y : Cubic 3}
    (w : (cubicGraph 3).Walk x y) : FiniteEntangled (walkEdgeFinset w) := by
  induction w with
  | nil => simpa using finiteEntangled_empty
  | @cons x y z hxy w ih =>
      let e : CubicEdge 3 := ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet]⟩
      rw [walkEdgeFinset_cons_entanglement]
      cases w with
      | nil =>
        simp only [walkEdgeFinset_nil_entanglement, Finset.insert_empty]
        apply finiteEntangled_of_isConnected
        simpa [finiteCubicEdgeRealization, e] using
          (cubicEdgeSegment_convex e).isConnected (cubicEdgeSegment_nonempty e)
      | @cons y u z hyu q =>
        have hsingle : FiniteEntangled {e} := by
          apply finiteEntangled_of_isConnected
          simpa [finiteCubicEdgeRealization] using
            (cubicEdgeSegment_convex e).isConnected (cubicEdgeSegment_nonempty e)
        have hinter : (finiteCubicEdgeRealization {e} ∩
            finiteCubicEdgeRealization (walkEdgeFinset (SimpleGraph.Walk.cons hyu q))).Nonempty := by
          refine ⟨cubicEuclideanPoint3 y, ?_, ?_⟩
          · simp only [finiteCubicEdgeRealization, Finset.mem_singleton, mem_iUnion]
            refine ⟨e, rfl, ?_⟩
            simpa [e] using
              (right_mem_segment ℝ (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y))
          · simp only [finiteCubicEdgeRealization, mem_iUnion]
            let f : CubicEdge 3 := ⟨s(y, u), by simpa [SimpleGraph.mem_edgeSet]⟩
            refine ⟨f, ?_, ?_⟩
            · rw [walkEdgeFinset_cons_entanglement]
              exact Finset.mem_insert_self _ _
            · simpa [f] using
                (left_mem_segment ℝ (cubicEuclideanPoint3 y) (cubicEuclideanPoint3 u))
        simpa only [Finset.singleton_union] using
          hsingle.union_of_realization_inter_nonempty ih hinter

/-- Two edges belong to one finite entanglement contained in `omega`. -/
def EdgeEntangledWithIn (omega : Set (CubicEdge 3))
    (e f : CubicEdge 3) : Prop :=
  ∃ E : Finset (CubicEdge 3),
    (E : Set (CubicEdge 3)) ⊆ omega ∧ FiniteEntangled E ∧ e ∈ E ∧ f ∈ E

theorem edgeEntangledWithIn_refl {omega : Set (CubicEdge 3)}
    {e : CubicEdge 3} (he : e ∈ omega) : EdgeEntangledWithIn omega e e := by
  refine ⟨{e}, by simpa using he, ?_, by simp, by simp⟩
  apply finiteEntangled_of_isConnected
  simpa [finiteCubicEdgeRealization] using
    (cubicEdgeSegment_convex e).isConnected (cubicEdgeSegment_nonempty e)

theorem edgeEntangledWithIn_symm {omega : Set (CubicEdge 3)}
    {e f : CubicEdge 3} :
    EdgeEntangledWithIn omega e f → EdgeEntangledWithIn omega f e := by
  rintro ⟨E, hEomega, hE, he, hf⟩
  exact ⟨E, hEomega, hE, hf, he⟩

theorem edgeEntangledWithIn_trans {omega : Set (CubicEdge 3)}
    {e f g : CubicEdge 3}
    (hef : EdgeEntangledWithIn omega e f)
    (hfg : EdgeEntangledWithIn omega f g) :
    EdgeEntangledWithIn omega e g := by
  obtain ⟨E, hEomega, hE, he, hfE⟩ := hef
  obtain ⟨F, hFomega, hF, hfF, hg⟩ := hfg
  have hinter : (finiteCubicEdgeRealization E ∩
      finiteCubicEdgeRealization F).Nonempty := by
    obtain ⟨z, hz⟩ := cubicEdgeSegment_nonempty f
    refine ⟨z, ?_, ?_⟩
    · simp only [finiteCubicEdgeRealization, mem_iUnion]
      exact ⟨f, hfE, hz⟩
    · simp only [finiteCubicEdgeRealization, mem_iUnion]
      exact ⟨f, hfF, hz⟩
  exact ⟨E ∪ F, by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact hEomega ha
      · exact hFomega ha,
    hE.union_of_realization_inter_nonempty hF hinter,
    Finset.mem_union_left F he, Finset.mem_union_right E hg⟩

/-! ### The maximal origin entanglement -/

/-- A cubic edge is incident to a specified lattice vertex. -/
def CubicEdgeIncident (x : Cubic 3) (e : CubicEdge 3) : Prop :=
  x ∈ e.1

theorem cubicEuclideanPoint3_mem_edgeSegment_of_incident
    {x : Cubic 3} {e : CubicEdge 3} (hxe : CubicEdgeIncident x e) :
    cubicEuclideanPoint3 x ∈ cubicEdgeSegment e := by
  obtain ⟨y, hxy⟩ := Sym2.mem_iff_exists.1 hxe
  unfold cubicEdgeSegment
  rw [hxy]
  exact left_mem_segment ℝ (cubicEuclideanPoint3 x) (cubicEuclideanPoint3 y)

/-- A finite entanglement, open in `omega`, that contains an edge incident to the origin. -/
def RootedFiniteEntanglement (omega : Set (CubicEdge 3))
    (E : Finset (CubicEdge 3)) : Prop :=
  (E : Set (CubicEdge 3)) ⊆ omega ∧ FiniteEntangled E ∧
    ∃ r ∈ E, CubicEdgeIncident cubicOrigin r

theorem RootedFiniteEntanglement.nonempty {omega : Set (CubicEdge 3)}
    {E : Finset (CubicEdge 3)} (hE : RootedFiniteEntanglement omega E) :
    E.Nonempty := by
  obtain ⟨r, hr, _⟩ := hE.2.2
  exact ⟨r, hr⟩

theorem RootedFiniteEntanglement.origin_mem_realization
    {omega : Set (CubicEdge 3)} {E : Finset (CubicEdge 3)}
    (hE : RootedFiniteEntanglement omega E) :
    cubicEuclideanPoint3 cubicOrigin ∈ finiteCubicEdgeRealization E := by
  obtain ⟨r, hrE, hr⟩ := hE.2.2
  simp only [finiteCubicEdgeRealization, mem_iUnion]
  exact ⟨r, hrE, cubicEuclideanPoint3_mem_edgeSegment_of_incident hr⟩

theorem RootedFiniteEntanglement.union {omega : Set (CubicEdge 3)}
    {E F : Finset (CubicEdge 3)}
    (hE : RootedFiniteEntanglement omega E)
    (hF : RootedFiniteEntanglement omega F) :
    RootedFiniteEntanglement omega (E ∪ F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact hE.1 he
    · exact hF.1 he
  · apply hE.2.1.union_of_realization_inter_nonempty hF.2.1
    exact ⟨cubicEuclideanPoint3 cubicOrigin,
      hE.origin_mem_realization, hF.origin_mem_realization⟩
  · obtain ⟨r, hrE, hr⟩ := hE.2.2
    exact ⟨r, Finset.mem_union_left F hrE, hr⟩

/-- A nontrivial open walk from the origin is itself a rooted finite entanglement. -/
theorem rootedFiniteEntanglement_walkEdgeFinset
    {omega : Set (CubicEdge 3)} {y : Cubic 3}
    (w : (cubicGraph 3).Walk cubicOrigin y) (hopen : walkIsOpen omega w)
    (hnil : ¬w.Nil) : RootedFiniteEntanglement omega (walkEdgeFinset w) := by
  refine ⟨?_, finiteEntangled_walkEdgeFinset w, ?_⟩
  · intro e he
    exact hopen e (by simpa [mem_walkEdgeFinset_iff] using he)
  · let r : CubicEdge 3 :=
      ⟨s(cubicOrigin, w.snd), w.edges_subset_edgeSet (w.mk_start_snd_mem_edges hnil)⟩
    refine ⟨r, ?_, ?_⟩
    · rw [mem_walkEdgeFinset_iff]
      exact w.mk_start_snd_mem_edges hnil
    · change cubicOrigin ∈ (r : Sym2 (Cubic 3))
      simp [r]

/-- The canonical maximal open entanglement containing the origin.  An edge belongs when it is
contained in some finite open entanglement that also contains an origin-incident edge. -/
def originEntanglementEdges (omega : Set (CubicEdge 3)) : Set (CubicEdge 3) :=
  {e | ∃ E : Finset (CubicEdge 3), RootedFiniteEntanglement omega E ∧ e ∈ E}

theorem originEntanglementEdges_subset (omega : Set (CubicEdge 3)) :
    originEntanglementEdges omega ⊆ omega := by
  rintro e ⟨E, hE, he⟩
  exact hE.1 he

theorem originEntanglementEdges_mono {omega eta : Set (CubicEdge 3)}
    (h : omega ⊆ eta) :
    originEntanglementEdges omega ⊆ originEntanglementEdges eta := by
  rintro e ⟨E, hE, he⟩
  exact ⟨E, ⟨hE.1.trans h, hE.2⟩, he⟩

/-- Every non-origin vertex in the ordinary open cluster is incident to an edge of the maximal
origin entanglement. -/
theorem exists_originEntanglementEdge_incident_of_mem_cubicOpenCluster
    {omega : Set (CubicEdge 3)} {y : Cubic 3}
    (hy : y ∈ cubicOpenCluster 3 omega) (hy0 : y ≠ cubicOrigin) :
    ∃ e ∈ originEntanglementEdges omega, CubicEdgeIncident y e := by
  obtain ⟨w, hopen⟩ := hy
  have hnil : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne (Ne.symm hy0)
  let e : CubicEdge 3 :=
    ⟨s(w.penultimate, y), w.edges_subset_edgeSet (w.mk_penultimate_end_mem_edges hnil)⟩
  refine ⟨e, ?_, ?_⟩
  · refine ⟨walkEdgeFinset w,
      rootedFiniteEntanglement_walkEdgeFinset w hopen hnil, ?_⟩
    rw [mem_walkEdgeFinset_iff]
    exact w.mk_penultimate_end_mem_edges hnil
  · change y ∈ (e : Sym2 (Cubic 3))
    simp [e]

/-- Vertices incident to one of the edges in a finite cubic edge set. -/
noncomputable def cubicEdgeEndpointFinset (E : Finset (CubicEdge 3)) :
    Finset (Cubic 3) :=
  E.biUnion fun e ↦ (e : Sym2 (Cubic 3)).toFinset

@[simp]
theorem mem_cubicEdgeEndpointFinset {E : Finset (CubicEdge 3)} {x : Cubic 3} :
    x ∈ cubicEdgeEndpointFinset E ↔ ∃ e ∈ E, CubicEdgeIncident x e := by
  classical
  simp [cubicEdgeEndpointFinset, CubicEdgeIncident, Sym2.mem_toFinset]

/-- Ordinary origin-cluster vertices are the origin itself or endpoints of edges in the maximal
origin entanglement. -/
theorem cubicOpenCluster_subset_originEntanglementEndpoints
    (omega : Set (CubicEdge 3)) :
    cubicOpenCluster 3 omega ⊆
      insert cubicOrigin (⋃ e ∈ originEntanglementEdges omega,
        (e : Sym2 (Cubic 3)) : Set (Cubic 3)) := by
  intro y hy
  by_cases hy0 : y = cubicOrigin
  · subst y
    exact Set.mem_insert _ _
  · obtain ⟨e, he, hye⟩ :=
      exists_originEntanglementEdge_incident_of_mem_cubicOpenCluster hy hy0
    simp only [Set.mem_insert_iff, mem_iUnion]
    exact Or.inr ⟨e, he, hye⟩

theorem exists_rootedFiniteEntanglement_superset
    {omega : Set (CubicEdge 3)} (F : Finset (CubicEdge 3))
    (hF : (F : Set (CubicEdge 3)) ⊆ originEntanglementEdges omega)
    (hne : F.Nonempty) :
    ∃ E : Finset (CubicEdge 3),
      (F : Set (CubicEdge 3)) ⊆ E ∧ RootedFiniteEntanglement omega E := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at hne
  | @insert e F heF ih =>
      obtain ⟨Ee, hEe, heEe⟩ := hF
        (show e ∈ insert e F by simp)
      by_cases hFempty : F = ∅
      · subst F
        exact ⟨Ee, by simpa using heEe, hEe⟩
      · have hFsub : (F : Set (CubicEdge 3)) ⊆ originEntanglementEdges omega := by
          intro f hf
          exact hF (by simp [hf])
        obtain ⟨EF, hFEF, hEF⟩ := ih hFsub (Finset.nonempty_iff_ne_empty.2 hFempty)
        exact ⟨Ee ∪ EF, by
          intro a ha
          rcases Finset.mem_insert.1 ha with rfl | ha
          · exact Finset.mem_union_left EF heEe
          · exact Finset.mem_union_right Ee (hFEF ha),
          hEe.union hEF⟩

/-- If the canonical origin entanglement is infinite, it is an infinite entangled set in the
literal finite-exhaustion sense of the source. -/
theorem entangled_originEntanglementEdges_of_infinite
    {omega : Set (CubicEdge 3)}
    (_hinf : (originEntanglementEdges omega).Infinite) :
    Entangled (originEntanglementEdges omega) := by
  intro F hF
  by_cases hFempty : F = ∅
  · subst F
    exact ⟨∅, by simp, by simp, finiteEntangled_empty⟩
  · obtain ⟨E, hFE, hE⟩ := exists_rootedFiniteEntanglement_superset F hF
      (Finset.nonempty_iff_ne_empty.2 hFempty)
    refine ⟨E, hFE, ?_, hE.2.1⟩
    intro e he
    exact ⟨E, hE, he⟩

/-- Event that the origin lies in an infinite open entanglement, using the canonical maximal
origin entanglement. -/
def hasInfiniteOriginEntanglement : Set (Set (CubicEdge 3)) :=
  {omega | (originEntanglementEdges omega).Infinite}

/-- An infinite ordinary open cluster supplies an infinite origin entanglement. -/
theorem hasInfiniteOpenCluster_imp_hasInfiniteOriginEntanglement
    {omega : Set (CubicEdge 3)} :
    hasInfiniteOpenCluster 3 omega → omega ∈ hasInfiniteOriginEntanglement := by
  intro hcluster hfinite
  have hE : (originEntanglementEdges omega).Finite := hfinite
  let E : Finset (CubicEdge 3) := hE.toFinset
  have hclusterFinite : (cubicOpenCluster 3 omega).Finite := by
    have hbound : (insert cubicOrigin (cubicEdgeEndpointFinset E : Set (Cubic 3))).Finite :=
      (Set.finite_singleton cubicOrigin).union (cubicEdgeEndpointFinset E).finite_toSet
    apply hbound.subset
    intro y hy
    by_cases hy0 : y = cubicOrigin
    · subst y
      exact Set.mem_insert _ _
    · obtain ⟨e, he, hye⟩ :=
        exists_originEntanglementEdge_incident_of_mem_cubicOpenCluster hy hy0
      exact Set.mem_insert_iff.2 <| Or.inr <|
        (mem_cubicEdgeEndpointFinset.2 ⟨e, by simpa [E] using he, hye⟩)
  exact hcluster hclusterFinite

theorem measurableSet_originEntanglementEdgeEvent (e : CubicEdge 3) :
    MeasurableSet {omega : Set (CubicEdge 3) | e ∈ originEntanglementEdges omega} := by
  classical
  rw [show {omega : Set (CubicEdge 3) | e ∈ originEntanglementEdges omega} =
      ⋃ E : Finset (CubicEdge 3),
        if FiniteEntangled E ∧ e ∈ E ∧
            (∃ r ∈ E, CubicEdgeIncident cubicOrigin r) then
          {omega : Set (CubicEdge 3) | (E : Set (CubicEdge 3)) ⊆ omega}
        else ∅ by
    ext omega
    simp only [originEntanglementEdges, Set.mem_setOf_eq, mem_iUnion,
      Set.mem_ite_empty_right, RootedFiniteEntanglement]
    constructor
    · rintro ⟨E, ⟨hEomega, hEnt, hroot⟩, heE⟩
      exact ⟨E, ⟨hEnt, heE, hroot⟩, hEomega⟩
    · rintro ⟨E, ⟨hEnt, heE, hroot⟩, hEomega⟩
      exact ⟨E, ⟨hEomega, hEnt, hroot⟩, heE⟩]
  exact MeasurableSet.iUnion fun E ↦ by
    split_ifs
    · exact measurableSet_superset_finset E
    · exact MeasurableSet.empty

/-- The maximal origin-entanglement map is measurable as a map into the coordinate product
`Set (CubicEdge 3)`. -/
theorem measurable_originEntanglementEdges : Measurable originEntanglementEdges := by
  change Measurable ((fun P : CubicEdge 3 → Prop ↦ {e | P e}) ∘
    fun omega e ↦ e ∈ originEntanglementEdges omega)
  apply Measurable.comp (by fun_prop)
  exact measurable_pi_lambda _ fun e ↦
    (measurableSet_originEntanglementEdgeEvent e).mem

/-- Extended size of the maximal origin entanglement. -/
noncomputable def originEntanglementSize (omega : Set (CubicEdge 3)) : ℕ∞ :=
  (originEntanglementEdges omega).encard

theorem measurable_originEntanglementSize : Measurable originEntanglementSize :=
  measurable_encard.comp measurable_originEntanglementEdges

theorem mem_hasInfiniteOriginEntanglement_iff (omega : Set (CubicEdge 3)) :
    omega ∈ hasInfiniteOriginEntanglement ↔ originEntanglementSize omega = ⊤ := by
  rw [hasInfiniteOriginEntanglement, Set.mem_setOf_eq,
    originEntanglementSize, Set.encard_eq_top_iff]

theorem measurableSet_hasInfiniteOriginEntanglement :
    MeasurableSet hasInfiniteOriginEntanglement := by
  rw [show hasInfiniteOriginEntanglement =
      originEntanglementSize ⁻¹' ({⊤} : Set ℕ∞) by
    ext omega
    simp [mem_hasInfiniteOriginEntanglement_iff]]
  exact (measurable_originEntanglementSize (measurableSet_singleton ⊤))

theorem isIncreasingEvent_hasInfiniteOriginEntanglement :
    IsIncreasingEvent hasInfiniteOriginEntanglement := by
  intro omega eta h hInf
  exact hInf.mono (originEntanglementEdges_mono h)

/-- Entanglement probability in three-dimensional cubic bond percolation. -/
noncomputable def entanglementTheta (p : I) : ℝ :=
  (bernoulliBondMeasure 3 p).real hasInfiniteOriginEntanglement

theorem entanglementTheta_mono : Monotone entanglementTheta := by
  intro p q hpq
  exact isIncreasingEvent_hasInfiniteOriginEntanglement.setBernoulli_real_mono
    measurableSet_hasInfiniteOriginEntanglement hpq

/-- Ordinary open connectivity is a special case of entanglement, so its percolation
probability is no larger. -/
theorem theta_le_entanglementTheta (p : I) :
    theta 3 p ≤ entanglementTheta p := by
  letI : IsProbabilityMeasure (bernoulliBondMeasure 3 p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  have hne : (bernoulliBondMeasure 3 p) hasInfiniteOriginEntanglement ≠ ⊤ :=
    measure_ne_top _ _
  unfold theta entanglementTheta
  exact measureReal_mono
    (fun _ h ↦ hasInfiniteOpenCluster_imp_hasInfiniteOriginEntanglement h) hne

/-- Equation (12.23), the entanglement critical probability. -/
noncomputable def entanglementCriticalProbability : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | entanglementTheta p = 0}) : Set ℝ)

theorem entanglementTheta_zero : entanglementTheta (0 : I) = 0 := by
  rw [entanglementTheta, bernoulliBondMeasure, setBernoulli_zero, Measure.real,
    Measure.dirac_apply' _ measurableSet_hasInfiniteOriginEntanglement]
  simp [hasInfiniteOriginEntanglement, originEntanglementEdges,
    RootedFiniteEntanglement]

theorem entanglementCriticalProbability_nonneg :
    0 ≤ entanglementCriticalProbability := by
  rw [entanglementCriticalProbability]
  apply le_csSup
  · exact ⟨1, by
      rintro q ⟨p, hp, rfl⟩
      exact p.2.2⟩
  · exact ⟨(0 : I), entanglementTheta_zero, rfl⟩

theorem entanglementCriticalProbability_le_one :
    entanglementCriticalProbability ≤ 1 := by
  rw [entanglementCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I), entanglementTheta_zero, rfl⟩⟩
  · rintro q ⟨p, hp, rfl⟩
    exact p.2.2

/-- The elementary half of (12.24): entanglement percolates whenever the ordinary origin
cluster is infinite. -/
theorem entanglementCriticalProbability_le_cubicCriticalProbability :
    entanglementCriticalProbability ≤ cubicCriticalProbability 3 := by
  rw [entanglementCriticalProbability, cubicCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I), entanglementTheta_zero, rfl⟩⟩
  · rintro q ⟨p, hp, rfl⟩
    apply le_csSup
    · exact ⟨1, by
        rintro q ⟨r, hr, rfl⟩
        exact r.2.2⟩
    · refine ⟨p, ?_, rfl⟩
      exact le_antisymm ((theta_le_entanglementTheta p).trans_eq hp)
        measureReal_nonneg

end Percolation
