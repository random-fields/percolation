import Percolation.Critical.InfiniteClusterUniqueness
import Percolation.Critical.ThreePartitions
import Percolation.Critical.TreeGraph

/-!
# Trifurcations of an open cluster

This file contains the graph-theoretic object in the infinite-multiplicity half of the
Burton--Keane proof (Grimmett, Theorem 8.1).  Deleting the incidence set of a vertex keeps the
ambient vertex type fixed, which makes the three infinite branches convenient to compare and to
restrict to finite lattice spheres.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval

/-- Infinite components produced from the component of `x` after deleting every edge incident
to `x`.  The existential neighbor condition excludes unrelated components elsewhere in `G`. -/
def trifurcationBranchComponents {V : Type*} (G : SimpleGraph V) (x : V) :
    Set (G.deleteIncidenceSet x).ConnectedComponent :=
  {C | C.supp.Infinite ∧ ∃ y, G.Adj x y ∧
    (G.deleteIncidenceSet x).connectedComponentMk y = C}

/-- Source-faithful graph formulation of a trifurcation: exactly three edges are incident to
`x`, and deleting them leaves exactly three infinite branches of the original component.

The equality of the two cardinalities forces the three neighbors to lie in three distinct
infinite components.  Hence there are no additional finite branches at `x`, matching Grimmett's
condition (c). -/
def IsTrifurcationVertex {V : Type*} (G : SimpleGraph V) (x : V) : Prop :=
  (G.neighborSet x).encard = 3 ∧ (trifurcationBranchComponents G x).encard = 3

/-- A graph isomorphism restricts to an isomorphism after deleting all edges incident to a
chosen vertex. -/
def SimpleGraph.Iso.deleteIncidenceSetIso
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (F : G ≃g G') (x : V) :
    G.deleteIncidenceSet x ≃g G'.deleteIncidenceSet (F x) where
  toEquiv := F.toEquiv
  map_rel_iff' := by
    intro u v
    rw [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨huv, hux, hvx⟩
      refine ⟨F.map_rel_iff.mp huv, ?_, ?_⟩
      · exact fun h ↦ hux (congrArg F h)
      · exact fun h ↦ hvx (congrArg F h)
    · rintro ⟨huv, hux, hvx⟩
      refine ⟨F.map_rel_iff.mpr huv, ?_, ?_⟩
      · exact fun h ↦ hux (F.injective h)
      · exact fun h ↦ hvx (F.injective h)

/-- The branch components at a vertex are carried bijectively by a graph isomorphism. -/
noncomputable def trifurcationBranchComponentsEquiv
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (F : G ≃g G') (x : V) :
    {C // C ∈ trifurcationBranchComponents G x} ≃
      {C // C ∈ trifurcationBranchComponents G' (F x)} := by
  classical
  let D := SimpleGraph.Iso.deleteIncidenceSetIso F x
  let eC := D.connectedComponentEquiv
  let forward : {C // C ∈ trifurcationBranchComponents G x} →
      {C // C ∈ trifurcationBranchComponents G' (F x)} := fun C ↦ by
    refine ⟨eC C.1, ?_, ?_⟩
    · rw [← Set.encard_eq_top_iff]
      rw [← Set.encard_congr (SimpleGraph.ConnectedComponent.isoEquivSupp D C.1)]
      exact Set.encard_eq_top_iff.mpr C.2.1
    · obtain ⟨y, hxy, hyC⟩ := C.2.2
      refine ⟨F y, F.map_rel_iff.mpr hxy, ?_⟩
      change eC ((G.deleteIncidenceSet x).connectedComponentMk y) = eC C.1
      exact congrArg eC hyC
  let backward : {C // C ∈ trifurcationBranchComponents G' (F x)} →
      {C // C ∈ trifurcationBranchComponents G x} := fun C ↦ by
    refine ⟨eC.symm C.1, ?_, ?_⟩
    · rw [← Set.encard_eq_top_iff]
      have hmap : D.symm.connectedComponentEquiv C.1 = eC.symm C.1 := by
        rw [SimpleGraph.Iso.connectedComponentEquiv_symm]
      have henc := Set.encard_congr
        (SimpleGraph.ConnectedComponent.isoEquivSupp D.symm C.1)
      rw [hmap] at henc
      exact henc.symm.trans (Set.encard_eq_top_iff.mpr C.2.1)
    · obtain ⟨z, hxz, hzC⟩ := C.2.2
      refine ⟨F.symm z, ?_, ?_⟩
      · simpa using F.symm.map_rel_iff.mpr hxz
      · change eC.symm ((G'.deleteIncidenceSet (F x)).connectedComponentMk z) =
          eC.symm C.1
        exact congrArg eC.symm hzC
  exact {
    toFun := forward
    invFun := backward
    left_inv := fun C ↦ by
      apply Subtype.ext
      exact eC.left_inv C.1
    right_inv := fun C ↦ by
      apply Subtype.ext
      exact eC.right_inv C.1 }

/-- Trifurcation is a graph-isomorphism invariant. -/
theorem isTrifurcationVertex_iso_iff
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (F : G ≃g G') (x : V) :
    IsTrifurcationVertex G x ↔ IsTrifurcationVertex G' (F x) := by
  let neighborEquiv : G.neighborSet x ≃ G'.neighborSet (F x) := {
    toFun := fun y ↦ ⟨F y.1, F.map_rel_iff.mpr y.2⟩
    invFun := fun y ↦ ⟨F.symm y.1, by
      simpa using F.symm.map_rel_iff.mpr y.2⟩
    left_inv := fun y ↦ Subtype.ext (F.toEquiv.left_inv y.1)
    right_inv := fun y ↦ Subtype.ext (F.toEquiv.right_inv y.1) }
  have hneighbor : (G.neighborSet x).encard =
      (G'.neighborSet (F x)).encard := Set.encard_congr neighborEquiv
  have hbranch : (trifurcationBranchComponents G x).encard =
      (trifurcationBranchComponents G' (F x)).encard :=
    Set.encard_congr (trifurcationBranchComponentsEquiv F x)
  simp only [IsTrifurcationVertex]
  rw [hneighbor, hbranch]

/-- A lattice vertex is a trifurcation in the open graph of `omega`. -/
def isOpenTrifurcation (d : ℕ) (omega : EdgeConfiguration d) (x : Cubic d) : Prop :=
  IsTrifurcationVertex (cubicOpenGraph d omega) x

/-- Pulling a configuration back along a cubic graph automorphism makes that automorphism an
isomorphism of the corresponding open graphs. -/
def cubicOpenGraphIsoConfigurationPullbackIso
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d) (omega : EdgeConfiguration d) :
    cubicOpenGraph d (cubicGraphIsoConfigurationPullback F omega) ≃g
      cubicOpenGraph d omega where
  toEquiv := F.toEquiv
  map_rel_iff' := by
    intro u v
    rw [cubicOpenGraph_adj, cubicOpenGraph_adj]
    constructor
    · rintro ⟨huv, hopen⟩
      refine ⟨F.map_rel_iff.mp huv, ?_⟩
      change F.mapEdgeSet
        (⟨s(u, v), (SimpleGraph.mem_edgeSet _).mpr (F.map_rel_iff.mp huv)⟩ :
          CubicEdge d) ∈ omega
      simpa using hopen
    · rintro ⟨huv, hopen⟩
      refine ⟨F.map_rel_iff.mpr huv, ?_⟩
      change F.mapEdgeSet
        (⟨s(u, v), (SimpleGraph.mem_edgeSet _).mpr huv⟩ : CubicEdge d) ∈ omega at hopen
      simpa using hopen

/-- Open trifurcations are carried exactly by every cubic graph automorphism. -/
theorem cubicGraphIsoConfigurationPullback_isOpenTrifurcation_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (omega : EdgeConfiguration d) (x : Cubic d) :
    isOpenTrifurcation d (cubicGraphIsoConfigurationPullback F omega) x ↔
      isOpenTrifurcation d omega (F x) :=
  isTrifurcationVertex_iso_iff
    (cubicOpenGraphIsoConfigurationPullbackIso F omega) x

/-- The event that a prescribed lattice vertex is a trifurcation. -/
def trifurcationEvent (d : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  {omega | isOpenTrifurcation d omega x}

/-- Close every cubic edge incident to `x`. -/
def closeIncidentConfiguration
    (d : ℕ) (x : Cubic d) (omega : EdgeConfiguration d) : EdgeConfiguration d :=
  spliceOn (cubicIncidentEdges d {x}) ∅ omega

/-- Closing all incident coordinates is exactly deletion of the incidence set in the random open
graph. -/
theorem cubicOpenGraph_closeIncidentConfiguration
    (d : ℕ) (x : Cubic d) (omega : EdgeConfiguration d) :
    cubicOpenGraph d (closeIncidentConfiguration d x omega) =
      (cubicOpenGraph d omega).deleteIncidenceSet x := by
  ext u v
  rw [SimpleGraph.deleteIncidenceSet_adj, cubicOpenGraph_adj, cubicOpenGraph_adj]
  constructor
  · rintro ⟨huv, hopen⟩
    have hopenData := mem_spliceOn.mp hopen
    rcases hopenData with hopenEmpty | ⟨hopenOmega, hnotIncident⟩
    · simp at hopenEmpty
    refine ⟨⟨huv, hopenOmega⟩, ?_, ?_⟩
    · intro hux
      apply hnotIncident
      apply mem_cubicIncidentEdges_of_endpoint (x := x) (by simp)
      subst u
      simp
    · intro hvx
      apply hnotIncident
      apply mem_cubicIncidentEdges_of_endpoint (x := x) (by simp)
      subst v
      simp
  · rintro ⟨⟨huv, hopenOmega⟩, hux, hvx⟩
    refine ⟨huv, mem_spliceOn.mpr (Or.inr ⟨hopenOmega, ?_⟩)⟩
    intro hIncident
    obtain ⟨z, hz, hze⟩ :=
      mem_cubicIncidentEdges_iff_exists_endpoint.mp hIncident
    simp only [Finset.mem_singleton] at hz
    subst z
    simp only [Sym2.mem_iff] at hze
    exact hze.elim (fun h ↦ hux h.symm) (fun h ↦ hvx h.symm)

/-- The three incident bonds prescribed by a direction triple. -/
noncomputable def trifurcationDirectionEdges
    (d : ℕ) (x : Cubic d) (a : Fin 3 → CubicDirection d) : Finset (CubicEdge d) :=
  Finset.univ.image fun i ↦ cubicStepEdge x (a i)

theorem trifurcationDirectionEdges_subset_incident
    (d : ℕ) (x : Cubic d) (a : Fin 3 → CubicDirection d) :
    trifurcationDirectionEdges d x a ⊆ cubicIncidentEdges d {x} := by
  intro e he
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
  exact cubicStepEdge_mem_cubicIncidentEdges (by simp) (a i)

/-- A prescribed triple of directions witnesses a trifurcation when those and only those
incident bonds are open, and their three endpoints lead to distinct infinite components after
the incident bonds are closed. -/
def trifurcationDirectionWitnessEvent
    (d : ℕ) (x : Cubic d) (a : Fin 3 → CubicDirection d) : Set (EdgeConfiguration d) :=
  finiteCylinder (cubicIncidentEdges d {x}) (trifurcationDirectionEdges d x a) ∩
    (⋂ i, (closeIncidentConfiguration d x) ⁻¹'
      infiniteClusterVertexEvent d (cubicStepFrom x (a i))) ∩
    ⋂ i, ⋂ j, if i = j then Set.univ else
      ((closeIncidentConfiguration d x) ⁻¹'
        connectionEvent d (cubicStepFrom x (a i)) (cubicStepFrom x (a j)))ᶜ

/-- The explicitly measurable union of all direction witnesses at `x`. -/
def strongTrifurcationEvent (d : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  ⋃ a : Fin 3 → CubicDirection d, trifurcationDirectionWitnessEvent d x a

/-- A measurable translate of a fixed strong-trifurcation event.  We only need that this event
implies an actual trifurcation at `y`; we deliberately avoid requiring the stronger direction
witness itself to be definitionally translation invariant. -/
def translatedStrongTrifurcationEvent
    (d : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  cubicTranslationConfigurationPullback x y ⁻¹' strongTrifurcationEvent d x

theorem measurable_closeIncidentConfiguration (d : ℕ) (x : Cubic d) :
    Measurable (closeIncidentConfiguration d x) := by
  apply (measurable_spliceOn_generateFrom
    (E := cubicIncidentEdges d {x}) (s := ∅) (by simp)).mono
  · exact generateFrom_coordinateEvents_le _
  · exact le_rfl

theorem measurableSet_trifurcationDirectionWitnessEvent
    (d : ℕ) (x : Cubic d) (a : Fin 3 → CubicDirection d) :
    MeasurableSet (trifurcationDirectionWitnessEvent d x a) := by
  rw [trifurcationDirectionWitnessEvent]
  apply ((measurableSet_finiteCylinder
    (trifurcationDirectionEdges_subset_incident d x a)).inter
      (MeasurableSet.iInter fun i ↦
        (measurable_closeIncidentConfiguration d x)
          (measurableSet_infiniteClusterVertexEvent d
            (cubicStepFrom x (a i))))).inter
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ by
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, if_false]
      exact ((measurable_closeIncidentConfiguration d x)
        (measurableSet_connectionEvent d
          (cubicStepFrom x (a i)) (cubicStepFrom x (a j)))).compl

theorem measurableSet_strongTrifurcationEvent (d : ℕ) (x : Cubic d) :
    MeasurableSet (strongTrifurcationEvent d x) :=
  MeasurableSet.iUnion fun a ↦ measurableSet_trifurcationDirectionWitnessEvent d x a

theorem measurableSet_translatedStrongTrifurcationEvent
    (d : ℕ) (x y : Cubic d) :
    MeasurableSet (translatedStrongTrifurcationEvent d x y) :=
  (measurable_cubicTranslationConfigurationPullback x y)
    (measurableSet_strongTrifurcationEvent d x)

@[simp]
theorem mem_trifurcationDirectionWitnessEvent_iff
    {d : ℕ} {x : Cubic d} {a : Fin 3 → CubicDirection d}
    {omega : EdgeConfiguration d} :
    omega ∈ trifurcationDirectionWitnessEvent d x a ↔
      (∀ e ∈ cubicIncidentEdges d {x},
        (e ∈ omega ↔ e ∈ trifurcationDirectionEdges d x a)) ∧
      (∀ i, hasInfiniteOpenClusterFrom d (closeIncidentConfiguration d x omega)
        (cubicStepFrom x (a i))) ∧
      ∀ i j, i ≠ j → closeIncidentConfiguration d x omega ∉
        connectionEvent d (cubicStepFrom x (a i)) (cubicStepFrom x (a j)) := by
  simp only [trifurcationDirectionWitnessEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_preimage, infiniteClusterVertexEvent, Set.mem_setOf_eq,
    mem_finiteCylinder]
  constructor
  · rintro ⟨⟨hcyl, hinf⟩, hsep⟩
    exact ⟨hcyl, hinf, fun i j hij ↦ by simpa [hij] using hsep i j⟩
  · rintro ⟨hcyl, hinf, hsep⟩
    exact ⟨⟨hcyl, hinf⟩, fun i j ↦ by
      by_cases hij : i = j
      · simp [hij]
      · simpa [hij] using hsep i j hij⟩

theorem cubicStepEdge_fixed_injective {d : ℕ} (x : Cubic d) :
    Function.Injective (cubicStepEdge x : CubicDirection d → CubicEdge d) := by
  intro a b hab
  have hs : s(x, cubicStepFrom x a) = s(x, cubicStepFrom x b) :=
    congrArg Subtype.val hab
  rcases Sym2.eq_iff.mp hs with h | h
  · exact cubicStepFrom_injective x h.2
  · exfalso
    exact (cubicGraph_adj_stepFrom x b).ne h.1

/-- Every explicit direction witness is a trifurcation in the graph-theoretic sense. -/
theorem trifurcationDirectionWitnessEvent_subset_trifurcationEvent
    (d : ℕ) (x : Cubic d) (a : Fin 3 → CubicDirection d) :
    trifurcationDirectionWitnessEvent d x a ⊆ trifurcationEvent d x := by
  classical
  intro omega homega
  have hdata := mem_trifurcationDirectionWitnessEvent_iff.mp homega
  let G := cubicOpenGraph d omega
  let closed := closeIncidentConfiguration d x omega
  let H := G.deleteIncidenceSet x
  have hgraph : cubicOpenGraph d closed = H :=
    cubicOpenGraph_closeIncidentConfiguration d x omega
  have haInj : Function.Injective a := by
    intro i j hij
    by_contra hijIndex
    apply hdata.2.2 i j hijIndex
    rw [hij]
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩
  have hvertexInj : Function.Injective (fun i : Fin 3 ↦ cubicStepFrom x (a i)) :=
    (cubicStepFrom_injective x).comp haInj
  have hopenStep (i : Fin 3) : G.Adj x (cubicStepFrom x (a i)) := by
    apply cubicOpenGraph_adj.mpr
    let e := cubicStepEdge x (a i)
    have heIncident : e ∈ cubicIncidentEdges d {x} :=
      cubicStepEdge_mem_cubicIncidentEdges (by simp) (a i)
    have heTrace : e ∈ trifurcationDirectionEdges d x a := by
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    refine ⟨cubicGraph_adj_stepFrom x (a i), ?_⟩
    simpa [e, cubicStepEdge] using (hdata.1 e heIncident).mpr heTrace
  have hneighborEq : G.neighborSet x =
      Set.range (fun i : Fin 3 ↦ cubicStepFrom x (a i)) := by
    ext y
    constructor
    · intro hy
      have hAdj : G.Adj x y := hy
      obtain ⟨b, hb⟩ := (cubicGraph_adj_iff_exists_stepFrom x y).mp
        (cubicOpenGraph_adj.mp hAdj).choose
      subst y
      let e := cubicStepEdge x b
      have heIncident : e ∈ cubicIncidentEdges d {x} :=
        cubicStepEdge_mem_cubicIncidentEdges (by simp) b
      have heOpen : e ∈ omega := by
        simpa [e, cubicStepEdge] using (cubicOpenGraph_adj.mp hAdj).choose_spec
      have heTrace : e ∈ trifurcationDirectionEdges d x a :=
        (hdata.1 e heIncident).mp heOpen
      obtain ⟨i, _hi, hei⟩ := Finset.mem_image.mp heTrace
      have hbi : b = a i := cubicStepEdge_fixed_injective x hei.symm
      exact ⟨i, by rw [hbi]⟩
    · rintro ⟨i, rfl⟩
      exact hopenStep i
  have hneighborCard : (G.neighborSet x).encard = 3 := by
    rw [hneighborEq, ← Set.image_univ]
    rw [hvertexInj.encard_image, Set.encard_univ,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    norm_num
  let f : Fin 3 → {C // C ∈ trifurcationBranchComponents G x} := fun i ↦ by
    let y := cubicStepFrom x (a i)
    have hinfinite : (H.connectedComponentMk y).supp.Infinite := by
      have hi := hdata.2.1 i
      have hi' : ((cubicOpenGraph d closed).connectedComponentMk y).supp.Infinite := by
        simpa [hasInfiniteOpenClusterFrom, cubicOpenClusterFrom,
          cubicOpenGraph_component_supp] using hi
      rwa [hgraph] at hi'
    exact ⟨H.connectedComponentMk y, hinfinite, y, hopenStep i, rfl⟩
  have hfInj : Function.Injective f := by
    intro i j hij
    by_contra hijIndex
    apply hdata.2.2 i j hijIndex
    rw [← connectedComponentMk_eq_iff_mem_connectionEvent, hgraph]
    exact congrArg Subtype.val hij
  have hbranchLower : (3 : ℕ∞) ≤ (trifurcationBranchComponents G x).encard := by
    have hcard := ENat.card_le_card_of_injective hfInj
    change ENat.card (Fin 3) ≤
      ENat.card {C // C ∈ trifurcationBranchComponents G x} at hcard
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Set.encard] using hcard
  have hbranchUpper : (trifurcationBranchComponents G x).encard ≤ 3 := by
    let R : Set H.ConnectedComponent :=
      (fun y ↦ H.connectedComponentMk y) '' G.neighborSet x
    have hsub : trifurcationBranchComponents G x ⊆ R := by
      intro C hC
      obtain ⟨y, hxy, hyC⟩ := hC.2
      exact ⟨y, hxy, hyC⟩
    calc
      (trifurcationBranchComponents G x).encard ≤ R.encard :=
        Set.encard_le_encard hsub
      _ ≤ (G.neighborSet x).encard := by
        simpa [R] using Set.encard_image_le
          (fun y ↦ H.connectedComponentMk y) (G.neighborSet x)
      _ = 3 := hneighborCard
  exact ⟨hneighborCard, le_antisymm hbranchUpper hbranchLower⟩

theorem strongTrifurcationEvent_subset_trifurcationEvent (d : ℕ) (x : Cubic d) :
    strongTrifurcationEvent d x ⊆ trifurcationEvent d x := by
  intro omega homega
  rw [strongTrifurcationEvent] at homega
  simp only [Set.mem_iUnion] at homega
  obtain ⟨a, ha⟩ := homega
  exact trifurcationDirectionWitnessEvent_subset_trifurcationEvent d x a ha

/-- Every translated strong witness is an actual trifurcation at the translated vertex. -/
theorem translatedStrongTrifurcationEvent_subset_trifurcationEvent
    (d : ℕ) (x y : Cubic d) :
    translatedStrongTrifurcationEvent d x y ⊆ trifurcationEvent d y := by
  intro omega homega
  have hsource : isOpenTrifurcation d
      (cubicTranslationConfigurationPullback x y omega) x :=
    strongTrifurcationEvent_subset_trifurcationEvent d x homega
  have htarget :=
    (cubicGraphIsoConfigurationPullback_isOpenTrifurcation_iff
      (cubicTranslationIso x y) omega x).mp hsource
  simpa [trifurcationEvent, cubicTranslationIso_apply, cubicTranslate] using htarget

/-- Bernoulli measure assigns a translated witness the same probability as its source event. -/
theorem bernoulliBondMeasure_real_translatedStrongTrifurcationEvent
    {d : ℕ} (p : I) (x y : Cubic d) :
    (bernoulliBondMeasure d p).real (translatedStrongTrifurcationEvent d x y) =
      (bernoulliBondMeasure d p).real (strongTrifurcationEvent d x) := by
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ (strongTrifurcationEvent d x))
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p x y)
  change (Measure.map (cubicTranslationConfigurationPullback x y)
      (bernoulliBondMeasure d p)) (strongTrifurcationEvent d x) =
    (bernoulliBondMeasure d p) (strongTrifurcationEvent d x) at hmap
  rw [Measure.map_apply (measurable_cubicTranslationConfigurationPullback x y)
    (measurableSet_strongTrifurcationEvent d x)] at hmap
  exact congrArg ENNReal.toReal hmap

/-! ### Exterior branches after isolating a finite vertex set -/

/-- If an infinite open cluster starts in a finite vertex set `B`, then after closing every
edge incident to `B` one can find a boundary edge leading to an infinite component of the
remaining graph.  The endpoint outside `B` is retained explicitly for the finite-energy
trifurcation construction. -/
theorem exists_infinite_boundary_attachment_after_closing_incident
    {d : ℕ} {omega : EdgeConfiguration d} (B : Finset (Cubic d))
    {x : Cubic d} (hxB : x ∈ B) (hxInf : hasInfiniteOpenClusterFrom d omega x) :
    ∃ b ∈ B, ∃ y : Cubic d, y ∉ B ∧
      (cubicOpenGraph d omega).Adj b y ∧
      (cubicOpenGraph d omega).Reachable x y ∧
      {z | ((cubicOpenGraph d omega).deleteEdges
        (underlyingCubicEdges (cubicIncidentEdges d B) : Set (Sym2 (Cubic d)))).Reachable y z}.Infinite := by
  classical
  let G := cubicOpenGraph d omega
  let E := underlyingCubicEdges (cubicIncidentEdges d B)
  let H := G.deleteEdges (E : Set (Sym2 (Cubic d)))
  have hxReachInf : {z | G.Reachable x z}.Infinite := by
    have hsupp : (G.connectedComponentMk x).supp = {z | G.Reachable x z} := by
      ext z
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq]
      exact SimpleGraph.reachable_comm
    have hxInf' : (G.connectedComponentMk x).supp.Infinite := by
      simpa [G, hasInfiniteOpenClusterFrom, cubicOpenClusterFrom,
        cubicOpenGraph_component_supp] using hxInf
    rwa [hsupp] at hxInf'
  obtain ⟨z, hxz, hzInf⟩ :=
    SimpleGraph.exists_infinite_reachable_deleteEdges_finset_of_root hxReachInf E
  have hzOutsideInf : ({w | H.Reachable z w} \ (B : Set (Cubic d))).Infinite := by
    exact hzInf.diff B.finite_toSet
  obtain ⟨z', hzz', hz'B⟩ := hzOutsideInf.nonempty
  have hxz' : G.Reachable x z' :=
    hxz.trans (hzz'.mono (SimpleGraph.deleteEdges_le _))
  obtain ⟨q⟩ := hxz'.symm
  have hex : ∃ j : ℕ, j ≤ q.length ∧ q.getVert j ∈ B := by
    refine ⟨q.length, le_rfl, ?_⟩
    simpa using hxB
  let j := Nat.find hex
  have hj : j ≤ q.length ∧ q.getVert j ∈ B := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra h
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos h
    apply hz'B
    simpa [j, hjzero] using hj.2
  let y := q.getVert (j - 1)
  let b := q.getVert j
  have hyB : y ∉ B := by
    intro hy
    have hcand : j - 1 ≤ q.length ∧ q.getVert (j - 1) ∈ B :=
      ⟨(Nat.sub_le j 1).trans hj.1, hy⟩
    have hmin := Nat.find_min' hex hcand
    omega
  have hjlt : j - 1 < q.length := by omega
  have hyb : G.Adj y b := by
    simpa [y, b, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hjpos.ne')]
      using q.adj_getVert_succ hjlt
  let r : G.Walk z' y := q.take (j - 1)
  have hrlen : r.length = j - 1 := by
    dsimp [r]
    rw [q.take_length, Nat.min_eq_left (Nat.sub_le j 1 |>.trans hj.1)]
  have hrAvoid : ∀ e ∈ r.edges, e ∉ (E : Set (Sym2 (Cubic d))) := by
    intro e he heE
    have heG : e ∈ G.edgeSet := r.edges_subset_edgeSet he
    have heCubic : e ∈ (cubicGraph d).edgeSet := by
      apply SimpleGraph.edgeSet_mono (G₁ := G) (G₂ := cubicGraph d) (fun _ _ h ↦
        (cubicOpenGraph_adj.mp h).1)
      exact heG
    let ce : CubicEdge d := ⟨e, heCubic⟩
    have hceE : ce ∈ cubicIncidentEdges d B := by
      exact (mem_underlyingCubicEdges_iff heCubic).mp heE
    obtain ⟨t, htB, hte⟩ :=
      mem_cubicIncidentEdges_iff_exists_endpoint.mp hceE
    have htSupport : t ∈ r.support := r.mem_support_of_mem_edges he hte
    obtain ⟨k, hkt, hklen⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp htSupport
    have hkj : k < j := by omega
    have hqkt : q.getVert k = t := by
      simpa [r, q.take_getVert, Nat.min_eq_right (by omega : k ≤ j - 1)] using hkt
    have hcand : k ≤ q.length ∧ q.getVert k ∈ B :=
      ⟨le_of_lt (hkj.trans_le hj.1), hqkt.symm ▸ htB⟩
    exact (not_lt_of_ge (Nat.find_min' hex hcand)) hkj
  have hz'y : H.Reachable z' y := by
    exact ⟨r.toDeleteEdges (E : Set (Sym2 (Cubic d))) hrAvoid⟩
  have hzy : H.Reachable z y := hzz'.trans hz'y
  have hyInf : {w | H.Reachable y w}.Infinite := by
    have hset : {w | H.Reachable y w} = {w | H.Reachable z w} := by
      ext w
      constructor
      · exact fun hyw ↦ hzy.trans hyw
      · exact fun hzw ↦ hzy.symm.trans hzw
    rw [hset]
    exact hzInf
  have hxy : G.Reachable x y :=
    hxz'.trans (hz'y.mono (SimpleGraph.deleteEdges_le _))
  exact ⟨b, hj.2, y, hyB, hyb.symm, hxy, by simpa [G, E, H] using hyInf⟩

/-- Three exterior infinite branches obtained by isolating a finite set containing a fixed
three-cluster witness. -/
structure ExteriorThreeBranchData
    (d : ℕ) (B : Finset (Cubic d)) (omega : EdgeConfiguration d)
    (x : Fin 3 → Cubic d) where
  boundaryVertex : Fin 3 → Cubic d
  exteriorVertex : Fin 3 → Cubic d
  boundary_mem : ∀ i, boundaryVertex i ∈ B
  exterior_notMem : ∀ i, exteriorVertex i ∉ B
  boundary_adj : ∀ i,
    (cubicOpenGraph d omega).Adj (boundaryVertex i) (exteriorVertex i)
  witness_reachable : ∀ i,
    (cubicOpenGraph d omega).Reachable (x i) (exteriorVertex i)
  exterior_infinite : ∀ i,
    {z | ((cubicOpenGraph d omega).deleteEdges
      (underlyingCubicEdges (cubicIncidentEdges d B) : Set (Sym2 (Cubic d)))).Reachable
        (exteriorVertex i) z}.Infinite
  exterior_separate : ∀ i j, i ≠ j →
    ¬((cubicOpenGraph d omega).deleteEdges
      (underlyingCubicEdges (cubicIncidentEdges d B) : Set (Sym2 (Cubic d)))).Reachable
        (exteriorVertex i) (exteriorVertex j)

theorem exists_exteriorThreeBranchData
    {d : ℕ} {omega : EdgeConfiguration d} {x : Fin 3 → Cubic d}
    (B : Finset (Cubic d)) (hxB : ∀ i, x i ∈ B)
    (hwitness : omega ∈ infiniteOpenClusterWitnessEvent x) :
    Nonempty (ExteriorThreeBranchData d B omega x) := by
  classical
  have hatt (i : Fin 3) : ∃ b ∈ B, ∃ y : Cubic d, y ∉ B ∧
      (cubicOpenGraph d omega).Adj b y ∧
      (cubicOpenGraph d omega).Reachable (x i) y ∧
      {z | ((cubicOpenGraph d omega).deleteEdges
        (underlyingCubicEdges (cubicIncidentEdges d B) : Set (Sym2 (Cubic d)))).Reachable y z}.Infinite :=
    exists_infinite_boundary_attachment_after_closing_incident B (hxB i)
      (hwitness.1 i)
  choose b hb y hyB hadj hxy hinf using hatt
  refine ⟨{
    boundaryVertex := b
    exteriorVertex := y
    boundary_mem := hb
    exterior_notMem := hyB
    boundary_adj := hadj
    witness_reachable := hxy
    exterior_infinite := hinf
    exterior_separate := ?_ }⟩
  intro i j hij hconn
  apply hwitness.2 i j hij
  exact cubicOpenGraph_reachable_iff.mp <|
    (hxy i).trans <| (hconn.mono (SimpleGraph.deleteEdges_le _)).trans (hxy j).symm

/-! ### A vertex-disjoint tripod -/

/-- Three distinct vertices in one connected component admit a tripod whose three branches are
internally vertex-disjoint.  This strengthens the edge-disjoint tripod used by the tree-graph
inequality just enough for the finite-energy construction of a trifurcation. -/
theorem exists_three_internally_vertexDisjoint_walks_of_reachable
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x₀ x₁ x₂ : V}
    (hr01 : G.Reachable x₀ x₁) (hr20 : G.Reachable x₂ x₀) :
    ∃ u : V, ∃ w₀ : G.Walk u x₀, ∃ w₁ : G.Walk u x₁, ∃ w₂ : G.Walk u x₂,
      w₀.IsPath ∧ w₁.IsPath ∧ w₂.IsPath ∧
        w₀.support.tail.Disjoint w₁.support.tail ∧
        w₀.support.tail.Disjoint w₂.support.tail ∧
        w₁.support.tail.Disjoint w₂.support.tail := by
  classical
  obtain ⟨p, hp⟩ := hr01.exists_isPath
  obtain ⟨q, hq⟩ := hr20.exists_isPath
  have hex : ∃ j : ℕ, j ≤ q.length ∧ q.getVert j ∈ p.support := by
    refine ⟨q.length, le_rfl, ?_⟩
    simpa using p.start_mem_support
  let j := Nat.find hex
  have hj : j ≤ q.length ∧ q.getVert j ∈ p.support := Nat.find_spec hex
  let u := q.getVert j
  have huP : u ∈ p.support := hj.2
  let pre : G.Walk x₀ u := p.takeUntil u huP
  let post : G.Walk u x₁ := p.dropUntil u huP
  let r : G.Walk x₂ u := q.take j
  let w₀ : G.Walk u x₀ := pre.reverse
  let w₁ : G.Walk u x₁ := post
  let w₂ : G.Walk u x₂ := r.reverse
  have hpSplit : pre.append post = p := by
    simpa [pre, post] using p.take_spec huP
  have hprePath : pre.IsPath := walk_isPath_of_isSubwalk hp (p.isSubwalk_takeUntil huP)
  have hpostPath : post.IsPath := walk_isPath_of_isSubwalk hp (p.isSubwalk_dropUntil huP)
  have hrPath : r.IsPath := hq.take j
  have hw₀Path : w₀.IsPath := hprePath.reverse
  have hw₁Path : w₁.IsPath := hpostPath
  have hw₂Path : w₂.IsPath := hrPath.reverse
  have htail₀Pre : w₀.support.tail ⊆ pre.support := by
    intro z hz
    have hz' : z ∈ pre.support.reverse := by
      simpa [w₀, SimpleGraph.Walk.support_reverse] using List.mem_of_mem_tail hz
    simpa using hz'
  have htail₁Post : w₁.support.tail ⊆ post.support.tail := by
    intro z hz
    exact hz
  have hprePost : pre.support.Disjoint post.support.tail := by
    by_cases hnil : post.Nil
    · have hsupp : post.support.tail = [] := by
        rw [SimpleGraph.Walk.nil_iff_support_eq] at hnil
        rw [hnil]
        simp
      rw [hsupp]
      simp
    · have hpath : (pre.append post).IsPath := hpSplit ▸ hp
      have hdisj := hpath.disjoint_support_of_append hnil
      rw [post.support_tail_of_not_nil hnil] at hdisj
      exact hdisj
  have h01tail : w₀.support.tail.Disjoint w₁.support.tail := by
    rw [List.disjoint_left] at hprePost ⊢
    intro z hz₀ hz₁
    exact hprePost (htail₀Pre hz₀) (htail₁Post hz₁)
  have htail₂P : w₂.support.tail.Disjoint p.support := by
    rw [List.disjoint_left]
    intro z hz₂ hzP
    have hnoStart : u ∉ w₂.support.tail := by
      have hnodup := hw₂Path.support_nodup
      rw [← w₂.cons_tail_support, List.nodup_cons] at hnodup
      exact hnodup.1
    have hzu : z ≠ u := fun h ↦ hnoStart (h ▸ hz₂)
    have hzR : z ∈ r.support := by
      have hzW : z ∈ w₂.support := List.mem_of_mem_tail hz₂
      simpa [w₂, SimpleGraph.Walk.support_reverse] using hzW
    obtain ⟨i, hiEq, hiLen⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzR
    have hrlen : r.length = j := by
      dsimp [r]
      rw [q.take_length, Nat.min_eq_left hj.1]
    have hiJ : i ≤ j := by simpa [hrlen] using hiLen
    have hqi : q.getVert i = z := by
      have := hiEq
      simpa [r, q.take_getVert, Nat.min_eq_right hiJ] using this
    have hij : i < j := by
      apply lt_of_le_of_ne hiJ
      intro hijEq
      apply hzu
      rw [← hiEq, hijEq]
      simp [r, u, q.take_getVert]
    have hcandidate : i ≤ q.length ∧ q.getVert i ∈ p.support :=
      ⟨hiJ.trans hj.1, hqi.symm ▸ hzP⟩
    exact (not_lt_of_ge (Nat.find_min' hex hcandidate)) hij
  have htail₀P : w₀.support.tail ⊆ p.support :=
    fun z hz ↦ p.support_takeUntil_subset_support huP (htail₀Pre hz)
  have htail₁P : w₁.support.tail ⊆ p.support :=
    fun z hz ↦ p.support_dropUntil_subset huP (List.mem_of_mem_tail (htail₁Post hz))
  have h02tail : w₀.support.tail.Disjoint w₂.support.tail := by
    rw [List.disjoint_left] at htail₂P ⊢
    intro z hz₀ hz₂
    exact htail₂P hz₂ (htail₀P hz₀)
  have h12tail : w₁.support.tail.Disjoint w₂.support.tail := by
    rw [List.disjoint_left] at htail₂P ⊢
    intro z hz₁ hz₂
    exact htail₂P hz₂ (htail₁P hz₁)
  exact ⟨u, w₀, w₁, w₂, hw₀Path, hw₁Path, hw₂Path,
    h01tail, h02tail, h12tail⟩

/-- If every vertex of a cubic walk except its final endpoint lies in `B`, every edge of the
walk is incident to `B`. -/
theorem walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support
    {d : ℕ} {B : Finset (Cubic d)} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v)
    (hB : ∀ z ∈ w.support.dropLast, z ∈ B) :
    walkEdgeFinset w ⊆ cubicIncidentEdges d B := by
  classical
  rintro ⟨e, heGraph⟩ heWalk
  rw [mem_walkEdgeFinset_iff] at heWalk
  induction e using Sym2.ind with
  | _ a b =>
      have hab : a ≠ b := ((SimpleGraph.mem_edgeSet (cubicGraph d)).mp heGraph).ne
      have haSupport : a ∈ w.support :=
        w.fst_mem_support_of_mem_edges heWalk
      have hbSupport : b ∈ w.support :=
        w.snd_mem_support_of_mem_edges heWalk
      by_cases hav : a = v
      · have hbv : b ≠ v := fun h ↦ hab (hav.trans h.symm)
        have hbDrop : b ∈ w.support.dropLast :=
          List.mem_dropLast_of_mem_of_ne_getLast hbSupport (by simpa using hbv)
        exact mem_cubicIncidentEdges_of_endpoint (hB b hbDrop) (by simp)
      · have haDrop : a ∈ w.support.dropLast :=
          List.mem_dropLast_of_mem_of_ne_getLast haSupport (by simpa using hav)
        exact mem_cubicIncidentEdges_of_endpoint (hB a haDrop) (by simp)

/-- The first edge of a nontrivial cubic walk. -/
def walkFirstCubicEdge {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hnil : ¬w.Nil) : CubicEdge d :=
  ⟨s(u, w.snd), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr (w.adj_snd hnil)⟩

/-- A path visits its starting vertex only once, so its first edge is the only edge incident to
that starting vertex. -/
theorem mem_walkEdgeFinset_of_isPath_of_mem_start_iff
    {d : ℕ} {u v : Cubic d} {w : (cubicGraph d).Walk u v}
    (hpath : w.IsPath) (hnil : ¬w.Nil) {e : CubicEdge d}
    (hue : u ∈ (e : Sym2 (Cubic d))) :
    e ∈ walkEdgeFinset w ↔ e = walkFirstCubicEdge w hnil := by
  constructor
  · intro he
    have he' : (e : Sym2 (Cubic d)) ∈ w.edges :=
      (mem_walkEdgeFinset_iff w e).mp he
    rw [← w.cons_tail_eq hnil, SimpleGraph.Walk.edges_cons, List.mem_cons] at he'
    rcases he' with he' | he'
    · apply Subtype.ext
      simpa [walkFirstCubicEdge] using he'
    · have huTail : u ∈ w.tail.support :=
        w.tail.mem_support_of_mem_edges he' hue
      have huNot : u ∉ w.support.tail := by
        have hnodup := hpath.support_nodup
        rw [← w.cons_tail_support, List.nodup_cons] at hnodup
        exact hnodup.1
      exact (huNot (w.support_tail_of_not_nil hnil ▸ huTail)).elim
  · rintro rfl
    rw [mem_walkEdgeFinset_iff]
    change s(u, w.snd) ∈ w.edges
    have hedges : w.edges = s(u, w.snd) :: w.tail.edges := by
      calc
        w.edges = (SimpleGraph.Walk.cons (w.adj_snd hnil) w.tail).edges :=
          congrArg SimpleGraph.Walk.edges (w.cons_tail_eq hnil).symm
        _ = s(u, w.snd) :: w.tail.edges := by
          rw [SimpleGraph.Walk.edges_cons]
    rw [hedges]
    simp

/-- Abstract separation lemma for a finite tripod attached to three different components of an
exterior graph.  It packages the only reachability argument needed in the finite-energy step. -/
theorem tripodBranches_not_reachable
    {V : Type*} [DecidableEq V] {K H : SimpleGraph V} {B : Set V}
    (L : Fin 3 → List V) (root endVertex : Fin 3 → V)
    (hroot : ∀ i, root i ∈ L i)
    (hdisjoint : ∀ i j, i ≠ j → (L i).Disjoint (L j))
    (hvertex : ∀ i z, z ∈ L i → z ∈ B ∨ z = endVertex i)
    (hHnoAdj : ∀ {z w}, z ∈ B → ¬H.Adj z w)
    (hHoutside : ∀ i z, H.Reachable (endVertex i) z → z ∉ B)
    (hHseparate : ∀ i j, i ≠ j → ¬H.Reachable (endVertex i) (endVertex j))
    (hKadj : ∀ {z w}, K.Adj z w →
      H.Adj z w ∨ ∃ i, z ∈ L i ∧ w ∈ L i) :
    ∀ i j, i ≠ j → ¬K.Reachable (root i) (root j) := by
  intro i j hij hreach
  let P : V → Prop := fun z ↦ z ∈ L i ∨ H.Reachable (endVertex i) z
  have hstep {z w : V} (hzw : K.Adj z w) (hz : P z) : P w := by
    rcases hKadj hzw with hH | ⟨k, hzLk, hwLk⟩
    · rcases hz with hzLi | hzHi
      · rcases hvertex i z hzLi with hzB | rfl
        · exact (hHnoAdj hzB hH).elim
        · exact Or.inr hH.reachable
      · exact Or.inr (hzHi.trans hH.reachable)
    · rcases hz with hzLi | hzHi
      · have hki : k = i := by
          by_contra hki
          exact hdisjoint i k (Ne.symm hki) hzLi hzLk
        subst k
        exact Or.inl hwLk
      · have hzNotB : z ∉ B := hHoutside i z hzHi
        have hzend : z = endVertex k := (hvertex k z hzLk).resolve_left hzNotB
        have hki : k = i := by
          by_contra hki
          exact hHseparate i k (Ne.symm hki) (hzend ▸ hzHi)
        subst k
        exact Or.inl hwLk
  obtain ⟨w⟩ := hreach
  have hwalk : ∀ {a b : V} (q : K.Walk a b), P a → P b := by
    intro a b q
    induction q with
    | nil => exact fun h ↦ h
    | @cons a c b hac tail ih =>
        exact fun h ↦ ih (hstep hac h)
  have hjP : P (root j) := hwalk w (Or.inl (hroot i))
  rcases hjP with hjLi | hjHi
  · exact hdisjoint i j hij hjLi (hroot j)
  · have hjNotB : root j ∉ B := hHoutside i (root j) hjHi
    have hjEnd : root j = endVertex j :=
      (hvertex j (root j) (hroot j)).resolve_left hjNotB
    exact hHseparate i j hij (hjEnd ▸ hjHi)

/-- Join three exterior attachments by a finite tripod whose internal vertices remain in `B`.
Appending the three boundary edges makes every branch nontrivial, even when the abstract tripod
centre coincides with one of its three terminals. -/
theorem exists_exterior_tripod
    {d : ℕ} {B : Finset (Cubic d)} {omega : EdgeConfiguration d}
    {x : Fin 3 → Cubic d} (D : ExteriorThreeBranchData d B omega x)
    (hBconn : (cubicRegionGraph d (B : Set (Cubic d))).Connected) :
    ∃ u ∈ B,
      ∃ t₀ : (cubicGraph d).Walk u (D.exteriorVertex 0),
      ∃ t₁ : (cubicGraph d).Walk u (D.exteriorVertex 1),
      ∃ t₂ : (cubicGraph d).Walk u (D.exteriorVertex 2),
        t₀.IsPath ∧ t₁.IsPath ∧ t₂.IsPath ∧
        ¬t₀.Nil ∧ ¬t₁.Nil ∧ ¬t₂.Nil ∧
        t₀.support.tail.Disjoint t₁.support.tail ∧
        t₀.support.tail.Disjoint t₂.support.tail ∧
        t₁.support.tail.Disjoint t₂.support.tail ∧
        (∀ z ∈ t₀.support.dropLast, z ∈ B) ∧
        (∀ z ∈ t₁.support.dropLast, z ∈ B) ∧
        ∀ z ∈ t₂.support.dropLast, z ∈ B := by
  classical
  let R := cubicRegionGraph d (B : Set (Cubic d))
  let b₀ : {z : Cubic d // z ∈ (B : Set (Cubic d))} :=
    ⟨D.boundaryVertex 0, D.boundary_mem 0⟩
  let b₁ : {z : Cubic d // z ∈ (B : Set (Cubic d))} :=
    ⟨D.boundaryVertex 1, D.boundary_mem 1⟩
  let b₂ : {z : Cubic d // z ∈ (B : Set (Cubic d))} :=
    ⟨D.boundaryVertex 2, D.boundary_mem 2⟩
  obtain ⟨uB, w₀, w₁, w₂, hp₀, hp₁, hp₂, h01, h02, h12⟩ :=
    exists_three_internally_vertexDisjoint_walks_of_reachable
      (G := R) (x₀ := b₀) (x₁ := b₁) (x₂ := b₂)
      (hBconn b₀ b₁) (hBconn b₂ b₀)
  let f := (SimpleGraph.Embedding.induce (G := cubicGraph d)
    (B : Set (Cubic d))).toHom
  let v₀ : (cubicGraph d).Walk uB.1 (D.boundaryVertex 0) := w₀.map f
  let v₁ : (cubicGraph d).Walk uB.1 (D.boundaryVertex 1) := w₁.map f
  let v₂ : (cubicGraph d).Walk uB.1 (D.boundaryVertex 2) := w₂.map f
  have hv₀Path : v₀.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp₀
  have hv₁Path : v₁.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp₁
  have hv₂Path : v₂.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hp₂
  have hv₀B : ∀ z ∈ v₀.support, z ∈ B := by
    intro z hz
    change z ∈ (w₀.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨zB, _hzB, rfl⟩ := List.mem_map.mp hz
    exact zB.2
  have hv₁B : ∀ z ∈ v₁.support, z ∈ B := by
    intro z hz
    change z ∈ (w₁.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨zB, _hzB, rfl⟩ := List.mem_map.mp hz
    exact zB.2
  have hv₂B : ∀ z ∈ v₂.support, z ∈ B := by
    intro z hz
    change z ∈ (w₂.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨zB, _hzB, rfl⟩ := List.mem_map.mp hz
    exact zB.2
  have hadj₀ : (cubicGraph d).Adj (D.boundaryVertex 0) (D.exteriorVertex 0) :=
    (cubicOpenGraph_adj.mp (D.boundary_adj 0)).1
  have hadj₁ : (cubicGraph d).Adj (D.boundaryVertex 1) (D.exteriorVertex 1) :=
    (cubicOpenGraph_adj.mp (D.boundary_adj 1)).1
  have hadj₂ : (cubicGraph d).Adj (D.boundaryVertex 2) (D.exteriorVertex 2) :=
    (cubicOpenGraph_adj.mp (D.boundary_adj 2)).1
  have hy₀v₀ : D.exteriorVertex 0 ∉ v₀.support := fun h ↦
    D.exterior_notMem 0 (hv₀B _ h)
  have hy₁v₁ : D.exteriorVertex 1 ∉ v₁.support := fun h ↦
    D.exterior_notMem 1 (hv₁B _ h)
  have hy₂v₂ : D.exteriorVertex 2 ∉ v₂.support := fun h ↦
    D.exterior_notMem 2 (hv₂B _ h)
  let t₀ := v₀.concat hadj₀
  let t₁ := v₁.concat hadj₁
  let t₂ := v₂.concat hadj₂
  have ht₀Path : t₀.IsPath := hv₀Path.concat hy₀v₀ hadj₀
  have ht₁Path : t₁.IsPath := hv₁Path.concat hy₁v₁ hadj₁
  have ht₂Path : t₂.IsPath := hv₂Path.concat hy₂v₂ hadj₂
  have ht₀nil : ¬t₀.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro h
    exact D.exterior_notMem 0 (h ▸ uB.2)
  have ht₁nil : ¬t₁.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro h
    exact D.exterior_notMem 1 (h ▸ uB.2)
  have ht₂nil : ¬t₂.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro h
    exact D.exterior_notMem 2 (h ▸ uB.2)
  have hv01 : v₀.support.tail.Disjoint v₁.support.tail := by
    rw [List.disjoint_left]
    intro z hz₀ hz₁
    change z ∈ (w₀.map f).support.tail at hz₀
    change z ∈ (w₁.map f).support.tail at hz₁
    rw [SimpleGraph.Walk.support_map, ← List.map_tail] at hz₀ hz₁
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz₀
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hz₁
    have hba : b = a := Subtype.ext hab
    subst b
    exact h01 ha hb
  have hv02 : v₀.support.tail.Disjoint v₂.support.tail := by
    rw [List.disjoint_left]
    intro z hz₀ hz₂
    change z ∈ (w₀.map f).support.tail at hz₀
    change z ∈ (w₂.map f).support.tail at hz₂
    rw [SimpleGraph.Walk.support_map, ← List.map_tail] at hz₀ hz₂
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz₀
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hz₂
    have hba : b = a := Subtype.ext hab
    subst b
    exact h02 ha hb
  have hv12 : v₁.support.tail.Disjoint v₂.support.tail := by
    rw [List.disjoint_left]
    intro z hz₁ hz₂
    change z ∈ (w₁.map f).support.tail at hz₁
    change z ∈ (w₂.map f).support.tail at hz₂
    rw [SimpleGraph.Walk.support_map, ← List.map_tail] at hz₁ hz₂
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz₁
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hz₂
    have hba : b = a := Subtype.ext hab
    subst b
    exact h12 ha hb
  have hy01 : D.exteriorVertex 0 ≠ D.exteriorVertex 1 := by
    intro h
    exact D.exterior_separate 0 1 (by decide) (h ▸ .rfl)
  have hy02 : D.exteriorVertex 0 ≠ D.exteriorVertex 2 := by
    intro h
    exact D.exterior_separate 0 2 (by decide) (h ▸ .rfl)
  have hy12 : D.exteriorVertex 1 ≠ D.exteriorVertex 2 := by
    intro h
    exact D.exterior_separate 1 2 (by decide) (h ▸ .rfl)
  have ht₀Tail : t₀.support.tail =
      v₀.support.tail ++ [D.exteriorVertex 0] := by
    change (v₀.concat hadj₀).support.tail = _
    rw [SimpleGraph.Walk.support_concat, ← v₀.cons_tail_support]
    simp
  have ht₁Tail : t₁.support.tail =
      v₁.support.tail ++ [D.exteriorVertex 1] := by
    change (v₁.concat hadj₁).support.tail = _
    rw [SimpleGraph.Walk.support_concat, ← v₁.cons_tail_support]
    simp
  have ht₂Tail : t₂.support.tail =
      v₂.support.tail ++ [D.exteriorVertex 2] := by
    change (v₂.concat hadj₂).support.tail = _
    rw [SimpleGraph.Walk.support_concat, ← v₂.cons_tail_support]
    simp
  have ht01 : t₀.support.tail.Disjoint t₁.support.tail := by
    rw [List.disjoint_left]
    intro z hz₀ hz₁
    have hz₀' : z ∈ v₀.support.tail ∨ z = D.exteriorVertex 0 := by
      rw [ht₀Tail] at hz₀
      simpa using hz₀
    have hz₁' : z ∈ v₁.support.tail ∨ z = D.exteriorVertex 1 := by
      rw [ht₁Tail] at hz₁
      simpa using hz₁
    rcases hz₀' with hz₀' | hz₀'
    · rcases hz₁' with hz₁' | hz₁'
      · exact hv01 hz₀' hz₁'
      · subst z
        exact D.exterior_notMem 1 (hv₀B _ (List.mem_of_mem_tail hz₀'))
    · rcases hz₁' with hz₁' | hz₁'
      · subst z
        exact D.exterior_notMem 0 (hv₁B _ (List.mem_of_mem_tail hz₁'))
      · exact hy01 (hz₀'.symm.trans hz₁')
  have ht02 : t₀.support.tail.Disjoint t₂.support.tail := by
    rw [List.disjoint_left]
    intro z hz₀ hz₂
    have hz₀' : z ∈ v₀.support.tail ∨ z = D.exteriorVertex 0 := by
      rw [ht₀Tail] at hz₀
      simpa using hz₀
    have hz₂' : z ∈ v₂.support.tail ∨ z = D.exteriorVertex 2 := by
      rw [ht₂Tail] at hz₂
      simpa using hz₂
    rcases hz₀' with hz₀' | hz₀'
    · rcases hz₂' with hz₂' | hz₂'
      · exact hv02 hz₀' hz₂'
      · subst z
        exact D.exterior_notMem 2 (hv₀B _ (List.mem_of_mem_tail hz₀'))
    · rcases hz₂' with hz₂' | hz₂'
      · subst z
        exact D.exterior_notMem 0 (hv₂B _ (List.mem_of_mem_tail hz₂'))
      · exact hy02 (hz₀'.symm.trans hz₂')
  have ht12 : t₁.support.tail.Disjoint t₂.support.tail := by
    rw [List.disjoint_left]
    intro z hz₁ hz₂
    have hz₁' : z ∈ v₁.support.tail ∨ z = D.exteriorVertex 1 := by
      rw [ht₁Tail] at hz₁
      simpa using hz₁
    have hz₂' : z ∈ v₂.support.tail ∨ z = D.exteriorVertex 2 := by
      rw [ht₂Tail] at hz₂
      simpa using hz₂
    rcases hz₁' with hz₁' | hz₁'
    · rcases hz₂' with hz₂' | hz₂'
      · exact hv12 hz₁' hz₂'
      · subst z
        exact D.exterior_notMem 2 (hv₁B _ (List.mem_of_mem_tail hz₁'))
    · rcases hz₂' with hz₂' | hz₂'
      · subst z
        exact D.exterior_notMem 1 (hv₂B _ (List.mem_of_mem_tail hz₂'))
      · exact hy12 (hz₁'.symm.trans hz₂')
  refine ⟨uB.1, uB.2, t₀, t₁, t₂, ht₀Path, ht₁Path, ht₂Path,
    ht₀nil, ht₁nil, ht₂nil, ht01, ht02, ht12, ?_, ?_, ?_⟩
  · intro z hz
    exact hv₀B z (by simpa [t₀] using hz)
  · intro z hz
    exact hv₁B z (by simpa [t₁] using hz)
  · intro z hz
    exact hv₂B z (by simpa [t₂] using hz)

/-- Opening exactly the edges of an exterior tripod, while closing every other edge incident
to its finite box, produces an explicit measurable trifurcation witness. -/
theorem spliceOn_exterior_tripod_mem_strongTrifurcationEvent
    {d : ℕ} {B : Finset (Cubic d)} {omega : EdgeConfiguration d}
    {x : Fin 3 → Cubic d} (D : ExteriorThreeBranchData d B omega x)
    {u : Cubic d} (huB : u ∈ B)
    {t₀ : (cubicGraph d).Walk u (D.exteriorVertex 0)}
    {t₁ : (cubicGraph d).Walk u (D.exteriorVertex 1)}
    {t₂ : (cubicGraph d).Walk u (D.exteriorVertex 2)}
    (hp₀ : t₀.IsPath) (hp₁ : t₁.IsPath) (hp₂ : t₂.IsPath)
    (hn₀ : ¬t₀.Nil) (hn₁ : ¬t₁.Nil) (hn₂ : ¬t₂.Nil)
    (h01 : t₀.support.tail.Disjoint t₁.support.tail)
    (h02 : t₀.support.tail.Disjoint t₂.support.tail)
    (h12 : t₁.support.tail.Disjoint t₂.support.tail)
    (hB₀ : ∀ z ∈ t₀.support.dropLast, z ∈ B)
    (hB₁ : ∀ z ∈ t₁.support.dropLast, z ∈ B)
    (hB₂ : ∀ z ∈ t₂.support.dropLast, z ∈ B) :
    spliceOn (cubicIncidentEdges d B)
        (walkEdgeFinset t₀ ∪ walkEdgeFinset t₁ ∪ walkEdgeFinset t₂) omega ∈
      strongTrifurcationEvent d u := by
  classical
  let E := cubicIncidentEdges d B
  let s := walkEdgeFinset t₀ ∪ walkEdgeFinset t₁ ∪ walkEdgeFinset t₂
  let eta := spliceOn E s omega
  let closed := closeIncidentConfiguration d u eta
  let G := cubicOpenGraph d omega
  let H := G.deleteEdges (underlyingCubicEdges E : Set (Sym2 (Cubic d)))
  let K := cubicOpenGraph d closed
  have ht₀E : walkEdgeFinset t₀ ⊆ E :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₀ hB₀
  have ht₁E : walkEdgeFinset t₁ ⊆ E :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₁ hB₁
  have ht₂E : walkEdgeFinset t₂ ⊆ E :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₂ hB₂
  have hsE : s ⊆ E := by
    intro e he
    simp only [s, Finset.mem_union] at he
    rcases he with (he | he) | he
    · exact ht₀E he
    · exact ht₁E he
    · exact ht₂E he
  have huNotTail₀ : u ∉ t₀.support.tail := by
    have h := hp₀.support_nodup
    rw [← t₀.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have huNotTail₁ : u ∉ t₁.support.tail := by
    have h := hp₁.support_nodup
    rw [← t₁.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have huNotTail₂ : u ∉ t₂.support.tail := by
    have h := hp₂.support_nodup
    rw [← t₂.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have hHnoAdj : ∀ {z w : Cubic d}, z ∈ B → ¬H.Adj z w := by
    intro z w hzB hAdj
    have hdata := SimpleGraph.deleteEdges_adj.mp hAdj
    apply hdata.2
    let ce : CubicEdge d := ⟨s(z, w), by
      rw [SimpleGraph.mem_edgeSet]
      exact (cubicOpenGraph_adj.mp hdata.1).1⟩
    have hceE : ce ∈ E := by
      exact mem_cubicIncidentEdges_of_endpoint hzB (by simp [ce])
    exact (mem_underlyingCubicEdges_iff ce.2).mpr hceE
  have hHoutside (i : Fin 3) (z : Cubic d)
      (hreach : H.Reachable (D.exteriorVertex i) z) : z ∉ B := by
    intro hzB
    obtain ⟨w⟩ := hreach.symm
    cases w with
    | nil => exact D.exterior_notMem i hzB
    | @cons z y v hzy tail => exact hHnoAdj hzB hzy
  have hHleK : H ≤ K := by
    intro z w hAdj
    have hdata := SimpleGraph.deleteEdges_adj.mp hAdj
    have hopen := (cubicOpenGraph_adj.mp hdata.1).2
    have hadjCubic := (cubicOpenGraph_adj.mp hdata.1).1
    let ce : CubicEdge d := ⟨s(z, w), (SimpleGraph.mem_edgeSet _).mpr hadjCubic⟩
    have hceNotE : ce ∉ E := by
      intro hce
      apply hdata.2
      exact (mem_underlyingCubicEdges_iff ce.2).mpr hce
    have hetaOpen : ce ∈ eta := by
      change ce ∈ spliceOn E s omega
      rw [mem_spliceOn]
      exact Or.inr ⟨hopen, hceNotE⟩
    have hzu : z ≠ u := by
      intro h
      subst z
      exact hceNotE (mem_cubicIncidentEdges_of_endpoint huB (by simp [ce]))
    have hwu : w ≠ u := by
      intro h
      subst w
      exact hceNotE (mem_cubicIncidentEdges_of_endpoint huB (by simp [ce]))
    change (cubicOpenGraph d closed).Adj z w
    simp only [closed, cubicOpenGraph_closeIncidentConfiguration,
      SimpleGraph.deleteIncidenceSet_adj]
    exact ⟨cubicOpenGraph_adj.mpr ⟨hadjCubic, hetaOpen⟩, hzu, hwu⟩
  have hTailEndpoints
      {v : Cubic d} {t : (cubicGraph d).Walk u v}
      (hnu : ¬t.Nil) {z w : Cubic d} (hadj : (cubicGraph d).Adj z w)
      (hzu : z ≠ u) (hwu : w ≠ u)
      (he : (⟨s(z, w), (SimpleGraph.mem_edgeSet _).mpr
        hadj⟩ : CubicEdge d) ∈
          walkEdgeFinset t) :
      z ∈ t.support.tail ∧ w ∈ t.support.tail := by
    have he' : s(z, w) ∈ t.edges := (mem_walkEdgeFinset_iff _ _).mp he
    have hzSupport : z ∈ t.support := t.fst_mem_support_of_mem_edges he'
    have hwSupport : w ∈ t.support := t.snd_mem_support_of_mem_edges he'
    rw [← t.cons_tail_support, List.mem_cons] at hzSupport hwSupport
    exact ⟨hzSupport.resolve_left hzu, hwSupport.resolve_left hwu⟩
  have hKadj : ∀ {z w : Cubic d}, K.Adj z w →
      H.Adj z w ∨
        (z ∈ t₀.support.tail ∧ w ∈ t₀.support.tail) ∨
        (z ∈ t₁.support.tail ∧ w ∈ t₁.support.tail) ∨
        (z ∈ t₂.support.tail ∧ w ∈ t₂.support.tail) := by
    intro z w hAdj
    have hclosedAdj : (cubicOpenGraph d eta).Adj z w ∧ z ≠ u ∧ w ≠ u := by
      simpa only [K, closed, cubicOpenGraph_closeIncidentConfiguration,
        SimpleGraph.deleteIncidenceSet_adj] using hAdj
    have hadjCubic := (cubicOpenGraph_adj.mp hclosedAdj.1).1
    have hetaOpen := (cubicOpenGraph_adj.mp hclosedAdj.1).2
    let ce : CubicEdge d := ⟨s(z, w), (SimpleGraph.mem_edgeSet _).mpr hadjCubic⟩
    have hopenData : ce ∈ s ∨ (ce ∈ omega ∧ ce ∉ E) := by
      simpa [eta, mem_spliceOn] using hetaOpen
    rcases hopenData with heS | ⟨heOmega, heNotE⟩
    · simp only [s, Finset.mem_union] at heS
      rcases heS with (he₀ | he₁) | he₂
      · exact Or.inr <| Or.inl <|
          hTailEndpoints hn₀ hadjCubic hclosedAdj.2.1 hclosedAdj.2.2 he₀
      · exact Or.inr <| Or.inr <| Or.inl <|
          hTailEndpoints hn₁ hadjCubic hclosedAdj.2.1 hclosedAdj.2.2 he₁
      · exact Or.inr <| Or.inr <| Or.inr <|
          hTailEndpoints hn₂ hadjCubic hclosedAdj.2.1 hclosedAdj.2.2 he₂
    · apply Or.inl
      simp only [H, SimpleGraph.deleteEdges_adj]
      refine ⟨cubicOpenGraph_adj.mpr ⟨hadjCubic, heOmega⟩, ?_⟩
      exact fun he ↦ heNotE ((mem_underlyingCubicEdges_iff ce.2).mp he)
  have hTailReach
      {v : Cubic d} (t : (cubicGraph d).Walk u v)
      (hp : t.IsPath) (hn : ¬t.Nil) (hts : walkEdgeFinset t ⊆ s) :
      K.Reachable t.snd v := by
    refine ⟨t.tail.transfer K ?_⟩
    intro e he
    induction e using Sym2.ind with
    | _ z w =>
        have hadjCubic : (cubicGraph d).Adj z w :=
          (SimpleGraph.mem_edgeSet _).mp (t.tail.edges_subset_edgeSet he)
        let ce : CubicEdge d := ⟨s(z, w), (SimpleGraph.mem_edgeSet _).mpr hadjCubic⟩
        have heTail : s(z, w) ∈ t.tail.edges := he
        have heWalk : ce ∈ walkEdgeFinset t := by
          rw [mem_walkEdgeFinset_iff]
          rw [← t.cons_tail_eq hn, SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr heTail
        have heS : ce ∈ s := hts heWalk
        have hetaOpen : ce ∈ eta := by
          change ce ∈ spliceOn E s omega
          rw [mem_spliceOn]
          exact Or.inl heS
        have hzTail : z ∈ t.support.tail := by
          rw [← t.support_tail_of_not_nil hn]
          exact t.tail.fst_mem_support_of_mem_edges heTail
        have hwTail : w ∈ t.support.tail := by
          rw [← t.support_tail_of_not_nil hn]
          exact t.tail.snd_mem_support_of_mem_edges heTail
        -- The caller supplies one of the three paths; use its path property to rule out the
        -- centre in its tail independently of which concrete branch it is.
        have huNotTail : u ∉ t.support.tail := by
          have h := hp.support_nodup
          rw [← t.cons_tail_support, List.nodup_cons] at h
          exact h.1
        have hzu' : z ≠ u := fun h ↦ huNotTail (h ▸ hzTail)
        have hwu' : w ≠ u := fun h ↦ huNotTail (h ▸ hwTail)
        rw [SimpleGraph.mem_edgeSet]
        simp only [K, closed, cubicOpenGraph_closeIncidentConfiguration,
          SimpleGraph.deleteIncidenceSet_adj]
        exact ⟨cubicOpenGraph_adj.mpr ⟨hadjCubic, hetaOpen⟩, hzu', hwu'⟩
  have ht₀s : walkEdgeFinset t₀ ⊆ s := fun e he ↦ by
    simp [s, he]
  have ht₁s : walkEdgeFinset t₁ ⊆ s := fun e he ↦ by
    simp [s, he]
  have ht₂s : walkEdgeFinset t₂ ⊆ s := fun e he ↦ by
    simp [s, he]
  have hreach₀ : K.Reachable t₀.snd (D.exteriorVertex 0) :=
    hTailReach t₀ hp₀ hn₀ ht₀s
  have hreach₁ : K.Reachable t₁.snd (D.exteriorVertex 1) :=
    hTailReach t₁ hp₁ hn₁ ht₁s
  have hreach₂ : K.Reachable t₂.snd (D.exteriorVertex 2) :=
    hTailReach t₂ hp₂ hn₂ ht₂s
  have hinf₀ : hasInfiniteOpenClusterFrom d closed t₀.snd := by
    change (cubicOpenClusterFrom d closed t₀.snd).Infinite
    rw [← cubicOpenGraph_component_supp]
    apply (D.exterior_infinite 0).mono
    intro z hz
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact (hreach₀.trans (hz.mono hHleK)).symm
  have hinf₁ : hasInfiniteOpenClusterFrom d closed t₁.snd := by
    change (cubicOpenClusterFrom d closed t₁.snd).Infinite
    rw [← cubicOpenGraph_component_supp]
    apply (D.exterior_infinite 1).mono
    intro z hz
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact (hreach₁.trans (hz.mono hHleK)).symm
  have hinf₂ : hasInfiniteOpenClusterFrom d closed t₂.snd := by
    change (cubicOpenClusterFrom d closed t₂.snd).Infinite
    rw [← cubicOpenGraph_component_supp]
    apply (D.exterior_infinite 2).mono
    intro z hz
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact (hreach₂.trans (hz.mono hHleK)).symm
  let L : Fin 3 → List (Cubic d) :=
    ![t₀.support.tail, t₁.support.tail, t₂.support.tail]
  let root : Fin 3 → Cubic d := ![t₀.snd, t₁.snd, t₂.snd]
  let endVertex : Fin 3 → Cubic d :=
    ![D.exteriorVertex 0, D.exteriorVertex 1, D.exteriorVertex 2]
  have hroot : ∀ i, root i ∈ L i := by
    intro i
    fin_cases i
    · exact t₀.snd_mem_tail_support hn₀
    · exact t₁.snd_mem_tail_support hn₁
    · exact t₂.snd_mem_tail_support hn₂
  have hLdisjoint : ∀ i j, i ≠ j → (L i).Disjoint (L j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [L, List.disjoint_comm]
  have hLvertex : ∀ i z, z ∈ L i → z ∈ (B : Set (Cubic d)) ∨ z = endVertex i := by
    intro i z hz
    fin_cases i
    · by_cases hzend : z = D.exteriorVertex 0
      · exact Or.inr hzend
      · apply Or.inl
        exact hB₀ z (List.mem_dropLast_of_mem_of_ne_getLast
          (List.mem_of_mem_tail hz) (by simpa using hzend))
    · by_cases hzend : z = D.exteriorVertex 1
      · exact Or.inr hzend
      · apply Or.inl
        exact hB₁ z (List.mem_dropLast_of_mem_of_ne_getLast
          (List.mem_of_mem_tail hz) (by simpa using hzend))
    · by_cases hzend : z = D.exteriorVertex 2
      · exact Or.inr hzend
      · apply Or.inl
        exact hB₂ z (List.mem_dropLast_of_mem_of_ne_getLast
          (List.mem_of_mem_tail hz) (by simpa using hzend))
  have hSepK : ∀ i j, i ≠ j → ¬K.Reachable (root i) (root j) := by
    apply tripodBranches_not_reachable L root endVertex hroot hLdisjoint hLvertex
    · exact hHnoAdj
    · intro i z hz
      fin_cases i
      · simpa [endVertex] using hHoutside (0 : Fin 3) z hz
      · simpa [endVertex] using hHoutside (1 : Fin 3) z hz
      · simpa [endVertex] using hHoutside (2 : Fin 3) z hz
    · intro i j hij
      have hend (k : Fin 3) : endVertex k = D.exteriorVertex k := by
        fin_cases k <;> rfl
      simpa only [hend] using D.exterior_separate i j hij
    · intro z w hAdj
      rcases hKadj hAdj with hH | h₀ | h₁ | h₂
      · exact Or.inl hH
      · exact Or.inr ⟨0, by simpa [L] using h₀.1, by simpa [L] using h₀.2⟩
      · exact Or.inr ⟨1, by simpa [L] using h₁.1, by simpa [L] using h₁.2⟩
      · exact Or.inr ⟨2, by simpa [L] using h₂.1, by simpa [L] using h₂.2⟩
  obtain ⟨a₀, ha₀⟩ := (cubicGraph_adj_iff_exists_stepFrom u t₀.snd).mp
    (t₀.adj_snd hn₀)
  obtain ⟨a₁, ha₁⟩ := (cubicGraph_adj_iff_exists_stepFrom u t₁.snd).mp
    (t₁.adj_snd hn₁)
  obtain ⟨a₂, ha₂⟩ := (cubicGraph_adj_iff_exists_stepFrom u t₂.snd).mp
    (t₂.adj_snd hn₂)
  let a : Fin 3 → CubicDirection d := ![a₀, a₁, a₂]
  rw [strongTrifurcationEvent, Set.mem_iUnion]
  refine ⟨a, mem_trifurcationDirectionWitnessEvent_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro e heIncident
    have heE : e ∈ E := by
      obtain ⟨z, hz, hze⟩ :=
        mem_cubicIncidentEdges_iff_exists_endpoint.mp heIncident
      simp only [Finset.mem_singleton] at hz
      subst z
      exact mem_cubicIncidentEdges_of_endpoint huB hze
    change (e ∈ spliceOn E s omega ↔ e ∈ trifurcationDirectionEdges d u a)
    rw [mem_spliceOn_of_mem heE]
    constructor
    · intro heS
      simp only [s, Finset.mem_union] at heS
      have hue : u ∈ (e : Sym2 (Cubic d)) := by
        obtain ⟨z, hz, hze⟩ :=
          mem_cubicIncidentEdges_iff_exists_endpoint.mp heIncident
        have hzu : z = u := Finset.mem_singleton.mp hz
        subst z
        exact hze
      rcases heS with (he₀ | he₁) | he₂
      · have heq := (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₀ hn₀ hue).mp he₀
        subst e
        apply Finset.mem_image.mpr
        refine ⟨0, by simp, ?_⟩
        apply Subtype.ext
        change s(u, cubicStepFrom u a₀) = s(u, t₀.snd)
        rw [ha₀]
      · have heq := (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₁ hn₁ hue).mp he₁
        subst e
        apply Finset.mem_image.mpr
        refine ⟨1, by simp, ?_⟩
        apply Subtype.ext
        change s(u, cubicStepFrom u a₁) = s(u, t₁.snd)
        rw [ha₁]
      · have heq := (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₂ hn₂ hue).mp he₂
        subst e
        apply Finset.mem_image.mpr
        refine ⟨2, by simp, ?_⟩
        apply Subtype.ext
        change s(u, cubicStepFrom u a₂) = s(u, t₂.snd)
        rw [ha₂]
    · intro heDir
      obtain ⟨i, _hi, hei⟩ := Finset.mem_image.mp heDir
      fin_cases i
      · have heq : e = walkFirstCubicEdge t₀ hn₀ := by
          apply Subtype.ext
          simpa [a, walkFirstCubicEdge, cubicStepEdge, ha₀] using
            (congrArg Subtype.val hei).symm
        simp [s, heq,
          (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₀ hn₀ (by
            simpa [heq, walkFirstCubicEdge])).2 rfl]
      · have heq : e = walkFirstCubicEdge t₁ hn₁ := by
          apply Subtype.ext
          simpa [a, walkFirstCubicEdge, cubicStepEdge, ha₁] using
            (congrArg Subtype.val hei).symm
        simp [s, heq,
          (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₁ hn₁ (by
            simpa [heq, walkFirstCubicEdge])).2 rfl]
      · have heq : e = walkFirstCubicEdge t₂ hn₂ := by
          apply Subtype.ext
          simpa [a, walkFirstCubicEdge, cubicStepEdge, ha₂] using
            (congrArg Subtype.val hei).symm
        simp [s, heq,
          (mem_walkEdgeFinset_of_isPath_of_mem_start_iff hp₂ hn₂ (by
            simpa [heq, walkFirstCubicEdge])).2 rfl]
  · intro i
    fin_cases i
    · change hasInfiniteOpenClusterFrom d closed (cubicStepFrom u a₀)
      simpa only [ha₀] using hinf₀
    · change hasInfiniteOpenClusterFrom d closed (cubicStepFrom u a₁)
      simpa only [ha₁] using hinf₁
    · change hasInfiniteOpenClusterFrom d closed (cubicStepFrom u a₂)
      simpa only [ha₂] using hinf₂
  · intro i j hij hconn
    have hconnK : K.Reachable (root i) (root j) := by
      have hreach := cubicOpenGraph_reachable_iff.mpr hconn
      change (cubicOpenGraph d closed).Reachable
        (cubicStepFrom u (a i)) (cubicStepFrom u (a j)) at hreach
      have hrootStep (k : Fin 3) : root k = cubicStepFrom u (a k) := by
        fin_cases k <;> simp [root, a, ← ha₀, ← ha₁, ← ha₂]
      simpa only [K, hrootStep] using hreach
    exact hSepK i j hij hconnK

/-- Pointwise finite-energy surgery.  Given three distinct infinite clusters represented inside
a finite connected region, one can prescribe a finite edge trace in that region which turns
some vertex of the region into a strong trifurcation. -/
theorem exists_spliceOn_mem_strongTrifurcationEvent_of_witness
    {d : ℕ} {B : Finset (Cubic d)} {omega : EdgeConfiguration d}
    {x : Fin 3 → Cubic d}
    (hBconn : (cubicRegionGraph d (B : Set (Cubic d))).Connected)
    (hxB : ∀ i, x i ∈ B)
    (hwitness : omega ∈ infiniteOpenClusterWitnessEvent x) :
    ∃ u ∈ B, ∃ trace ⊆ cubicIncidentEdges d B,
      spliceOn (cubicIncidentEdges d B) trace omega ∈
        strongTrifurcationEvent d u := by
  classical
  let D := Classical.choice (exists_exteriorThreeBranchData B hxB hwitness)
  obtain ⟨u, huB, t₀, t₁, t₂, hp₀, hp₁, hp₂, hn₀, hn₁, hn₂,
      h01, h02, h12, hB₀, hB₁, hB₂⟩ := exists_exterior_tripod D hBconn
  let trace := walkEdgeFinset t₀ ∪ walkEdgeFinset t₁ ∪ walkEdgeFinset t₂
  have ht₀ : walkEdgeFinset t₀ ⊆ cubicIncidentEdges d B :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₀ hB₀
  have ht₁ : walkEdgeFinset t₁ ⊆ cubicIncidentEdges d B :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₁ hB₁
  have ht₂ : walkEdgeFinset t₂ ⊆ cubicIncidentEdges d B :=
    walkEdgeFinset_subset_cubicIncidentEdges_of_dropLast_support t₂ hB₂
  have htrace : trace ⊆ cubicIncidentEdges d B := by
    intro e he
    simp only [trace, Finset.mem_union] at he
    rcases he with (he | he) | he
    · exact ht₀ he
    · exact ht₁ he
    · exact ht₂ he
  refine ⟨u, huB, trace, htrace, ?_⟩
  exact spliceOn_exterior_tripod_mem_strongTrifurcationEvent D huB
    hp₀ hp₁ hp₂ hn₀ hn₁ hn₂ h01 h02 h12 hB₀ hB₁ hB₂

/-- Probabilistic finite-energy extraction from the pointwise surgery theorem.  Positive
probability of a fixed three-cluster witness inside a finite connected region forces positive
probability of a strong trifurcation at one fixed vertex of that region. -/
theorem exists_strongTrifurcation_measureReal_pos_of_witness
    {d : ℕ} {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {B : Finset (Cubic d)} {x : Fin 3 → Cubic d}
    (hBconn : (cubicRegionGraph d (B : Set (Cubic d))).Connected)
    (hxB : ∀ i, x i ∈ B)
    (hpos : 0 < (bernoulliBondMeasure d p).real
      (infiniteOpenClusterWitnessEvent x)) :
    ∃ u ∈ B, 0 < (bernoulliBondMeasure d p).real
      (strongTrifurcationEvent d u) := by
  classical
  let μ := bernoulliBondMeasure d p
  let E := cubicIncidentEdges d B
  let A := infiniteOpenClusterWitnessEvent x
  let F (u : Cubic d) (trace : Finset (CubicEdge d)) : Set (EdgeConfiguration d) :=
    (fun omega ↦ spliceOn E trace omega) ⁻¹' strongTrifurcationEvent d u
  have hcover : A ⊆ ⋃ u ∈ B, ⋃ trace ∈ E.powerset, F u trace := by
    intro omega homega
    obtain ⟨u, huB, trace, htrace, hstrong⟩ :=
      exists_spliceOn_mem_strongTrifurcationEvent_of_witness hBconn hxB homega
    rw [Set.mem_iUnion]
    refine ⟨u, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨huB, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨trace, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_powerset.mpr htrace, hstrong⟩
  have hpre : ∃ u ∈ B, ∃ trace ⊆ E, 0 < μ.real (F u trace) := by
    by_contra hnone
    push_neg at hnone
    have htermZero (u : Cubic d) (hu : u ∈ B)
        (trace : Finset (CubicEdge d)) (htrace : trace ⊆ E) :
        μ.real (F u trace) = 0 :=
      le_antisymm (hnone u hu trace htrace) measureReal_nonneg
    have hinnerZero (u : Cubic d) (hu : u ∈ B) :
        μ.real (⋃ trace ∈ E.powerset, F u trace) = 0 := by
      apply le_antisymm
      · refine (measureReal_biUnion_finset_le E.powerset (F u)).trans ?_
        rw [Finset.sum_eq_zero]
        intro trace htrace
        exact htermZero u hu trace (Finset.mem_powerset.mp htrace)
      · exact measureReal_nonneg
    have hunionZero : μ.real (⋃ u ∈ B, ⋃ trace ∈ E.powerset, F u trace) = 0 := by
      apply le_antisymm
      · refine (measureReal_biUnion_finset_le B
          (fun u ↦ ⋃ trace ∈ E.powerset, F u trace)).trans ?_
        rw [Finset.sum_eq_zero]
        intro u hu
        exact hinnerZero u hu
      · exact measureReal_nonneg
    have hAle : μ.real A ≤ 0 := by
      calc
        μ.real A ≤ μ.real (⋃ u ∈ B, ⋃ trace ∈ E.powerset, F u trace) :=
          measureReal_mono hcover (measure_ne_top μ _)
        _ = 0 := hunionZero
    exact (not_le_of_gt (by simpa [μ, A] using hpos)) hAle
  obtain ⟨u, huB, trace, htrace, hprePos⟩ := hpre
  have hstrongMeas := measurableSet_strongTrifurcationEvent d u
  have hfactor := setBernoulli_real_inter_finiteCylinder
    (ι := CubicEdge d) p htrace hstrongMeas
  change μ.real (strongTrifurcationEvent d u ∩ finiteCylinder E trace) =
    μ.real (F u trace) * finiteBernoulliWeight E (p : ℝ) trace at hfactor
  have hweight : 0 < finiteBernoulliWeight E (p : ℝ) trace :=
    finiteBernoulliWeight_pos hp0 hp1 trace
  have hinterPos : 0 < μ.real
      (strongTrifurcationEvent d u ∩ finiteCylinder E trace) := by
    rw [hfactor]
    exact mul_pos hprePos hweight
  refine ⟨u, huB, ?_⟩
  exact hinterPos.trans_le (measureReal_mono Set.inter_subset_left)

@[simp]
theorem mem_trifurcationEvent_iff {d : ℕ} {x : Cubic d} {omega : EdgeConfiguration d} :
    omega ∈ trifurcationEvent d x ↔ isOpenTrifurcation d omega x :=
  Iff.rfl

theorem trifurcationBranchComponents_encard_eq_three
    {V : Type*} {G : SimpleGraph V} {x : V}
    (hx : IsTrifurcationVertex G x) :
    (trifurcationBranchComponents G x).encard = 3 :=
  hx.2

theorem neighborSet_encard_eq_three_of_isTrifurcationVertex
    {V : Type*} {G : SimpleGraph V} {x : V}
    (hx : IsTrifurcationVertex G x) : (G.neighborSet x).encard = 3 :=
  hx.1

/-- Every trifurcation branch has an adjacent representative at the deleted vertex. -/
theorem exists_adjacent_of_mem_trifurcationBranchComponents
    {V : Type*} {G : SimpleGraph V} {x : V}
    {C : (G.deleteIncidenceSet x).ConnectedComponent}
    (hC : C ∈ trifurcationBranchComponents G x) :
    ∃ y, G.Adj x y ∧ (G.deleteIncidenceSet x).connectedComponentMk y = C :=
  hC.2

/-- A branch component is infinite. -/
theorem infinite_of_mem_trifurcationBranchComponents
    {V : Type*} {G : SimpleGraph V} {x : V}
    {C : (G.deleteIncidenceSet x).ConnectedComponent}
    (hC : C ∈ trifurcationBranchComponents G x) : C.supp.Infinite :=
  hC.1

/-- A walk none of whose vertices is `x` remains a walk after deleting the incidence set of
`x`. -/
theorem deleteIncidenceSet_reachable_of_walk_not_mem_support
    {V : Type*} {G : SimpleGraph V} {x a b : V} (w : G.Walk a b)
    (hx : x ∉ w.support) : (G.deleteIncidenceSet x).Reachable a b := by
  induction w with
  | nil => exact .rfl
  | @cons u v b huv tail ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hx
      have hadj : (G.deleteIncidenceSet x).Adj u v :=
        SimpleGraph.deleteIncidenceSet_adj.mpr
          ⟨huv, (fun h ↦ hx.1 h.symm), fun h ↦ hx.2 (h ▸ tail.start_mem_support)⟩
      exact hadj.reachable.trans (ih hx.2)

/-- The first edge of a nontrivial simple path gives a neighbor which remains connected to the
endpoint after deleting the incidence set of the starting vertex. -/
theorem exists_neighbor_reachable_deleteIncidenceSet
    {V : Type*} {G : SimpleGraph V} {x z : V} (hxz : x ≠ z)
    (hreach : G.Reachable x z) :
    ∃ u, G.Adj x u ∧ (G.deleteIncidenceSet x).Reachable u z := by
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  cases p with
  | nil => exact (hxz rfl).elim
  | @cons _ u _ hxu tail =>
      have hxTail : x ∉ tail.support := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
        exact hnodup.1
      exact ⟨u, hxu,
        deleteIncidenceSet_reachable_of_walk_not_mem_support tail hxTail⟩

/-- At a trifurcation, every neighbor belongs to one of the three infinite branches. -/
theorem connectedComponentMk_mem_trifurcationBranchComponents_of_adj
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (hx : IsTrifurcationVertex G x) (hxy : G.Adj x y) :
    (G.deleteIncidenceSet x).connectedComponentMk y ∈
      trifurcationBranchComponents G x := by
  let H := G.deleteIncidenceSet x
  let R : Set H.ConnectedComponent :=
    (fun z ↦ H.connectedComponentMk z) '' G.neighborSet x
  have hBR : trifurcationBranchComponents G x ⊆ R := by
    intro C hC
    obtain ⟨z, hxz, hzC⟩ := hC.2
    exact ⟨z, hxz, hzC⟩
  have hRcard : R.encard ≤ 3 := by
    calc
      R.encard ≤ (G.neighborSet x).encard := by
        simpa [R] using Set.encard_image_le
          (fun z ↦ H.connectedComponentMk z) (G.neighborSet x)
      _ = 3 := hx.1
  have hBfinite : (trifurcationBranchComponents G x).Finite :=
    Set.finite_of_encard_eq_coe hx.2
  have hEq : trifurcationBranchComponents G x = R :=
    hBfinite.eq_of_subset_of_encard_le hBR (by simpa [hx.2] using hRcard)
  rw [hEq]
  exact ⟨y, hxy, rfl⟩

/-- Every nondeleted vertex in the original component of a trifurcation lies in one of its three
infinite branches. -/
theorem connectedComponentMk_mem_trifurcationBranchComponents_of_reachable_from
    {V : Type*} {G : SimpleGraph V} {x y : V}
    (hx : IsTrifurcationVertex G x) (hxy : x ≠ y) (hreach : G.Reachable x y) :
    (G.deleteIncidenceSet x).connectedComponentMk y ∈
      trifurcationBranchComponents G x := by
  obtain ⟨u, hxu, huy⟩ :=
    exists_neighbor_reachable_deleteIncidenceSet hxy hreach
  have huBranch :=
    connectedComponentMk_mem_trifurcationBranchComponents_of_adj hx hxu
  have hcomp : (G.deleteIncidenceSet x).connectedComponentMk u =
      (G.deleteIncidenceSet x).connectedComponentMk y :=
    SimpleGraph.ConnectedComponent.sound huy
  rwa [hcomp] at huBranch

/-- Restricting deletion-connectivity to a finite set which meets every infinite branch gives a
three-partition.  This is the abstract construction used for the boundary partition `Π(x)` in
Grimmett's proof. -/
noncomputable def trifurcationBoundaryPartition
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V} (Y : Finset V)
    (hx : IsTrifurcationVertex G x)
    (hYbranch : ∀ y ∈ Y,
      (G.deleteIncidenceSet x).connectedComponentMk y ∈
        trifurcationBranchComponents G x)
    (hbranchY : ∀ C ∈ trifurcationBranchComponents G x,
      ∃ y ∈ Y, (G.deleteIncidenceSet x).connectedComponentMk y = C) :
    ThreePartition Y := by
  classical
  let H := G.deleteIncidenceSet x
  let P : Finpartition Y := Finpartition.ofSetSetoid H.reachableSetoid Y
  have hbranchesFinite : (trifurcationBranchComponents G x).Finite :=
    Set.finite_of_encard_eq_coe hx.2
  letI : Fintype {C // C ∈ trifurcationBranchComponents G x} :=
    hbranchesFinite.fintype
  let rep : {A // A ∈ P.parts} → V := fun A ↦
    Classical.choose (P.nonempty_of_mem_parts A.2)
  have hrepMem (A : {A // A ∈ P.parts}) : rep A ∈ A.1 :=
    Classical.choose_spec (P.nonempty_of_mem_parts A.2)
  have hrepY (A : {A // A ∈ P.parts}) : rep A ∈ Y :=
    P.le A.2 (hrepMem A)
  let f : {A // A ∈ P.parts} →
      {C // C ∈ trifurcationBranchComponents G x} := fun A ↦
    ⟨H.connectedComponentMk (rep A), hYbranch (rep A) (hrepY A)⟩
  have hfInj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    apply P.eq_of_mem_parts A.2 B.2 (hrepMem A)
    have hcomp : H.connectedComponentMk (rep B) = H.connectedComponentMk (rep A) := by
      exact (congrArg Subtype.val hAB).symm
    have hreach : H.Reachable (rep B) (rep A) :=
      SimpleGraph.ConnectedComponent.eq.mp hcomp
    have hmemPart : rep A ∈ P.part (rep B) := by
      exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mpr
        ⟨hrepY B, hrepY A, hreach⟩
    rwa [P.part_eq_of_mem B.2 (hrepMem B)] at hmemPart
  have hfSurj : Function.Surjective f := by
    intro C
    obtain ⟨y, hyY, hyC⟩ := hbranchY C C.2
    let A : {A // A ∈ P.parts} := ⟨P.part y, P.part_mem.mpr hyY⟩
    refine ⟨A, ?_⟩
    apply Subtype.ext
    have hrepPart : rep A ∈ P.part y := by
      simpa [A] using hrepMem A
    have hreach : H.Reachable y (rep A) := by
      exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mp hrepPart |>.2.2
    change H.connectedComponentMk (rep A) = C.1
    rw [← hyC]
    exact SimpleGraph.ConnectedComponent.sound hreach.symm
  refine ⟨P, ?_⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hfInj, hfSurj⟩)
  change Fintype.card {A // A ∈ P.parts} =
    Fintype.card {C // C ∈ trifurcationBranchComponents G x} at hcard
  rw [Fintype.card_coe] at hcard
  calc
    P.parts.card = Fintype.card {C // C ∈ trifurcationBranchComponents G x} := hcard
    _ = (trifurcationBranchComponents G x).encard.toNat := by
      rw [Set.encard, ENat.card_eq_coe_fintype_card, ENat.toNat_coe]
    _ = 3 := by rw [hx.2, ENat.toNat_ofNat]

/-- A path avoiding the incidence set of `x` also avoids the incidence set of `z` when `z`
cannot reach the endpoint along the first deleted graph. -/
theorem deleteIncidenceSet_reachable_of_reachable_of_not_reachable
    {V : Type*} {G : SimpleGraph V} {x z a b : V}
    (hab : (G.deleteIncidenceSet x).Reachable a b)
    (hzb : ¬(G.deleteIncidenceSet x).Reachable z b) :
    (G.deleteIncidenceSet z).Reachable a b := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact .rfl
  | @cons u v b huv tail ih =>
      have hub : (G.deleteIncidenceSet x).Reachable u b :=
        ⟨SimpleGraph.Walk.cons huv tail⟩
      have huz : u ≠ z := fun h ↦ hzb (h ▸ hub)
      have hvb : (G.deleteIncidenceSet x).Reachable v b := ⟨tail⟩
      have hvz : v ≠ z := fun h ↦ hzb (h ▸ hvb)
      have hadjG : G.Adj u v :=
        (SimpleGraph.deleteIncidenceSet_adj.mp huv).1
      have hadj : (G.deleteIncidenceSet z).Adj u v :=
        SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hadjG, huz, hvz⟩
      exact hadj.reachable.trans (ih hzb)

/-- Distinct trifurcations in the same component lie in infinite branches of one another. -/
theorem connectedComponentMk_mem_trifurcationBranchComponents_of_reachable
    {V : Type*} {G : SimpleGraph V}
    {x z : V} (hxz : x ≠ z) (hz : IsTrifurcationVertex G z)
    (hreach : G.Reachable x z) :
    (G.deleteIncidenceSet x).connectedComponentMk z ∈
      trifurcationBranchComponents G x := by
  classical
  let Hx := G.deleteIncidenceSet x
  let Hz := G.deleteIncidenceSet z
  have hthree : (trifurcationBranchComponents G z).encard = 3 := hz.2
  have hone : 1 < (trifurcationBranchComponents G z).encard := by
    rw [hthree]
    norm_num
  obtain ⟨C, hCbranch, hCne⟩ := Set.exists_ne_of_one_lt_encard hone
    (Hz.connectedComponentMk x)
  obtain ⟨y, hzy, hyC⟩ :=
    exists_adjacent_of_mem_trifurcationBranchComponents hCbranch
  have hyx : y ≠ x := by
    intro h
    apply hCne
    rw [← hyC, h]
  have hzyX : Hx.Reachable z y :=
    (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hzy, hxz.symm, hyx⟩).reachable
  have hCsubset : C.supp ⊆ (Hx.connectedComponentMk z).supp := by
    intro v hv
    have hvComp : Hz.connectedComponentMk v = C := (C.mem_supp_iff v).mp hv
    have hyv : Hz.Reachable y v := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      exact hyC.trans hvComp.symm
    have hnotxv : ¬Hz.Reachable x v := by
      intro hxv
      apply hCne
      have hxComp : Hz.connectedComponentMk x = Hz.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.sound hxv
      exact (hxComp.trans hvComp).symm
    have hyvX : Hx.Reachable y v :=
      deleteIncidenceSet_reachable_of_reachable_of_not_reachable hyv hnotxv
    exact (Hx.connectedComponentMk z).mem_supp_iff v |>.mpr
      (SimpleGraph.ConnectedComponent.sound (hzyX.trans hyvX)).symm
  have hinfinite : (Hx.connectedComponentMk z).supp.Infinite :=
    (infinite_of_mem_trifurcationBranchComponents hCbranch).mono hCsubset
  obtain ⟨u, hxu, huz⟩ :=
    exists_neighbor_reachable_deleteIncidenceSet hxz hreach
  refine ⟨hinfinite, u, hxu, ?_⟩
  exact SimpleGraph.ConnectedComponent.sound huz

/-- Boundary partitions induced by two distinct trifurcations in the same cluster are compatible.
The two branch hypotheses say that each trifurcation lies in an infinite branch of the other. -/
theorem trifurcationBoundaryPartition_compatible
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x z : V} (hxz : x ≠ z) (Y : Finset V)
    (hx : IsTrifurcationVertex G x) (hz : IsTrifurcationVertex G z)
    (hYx : ∀ y ∈ Y,
      (G.deleteIncidenceSet x).connectedComponentMk y ∈
        trifurcationBranchComponents G x)
    (hxY : ∀ C ∈ trifurcationBranchComponents G x,
      ∃ y ∈ Y, (G.deleteIncidenceSet x).connectedComponentMk y = C)
    (hYz : ∀ y ∈ Y,
      (G.deleteIncidenceSet z).connectedComponentMk y ∈
        trifurcationBranchComponents G z)
    (hzY : ∀ C ∈ trifurcationBranchComponents G z,
      ∃ y ∈ Y, (G.deleteIncidenceSet z).connectedComponentMk y = C)
    (hzBranchX : (G.deleteIncidenceSet x).connectedComponentMk z ∈
      trifurcationBranchComponents G x)
    (hxBranchZ : (G.deleteIncidenceSet z).connectedComponentMk x ∈
      trifurcationBranchComponents G z) :
    (trifurcationBoundaryPartition Y hx hYx hxY).Compatible
      (trifurcationBoundaryPartition Y hz hYz hzY) := by
  classical
  let Hx := G.deleteIncidenceSet x
  let Hz := G.deleteIncidenceSet z
  let P := trifurcationBoundaryPartition Y hx hYx hxY
  let Q := trifurcationBoundaryPartition Y hz hYz hzY
  obtain ⟨yx, hyxY, hyxComp⟩ := hxY _ hzBranchX
  obtain ⟨yz, hyzY, hyzComp⟩ := hzY _ hxBranchZ
  let A := P.partition.part yx
  let B := Q.partition.part yz
  have hAParts : A ∈ P.parts := P.partition.part_mem.mpr hyxY
  have hBParts : B ∈ Q.parts := Q.partition.part_mem.mpr hyzY
  refine ⟨A, hAParts, B, hBParts, ?_, ?_⟩
  · intro y hy
    obtain ⟨hyY, hyA⟩ := Finset.mem_sdiff.mp hy
    have hnotReachZX : ¬Hx.Reachable z y := by
      intro hzy
      have hyxReachZ : Hx.Reachable yx z :=
        SimpleGraph.ConnectedComponent.eq.mp hyxComp
      have hyxReachY : Hx.Reachable yx y := hyxReachZ.trans hzy
      apply hyA
      change y ∈ P.partition.part yx
      exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mpr
        ⟨hyxY, hyY, hyxReachY⟩
    have hyBranch := hYx y hyY
    obtain ⟨u, hxu, huComp⟩ :=
      exists_adjacent_of_mem_trifurcationBranchComponents hyBranch
    have huy : Hx.Reachable u y :=
      SimpleGraph.ConnectedComponent.eq.mp huComp
    have huz : u ≠ z := by
      intro h
      apply hnotReachZX
      simpa [h] using huy
    have huyZ : Hz.Reachable u y :=
      deleteIncidenceSet_reachable_of_reachable_of_not_reachable huy hnotReachZX
    have hxuZ : Hz.Reachable x u :=
      (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hxu, hxz, huz⟩).reachable
    have hyzReachX : Hz.Reachable yz x :=
      SimpleGraph.ConnectedComponent.eq.mp hyzComp
    have hyzReachY : Hz.Reachable yz y := hyzReachX.trans (hxuZ.trans huyZ)
    change y ∈ Q.partition.part yz
    exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mpr
      ⟨hyzY, hyY, hyzReachY⟩
  · intro y hy
    obtain ⟨hyY, hyB⟩ := Finset.mem_sdiff.mp hy
    have hnotReachXZ : ¬Hz.Reachable x y := by
      intro hxy
      have hyzReachX : Hz.Reachable yz x :=
        SimpleGraph.ConnectedComponent.eq.mp hyzComp
      have hyzReachY : Hz.Reachable yz y := hyzReachX.trans hxy
      apply hyB
      change y ∈ Q.partition.part yz
      exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mpr
        ⟨hyzY, hyY, hyzReachY⟩
    have hyBranch := hYz y hyY
    obtain ⟨u, hzu, huComp⟩ :=
      exists_adjacent_of_mem_trifurcationBranchComponents hyBranch
    have huy : Hz.Reachable u y :=
      SimpleGraph.ConnectedComponent.eq.mp huComp
    have hux : u ≠ x := by
      intro h
      apply hnotReachXZ
      simpa [h] using huy
    have huyX : Hx.Reachable u y :=
      deleteIncidenceSet_reachable_of_reachable_of_not_reachable huy hnotReachXZ
    have hzxX : Hx.Reachable z u :=
      (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hzu, hxz.symm, hux⟩).reachable
    have hyxReachZ : Hx.Reachable yx z :=
      SimpleGraph.ConnectedComponent.eq.mp hyxComp
    have hyxReachY : Hx.Reachable yx y := hyxReachZ.trans (hzxX.trans huyX)
    change y ∈ P.partition.part yx
    exact (Finpartition.mem_part_ofSetSetoid_iff_rel Y).mpr
      ⟨hyxY, hyY, hyxReachY⟩

/-! ### Cubic boundary partitions -/

/-- A nearest-neighbor walk which starts weakly inside and ends weakly outside a Manhattan
sphere visits that sphere.  The ambient walk may live in any subgraph of the cubic lattice. -/
theorem exists_mem_walk_support_cubicL1Dist_eq_of_le_of_ge
    {d n : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {root u v : Cubic d} (w : G.Walk u v)
    (hu : cubicL1Dist root u ≤ n) (hv : n ≤ cubicL1Dist root v) :
    ∃ y ∈ w.support, cubicL1Dist root y = n := by
  induction w with
  | nil =>
      exact ⟨_, by simp, le_antisymm hu hv⟩
  | @cons u₀ u₁ v₀ hu₀u₁ tail ih =>
      by_cases hlevel : cubicL1Dist root u₀ = n
      · exact ⟨u₀, by simp, hlevel⟩
      · have hlt : cubicL1Dist root u₀ < n := lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hu₁ : cubicL1Dist root u₁ ≤ n := by
          calc
            cubicL1Dist root u₁ ≤
                cubicL1Dist root u₀ + cubicL1Dist u₀ u₁ :=
              cubicL1Dist_triangle _ _ _
            _ = cubicL1Dist root u₀ + 1 := by
              rw [ha, cubicL1Dist_stepFrom]
            _ ≤ n := by omega
        obtain ⟨y, hyTail, hyDist⟩ := ih hu₁ hv
        exact ⟨y, by simp [hyTail], hyDist⟩

/-- Vertices of a fixed open connected component lying on the origin-centered metric sphere. -/
noncomputable def openComponentMetricSphere
    (d : ℕ) (omega : EdgeConfiguration d)
    (K : (cubicOpenGraph d omega).ConnectedComponent) (n : ℕ) : Finset (Cubic d) :=
  by
    classical
    exact (cubicMetricSphere d cubicOrigin n).filter fun y ↦
      (cubicOpenGraph d omega).connectedComponentMk y = K

@[simp]
theorem mem_openComponentMetricSphere_iff
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {y : Cubic d} :
    y ∈ openComponentMetricSphere d omega K n ↔
      cubicL1Dist cubicOrigin y = n ∧
        (cubicOpenGraph d omega).connectedComponentMk y = K := by
  classical
  rw [openComponentMetricSphere, Finset.mem_filter,
    mem_cubicMetricSphere_iff_l1Dist_eq]

/-- Every infinite branch of an interior trifurcation reaches the common component boundary on
the outer metric sphere. -/
theorem exists_openComponentMetricSphere_in_trifurcationBranch
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d}
    (hn : 1 ≤ n)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBall : cubicL1Dist cubicOrigin x ≤ n - 1)
    {C : ((cubicOpenGraph d omega).deleteIncidenceSet x).ConnectedComponent}
    (hC : C ∈ trifurcationBranchComponents (cubicOpenGraph d omega) x) :
    ∃ y ∈ openComponentMetricSphere d omega K n,
      ((cubicOpenGraph d omega).deleteIncidenceSet x).connectedComponentMk y = C := by
  classical
  let G := cubicOpenGraph d omega
  let H := G.deleteIncidenceSet x
  obtain ⟨u, hxu, huC⟩ :=
    exists_adjacent_of_mem_trifurcationBranchComponents hC
  have huBall : cubicL1Dist cubicOrigin u ≤ n := by
    have hadj : (cubicGraph d).Adj x u := (cubicOpenGraph_adj.mp hxu).choose
    obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom x u).mp hadj
    calc
      cubicL1Dist cubicOrigin u ≤
          cubicL1Dist cubicOrigin x + cubicL1Dist x u :=
        cubicL1Dist_triangle _ _ _
      _ = cubicL1Dist cubicOrigin x + 1 := by
        rw [ha, cubicL1Dist_stepFrom]
      _ ≤ n := by omega
  have hnotSubset : ¬C.supp ⊆ (cubicMetricBall d cubicOrigin n : Set (Cubic d)) := by
    intro hsub
    exact (infinite_of_mem_trifurcationBranchComponents hC)
      ((cubicMetricBall d cubicOrigin n).finite_toSet.subset hsub)
  obtain ⟨v, hvC, hvOutside⟩ := Set.not_subset.mp hnotSubset
  have hvFar : n ≤ cubicL1Dist cubicOrigin v := by
    have hnotle : ¬cubicL1Dist cubicOrigin v ≤ n := by
      intro hle
      exact hvOutside (mem_cubicMetricBall_iff_l1Dist_le.mpr hle)
    omega
  have huv : H.Reachable u v := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact huC.trans ((C.mem_supp_iff v).mp hvC).symm
  obtain ⟨w⟩ := huv
  have hOpenLe : G ≤ cubicGraph d := by
    intro a b hab
    exact (cubicOpenGraph_adj.mp hab).choose
  have hHle : H ≤ cubicGraph d :=
    (SimpleGraph.deleteIncidenceSet_le G x).trans hOpenLe
  obtain ⟨y, hySupport, hyDist⟩ :=
    exists_mem_walk_support_cubicL1Dist_eq_of_le_of_ge hHle w huBall hvFar
  obtain ⟨q, _r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hySupport
  have huy : H.Reachable u y := ⟨q⟩
  have hyC : H.connectedComponentMk y = C :=
    (SimpleGraph.ConnectedComponent.sound huy).symm.trans huC
  have hxyG : G.Reachable x y := by
    have hxuG : G.Reachable x u := hxu.reachable
    exact hxuG.trans (huy.mono (SimpleGraph.deleteIncidenceSet_le G x))
  refine ⟨y, mem_openComponentMetricSphere_iff.mpr ⟨hyDist, ?_⟩, hyC⟩
  exact (SimpleGraph.ConnectedComponent.sound hxyG).symm.trans hxK

/-- Every vertex of the common component boundary belongs to an infinite branch of an interior
trifurcation. -/
theorem openComponentMetricSphere_vertex_mem_trifurcationBranch
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x y : Cubic d}
    (hn : 1 ≤ n)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBall : cubicL1Dist cubicOrigin x ≤ n - 1)
    (hy : y ∈ openComponentMetricSphere d omega K n) :
    ((cubicOpenGraph d omega).deleteIncidenceSet x).connectedComponentMk y ∈
      trifurcationBranchComponents (cubicOpenGraph d omega) x := by
  have hyData := mem_openComponentMetricSphere_iff.mp hy
  have hxy : x ≠ y := by
    intro h
    subst y
    rw [hyData.1] at hxBall
    omega
  have hreach : (cubicOpenGraph d omega).Reachable x y := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact hxK.trans hyData.2.symm
  exact connectedComponentMk_mem_trifurcationBranchComponents_of_reachable_from
    hx hxy hreach

/-- The source boundary partition attached to an interior open trifurcation. -/
noncomputable def openTrifurcationBoundaryPartition
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d}
    (hn : 1 ≤ n)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBall : cubicL1Dist cubicOrigin x ≤ n - 1) :
    ThreePartition (openComponentMetricSphere d omega K n) :=
  trifurcationBoundaryPartition (openComponentMetricSphere d omega K n) hx
    (fun _y _hy ↦ openComponentMetricSphere_vertex_mem_trifurcationBranch
      hn hx hxK hxBall _hy)
    (fun _C hC ↦ exists_openComponentMetricSphere_in_trifurcationBranch
      hn hxK hxBall hC)

/-- The boundary partitions of distinct interior trifurcations in one open component are
compatible. -/
theorem openTrifurcationBoundaryPartition_compatible
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x z : Cubic d}
    (hn : 1 ≤ n) (hxz : x ≠ z)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hz : IsTrifurcationVertex (cubicOpenGraph d omega) z)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hzK : (cubicOpenGraph d omega).connectedComponentMk z = K)
    (hxBall : cubicL1Dist cubicOrigin x ≤ n - 1)
    (hzBall : cubicL1Dist cubicOrigin z ≤ n - 1) :
    (openTrifurcationBoundaryPartition hn hx hxK hxBall).Compatible
      (openTrifurcationBoundaryPartition hn hz hzK hzBall) := by
  let G := cubicOpenGraph d omega
  have hreachXZ : G.Reachable x z := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact hxK.trans hzK.symm
  have hzBranchX : (G.deleteIncidenceSet x).connectedComponentMk z ∈
      trifurcationBranchComponents G x :=
    connectedComponentMk_mem_trifurcationBranchComponents_of_reachable
      hxz hz hreachXZ
  have hxBranchZ : (G.deleteIncidenceSet z).connectedComponentMk x ∈
      trifurcationBranchComponents G z :=
    connectedComponentMk_mem_trifurcationBranchComponents_of_reachable
      hxz.symm hx hreachXZ.symm
  exact trifurcationBoundaryPartition_compatible hxz
    (openComponentMetricSphere d omega K n) hx hz
    (fun y hy ↦ openComponentMetricSphere_vertex_mem_trifurcationBranch
      hn hx hxK hxBall hy)
    (fun C hC ↦ exists_openComponentMetricSphere_in_trifurcationBranch
      hn hxK hxBall hC)
    (fun y hy ↦ openComponentMetricSphere_vertex_mem_trifurcationBranch
      hn hz hzK hzBall hy)
    (fun C hC ↦ exists_openComponentMetricSphere_in_trifurcationBranch
      hn hzK hzBall hC)
    hzBranchX hxBranchZ

/-- Interior trifurcations belonging to a fixed open component. -/
noncomputable def openTrifurcationsInComponentBall
    (d : ℕ) (omega : EdgeConfiguration d)
    (K : (cubicOpenGraph d omega).ConnectedComponent) (n : ℕ) : Finset (Cubic d) :=
  by
    classical
    exact (cubicMetricBall d cubicOrigin (n - 1)).filter fun x ↦
      IsTrifurcationVertex (cubicOpenGraph d omega) x ∧
        (cubicOpenGraph d omega).connectedComponentMk x = K

@[simp]
theorem mem_openTrifurcationsInComponentBall_iff
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d} :
    x ∈ openTrifurcationsInComponentBall d omega K n ↔
      cubicL1Dist cubicOrigin x ≤ n - 1 ∧
        IsTrifurcationVertex (cubicOpenGraph d omega) x ∧
          (cubicOpenGraph d omega).connectedComponentMk x = K := by
  classical
  rw [openTrifurcationsInComponentBall, Finset.mem_filter,
    mem_cubicMetricBall_iff_l1Dist_le]

/-- Equation (8.6): a fixed open component has at most `|K ∩ ∂S(n)| - 2`
trifurcations in `S(n-1)`. -/
theorem openTrifurcationsInComponentBall_card_le
    {d n : ℕ} {omega : EdgeConfiguration d}
    (K : (cubicOpenGraph d omega).ConnectedComponent) (hn : 1 ≤ n) :
    (openTrifurcationsInComponentBall d omega K n).card ≤
      (openComponentMetricSphere d omega K n).card - 2 := by
  classical
  let T := openTrifurcationsInComponentBall d omega K n
  let Y := openComponentMetricSphere d omega K n
  let part : {x // x ∈ T} → ThreePartition Y := fun x ↦
    openTrifurcationBoundaryPartition hn
      (mem_openTrifurcationsInComponentBall_iff.mp x.2).2.1
      (mem_openTrifurcationsInComponentBall_iff.mp x.2).2.2
      (mem_openTrifurcationsInComponentBall_iff.mp x.2).1
  have hpartCompat {x z : {x // x ∈ T}} (hxz : x ≠ z) :
      (part x).Compatible (part z) := by
    have hxData := mem_openTrifurcationsInComponentBall_iff.mp x.2
    have hzData := mem_openTrifurcationsInComponentBall_iff.mp z.2
    apply openTrifurcationBoundaryPartition_compatible hn
      (fun h ↦ hxz (Subtype.ext h))
      hxData.2.1 hzData.2.1 hxData.2.2 hzData.2.2 hxData.1 hzData.1
  have hpartInj : Function.Injective part := by
    intro x z hEq
    by_contra hxz
    have hcompat := hpartCompat hxz
    rw [hEq] at hcompat
    exact ThreePartition.not_compatible_self _ hcompat
  let emb : {x // x ∈ T} ↪ ThreePartition Y := ⟨part, hpartInj⟩
  let F : Finset (ThreePartition Y) := T.attach.map emb
  have hFcard : F.card = T.card := by simp [F]
  have hFcompat : (F : Set (ThreePartition Y)).Pairwise ThreePartition.Compatible := by
    intro P hP Q hQ hPQ
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hP
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_map.mp hQ
    apply hpartCompat
    intro hxz
    apply hPQ
    exact congrArg emb hxz
  rw [← hFcard]
  exact ThreePartition.compatibleThreePartitions_card_le F hFcompat

/-- All open trifurcations in the inner metric ball. -/
noncomputable def openTrifurcationsInBall
    (d : ℕ) (omega : EdgeConfiguration d) (n : ℕ) : Finset (Cubic d) :=
  by
    classical
    exact (cubicMetricBall d cubicOrigin (n - 1)).filter fun x ↦
      IsTrifurcationVertex (cubicOpenGraph d omega) x

@[simp]
theorem mem_openTrifurcationsInBall_iff
    {d n : ℕ} {omega : EdgeConfiguration d} {x : Cubic d} :
    x ∈ openTrifurcationsInBall d omega n ↔
      cubicL1Dist cubicOrigin x ≤ n - 1 ∧
        IsTrifurcationVertex (cubicOpenGraph d omega) x := by
  classical
  rw [openTrifurcationsInBall, Finset.mem_filter,
    mem_cubicMetricBall_iff_l1Dist_le]

/-- Summed form of (8.6): the number of trifurcations in `S(n-1)` is at most the size of
`∂S(n)`. -/
theorem openTrifurcationsInBall_card_le_sphere
    {d n : ℕ} (omega : EdgeConfiguration d) (hn : 1 ≤ n) :
    (openTrifurcationsInBall d omega n).card ≤
      (cubicMetricSphere d cubicOrigin n).card := by
  classical
  let G := cubicOpenGraph d omega
  let T := openTrifurcationsInBall d omega n
  let sphere := cubicMetricSphere d cubicOrigin n
  let component : Cubic d → G.ConnectedComponent := G.connectedComponentMk
  let components := T.image component
  have hfiber (K : G.ConnectedComponent) :
      T.filter (fun x ↦ component x = K) =
        openTrifurcationsInComponentBall d omega K n := by
    ext x
    simp [T, component, mem_openTrifurcationsInBall_iff,
      mem_openTrifurcationsInComponentBall_iff]
    tauto
  have hsphereFiber (K : G.ConnectedComponent) :
      (sphere.filter fun y ↦ component y = K).card =
        (openComponentMetricSphere d omega K n).card := by
    change ((cubicMetricSphere d cubicOrigin n).filter fun y ↦
      (cubicOpenGraph d omega).connectedComponentMk y = K).card = _
    rfl
  calc
    T.card = ∑ K ∈ components, (T.filter fun x ↦ component x = K).card := by
      exact Finset.card_eq_sum_card_image component T
    _ = ∑ K ∈ components,
        (openTrifurcationsInComponentBall d omega K n).card := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [hfiber]
    _ ≤ ∑ K ∈ components, (openComponentMetricSphere d omega K n).card := by
      apply Finset.sum_le_sum
      intro K _hK
      exact (openTrifurcationsInComponentBall_card_le K hn).trans (Nat.sub_le _ _)
    _ = ∑ K ∈ components, (sphere.filter fun y ↦ component y = K).card := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [hsphereFiber]
    _ = (sphere.filter fun y ↦ component y ∈ components).card :=
      Finset.sum_card_fiberwise_eq_card_filter sphere components component
    _ ≤ sphere.card := Finset.card_filter_le _ _

end Percolation
