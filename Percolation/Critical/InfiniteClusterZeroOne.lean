import Percolation.Bernoulli.TailZeroOne
import Percolation.Critical.BoxRadius
import Percolation.Critical.Regions

/-!
# Zero--one infrastructure for existence of a global infinite cluster

The first step supplies a denumeration of cubic edges in every positive dimension.  The
finite-closing invariance of the global infinite-cluster event is developed below this
enumeration and then fed to the generic Bernoulli tail theorem.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

section DeleteOneEdge

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- Deleting one edge from a connected graph leaves every vertex connected to at least one of
the two endpoints. -/
theorem SimpleGraph.Connected.reachable_deleteEdges_endpoint_cover
    (hG : G.Connected) (huv : G.Adj u v) (w : V) :
    (G.deleteEdges {s(u, v)}).Reachable u w ∨
      (G.deleteEdges {s(u, v)}).Reachable v w := by
  classical
  obtain ⟨P, hP⟩ := hG.exists_isPath w u
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

/-- A connected infinite graph still has an infinite component after one edge is deleted. -/
theorem SimpleGraph.Connected.exists_infinite_reachable_deleteEdges_singleton
    [Infinite V] (hG : G.Connected) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ x : V, {y | (G.deleteEdges {e}).Reachable x y}.Infinite := by
  induction e using Sym2.ind with
  | _ u v =>
      have huv : G.Adj u v := by simpa [SimpleGraph.mem_edgeSet] using he
      let U : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable u y}
      let W : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable v y}
      by_cases hU : U.Infinite
      · exact ⟨u, hU⟩
      · have hUfin : U.Finite := Set.not_infinite.mp hU
        have hcover : Set.univ ⊆ U ∪ W := by
          intro y _hy
          exact reachable_deleteEdges_endpoint_cover hG huv y
        have hW : W.Infinite := by
          intro hWfin
          have huniv : (Set.univ : Set V).Finite :=
            (hUfin.union hWfin).subset hcover
          exact Set.infinite_univ huniv
        exact ⟨v, hW⟩

/-- If a graph has an infinite component, then it still has an infinite component after one
edge is deleted.  The deleted edge need not belong to the graph. -/
theorem SimpleGraph.exists_infinite_reachable_deleteEdges_singleton
    (hinf : ∃ x : V, {y | G.Reachable x y}.Infinite) (e : Sym2 V) :
    ∃ x : V, {y | (G.deleteEdges {e}).Reachable x y}.Infinite := by
  classical
  obtain ⟨x, hx⟩ := hinf
  induction e using Sym2.ind with
  | _ u v =>
      let X : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable x y}
      let U : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable u y}
      let W : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable v y}
      have hcover : {y | G.Reachable x y} ⊆ X ∪ U ∪ W := by
        intro y hy
        obtain ⟨P, hP⟩ := hy.symm.exists_isPath
        by_cases heP : s(u, v) ∈ P.edges
        · have huP : u ∈ P.support := P.fst_mem_support_of_mem_edges heP
          have hvP : v ∈ P.support := P.snd_mem_support_of_mem_edges heP
          have huv : u ≠ v :=
            ((SimpleGraph.mem_edgeSet G).mp (P.edges_subset_edgeSet heP)).ne
          let Qu := P.takeUntil u huP
          by_cases heQu : s(u, v) ∈ Qu.edges
          · let Qv := P.takeUntil v hvP
            have hvQu : v ∈ Qu.support := Qu.snd_mem_support_of_mem_edges heQu
            have huNotQv : u ∉ Qv.support := by
              simpa [Qv] using
                (P.notMem_support_takeUntil_support_takeUntil_subset huv.symm huP hvQu)
            have heNotQv : s(u, v) ∉ Qv.edges := by
              intro heQv
              exact huNotQv (Qv.fst_mem_support_of_mem_edges heQv)
            exact Or.inr
              (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨Qv, heNotQv⟩).symm
          · exact Or.inl (Or.inr
              (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨Qu, heQu⟩).symm)
        · exact Or.inl (Or.inl
            (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨P, heP⟩).symm
          )
      by_cases hX : X.Infinite
      · exact ⟨x, hX⟩
      · by_cases hU : U.Infinite
        · exact ⟨u, hU⟩
        · by_cases hW : W.Infinite
          · exact ⟨v, hW⟩
          · have hfinite : (X ∪ U ∪ W).Finite :=
              ((Set.not_infinite.mp hX).union (Set.not_infinite.mp hU)).union
                (Set.not_infinite.mp hW)
            exact False.elim (hx (hfinite.subset hcover))

/-- Deleting finitely many edges cannot destroy every infinite component of a graph. -/
theorem SimpleGraph.exists_infinite_reachable_deleteEdges_finset
    (hinf : ∃ x : V, {y | G.Reachable x y}.Infinite) (E : Finset (Sym2 V)) :
    ∃ x : V, {y | (G.deleteEdges (E : Set (Sym2 V))).Reachable x y}.Infinite := by
  classical
  induction E using Finset.induction_on with
  | empty => simpa [SimpleGraph.deleteEdges_empty] using hinf
  | @insert e E he ih =>
      have hsingle := SimpleGraph.exists_infinite_reachable_deleteEdges_singleton ih e
      simpa [SimpleGraph.deleteEdges_deleteEdges, Set.union_comm] using hsingle

/-- Rooted strengthening of finite-edge deletion: the surviving infinite component may be
chosen inside the original component of the root. -/
theorem SimpleGraph.exists_infinite_reachable_deleteEdges_finset_of_root
    {r : V} (hinf : {y | G.Reachable r y}.Infinite) (E : Finset (Sym2 V)) :
    ∃ x : V, G.Reachable r x ∧
      {y | (G.deleteEdges (E : Set (Sym2 V))).Reachable x y}.Infinite := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      refine ⟨r, ⟨SimpleGraph.Walk.nil⟩, ?_⟩
      simpa [SimpleGraph.deleteEdges_empty] using hinf
  | @insert e E he ih =>
      obtain ⟨x, hrx, hxinf⟩ := ih
      induction e using Sym2.ind with
      | _ u v =>
          let H := G.deleteEdges (E : Set (Sym2 V))
          let X : Set V := {y | (H.deleteEdges {s(u, v)}).Reachable x y}
          let U : Set V := {y | H.Reachable x y ∧
            (H.deleteEdges {s(u, v)}).Reachable u y}
          let W : Set V := {y | H.Reachable x y ∧
            (H.deleteEdges {s(u, v)}).Reachable v y}
          have hcover : {y | H.Reachable x y} ⊆ X ∪ U ∪ W := by
            intro y hy
            obtain ⟨P, hP⟩ := hy.symm.exists_isPath
            by_cases heP : s(u, v) ∈ P.edges
            · have huP : u ∈ P.support := P.fst_mem_support_of_mem_edges heP
              have hvP : v ∈ P.support := P.snd_mem_support_of_mem_edges heP
              have huv : u ≠ v :=
                ((SimpleGraph.mem_edgeSet H).mp (P.edges_subset_edgeSet heP)).ne
              let Qu := P.takeUntil u huP
              by_cases heQu : s(u, v) ∈ Qu.edges
              · let Qv := P.takeUntil v hvP
                have hvQu : v ∈ Qu.support := Qu.snd_mem_support_of_mem_edges heQu
                have huNotQv : u ∉ Qv.support := by
                  simpa [Qv] using
                    (P.notMem_support_takeUntil_support_takeUntil_subset huv.symm huP hvQu)
                have heNotQv : s(u, v) ∉ Qv.edges := by
                  intro heQv
                  exact huNotQv (Qv.fst_mem_support_of_mem_edges heQv)
                exact Or.inr ⟨hy,
                  (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
                    ⟨Qv, heNotQv⟩).symm⟩
              · exact Or.inl (Or.inr ⟨hy,
                  (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
                    ⟨Qu, heQu⟩).symm⟩)
            · exact Or.inl (Or.inl
                (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨P, heP⟩).symm)
          by_cases hX : X.Infinite
          · refine ⟨x, hrx, ?_⟩
            simpa [H, X, SimpleGraph.deleteEdges_deleteEdges, Set.union_comm] using hX
          · by_cases hU : U.Infinite
            · obtain ⟨y, hyH, huy⟩ := hU.nonempty
              have hxuG : G.Reachable x u :=
                (hyH.trans (huy.symm.mono (SimpleGraph.deleteEdges_le _))).mono
                  (by simp [H])
              refine ⟨u, hrx.trans hxuG, ?_⟩
              have hraw : {y | (H.deleteEdges {s(u, v)}).Reachable u y}.Infinite :=
                hU.mono fun _ hy ↦ hy.2
              simpa [H, SimpleGraph.deleteEdges_deleteEdges, Set.union_comm] using hraw
            · by_cases hW : W.Infinite
              · obtain ⟨y, hyH, hvy⟩ := hW.nonempty
                have hxvG : G.Reachable x v :=
                  (hyH.trans (hvy.symm.mono (SimpleGraph.deleteEdges_le _))).mono
                    (by simp [H])
                refine ⟨v, hrx.trans hxvG, ?_⟩
                have hraw : {y | (H.deleteEdges {s(u, v)}).Reachable v y}.Infinite :=
                  hW.mono fun _ hy ↦ hy.2
                simpa [H, SimpleGraph.deleteEdges_deleteEdges, Set.union_comm] using hraw
              · have hfinite : (X ∪ U ∪ W).Finite :=
                  ((Set.not_infinite.mp hX).union (Set.not_infinite.mp hU)).union
                    (Set.not_infinite.mp hW)
                exact False.elim (hxinf (hfinite.subset hcover))

end DeleteOneEdge

section InfiniteComponentComparison

variable {V : Type*} {G G' : SimpleGraph V}

/-- Infinite connected components of an arbitrary graph, as a subtype. -/
def InfiniteGraphComponent (G : SimpleGraph V) :=
  {C : G.ConnectedComponent // C.supp.Infinite}

/-- Inclusion of graphs sends an infinite component into an infinite component. -/
noncomputable def InfiniteGraphComponent.mapOfLE (h : G ≤ G') :
    InfiniteGraphComponent G → InfiniteGraphComponent G' := fun C ↦ by
  let C' := C.1.map (SimpleGraph.Hom.ofLE h)
  refine ⟨C', ?_⟩
  apply C.2.mono
  intro x hx
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  simpa [C'] using congrArg
    (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE h)) hx

/-- If the smaller graph is obtained by deleting finitely many edges, every infinite component
of the larger graph contains an infinite component of the smaller graph. -/
theorem InfiniteGraphComponent.mapOfLE_surjective_of_eq_deleteEdges
    (G' : SimpleGraph V) (E : Finset (Sym2 V)) :
    Function.Surjective
      (InfiniteGraphComponent.mapOfLE
        (G := G'.deleteEdges (E : Set (Sym2 V))) (G' := G')
        (SimpleGraph.deleteEdges_le _)) := by
  intro C'
  obtain ⟨x, hx⟩ := C'.2.nonempty
  have hxInf : {y | G'.Reachable x y}.Infinite := by
    rw [show {y | G'.Reachable x y} = C'.1.supp by
      ext y
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hxComponent : G'.connectedComponentMk x = C'.1 :=
        C'.1.mem_supp_iff x |>.mp hx
      rw [← hxComponent, SimpleGraph.ConnectedComponent.eq]
      exact SimpleGraph.reachable_comm]
    exact C'.2
  obtain ⟨z, hxz, hzInf⟩ :=
    SimpleGraph.exists_infinite_reachable_deleteEdges_finset_of_root hxInf E
  let C : InfiniteGraphComponent (G'.deleteEdges (E : Set (Sym2 V))) :=
    ⟨(G'.deleteEdges (E : Set (Sym2 V))).connectedComponentMk z, by
      rw [show ((G'.deleteEdges (E : Set (Sym2 V))).connectedComponentMk z).supp =
          {y | (G'.deleteEdges (E : Set (Sym2 V))).Reachable z y} by
        ext y
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
          SimpleGraph.ConnectedComponent.eq]
        exact SimpleGraph.reachable_comm]
      exact hzInf⟩
  refine ⟨C, Subtype.ext ?_⟩
  change G'.connectedComponentMk z = C'.1
  have hxComponent : G'.connectedComponentMk x = C'.1 := C'.1.mem_supp_iff x |>.mp hx
  exact (SimpleGraph.ConnectedComponent.sound hxz).symm.trans hxComponent

theorem encard_infiniteGraphComponent_le_of_deleteEdges
    (G' : SimpleGraph V) (E : Finset (Sym2 V)) :
    ENat.card (InfiniteGraphComponent G') ≤
      ENat.card (InfiniteGraphComponent (G'.deleteEdges (E : Set (Sym2 V)))) := by
  classical
  have hsurj := InfiniteGraphComponent.mapOfLE_surjective_of_eq_deleteEdges G' E
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  exact ENat.card_le_card_of_injective hg.injective

theorem encard_infiniteGraphComponent_lt_of_deleteEdges_of_not_injective
    (G' : SimpleGraph V) (E : Finset (Sym2 V))
    [Finite (InfiniteGraphComponent (G'.deleteEdges (E : Set (Sym2 V))))]
    (hnotinj : ¬Function.Injective
      (InfiniteGraphComponent.mapOfLE
        (G := G'.deleteEdges (E : Set (Sym2 V))) (G' := G')
        (SimpleGraph.deleteEdges_le _))) :
    ENat.card (InfiniteGraphComponent G') <
      ENat.card (InfiniteGraphComponent (G'.deleteEdges (E : Set (Sym2 V)))) := by
  let f := InfiniteGraphComponent.mapOfLE
    (G := G'.deleteEdges (E : Set (Sym2 V))) (G' := G')
    (SimpleGraph.deleteEdges_le _)
  have hsurj : Function.Surjective f :=
    InfiniteGraphComponent.mapOfLE_surjective_of_eq_deleteEdges G' E
  letI : Fintype (InfiniteGraphComponent (G'.deleteEdges (E : Set (Sym2 V)))) :=
    Fintype.ofFinite _
  letI : Finite (InfiniteGraphComponent G') := Finite.of_surjective f hsurj
  letI : Fintype (InfiniteGraphComponent G') := Fintype.ofFinite _
  rw [ENat.card_eq_coe_fintype_card, ENat.card_eq_coe_fintype_card, ENat.coe_lt_coe]
  exact Fintype.card_lt_of_surjective_not_injective f hsurj hnotinj

end InfiniteComponentComparison

section OpenGraphFiniteClosing

variable {d : ℕ}

/-- The underlying unoriented lattice edges of a finite set of cubic edge coordinates. -/
def underlyingCubicEdges (E : Finset (CubicEdge d)) : Finset (Sym2 (Cubic d)) :=
  E.image Subtype.val

theorem mem_underlyingCubicEdges_iff {E : Finset (CubicEdge d)}
    {e : Sym2 (Cubic d)} (he : e ∈ (cubicGraph d).edgeSet) :
    e ∈ underlyingCubicEdges E ↔ (⟨e, he⟩ : CubicEdge d) ∈ E := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    have : a = ⟨e, he⟩ := Subtype.ext hae
    simpa [this] using ha
  · intro h
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, h, rfl⟩

/-- Forcing a finite edge set closed deletes exactly those edges from the random open graph. -/
theorem cubicOpenGraph_spliceOn_empty (E : Finset (CubicEdge d))
    (omega : EdgeConfiguration d) :
    cubicOpenGraph d (spliceOn E ∅ omega) =
      (cubicOpenGraph d omega).deleteEdges (underlyingCubicEdges E : Set (Sym2 (Cubic d))) := by
  classical
  ext x y
  rw [SimpleGraph.deleteEdges_adj]
  simp only [cubicOpenGraph_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    have hopenPair :
        (⟨s(x, y), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hxy⟩ : CubicEdge d) ∈
            omega ∧
          (⟨s(x, y), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hxy⟩ : CubicEdge d) ∉ E := by
      simpa [mem_spliceOn] using hopen
    refine ⟨⟨hxy, hopenPair.1⟩, ?_⟩
    exact (mem_underlyingCubicEdges_iff
      ((SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hxy)).not.mpr hopenPair.2
  · rintro ⟨⟨hxy, hopen⟩, hnot⟩
    refine ⟨hxy, ?_⟩
    rw [mem_spliceOn]
    exact Or.inr ⟨hopen, by
      exact (mem_underlyingCubicEdges_iff
        ((SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hxy)).not.mp hnot⟩

/-- Closing `E` after first opening `E` simply recovers the configuration with `E` closed. -/
theorem cubicOpenGraph_spliceOn_empty_eq_deleteEdges_spliceOn_all
    (E : Finset (CubicEdge d)) (omega : EdgeConfiguration d) :
    cubicOpenGraph d (spliceOn E ∅ omega) =
      (cubicOpenGraph d (spliceOn E E omega)).deleteEdges
        (underlyingCubicEdges E : Set (Sym2 (Cubic d))) := by
  calc
    cubicOpenGraph d (spliceOn E ∅ omega) =
        cubicOpenGraph d (spliceOn E ∅ (spliceOn E E omega)) := by
      apply congrArg (cubicOpenGraph d)
      ext e
      by_cases he : e ∈ E
      · simp [mem_spliceOn, he]
      · simp [mem_spliceOn, he]
    _ = (cubicOpenGraph d (spliceOn E E omega)).deleteEdges
        (underlyingCubicEdges E : Set (Sym2 (Cubic d))) :=
      cubicOpenGraph_spliceOn_empty E (spliceOn E E omega)

/-- A prescribed trace `s ⊆ E` is obtained from the all-open trace by deleting precisely
the edges of `E \ s`. -/
theorem cubicOpenGraph_spliceOn_eq_deleteEdges_spliceOn_all
    (E s : Finset (CubicEdge d)) (hs : s ⊆ E) (omega : EdgeConfiguration d) :
    cubicOpenGraph d (spliceOn E s omega) =
      (cubicOpenGraph d (spliceOn E E omega)).deleteEdges
        (underlyingCubicEdges (E \ s) : Set (Sym2 (Cubic d))) := by
  calc
    cubicOpenGraph d (spliceOn E s omega) =
        cubicOpenGraph d (spliceOn (E \ s) ∅ (spliceOn E E omega)) := by
      apply congrArg (cubicOpenGraph d)
      ext e
      by_cases hes : e ∈ s
      · have heE : e ∈ E := hs hes
        simp [mem_spliceOn, hes, heE]
      · by_cases heE : e ∈ E
        · have heDiff : e ∈ E \ s := Finset.mem_sdiff.mpr ⟨heE, hes⟩
          simp [mem_spliceOn, hes, heE, heDiff]
        · have heDiff : e ∉ E \ s := by simp [heE]
          simp [mem_spliceOn, hes, heE, heDiff]
    _ = (cubicOpenGraph d (spliceOn E E omega)).deleteEdges
        (underlyingCubicEdges (E \ s) : Set (Sym2 (Cubic d))) :=
      cubicOpenGraph_spliceOn_empty (E \ s) (spliceOn E E omega)

/-- Global infinitude is equivalently infinitude of a reachability class in the random open
graph. -/
theorem hasInfiniteOpenClusterInVertices_univ_iff_openGraph
    (omega : EdgeConfiguration d) :
    hasInfiniteOpenClusterInVertices d Set.univ omega ↔
      ∃ x : Cubic d, {y | (cubicOpenGraph d omega).Reachable x y}.Infinite := by
  simp only [hasInfiniteOpenClusterInVertices, Set.mem_univ, true_and,
    cubicOpenClusterWithinVertices_univ]
  apply exists_congr
  intro x
  rw [show cubicOpenClusterFrom d omega x =
      {y | (cubicOpenGraph d omega).Reachable x y} by
    ext y
    exact cubicOpenGraph_reachable_iff.symm]

end OpenGraphFiniteClosing

/-- Pairwise separated positive first-axis edges. -/
def separatedAxisEdge {d : ℕ} (hd : 0 < d) (n : ℕ) : CubicEdge d :=
  cubicStepEdge (cubicAxisVertex d (2 * n)) ((⟨0, hd⟩ : Fin d), true)

theorem separatedAxisEdge_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (separatedAxisEdge hd) := by
  intro m n hmn
  have hmem : cubicAxisVertex d (2 * m) ∈ (separatedAxisEdge hd n).1 := by
    rw [← hmn]
    simp [separatedAxisEdge, cubicStepEdge]
  rw [separatedAxisEdge, cubicStepEdge, Sym2.mem_iff] at hmem
  rcases hmem with hleft | hright
  · have hcoord := congrFun hleft (⟨0, hd⟩ : Fin d)
    simp [cubicAxisVertex] at hcoord
    omega
  · have hcoord := congrFun hright (⟨0, hd⟩ : Fin d)
    simp [cubicAxisVertex, cubicStepFrom, cubicDirectionIncrement] at hcoord
    omega

noncomputable instance cubicEdgeInfinite {d : ℕ} [NeZero d] : Infinite (CubicEdge d) :=
  Infinite.of_injective (separatedAxisEdge (Nat.pos_of_ne_zero NeZero.out))
    (separatedAxisEdge_injective (Nat.pos_of_ne_zero NeZero.out))

noncomputable instance cubicEdgeDenumerable {d : ℕ} [NeZero d] :
    Denumerable (CubicEdge d) := by
  letI := Encodable.ofCountable (CubicEdge d)
  exact Denumerable.ofEncodableOfInfinite (CubicEdge d)

/-- The event that some infinite open component exists is unchanged when finitely many bonds are
forced closed. -/
theorem isInvariantUnderFiniteClosing_hasInfiniteOpenClusterInVertices_univ (d : ℕ) :
    IsInvariantUnderFiniteClosing
      {omega : EdgeConfiguration d | hasInfiniteOpenClusterInVertices d Set.univ omega} := by
  intro E omega
  constructor
  · intro hclosed
    change hasInfiniteOpenClusterInVertices d Set.univ (spliceOn E ∅ omega) at hclosed
    change hasInfiniteOpenClusterInVertices d Set.univ omega
    exact (isIncreasingEvent_hasInfiniteOpenClusterInVertices d Set.univ) (by
      intro e he
      have hp : e ∈ omega ∧ e ∉ E := by simpa [mem_spliceOn] using he
      exact hp.1) hclosed
  · intro hinf
    change hasInfiniteOpenClusterInVertices d Set.univ omega at hinf
    change hasInfiniteOpenClusterInVertices d Set.univ (spliceOn E ∅ omega)
    rw [hasInfiniteOpenClusterInVertices_univ_iff_openGraph,
      cubicOpenGraph_spliceOn_empty]
    exact SimpleGraph.exists_infinite_reachable_deleteEdges_finset
      (hasInfiniteOpenClusterInVertices_univ_iff_openGraph omega |>.mp hinf)
      (underlyingCubicEdges E)

/-- The probability that Bernoulli bond percolation has some infinite component is zero or one. -/
theorem regionHasInfiniteClusterProbability_univ_eq_zero_or_one
    (d : ℕ) [NeZero d] (p : I) :
    regionHasInfiniteClusterProbability d Set.univ p = 0 ∨
      regionHasInfiniteClusterProbability d Set.univ p = 1 := by
  rcases bernoulli_zero_or_one_of_invariantUnderFiniteClosing p
      (measurableSet_hasInfiniteOpenClusterInVertices d Set.univ)
      (isInvariantUnderFiniteClosing_hasInfiniteOpenClusterInVertices_univ d) with hzero | hone
  · left
    unfold regionHasInfiniteClusterProbability bernoulliBondMeasure
    rw [Measure.real, hzero]
    rfl
  · right
    unfold regionHasInfiniteClusterProbability bernoulliBondMeasure
    rw [Measure.real, hone]
    rfl

/-- Positive rooted percolation forces the root-free infinite-cluster event to have probability
one.  This is the zero--one upgrade used in the boundary-contact proof of Lemma 7.9. -/
theorem regionHasInfiniteClusterProbability_univ_eq_one_of_theta_pos
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p) :
    regionHasInfiniteClusterProbability d Set.univ p = 1 := by
  rcases regionHasInfiniteClusterProbability_univ_eq_zero_or_one d p with hzero | hone
  · have hrootzero : regionThetaFrom d Set.univ p cubicOrigin = 0 :=
      (regionHasInfiniteClusterProbability_eq_zero_iff_regionThetaFrom_eq_zero_of_connected
        (cubicRegionGraph_univ_connected d) p (Set.mem_univ cubicOrigin)).mp hzero
    have : theta d p = 0 := by simpa using hrootzero
    exact (ne_of_gt htheta this).elim
  · exact hone

end Percolation
