import Percolation.Critical.TranslationErgodicity
import Percolation.Critical.TwoPoint
import Percolation.Critical.InfiniteClusterZeroOne

/-!
# Infinite open components

This file defines the extended-natural number of infinite connected components in the random
open subgraph of the cubic lattice.  It is the component-counting object used in Grimmett's
proof of Theorem 8.1.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The infinite connected components of the random open subgraph. -/
def infiniteOpenComponents (d : ℕ) (omega : EdgeConfiguration d) :
    Set (cubicOpenGraph d omega).ConnectedComponent :=
  {C | C.supp.Infinite}

/-- The number of infinite open components, with value `⊤` when there are infinitely many. -/
noncomputable def numberOfInfiniteOpenClusters (d : ℕ) (omega : EdgeConfiguration d) : ℕ∞ :=
  (infiniteOpenComponents d omega).encard

/-- The event that the open subgraph has exactly one infinite connected component. -/
def exactlyOneInfiniteOpenClusterEvent (d : ℕ) : Set (EdgeConfiguration d) :=
  {omega | numberOfInfiniteOpenClusters d omega = 1}

/-- The event that there are at least `k` distinct infinite open components.  Representatives
are vertices rather than quotient components, which makes measurability and translation
invariance explicit. -/
def atLeastInfiniteOpenClustersEvent (d k : ℕ) : Set (EdgeConfiguration d) :=
  {omega | ∃ x : Fin k → Cubic d,
    (∀ i, hasInfiniteOpenClusterFrom d omega (x i)) ∧
      ∀ i j, i ≠ j → omega ∉ connectionEvent d (x i) (x j)}

/-- A fixed tuple of vertices witnesses `k` distinct infinite components. -/
def infiniteOpenClusterWitnessEvent {d k : ℕ} (x : Fin k → Cubic d) :
    Set (EdgeConfiguration d) :=
  {omega | (∀ i, hasInfiniteOpenClusterFrom d omega (x i)) ∧
    ∀ i j, i ≠ j → omega ∉ connectionEvent d (x i) (x j)}

/-- The event that the infinite-component count is the finite value `k`. -/
def exactlyKInfiniteOpenClustersEvent (d k : ℕ) : Set (EdgeConfiguration d) :=
  atLeastInfiniteOpenClustersEvent d k \ atLeastInfiniteOpenClustersEvent d (k + 1)

@[simp]
theorem mem_infiniteOpenComponents {d : ℕ} {omega : EdgeConfiguration d}
    {C : (cubicOpenGraph d omega).ConnectedComponent} :
    C ∈ infiniteOpenComponents d omega ↔ C.supp.Infinite :=
  Iff.rfl

@[simp]
theorem connectedComponentMk_mem_infiniteOpenComponents_iff {d : ℕ}
    {omega : EdgeConfiguration d} {x : Cubic d} :
    (cubicOpenGraph d omega).connectedComponentMk x ∈ infiniteOpenComponents d omega ↔
      hasInfiniteOpenClusterFrom d omega x := by
  rw [mem_infiniteOpenComponents, cubicOpenGraph_component_supp]
  rfl

theorem connectedComponentMk_eq_iff_mem_connectionEvent {d : ℕ}
    {omega : EdgeConfiguration d} {x y : Cubic d} :
    (cubicOpenGraph d omega).connectedComponentMk x =
        (cubicOpenGraph d omega).connectedComponentMk y ↔
      omega ∈ connectionEvent d x y := by
  rw [SimpleGraph.ConnectedComponent.eq]
  exact cubicOpenGraph_reachable_iff

theorem infiniteOpenComponents_nonempty_iff {d : ℕ} {omega : EdgeConfiguration d} :
    (infiniteOpenComponents d omega).Nonempty ↔
      ∃ x : Cubic d, hasInfiniteOpenClusterFrom d omega x := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨x, hx⟩ := hC.nonempty
    refine ⟨x, ?_⟩
    rw [← connectedComponentMk_mem_infiniteOpenComponents_iff]
    rw [(C.mem_supp_iff x).mp hx]
    exact hC
  · rintro ⟨x, hx⟩
    exact ⟨(cubicOpenGraph d omega).connectedComponentMk x,
      connectedComponentMk_mem_infiniteOpenComponents_iff.mpr hx⟩

theorem numberOfInfiniteOpenClusters_eq_zero_iff {d : ℕ} {omega : EdgeConfiguration d} :
    numberOfInfiniteOpenClusters d omega = 0 ↔
      ∀ x : Cubic d, ¬hasInfiniteOpenClusterFrom d omega x := by
  rw [numberOfInfiniteOpenClusters, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    exact h ((cubicOpenGraph d omega).connectedComponentMk x)
      (connectedComponentMk_mem_infiniteOpenComponents_iff.mpr hx)
  · intro h C hC
    obtain ⟨x, hx⟩ := hC.nonempty
    apply h x
    rw [← connectedComponentMk_mem_infiniteOpenComponents_iff, (C.mem_supp_iff x).mp hx]
    exact hC

theorem numberOfInfiniteOpenClusters_ne_zero_iff {d : ℕ} {omega : EdgeConfiguration d} :
    numberOfInfiniteOpenClusters d omega ≠ 0 ↔
      ∃ x : Cubic d, hasInfiniteOpenClusterFrom d omega x := by
  rw [numberOfInfiniteOpenClusters, Set.encard_ne_zero, infiniteOpenComponents_nonempty_iff]

/-- Opening a finite collection of bonds cannot increase the number of infinite components. -/
theorem numberOfInfiniteOpenClusters_spliceOn_all_le_spliceOn_empty
    {d : ℕ} (E : Finset (CubicEdge d)) (omega : EdgeConfiguration d) :
    numberOfInfiniteOpenClusters d (spliceOn E E omega) ≤
      numberOfInfiniteOpenClusters d (spliceOn E ∅ omega) := by
  have h := encard_infiniteGraphComponent_le_of_deleteEdges
    (cubicOpenGraph d (spliceOn E E omega)) (underlyingCubicEdges E)
  have hgraph := cubicOpenGraph_spliceOn_empty_eq_deleteEdges_spliceOn_all E omega
  rw [← hgraph] at h
  change ENat.card (InfiniteGraphComponent (cubicOpenGraph d (spliceOn E E omega))) ≤
    ENat.card (InfiniteGraphComponent (cubicOpenGraph d (spliceOn E ∅ omega)))
  exact h

/-- If opening a finite edge set joins two formerly distinct infinite components and the closed
configuration has only finitely many infinite components, the component count drops strictly. -/
theorem numberOfInfiniteOpenClusters_spliceOn_all_lt_spliceOn
    {d : ℕ} (E s : Finset (CubicEdge d)) (hs : s ⊆ E)
    (omega : EdgeConfiguration d)
    {x y : Cubic d}
    (hfinite : numberOfInfiniteOpenClusters d (spliceOn E s omega) < ⊤)
    (hx : hasInfiniteOpenClusterFrom d (spliceOn E s omega) x)
    (hy : hasInfiniteOpenClusterFrom d (spliceOn E s omega) y)
    (hsep : spliceOn E s omega ∉ connectionEvent d x y)
    (hjoin : spliceOn E E omega ∈ connectionEvent d x y) :
    numberOfInfiniteOpenClusters d (spliceOn E E omega) <
      numberOfInfiniteOpenClusters d (spliceOn E s omega) := by
  let Gopen := cubicOpenGraph d (spliceOn E E omega)
  let Gclosed := cubicOpenGraph d (spliceOn E s omega)
  let F := underlyingCubicEdges (E \ s)
  have hgraph : Gclosed = Gopen.deleteEdges (F : Set (Sym2 (Cubic d))) := by
    exact cubicOpenGraph_spliceOn_eq_deleteEdges_spliceOn_all E s hs omega
  have hxInf : (Gclosed.connectedComponentMk x).supp.Infinite := by
    simpa [Gclosed, hasInfiniteOpenClusterFrom, cubicOpenClusterFrom,
      cubicOpenGraph_component_supp] using hx
  have hyInf : (Gclosed.connectedComponentMk y).supp.Infinite := by
    simpa [Gclosed, hasInfiniteOpenClusterFrom, cubicOpenClusterFrom,
      cubicOpenGraph_component_supp] using hy
  rw [hgraph] at hxInf hyInf
  let Cx : InfiniteGraphComponent (Gopen.deleteEdges (F : Set (Sym2 (Cubic d)))) :=
    ⟨(Gopen.deleteEdges (F : Set (Sym2 (Cubic d)))).connectedComponentMk x, hxInf⟩
  let Cy : InfiniteGraphComponent (Gopen.deleteEdges (F : Set (Sym2 (Cubic d)))) :=
    ⟨(Gopen.deleteEdges (F : Set (Sym2 (Cubic d)))).connectedComponentMk y, hyInf⟩
  have hsourceFinite :
      (infiniteOpenComponents d (spliceOn E s omega)).Finite :=
    Set.encard_lt_top_iff.mp hfinite
  have hsourceFinite' : Finite
      (InfiniteGraphComponent (Gopen.deleteEdges (F : Set (Sym2 (Cubic d))))) := by
    rw [← hgraph]
    change Finite {C // C ∈ infiniteOpenComponents d (spliceOn E s omega)}
    exact hsourceFinite.fintype.finite
  letI : Finite
      (InfiniteGraphComponent (Gopen.deleteEdges (F : Set (Sym2 (Cubic d))))) :=
    hsourceFinite'
  let f := InfiniteGraphComponent.mapOfLE
    (G := Gopen.deleteEdges (F : Set (Sym2 (Cubic d)))) (G' := Gopen)
    (SimpleGraph.deleteEdges_le _)
  have hmapEq : f Cx = f Cy := by
    apply Subtype.ext
    change Gopen.connectedComponentMk x = Gopen.connectedComponentMk y
    exact connectedComponentMk_eq_iff_mem_connectionEvent.mpr hjoin
  have hnotinj : ¬Function.Injective f := by
    intro hinj
    apply hsep
    rw [← connectedComponentMk_eq_iff_mem_connectionEvent]
    change Gclosed.connectedComponentMk x = Gclosed.connectedComponentMk y
    rw [hgraph]
    exact congrArg Subtype.val (hinj hmapEq)
  have hstrict :=
    encard_infiniteGraphComponent_lt_of_deleteEdges_of_not_injective Gopen F hnotinj
  change ENat.card (InfiniteGraphComponent Gopen) <
    ENat.card (InfiniteGraphComponent Gclosed)
  rw [hgraph]
  exact hstrict

theorem numberOfInfiniteOpenClusters_spliceOn_all_lt_spliceOn_empty
    {d : ℕ} (E : Finset (CubicEdge d)) (omega : EdgeConfiguration d)
    {x y : Cubic d}
    (hfinite : numberOfInfiniteOpenClusters d (spliceOn E ∅ omega) < ⊤)
    (hx : hasInfiniteOpenClusterFrom d (spliceOn E ∅ omega) x)
    (hy : hasInfiniteOpenClusterFrom d (spliceOn E ∅ omega) y)
    (hsep : spliceOn E ∅ omega ∉ connectionEvent d x y)
    (hjoin : spliceOn E E omega ∈ connectionEvent d x y) :
    numberOfInfiniteOpenClusters d (spliceOn E E omega) <
      numberOfInfiniteOpenClusters d (spliceOn E ∅ omega) :=
  numberOfInfiniteOpenClusters_spliceOn_all_lt_spliceOn E ∅ (by simp) omega
    hfinite hx hy hsep hjoin

theorem mem_exactlyOneInfiniteOpenClusterEvent_iff {d : ℕ} {omega : EdgeConfiguration d} :
    omega ∈ exactlyOneInfiniteOpenClusterEvent d ↔
      ∃ x : Cubic d, hasInfiniteOpenClusterFrom d omega x ∧
        ∀ y : Cubic d, hasInfiniteOpenClusterFrom d omega y →
          omega ∈ connectionEvent d x y := by
  constructor
  · rw [exactlyOneInfiniteOpenClusterEvent, Set.mem_setOf_eq, numberOfInfiniteOpenClusters,
      Set.encard_eq_one]
    rintro ⟨C, hC⟩
    have hCinf : C ∈ infiniteOpenComponents d omega := by simp [hC]
    obtain ⟨x, hx⟩ := hCinf.nonempty
    have hxC : (cubicOpenGraph d omega).connectedComponentMk x = C :=
      (C.mem_supp_iff x).mp hx
    refine ⟨x, ?_, ?_⟩
    · rw [← connectedComponentMk_mem_infiniteOpenComponents_iff, hC]
      exact hxC ▸ Set.mem_singleton C
    · intro y hy
      rw [← connectedComponentMk_eq_iff_mem_connectionEvent]
      have hyC : (cubicOpenGraph d omega).connectedComponentMk y = C := by
        have hyMem : (cubicOpenGraph d omega).connectedComponentMk y ∈
            infiniteOpenComponents d omega :=
          connectedComponentMk_mem_infiniteOpenComponents_iff.mpr hy
        simpa [hC] using hyMem
      exact hxC.trans hyC.symm
  · rintro ⟨x, hx, hunique⟩
    rw [exactlyOneInfiniteOpenClusterEvent, Set.mem_setOf_eq, numberOfInfiniteOpenClusters,
      Set.encard_eq_one]
    refine ⟨(cubicOpenGraph d omega).connectedComponentMk x, ?_⟩
    ext C
    constructor
    · intro hC
      obtain ⟨y, hy⟩ := hC.nonempty
      have hyC : (cubicOpenGraph d omega).connectedComponentMk y = C :=
        (C.mem_supp_iff y).mp hy
      have hyInf : hasInfiniteOpenClusterFrom d omega y := by
        rw [← connectedComponentMk_mem_infiniteOpenComponents_iff, hyC]
        exact hC
      have hxy : (cubicOpenGraph d omega).connectedComponentMk x =
          (cubicOpenGraph d omega).connectedComponentMk y :=
        connectedComponentMk_eq_iff_mem_connectionEvent.mpr (hunique y hyInf)
      rw [Set.mem_singleton_iff]
      exact hyC.symm.trans hxy.symm
    · rw [Set.mem_singleton_iff]
      rintro rfl
      exact connectedComponentMk_mem_infiniteOpenComponents_iff.mpr hx

theorem measurableSet_exactlyOneInfiniteOpenClusterEvent (d : ℕ) :
    MeasurableSet (exactlyOneInfiniteOpenClusterEvent d) := by
  have hrepr : exactlyOneInfiniteOpenClusterEvent d =
      ⋃ x : Cubic d, infiniteClusterVertexEvent d x ∩
        ⋂ y : Cubic d, (infiniteClusterVertexEvent d y)ᶜ ∪ connectionEvent d x y := by
    ext omega
    rw [mem_exactlyOneInfiniteOpenClusterEvent_iff]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff, infiniteClusterVertexEvent, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, hall⟩
      refine ⟨x, hx, fun y ↦ ?_⟩
      by_cases hy : hasInfiniteOpenClusterFrom d omega y
      · exact Or.inr (hall y hy)
      · exact Or.inl hy
    · rintro ⟨x, hx, hall⟩
      refine ⟨x, hx, fun y hy ↦ ?_⟩
      rcases hall y with hnot | hconn
      · exact (hnot hy).elim
      · exact hconn
  rw [hrepr]
  exact MeasurableSet.iUnion fun x ↦
    (measurableSet_infiniteClusterVertexEvent d x).inter <|
      MeasurableSet.iInter fun y ↦
        (measurableSet_infiniteClusterVertexEvent d y).compl.union
          (measurableSet_connectionEvent d x y)

theorem measurableSet_atLeastInfiniteOpenClustersEvent (d k : ℕ) :
    MeasurableSet (atLeastInfiniteOpenClustersEvent d k) := by
  have hrepr : atLeastInfiniteOpenClustersEvent d k =
      ⋃ x : Fin k → Cubic d,
        (⋂ i, infiniteClusterVertexEvent d (x i)) ∩
          ⋂ i, ⋂ j, if i = j then Set.univ else (connectionEvent d (x i) (x j))ᶜ := by
    ext omega
    simp only [atLeastInfiniteOpenClustersEvent, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_iInter, infiniteClusterVertexEvent]
    constructor
    · rintro ⟨x, hinf, hsep⟩
      refine ⟨x, hinf, fun i j ↦ ?_⟩
      split_ifs with hij
      · trivial
      · exact hsep i j hij
    · rintro ⟨x, hinf, hsep⟩
      refine ⟨x, hinf, fun i j hij ↦ ?_⟩
      simpa [hij] using hsep i j
  rw [hrepr]
  exact MeasurableSet.iUnion fun x ↦
    (MeasurableSet.iInter fun i ↦ measurableSet_infiniteClusterVertexEvent d (x i)).inter <|
      MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ by
        by_cases hij : i = j
        · simp [hij]
        · simp only [hij, if_false]
          exact (measurableSet_connectionEvent d (x i) (x j)).compl

theorem measurableSet_infiniteOpenClusterWitnessEvent {d k : ℕ}
    (x : Fin k → Cubic d) : MeasurableSet (infiniteOpenClusterWitnessEvent x) := by
  have hrepr : infiniteOpenClusterWitnessEvent x =
      (⋂ i, infiniteClusterVertexEvent d (x i)) ∩
        ⋂ i, ⋂ j, if i = j then Set.univ else (connectionEvent d (x i) (x j))ᶜ := by
    ext omega
    simp only [infiniteOpenClusterWitnessEvent, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter, infiniteClusterVertexEvent]
    constructor
    · rintro ⟨hinf, hsep⟩
      refine ⟨hinf, fun i j ↦ ?_⟩
      split_ifs with hij
      · trivial
      · exact hsep i j hij
    · rintro ⟨hinf, hsep⟩
      refine ⟨hinf, fun i j hij ↦ ?_⟩
      simpa [hij] using hsep i j
  rw [hrepr]
  exact (MeasurableSet.iInter fun i ↦
    measurableSet_infiniteClusterVertexEvent d (x i)).inter <|
      MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ by
        by_cases hij : i = j
        · simp [hij]
        · simp only [hij, if_false]
          exact (measurableSet_connectionEvent d (x i) (x j)).compl

theorem atLeastInfiniteOpenClustersEvent_eq_iUnion_witness (d k : ℕ) :
    atLeastInfiniteOpenClustersEvent d k =
      ⋃ x : Fin k → Cubic d, infiniteOpenClusterWitnessEvent x := by
  ext omega
  simp [atLeastInfiniteOpenClustersEvent, infiniteOpenClusterWitnessEvent]

theorem atLeastInfiniteOpenClustersEvent_succ_subset (d k : ℕ) :
    atLeastInfiniteOpenClustersEvent d (k + 1) ⊆
      atLeastInfiniteOpenClustersEvent d k := by
  rintro omega ⟨x, hinf, hsep⟩
  refine ⟨fun i ↦ x i.castSucc, fun i ↦ hinf i.castSucc, fun i j hij ↦ ?_⟩
  apply hsep i.castSucc j.castSucc
  intro heq
  apply hij
  exact Fin.castSucc_injective _ heq

theorem measurableSet_exactlyKInfiniteOpenClustersEvent (d k : ℕ) :
    MeasurableSet (exactlyKInfiniteOpenClustersEvent d k) :=
  (measurableSet_atLeastInfiniteOpenClustersEvent d k).diff
    (measurableSet_atLeastInfiniteOpenClustersEvent d (k + 1))

theorem mem_atLeastInfiniteOpenClustersEvent_iff {d k : ℕ}
    {omega : EdgeConfiguration d} :
    omega ∈ atLeastInfiniteOpenClustersEvent d k ↔
      (k : ℕ∞) ≤ numberOfInfiniteOpenClusters d omega := by
  constructor
  · rintro ⟨x, hinf, hsep⟩
    let f : Fin k → {C // C ∈ infiniteOpenComponents d omega} := fun i ↦
      ⟨(cubicOpenGraph d omega).connectedComponentMk (x i),
        connectedComponentMk_mem_infiniteOpenComponents_iff.mpr (hinf i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hijIndex
      apply hsep i j hijIndex
      rw [← connectedComponentMk_eq_iff_mem_connectionEvent]
      exact congrArg Subtype.val hij
    have hcard := ENat.card_le_card_of_injective hf
    change (k : ℕ∞) ≤ (infiniteOpenComponents d omega).encard
    change ENat.card (Fin k) ≤ ENat.card {C // C ∈ infiniteOpenComponents d omega} at hcard
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] using hcard
  · intro hcard
    obtain ⟨t, htSub, htCard⟩ := Set.exists_subset_encard_eq hcard
    have htFinite : t.Finite := Set.finite_of_encard_eq_coe htCard
    letI : Fintype t := htFinite.fintype
    have hftCard : Fintype.card t = k := by
      apply ENat.coe_inj.mp
      calc
        (Fintype.card t : ℕ∞) = t.encard := by
          rw [Set.encard, ENat.card_eq_coe_fintype_card]
        _ = (k : ℕ∞) := htCard
    let e : Fin k ≃ t := (Fintype.equivFinOfCardEq hftCard).symm
    let rep : (cubicOpenGraph d omega).ConnectedComponent → Cubic d := fun C ↦
      Classical.choose C.nonempty_supp
    have hrep (C : (cubicOpenGraph d omega).ConnectedComponent) :
        (cubicOpenGraph d omega).connectedComponentMk (rep C) = C := by
      exact C.mem_supp_iff (rep C) |>.mp (Classical.choose_spec C.nonempty_supp)
    refine ⟨fun i ↦ rep (e i).1, fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · rw [← connectedComponentMk_mem_infiniteOpenComponents_iff, hrep]
      exact htSub (e i).2
    · intro hconn
      apply hij
      apply e.injective
      apply Subtype.ext
      have hcomponents := connectedComponentMk_eq_iff_mem_connectionEvent.mpr hconn
      simpa only [hrep] using hcomponents

theorem mem_exactlyKInfiniteOpenClustersEvent_iff {d k : ℕ}
    {omega : EdgeConfiguration d} :
    omega ∈ exactlyKInfiniteOpenClustersEvent d k ↔
      numberOfInfiniteOpenClusters d omega = k := by
  rw [exactlyKInfiniteOpenClustersEvent, Set.mem_diff,
    mem_atLeastInfiniteOpenClustersEvent_iff,
    mem_atLeastInfiniteOpenClustersEvent_iff]
  constructor
  · rintro ⟨hlower, hnot⟩
    apply le_antisymm
    · rw [← ENat.lt_coe_add_one_iff]
      exact lt_of_not_ge hnot
    · exact hlower
  · intro heq
    rw [heq]
    constructor
    · exact le_rfl
    · exact_mod_cast Nat.not_succ_le_self k

theorem bernoulliBondMeasure_real_exactlyKInfiniteOpenClustersEvent_eq_one
    {d k : ℕ} (p : I)
    (hk : (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d k) = 1)
    (hksucc : (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d (k + 1)) = 0) :
    (bernoulliBondMeasure d p).real (exactlyKInfiniteOpenClustersEvent d k) = 1 := by
  rw [exactlyKInfiniteOpenClustersEvent,
    measureReal_diff (atLeastInfiniteOpenClustersEvent_succ_subset d k)
      (measurableSet_atLeastInfiniteOpenClustersEvent d (k + 1)), hk, hksucc]
  norm_num

theorem exists_infiniteOpenClusterWitness_measureReal_pos
    {d k : ℕ} (p : I)
    (hexact : (bernoulliBondMeasure d p).real
      (exactlyKInfiniteOpenClustersEvent d k) = 1) :
    ∃ x : Fin k → Cubic d,
      0 < (bernoulliBondMeasure d p).real
        (infiniteOpenClusterWitnessEvent x ∩ exactlyKInfiniteOpenClustersEvent d k) := by
  let μ := bernoulliBondMeasure d p
  have hunion : exactlyKInfiniteOpenClustersEvent d k =
      ⋃ x : Fin k → Cubic d,
        infiniteOpenClusterWitnessEvent x ∩ exactlyKInfiniteOpenClustersEvent d k := by
    rw [← Set.iUnion_inter, ← atLeastInfiniteOpenClustersEvent_eq_iUnion_witness]
    exact (Set.inter_eq_right.mpr Set.diff_subset).symm
  have hnonzero : μ (⋃ x : Fin k → Cubic d,
      infiniteOpenClusterWitnessEvent x ∩ exactlyKInfiniteOpenClustersEvent d k) ≠ 0 := by
    rw [← hunion]
    intro hzero
    have hreal := congrArg ENNReal.toReal hzero
    rw [← Measure.real, hexact] at hreal
    norm_num at hreal
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null hnonzero
  refine ⟨x, ?_⟩
  change 0 < ENNReal.toReal (μ
    (infiniteOpenClusterWitnessEvent x ∩ exactlyKInfiniteOpenClustersEvent d k))
  exact ENNReal.toReal_pos hx.ne' (measure_ne_top μ _)

/-- If the event of having at least `k` infinite clusters has positive probability, then one
fixed `k`-tuple of lattice vertices witnesses this on an event of positive probability.  This
is the countable-union extraction used in the infinite-multiplicity half of Burton--Keane. -/
theorem exists_infiniteOpenClusterWitness_measureReal_pos_of_atLeast
    {d k : ℕ} (p : I)
    (hpos : 0 < (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d k)) :
    ∃ x : Fin k → Cubic d,
      0 < (bernoulliBondMeasure d p).real
        (infiniteOpenClusterWitnessEvent x) := by
  let μ := bernoulliBondMeasure d p
  have hnonzero : μ (⋃ x : Fin k → Cubic d,
      infiniteOpenClusterWitnessEvent x) ≠ 0 := by
    rw [← atLeastInfiniteOpenClustersEvent_eq_iUnion_witness]
    intro hzero
    have hreal := congrArg ENNReal.toReal hzero
    rw [← Measure.real] at hreal
    exact (ne_of_gt hpos) hreal
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null hnonzero
  refine ⟨x, ?_⟩
  change 0 < ENNReal.toReal (μ (infiniteOpenClusterWitnessEvent x))
  exact ENNReal.toReal_pos hx.ne' (measure_ne_top μ _)

theorem exists_trace_spliceOn_preimage_measureReal_pos
    {d : ℕ} {p : I}
    (E : Finset (CubicEdge d)) {A : Set (EdgeConfiguration d)}
    (hA : MeasurableSet A) (hpos : 0 < (bernoulliBondMeasure d p).real A) :
    ∃ s ⊆ E, 0 < (bernoulliBondMeasure d p).real
      ((fun omega ↦ spliceOn E s omega) ⁻¹' A) := by
  classical
  have hdecomp := setBernoulli_real_eq_sum_splice
    (ι := CubicEdge d) p E hA
  change (bernoulliBondMeasure d p).real A = _ at hdecomp
  by_contra hnone
  push Not at hnone
  have hzero (s : Finset (CubicEdge d)) (hs : s ⊆ E) :
      (bernoulliBondMeasure d p).real
        ((fun omega ↦ spliceOn E s omega) ⁻¹' A) = 0 := by
    exact le_antisymm (hnone s hs) measureReal_nonneg
  have hsumzero :
      ∑ s ∈ E.powerset, finiteBernoulliWeight E (p : ℝ) s *
        (bernoulliBondMeasure d p).real
          ((fun omega ↦ spliceOn E s omega) ⁻¹' A) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero s (Finset.mem_powerset.mp hs), mul_zero]
  have hsumzero' :
      ∑ s ∈ E.powerset, finiteBernoulliWeight E (p : ℝ) s *
        setBer((Set.univ : Set (CubicEdge d)), p).real
          ((fun omega ↦ spliceOn E s omega) ⁻¹' A) = 0 := by
    simpa [bernoulliBondMeasure] using hsumzero
  rw [hdecomp, hsumzero'] at hpos
  exact lt_irrefl 0 hpos

/-- The finite-energy step of Burton--Keane: an almost-sure finite component multiplicity
cannot be at least two. -/
theorem not_finite_infiniteOpenCluster_multiplicity
    {d k : ℕ} {p : I} (hk2 : 2 ≤ k)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hk : (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d k) = 1)
    (hksucc : (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d (k + 1)) = 0) : False := by
  classical
  let μ := bernoulliBondMeasure d p
  have hexact := bernoulliBondMeasure_real_exactlyKInfiniteOpenClustersEvent_eq_one
    p hk hksucc
  obtain ⟨x, hxpos⟩ := exists_infiniteOpenClusterWitness_measureReal_pos p hexact
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  obtain ⟨w⟩ := nonempty_cubicWalk d (x i0) (x i1)
  let E := walkEdgeFinset w
  let A := infiniteOpenClusterWitnessEvent x ∩ exactlyKInfiniteOpenClustersEvent d k
  have hAm : MeasurableSet A :=
    (measurableSet_infiniteOpenClusterWitnessEvent x).inter
      (measurableSet_exactlyKInfiniteOpenClustersEvent d k)
  obtain ⟨s, hs, hspliced⟩ :=
    exists_trace_spliceOn_preimage_measureReal_pos E hAm (by simpa [μ, A] using hxpos)
  let B := (atLeastInfiniteOpenClustersEvent d k)ᶜ
  have hBm : MeasurableSet B :=
    (measurableSet_atLeastInfiniteOpenClustersEvent d k).compl
  have hsubset :
      (fun omega ↦ spliceOn E s omega) ⁻¹' A ⊆
        (fun omega ↦ spliceOn E E omega) ⁻¹' B := by
    intro omega homega
    rcases homega with ⟨hwitness, hexactOmega⟩
    have hcount : numberOfInfiniteOpenClusters d (spliceOn E s omega) = k :=
      mem_exactlyKInfiniteOpenClustersEvent_iff.mp hexactOmega
    have hfinite : numberOfInfiniteOpenClusters d (spliceOn E s omega) < ⊤ := by
      rw [hcount]
      exact ENat.coe_lt_top k
    have hjoin : spliceOn E E omega ∈ connectionEvent d (x i0) (x i1) := by
      refine ⟨w, walkIsOpen_of_mem_openEdgeSetEvent_of_walkEdgeFinset_subset ?_ w
        (show walkEdgeFinset w ⊆ E from Finset.Subset.rfl)⟩
      intro e he
      rw [mem_spliceOn]
      exact Or.inl he
    have hdrop := numberOfInfiniteOpenClusters_spliceOn_all_lt_spliceOn
      E s hs omega hfinite (hwitness.1 i0) (hwitness.1 i1)
        (hwitness.2 i0 i1 hi01) hjoin
    change spliceOn E E omega ∉ atLeastInfiniteOpenClustersEvent d k
    rw [mem_atLeastInfiniteOpenClustersEvent_iff]
    intro hatLeast
    rw [hcount] at hdrop
    exact (not_le_of_gt hdrop) hatLeast
  have hallPreimagePos :
      0 < μ.real ((fun omega ↦ spliceOn E E omega) ⁻¹' B) :=
    hspliced.trans_le (measureReal_mono hsubset)
  have hfactor := setBernoulli_real_inter_finiteCylinder
    (ι := CubicEdge d) p (E := E) (s := E) Finset.Subset.rfl hBm
  change μ.real (B ∩ finiteCylinder E E) =
    μ.real ((fun omega ↦ spliceOn E E omega) ⁻¹' B) *
      finiteBernoulliWeight E (p : ℝ) E at hfactor
  have hweight : 0 < finiteBernoulliWeight E (p : ℝ) E :=
    finiteBernoulliWeight_pos hp0 hp1 E
  have hinterPos : 0 < μ.real (B ∩ finiteCylinder E E) := by
    rw [hfactor]
    exact mul_pos hallPreimagePos hweight
  have hBpos : 0 < μ.real B :=
    hinterPos.trans_le (measureReal_mono Set.inter_subset_left)
  have hBzero : μ.real B = 0 := by
    change μ.real (atLeastInfiniteOpenClustersEvent d k)ᶜ = 0
    rw [measureReal_compl
      (measurableSet_atLeastInfiniteOpenClustersEvent d k), probReal_univ, hk]
    norm_num
  exact (ne_of_gt hBpos) hBzero

private theorem cubicTranslationConfigurationPullback_mem_atLeastInfiniteOpenClustersEvent_iff
    {d k : ℕ} (a : Cubic d) (omega : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback cubicOrigin a omega ∈
        atLeastInfiniteOpenClustersEvent d k ↔
      omega ∈ atLeastInfiniteOpenClustersEvent d k := by
  let T := cubicTranslationConfigurationPullback cubicOrigin a
  let f : Cubic d → Cubic d := cubicTranslate cubicOrigin a
  let g : Cubic d → Cubic d := cubicTranslate a cubicOrigin
  have hfg (z : Cubic d) : f (g z) = z := by
    change cubicTranslationEquiv cubicOrigin a
      (cubicTranslationEquiv a cubicOrigin z) = z
    exact (cubicTranslationEquiv cubicOrigin a).right_inv z
  constructor
  · rintro ⟨x, hinf, hsep⟩
    refine ⟨fun i ↦ f (x i), fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · exact (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        omega cubicOrigin a (x i)).mp (hinf i)
    · intro hconn
      apply hsep i j hij
      have hiff := cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
        (cubicTranslationIso cubicOrigin a) omega (x i) (x j)
      exact hiff.mpr hconn
  · rintro ⟨x, hinf, hsep⟩
    refine ⟨fun i ↦ g (x i), fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · have hback :=
        (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
          omega cubicOrigin a (g (x i))).mpr ?_
      · exact hback
      · change hasInfiniteOpenClusterFrom d omega (f (g (x i)))
        rw [hfg]
        exact hinf i
    · intro hconn
      have hiff := cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
        (cubicTranslationIso cubicOrigin a) omega (g (x i)) (g (x j))
      apply hsep i j hij
      have := hiff.mp hconn
      change omega ∈ connectionEvent d (f (g (x i))) (f (g (x j))) at this
      simpa only [hfg] using this

theorem invariantUnderCubicTranslations_atLeastInfiniteOpenClustersEvent (d k : ℕ) :
    IsInvariantUnderCubicTranslations (atLeastInfiniteOpenClustersEvent d k) := by
  intro a
  ext omega
  exact cubicTranslationConfigurationPullback_mem_atLeastInfiniteOpenClustersEvent_iff a omega

theorem bernoulliBondMeasure_real_atLeastInfiniteOpenClustersEvent_eq_zero_or_one
    {d : ℕ} (hd : 1 ≤ d) (p : I) (k : ℕ) :
    (bernoulliBondMeasure d p).real (atLeastInfiniteOpenClustersEvent d k) = 0 ∨
      (bernoulliBondMeasure d p).real (atLeastInfiniteOpenClustersEvent d k) = 1 :=
  bernoulliBondMeasure_real_eq_zero_or_one_of_translationInvariant hd p
    (measurableSet_atLeastInfiniteOpenClustersEvent d k)
    (invariantUnderCubicTranslations_atLeastInfiniteOpenClustersEvent d k)

end Percolation
