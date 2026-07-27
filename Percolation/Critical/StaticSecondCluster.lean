import Percolation.Critical.StaticCoalescence
import Percolation.Core.CubicWalkLevel
import Percolation.Critical.SlabConnectivity
import Percolation.Critical.StaticBlockPath
import Percolation.Critical.StaticLargeCrossing

/-!
# Strip events for a second macroscopic cluster

This file introduces the exact finite events `A_k(x,y)` used in Grimmett (7.105)--(7.109).
The coordinate parameter is an integer because the source peels hyperplanes from `-n` to `n`.
Keeping the strip half open is important: it makes the two entrance vertices belong to the
strip while the target hyperplane is fresh for the next conditional step.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A pointwise contraction of finite-support conditional slice probabilities integrates to
the corresponding ratio-free event inequality. -/
theorem setBernoulli_real_le_mul_of_sliceProbability_le
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (E : Finset ι) (p : I) {A B : Set (Set ι)} {q : ℝ}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hpoint : ∀ ω, sliceProbability E p B ω ≤ q * sliceProbability E p A ω) :
    setBer((Set.univ : Set ι), p).real B ≤
      q * setBer((Set.univ : Set ι), p).real A := by
  let f := sliceProbability E p A
  let g := sliceProbability E p B
  have hfDep : DependsOnFun E f := sliceProbability_dependsOnFun E p A
  have hgDep : DependsOnFun E g := sliceProbability_dependsOnFun E p B
  have hfInt : Integrable f setBer((Set.univ : Set ι), p) := by
    apply integrable_of_bounded_measurable hfDep.measurable
    intro ω
    rw [abs_of_nonneg (sliceProbability_nonneg E p A ω)]
    exact sliceProbability_le_one E p A ω
  have hgInt : Integrable g setBer((Set.univ : Set ι), p) := by
    apply integrable_of_bounded_measurable hgDep.measurable
    intro ω
    rw [abs_of_nonneg (sliceProbability_nonneg E p B ω)]
    exact sliceProbability_le_one E p B ω
  calc
    setBer((Set.univ : Set ι), p).real B =
        ∫ ω, g ω ∂setBer((Set.univ : Set ι), p) :=
      (integral_sliceProbability E p hBm).symm
    _ ≤ ∫ ω, q * f ω ∂setBer((Set.univ : Set ι), p) :=
      integral_mono hgInt (hfInt.const_mul q) hpoint
    _ = q * ∫ ω, f ω ∂setBer((Set.univ : Set ι), p) :=
      integral_const_mul q f
    _ = q * setBer((Set.univ : Set ι), p).real A := by
      rw [integral_sliceProbability E p hAm]

/-- Splicing a disjoint coordinate block leaves a finitely supported event unchanged. -/
theorem DependsOn.spliceOn_mem_iff_of_disjoint
    {ι : Type*} [DecidableEq ι] {E F s : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn F A) (hs : s ⊆ E)
    (hdisj : Disjoint (E : Set ι) (F : Set ι)) (ω : Set ι) :
    spliceOn E s ω ∈ A ↔ ω ∈ A := by
  apply hA
  intro e heF
  have heE : e ∉ E := by
    intro heE
    exact Set.disjoint_left.mp hdisj heE heF
  exact mem_spliceOn_of_notMem hs heE

/-! ### Finite-component path and diameter witnesses -/

/-- Two ambient vertices in one finite-box component are connected by an open walk which stays
inside that box. -/
theorem mem_connectionEventWithinVertices_of_mem_finiteBoxGraphComponent
    {d n : ℕ} {ω : EdgeConfiguration d} {c u v : Cubic d}
    {C : (finiteBoxOpenGraph d ω c n).ConnectedComponent}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices C) :
    ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d c n : Set (Cubic d)) u v := by
  classical
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at hu hv
  obtain ⟨huBox, _huBox', huSupp⟩ := hu
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := hv
  let uBox : {z : Cubic d // z ∈ cubicMetricBox d c n} := ⟨u, huBox⟩
  let vBox : {z : Cubic d // z ∈ cubicMetricBox d c n} := ⟨v, hvBox⟩
  have huSupp' : uBox ∈ C.supp := by simpa [uBox] using huSupp
  have hvSupp' : vBox ∈ C.supp := by simpa [vBox] using hvSupp
  let emb := SimpleGraph.Embedding.induce
    (G := cubicOpenGraph d ω) (cubicMetricBox d c n : Set (Cubic d))
  let wBox := (C.reachable_of_mem_supp huSupp' hvSupp').some
  let wOpen := wBox.map emb.toHom
  let w := wOpen.map (cubicOpenGraphHom d ω)
  refine ⟨w, walkIsOpen_map_cubicOpenGraphHom wOpen, ?_⟩
  intro z hz
  have hwSupport : w.support = wOpen.support := by
    change (wOpen.map (cubicOpenGraphHom d ω)).support = wOpen.support
    rw [SimpleGraph.Walk.support_map]
    change List.map id wOpen.support = wOpen.support
    exact List.map_id _
  have hz' : z ∈ wOpen.support := by
    rw [← hwSupport]
    exact hz
  change z ∈ (wBox.map emb.toHom).support at hz'
  rw [SimpleGraph.Walk.support_map] at hz'
  obtain ⟨zBox, hzBox, hzval⟩ := List.mem_map.mp hz'
  simpa [emb, ← hzval] using zBox.property

/-- The nested finite suprema defining a nonempty component's diameter are attained. -/
theorem exists_pair_mem_finiteBoxGraphComponent_lInfDist_eq_diameter
    {d n : ℕ} {x : Cubic d}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) :
    ∃ u ∈ finiteBoxGraphComponentVertices C,
      ∃ v ∈ finiteBoxGraphComponentVertices C,
        cubicLInfDist u v = finiteBoxGraphComponentDiameter C := by
  classical
  let S := finiteBoxGraphComponentVertices C
  have hS : S.Nonempty := finiteBoxGraphComponentVertices_nonempty C
  have hout := Finset.sup_mem_of_nonempty
    (s := S) (f := fun u ↦ S.sup fun v ↦ cubicLInfDist u v) hS
  rcases hout with ⟨u, hu, huEq⟩
  have hin := Finset.sup_mem_of_nonempty
    (s := S) (f := fun v ↦ cubicLInfDist u v) hS
  rcases hin with ⟨v, hv, hvEq⟩
  exact ⟨u, hu, v, hv, by
    simpa [S, finiteBoxGraphComponentDiameter] using hvEq.trans huEq⟩

/-- In positive dimension, one coordinate attains the `L∞` distance. -/
theorem exists_coord_natAbs_eq_cubicLInfDist {d : ℕ} (hd : 1 ≤ d)
    (u v : Cubic d) :
    ∃ i : Fin d, (v i - u i).natAbs = cubicLInfDist u v := by
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  have hU : (Finset.univ : Finset (Fin d)).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
  have h := Finset.sup_mem_of_nonempty
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i ↦ (v i - u i).natAbs) hU
  rcases h with ⟨i, _hi, hi⟩
  exact ⟨i, by simpa [cubicLInfDist] using hi⟩

/-- A within-box open connection between representatives of two finite-box components forces
the components to be equal. -/
theorem finiteBoxGraphComponents_eq_of_connectionWithinVertices
    {d n : ℕ} {ω : EdgeConfiguration d} {c u v : Cubic d}
    {C D : (finiteBoxOpenGraph d ω c n).ConnectedComponent}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices D)
    (huv : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d c n : Set (Cubic d)) u v) : C = D := by
  classical
  obtain ⟨huBox, _huBox', huSupp⟩ := by
    simpa only [finiteBoxGraphComponentVertices, Finset.mem_filter] using hu
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := by
    simpa only [finiteBoxGraphComponentVertices, Finset.mem_filter] using hv
  obtain ⟨w, hwopen, hwbox⟩ := huv
  obtain ⟨q⟩ := nonempty_finiteBoxOpenGraph_walk_of_walkIsOpen_of_support w hwopen hwbox
  have hreach : (finiteBoxOpenGraph d ω c n).Reachable
      ⟨u, huBox⟩ ⟨v, hvBox⟩ := by
    exact ⟨q.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
  have huC : (⟨u, huBox⟩ : {z // z ∈ cubicMetricBox d c n}) ∈ C.supp := by
    simpa using huSupp
  have hvD : (⟨v, hvBox⟩ : {z // z ∈ cubicMetricBox d c n}) ∈ D.supp := by
    simpa using hvSupp
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at huC hvD
  exact huC.symm.trans ((SimpleGraph.ConnectedComponent.sound hreach).trans hvD)

/-- A component of diameter at least `m` contains an oriented coordinate span of length at
least `m`. -/
theorem exists_oriented_coordinate_span_of_le_finiteBoxGraphComponentDiameter
    {d n m : ℕ} (hd : 1 ≤ d) {x : Cubic d}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (D : G.ConnectedComponent) (hm : m ≤ finiteBoxGraphComponentDiameter D) :
    ∃ i : Fin d, ∃ u ∈ finiteBoxGraphComponentVertices D,
      ∃ v ∈ finiteBoxGraphComponentVertices D,
        u i ≤ v i ∧ (m : ℤ) ≤ v i - u i := by
  obtain ⟨u, hu, v, hv, huvdiam⟩ :=
    exists_pair_mem_finiteBoxGraphComponent_lInfDist_eq_diameter D
  obtain ⟨i, hi⟩ := exists_coord_natAbs_eq_cubicLInfDist hd u v
  have hmnat : m ≤ (v i - u i).natAbs := by
    rw [hi, huvdiam]
    exact hm
  rcases le_total (u i) (v i) with huv | hvu
  · refine ⟨i, u, hu, v, hv, huv, ?_⟩
    have hmz : (m : ℤ) ≤ ((v i - u i).natAbs : ℤ) := by exact_mod_cast hmnat
    rwa [Int.natAbs_of_nonneg (sub_nonneg.mpr huv)] at hmz
  · refine ⟨i, v, hv, u, hu, hvu, ?_⟩
    have hmnat' : m ≤ (u i - v i).natAbs := by
      rw [show u i - v i = -(v i - u i) by omega, Int.natAbs_neg]
      exact hmnat
    have hmz : (m : ℤ) ≤ ((u i - v i).natAbs : ℤ) := by exact_mod_cast hmnat'
    rwa [Int.natAbs_of_nonneg (sub_nonneg.mpr hvu)] at hmz

/-- Symmetry of an open connection constrained to a vertex region. -/
theorem connectionEventWithinVertices_symm_mem
    {d : ℕ} {A : Set (Cubic d)} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventWithinVertices d A x y) :
    ω ∈ connectionEventWithinVertices d A y x := by
  obtain ⟨w, hwopen, hwA⟩ := hxy
  exact ⟨w.reverse, walkIsOpen_reverse hwopen, by
    intro z hz
    exact hwA z (by simpa using hz)⟩

/-- Transitivity of open connections constrained to one vertex region. -/
theorem connectionEventWithinVertices_trans_mem
    {d : ℕ} {A : Set (Cubic d)} {x y z : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventWithinVertices d A x y)
    (hyz : ω ∈ connectionEventWithinVertices d A y z) :
    ω ∈ connectionEventWithinVertices d A x z := by
  obtain ⟨p, hpopen, hpA⟩ := hxy
  obtain ⟨q, hqopen, hqA⟩ := hyz
  exact ⟨p.append q, walkIsOpen_append hpopen hqopen, by
    intro u hu
    rw [SimpleGraph.Walk.mem_support_append_iff] at hu
    exact hu.elim (hpA u) (hqA u)⟩

/-- Extract the part of an open cubic walk between its last visit to the lower level and its
first subsequent visit to the upper level.  Every vertex of the extracted walk lies in the
closed coordinate band.  This is the precise deterministic localization used for Grimmett's
frontier sets `V_i(z)`. -/
theorem exists_open_cubicWalk_between_levels
    {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hwopen : walkIsOpen ω w)
    (i : Fin d) (a b : ℤ) (hab : a ≤ b)
    (hu : u i ≤ a) (hv : b ≤ v i) :
    ∃ x y : Cubic d, ∃ q : (cubicGraph d).Walk x y,
      x i = a ∧ y i = b ∧ walkIsOpen ω q ∧
        ∀ z ∈ q.support, a ≤ z i ∧ z i ≤ b ∧ z ∈ w.support := by
  obtain ⟨y, q, hy, hqUpper, hqSupport, hqPrefix⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end (G := cubicGraph d) le_rfl
      w i b (hu.trans hab) hv
  have hqOpen : walkIsOpen ω q :=
    walkIsOpen_of_edges_subset hwopen hqPrefix.subset
  obtain ⟨x, r, hx, hrLower, hrSupport, hrPrefix⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_end_le (G := cubicGraph d) le_rfl
      q.reverse i a (by simpa [hy] using hab) (by simpa using hu)
  have hrOpen : walkIsOpen ω r :=
    walkIsOpen_of_edges_subset (walkIsOpen_reverse hqOpen) hrPrefix.subset
  refine ⟨x, y, r.reverse, hx, hy, walkIsOpen_reverse hrOpen, ?_⟩
  intro z hz
  have hzr : z ∈ r.support := by simpa using hz
  have hzqrev : z ∈ q.reverse.support := hrSupport z hzr
  have hzq : z ∈ q.support := by simpa using hzqrev
  exact ⟨hrLower z hzr, hqUpper z hzq, hqSupport z hzq⟩

/-- The coordinate hyperplane `H_r={x∈B(n):x_i=r}`. -/
noncomputable def coordinateHyperplaneVertices
    (d n : ℕ) (i : Fin d) (r : ℤ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin n).filter fun x ↦ x i = r

@[simp]
theorem mem_coordinateHyperplaneVertices_iff {d n : ℕ} {i : Fin d} {r : ℤ}
    {x : Cubic d} :
    x ∈ coordinateHyperplaneVertices d n i r ↔
      x ∈ cubicMetricBox d cubicOrigin n ∧ x i = r := by
  simp [coordinateHyperplaneVertices]

/-- The half-open coordinate strip `U_[a,b)={x∈B(n):a≤x_i<b}`. -/
noncomputable def coordinateHalfOpenStripVertices
    (d n : ℕ) (i : Fin d) (a b : ℤ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin n).filter fun x ↦ a ≤ x i ∧ x i < b

@[simp]
theorem mem_coordinateHalfOpenStripVertices_iff {d n : ℕ} {i : Fin d} {a b : ℤ}
    {x : Cubic d} :
    x ∈ coordinateHalfOpenStripVertices d n i a b ↔
      x ∈ cubicMetricBox d cubicOrigin n ∧ a ≤ x i ∧ x i < b := by
  simp [coordinateHalfOpenStripVertices]

@[simp]
theorem coordinateHalfOpenStripVertices_self
    (d n : ℕ) (i : Fin d) (a : ℤ) :
    coordinateHalfOpenStripVertices d n i a a = ∅ := by
  ext x
  simp

/-- The closed coordinate strip `U_[a,b]={x∈B(n):a≤x_i≤b}`.  Closed strips carry the
first/last-hit paths to the next frontier; the non-coalescence event uses the half-open strip
so that the next layer remains fresh. -/
noncomputable def coordinateClosedStripVertices
    (d n : ℕ) (i : Fin d) (a b : ℤ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin n).filter fun x ↦ a ≤ x i ∧ x i ≤ b

@[simp]
theorem mem_coordinateClosedStripVertices_iff {d n : ℕ} {i : Fin d} {a b : ℤ}
    {x : Cubic d} :
    x ∈ coordinateClosedStripVertices d n i a b ↔
      x ∈ cubicMetricBox d cubicOrigin n ∧ a ≤ x i ∧ x i ≤ b := by
  simp [coordinateClosedStripVertices]

/-- All cubic edges whose two endpoints lie in one closed coordinate band. -/
noncomputable def coordinateClosedBandEdges
    (d n : ℕ) (i : Fin d) (a b : ℤ) : Finset (CubicEdge d) := by
  classical
  exact (cubicBoxEdges d cubicOrigin n).filter fun e ↦
    ∀ z ∈ (e : Sym2 (Cubic d)), a ≤ z i ∧ z i ≤ b

@[simp]
theorem mem_coordinateClosedBandEdges_iff {d n : ℕ} {i : Fin d} {a b : ℤ}
    {e : CubicEdge d} :
    e ∈ coordinateClosedBandEdges d n i a b ↔
      e ∈ cubicBoxEdges d cubicOrigin n ∧
        ∀ z ∈ (e : Sym2 (Cubic d)), a ≤ z i ∧ z i ≤ b := by
  classical
  simp [coordinateClosedBandEdges]

/-- Every edge of a walk supported in a closed coordinate band belongs to its explicit finite
edge support. -/
theorem walkEdgeFinset_subset_coordinateClosedBandEdges_of_support
    {d n : ℕ} {i : Fin d} {a b : ℤ} {x y : Cubic d}
    (w : (cubicGraph d).Walk x y)
    (hw : ∀ z ∈ w.support, z ∈ coordinateClosedStripVertices d n i a b) :
    walkEdgeFinset w ⊆ coordinateClosedBandEdges d n i a b := by
  intro e he
  rw [mem_coordinateClosedBandEdges_iff]
  have hwbox : ∀ z ∈ w.support, z ∈ cubicMetricBox d cubicOrigin n := by
    intro z hz
    exact (mem_coordinateClosedStripVertices_iff.mp (hw z hz)).1
  refine ⟨walkEdgeFinset_subset_cubicBoxEdges_of_support w hwbox he, ?_⟩
  intro z hz
  have he' : (e : Sym2 (Cubic d)) ∈ w.edges := (mem_walkEdgeFinset_iff w e).mp he
  have hzsupport : z ∈ w.support := w.mem_support_of_mem_edges he' hz
  exact (mem_coordinateClosedStripVertices_iff.mp (hw z hzsupport)).2

/-- A walk starting in a closed band and using only its internal edges remains in that band. -/
theorem walk_support_subset_coordinateClosedStrip_of_edges
    {d n : ℕ} {i : Fin d} {a b : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateClosedStripVertices d n i a b)
    (w : (cubicGraph d).Walk x y)
    (hw : walkEdgeFinset w ⊆ coordinateClosedBandEdges d n i a b) :
    ∀ z ∈ w.support, z ∈ coordinateClosedStripVertices d n i a b := by
  induction w with
  | nil => simpa using hx
  | @cons u v z huv q ih =>
      have he : (⟨s(u, v), (cubicGraph d).mem_edgeSet.mpr huv⟩ : CubicEdge d) ∈
          coordinateClosedBandEdges d n i a b := by
        apply hw
        rw [mem_walkEdgeFinset_iff]
        simp
      have hv : v ∈ coordinateClosedStripVertices d n i a b := by
        rw [mem_coordinateClosedStripVertices_iff]
        have heData := mem_coordinateClosedBandEdges_iff.mp he
        refine ⟨endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heData.1 (by simp), ?_⟩
        exact heData.2 v (by simp)
      have hq : walkEdgeFinset q ⊆ coordinateClosedBandEdges d n i a b := by
        intro e heq
        apply hw
        rw [mem_walkEdgeFinset_iff] at heq ⊢
        simp [heq]
      intro t ht
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hx
      · exact ih hv hq t ht

/-- On an entrance vertex in the band, vertex-constrained connectivity is exactly connectivity
using the explicit finite internal edge support. -/
theorem connectionEventWithinVertices_closedBand_eq_connectionEventIn
    {d n : ℕ} {i : Fin d} {a b : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateClosedStripVertices d n i a b) :
    connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i a b : Set (Cubic d)) x y =
      connectionEventIn d (coordinateClosedBandEdges d n i a b) x y := by
  apply Set.Subset.antisymm
  · rintro ω ⟨w, hwopen, hwband⟩
    exact ⟨w, hwopen, walkEdgeFinset_subset_coordinateClosedBandEdges_of_support w
      (fun z hz ↦ Finset.mem_coe.mp (hwband z hz))⟩
  · rintro ω ⟨w, hwopen, hwedges⟩
    exact ⟨w, hwopen, fun z hz ↦ Finset.mem_coe.mpr
      (walk_support_subset_coordinateClosedStrip_of_edges hx w hwedges z hz)⟩

/-- A connection constrained to a finite closed band depends only on that band's internal
edges. -/
theorem dependsOn_connectionEventWithinVertices_closedBand
    {d n : ℕ} {i : Fin d} {a b : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateClosedStripVertices d n i a b) :
    DependsOn (coordinateClosedBandEdges d n i a b)
      (connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i a b : Set (Cubic d)) x y) := by
  rw [connectionEventWithinVertices_closedBand_eq_connectionEventIn hx]
  exact dependsOn_connectionEventIn d _ x y

/-- Connection from `x` to `H_r`, constrained to the ambient box `B(n)`. -/
def connectionToCoordinateHyperplaneEvent
    (d n : ℕ) (i : Fin d) (r : ℤ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  ⋃ y ∈ coordinateHyperplaneVertices d n i r,
    connectionEventWithinVertices d (cubicMetricBox d cubicOrigin n : Set (Cubic d)) x y

theorem measurableSet_connectionToCoordinateHyperplaneEvent
    (d n : ℕ) (i : Fin d) (r : ℤ) (x : Cubic d) :
    MeasurableSet (connectionToCoordinateHyperplaneEvent d n i r x) := by
  apply (coordinateHyperplaneVertices d n i r).measurableSet_biUnion
  intro y _hy
  exact measurableSet_connectionEventWithinVertices d _ x y

theorem isIncreasingEvent_connectionToCoordinateHyperplaneEvent
    (d n : ℕ) (i : Fin d) (r : ℤ) (x : Cubic d) :
    IsIncreasingEvent (connectionToCoordinateHyperplaneEvent d n i r x) := by
  intro ω η hωη hω
  simp only [connectionToCoordinateHyperplaneEvent, Set.mem_iUnion] at hω ⊢
  obtain ⟨y, hy, hxy⟩ := hω
  exact ⟨y, hy, isIncreasingEvent_connectionEventWithinVertices d _ x y hωη hxy⟩

/-- An in-box connection whose endpoint lies beyond level `r` contains a first-hit connection
to `H_r`. -/
theorem mem_connectionToCoordinateHyperplaneEvent_of_connectionWithin
    {d n : ℕ} {i : Fin d} {r : ℤ} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) x y)
    (hxr : x i ≤ r) (hry : r ≤ y i) :
    ω ∈ connectionToCoordinateHyperplaneEvent d n i r x := by
  obtain ⟨w, hwopen, hwbox⟩ := hxy
  obtain ⟨z, q, hzcoord, hqside, hqsupport, hqedges⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end (G := cubicGraph d) le_rfl
      w i r hxr hry
  simp only [connectionToCoordinateHyperplaneEvent, Set.mem_iUnion]
  refine ⟨z, ?_, q, walkIsOpen_of_edges_subset hwopen hqedges.subset, ?_⟩
  · rw [mem_coordinateHyperplaneVertices_iff]
    exact ⟨hwbox z (hqsupport z q.end_mem_support), hzcoord⟩
  · intro u hu
    exact hwbox u (hqsupport u hu)

/-- A connection to a farther forward hyperplane contains a first-hit connection to every
intermediate hyperplane. -/
theorem connectionToCoordinateHyperplaneEvent_mono_width
    {d n k l : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ) (hkl : k ≤ l) :
    connectionToCoordinateHyperplaneEvent d n i (φ + l) x ⊆
      connectionToCoordinateHyperplaneEvent d n i (φ + k) x := by
  intro ω hω
  simp only [connectionToCoordinateHyperplaneEvent, Set.mem_iUnion] at hω ⊢
  obtain ⟨y, hy, w, hwopen, hwbox⟩ := hω
  have hxcoord := (mem_coordinateHyperplaneVertices_iff.mp hx).2
  have hycoord := (mem_coordinateHyperplaneVertices_iff.mp hy).2
  obtain ⟨z, q, hzcoord, hqside, hqsupport, hqedges⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end (G := cubicGraph d) le_rfl
      w i (φ + k) (by omega) (by omega)
  refine ⟨z, ?_, q, walkIsOpen_of_edges_subset hwopen hqedges.subset, ?_⟩
  · rw [mem_coordinateHyperplaneVertices_iff]
    exact ⟨hwbox z (hqsupport z q.end_mem_support), hzcoord⟩
  · intro u hu
    exact hwbox u (hqsupport u hu)

/-- Narrower half-open strips are contained in wider ones. -/
theorem coordinateHalfOpenStripVertices_mono_width
    {d n k l : ℕ} {i : Fin d} {φ : ℤ} (hkl : k ≤ l) :
    coordinateHalfOpenStripVertices d n i φ (φ + k) ⊆
      coordinateHalfOpenStripVertices d n i φ (φ + l) := by
  intro x hx
  rw [mem_coordinateHalfOpenStripVertices_iff] at hx ⊢
  exact ⟨hx.1, hx.2.1, by omega⟩

/-- Connection from an entrance vertex on `H_φ` to `H_(φ+k)` using only the closed forward
band.  This is the localized connection implicit in Grimmett's frontier construction. -/
def connectionAcrossCoordinateBandEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x : Cubic d) :
    Set (EdgeConfiguration d) :=
  ⋃ y ∈ coordinateHyperplaneVertices d n i (φ + k),
    connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ (φ + k) : Set (Cubic d)) x y

theorem measurableSet_connectionAcrossCoordinateBandEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x : Cubic d) :
    MeasurableSet (connectionAcrossCoordinateBandEvent d n i φ k x) := by
  apply (coordinateHyperplaneVertices d n i (φ + k)).measurableSet_biUnion
  intro y _hy
  exact measurableSet_connectionEventWithinVertices d _ x y

/-- The localized frontier event is measurable with respect to the finite closed-band edge
support. -/
theorem dependsOn_connectionAcrossCoordinateBandEvent
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ) :
    DependsOn (coordinateClosedBandEdges d n i φ (φ + k))
      (connectionAcrossCoordinateBandEvent d n i φ k x) := by
  have hxBand : x ∈ coordinateClosedStripVertices d n i φ (φ + k) := by
    rw [mem_coordinateClosedStripVertices_iff]
    have hxeq := (mem_coordinateHyperplaneVertices_iff.mp hx).2
    exact ⟨(mem_coordinateHyperplaneVertices_iff.mp hx).1, by omega, by omega⟩
  intro ω η hagree
  constructor
  · intro hω
    simp only [connectionAcrossCoordinateBandEvent, Set.mem_iUnion] at hω ⊢
    obtain ⟨y, hy, hxy⟩ := hω
    exact ⟨y, hy,
      (dependsOn_connectionEventWithinVertices_closedBand hxBand hagree).mp hxy⟩
  · intro hη
    simp only [connectionAcrossCoordinateBandEvent, Set.mem_iUnion] at hη ⊢
    obtain ⟨y, hy, hxy⟩ := hη
    exact ⟨y, hy,
      (dependsOn_connectionEventWithinVertices_closedBand hxBand hagree).mpr hxy⟩

/-- A farther localized band connection contains a localized connection to every intermediate
hyperplane. -/
theorem connectionAcrossCoordinateBandEvent_mono_width
    {d n k l : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ) (hkl : k ≤ l) :
    connectionAcrossCoordinateBandEvent d n i φ l x ⊆
      connectionAcrossCoordinateBandEvent d n i φ k x := by
  intro ω hω
  simp only [connectionAcrossCoordinateBandEvent, Set.mem_iUnion] at hω ⊢
  obtain ⟨y, hy, w, hwopen, hwband⟩ := hω
  have hxcoord := (mem_coordinateHyperplaneVertices_iff.mp hx).2
  have hycoord := (mem_coordinateHyperplaneVertices_iff.mp hy).2
  obtain ⟨z, q, hzcoord, hqside, hqsupport, hqedges⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end (G := cubicGraph d) le_rfl
      w i (φ + k) (by omega) (by omega)
  refine ⟨z, ?_, q, walkIsOpen_of_edges_subset hwopen hqedges.subset, ?_⟩
  · rw [mem_coordinateHyperplaneVertices_iff]
    have hzband := Finset.mem_coe.mp (hwband z (hqsupport z q.end_mem_support))
    rw [mem_coordinateClosedStripVertices_iff] at hzband
    exact ⟨hzband.1, hzcoord⟩
  · intro u hu
    have huband := Finset.mem_coe.mp (hwband u (hqsupport u hu))
    rw [mem_coordinateClosedStripVertices_iff] at huband
    exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
      ⟨huband.1, huband.2.1, hqside u hu⟩

/-- Proof-safe version of Grimmett's event `A_k(x,y)`: both entrance vertices reach the future
hyperplane, but they have not coalesced inside the intervening closed band.  Including the right
boundary layer is a harmless strengthening for the deterministic cover and makes the frontier
disjointness used by the peeling argument literally valid for vertex-induced connections. -/
def forwardTwoArmSeparationEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x y : Cubic d) :
    Set (EdgeConfiguration d) :=
  connectionAcrossCoordinateBandEvent d n i φ k x ∩
    connectionAcrossCoordinateBandEvent d n i φ k y ∩
      (connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i φ (φ + k) : Set (Cubic d)) x y)ᶜ

theorem measurableSet_forwardTwoArmSeparationEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x y : Cubic d) :
    MeasurableSet (forwardTwoArmSeparationEvent d n i φ k x y) :=
  ((measurableSet_connectionAcrossCoordinateBandEvent d n i φ k x).inter
    (measurableSet_connectionAcrossCoordinateBandEvent d n i φ k y)).inter
      (measurableSet_connectionEventWithinVertices d _ x y).compl

/-- `A_k(x,y)` is a finite cylinder on the explored closed band. -/
theorem dependsOn_forwardTwoArmSeparationEvent
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ) :
    DependsOn (coordinateClosedBandEdges d n i φ (φ + k))
      (forwardTwoArmSeparationEvent d n i φ k x y) := by
  have hxBand : x ∈ coordinateClosedStripVertices d n i φ (φ + k) := by
    rw [mem_coordinateClosedStripVertices_iff]
    have hxeq := (mem_coordinateHyperplaneVertices_iff.mp hx).2
    exact ⟨(mem_coordinateHyperplaneVertices_iff.mp hx).1, by omega, by omega⟩
  exact ((dependsOn_connectionAcrossCoordinateBandEvent hx).inter
    (dependsOn_connectionAcrossCoordinateBandEvent hy)).inter
      (dependsOn_connectionEventWithinVertices_closedBand hxBand).compl

/-! ### Frontier sets and fresh right-hand connections -/

/-- Vertices on the current hyperplane which are reachable from `x` through the explored
closed band. -/
noncomputable def coordinateBandFrontierVertices
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ)
    (x : Cubic d) (ω : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (coordinateHyperplaneVertices d n i (φ + k)).filter fun u ↦
    ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ (φ + k) : Set (Cubic d)) x u

@[simp]
theorem mem_coordinateBandFrontierVertices_iff
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x u : Cubic d} {ω : EdgeConfiguration d} :
    u ∈ coordinateBandFrontierVertices d n i φ k x ω ↔
      u ∈ coordinateHyperplaneVertices d n i (φ + k) ∧
        ω ∈ connectionEventWithinVertices d
          (coordinateClosedStripVertices d n i φ (φ + k) : Set (Cubic d)) x u := by
  classical
  simp [coordinateBandFrontierVertices]

/-- On `A_k(x,y)`, each entrance has a nonempty explored frontier. -/
theorem coordinateBandFrontierVertices_nonempty_of_mem_forwardTwoArm
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ forwardTwoArmSeparationEvent d n i φ k x y) :
    (coordinateBandFrontierVertices d n i φ k x ω).Nonempty ∧
      (coordinateBandFrontierVertices d n i φ k y ω).Nonempty := by
  simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff,
    connectionAcrossCoordinateBandEvent, Set.mem_iUnion] at hω
  obtain ⟨u, hu, hxu⟩ := hω.1.1
  obtain ⟨v, hv, hyv⟩ := hω.1.2
  exact ⟨⟨u, mem_coordinateBandFrontierVertices_iff.mpr ⟨hu, hxu⟩⟩,
    ⟨v, mem_coordinateBandFrontierVertices_iff.mpr ⟨hv, hyv⟩⟩⟩

/-- The two explored frontiers are disjoint on the separation event. -/
theorem coordinateBandFrontierVertices_disjoint_of_mem_forwardTwoArm
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ forwardTwoArmSeparationEvent d n i φ k x y) :
    Disjoint (coordinateBandFrontierVertices d n i φ k x ω)
      (coordinateBandFrontierVertices d n i φ k y ω) := by
  rw [Finset.disjoint_left]
  intro u hux huy
  have hux' := (mem_coordinateBandFrontierVertices_iff.mp hux).2
  have huy' := (mem_coordinateBandFrontierVertices_iff.mp huy).2
  have hxy := connectionEventWithinVertices_trans_mem hux'
    (connectionEventWithinVertices_symm_mem huy')
  exact hω.2 hxy

/-- Frontier sets are determined by the explored closed-band edge trace. -/
theorem coordinateBandFrontierVertices_eq_of_agree
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    {ω η : EdgeConfiguration d}
    (hagree : ∀ e ∈ coordinateClosedBandEdges d n i φ (φ + k),
      (e ∈ ω ↔ e ∈ η)) :
    coordinateBandFrontierVertices d n i φ k x ω =
      coordinateBandFrontierVertices d n i φ k x η := by
  have hxBand : x ∈ coordinateClosedStripVertices d n i φ (φ + k) := by
    rw [mem_coordinateClosedStripVertices_iff]
    have hxeq := (mem_coordinateHyperplaneVertices_iff.mp hx).2
    exact ⟨(mem_coordinateHyperplaneVertices_iff.mp hx).1, by omega, by omega⟩
  ext u
  simp only [mem_coordinateBandFrontierVertices_iff]
  constructor
  · rintro ⟨hu, hconn⟩
    exact ⟨hu, (dependsOn_connectionEventWithinVertices_closedBand hxBand hagree).mp hconn⟩
  · rintro ⟨hu, hconn⟩
    exact ⟨hu, (dependsOn_connectionEventWithinVertices_closedBand hxBand hagree).mpr hconn⟩

/-- The vertex one positive step from `x` in coordinate `i`. -/
def coordinateForwardStep {d : ℕ} (i : Fin d) (x : Cubic d) : Cubic d :=
  cubicStepFrom x (i, true)

/-- The corresponding positive coordinate edge. -/
def coordinateForwardStepEdge {d : ℕ} (i : Fin d) (x : Cubic d) : CubicEdge d :=
  cubicStepEdge x (i, true)

@[simp]
theorem coordinateForwardStep_apply_self {d : ℕ} (i : Fin d) (x : Cubic d) :
    coordinateForwardStep i x i = x i + 1 := by
  simp [coordinateForwardStep, cubicStepFrom, cubicDirectionIncrement]

theorem coordinateForwardStep_apply_of_ne {d : ℕ} {i j : Fin d} (hji : j ≠ i)
    (x : Cubic d) : coordinateForwardStep i x j = x j := by
  simp [coordinateForwardStep, cubicStepFrom, hji]

/-- A positive coordinate step stays in `B(n)` whenever its new coordinate has not crossed the
positive face. -/
theorem coordinateForwardStep_mem_cubicMetricBox
    {d n : ℕ} {i : Fin d} {x : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n) (hi : x i + 1 ≤ n) :
    coordinateForwardStep i x ∈ cubicMetricBox d cubicOrigin n := by
  rw [mem_cubicMetricBox]
  intro j
  have hxj := mem_cubicMetricBox.mp hx j
  simp only [cubicOrigin, zero_sub, zero_add] at hxj ⊢
  by_cases hji : j = i
  · subst j
    rw [coordinateForwardStep_apply_self]
    constructor <;> omega
  · rw [coordinateForwardStep_apply_of_ne hji]
    exact hxj

/-- An open positive step edge gives a one-edge connection inside every region containing its
two endpoints. -/
theorem mem_connectionEventWithinVertices_coordinateForwardStep
    {d : ℕ} {ω : EdgeConfiguration d} {i : Fin d} {x : Cubic d} {A : Set (Cubic d)}
    (hx : x ∈ A) (hstep : coordinateForwardStep i x ∈ A)
    (hopen : coordinateForwardStepEdge i x ∈ ω) :
    ω ∈ connectionEventWithinVertices d A x (coordinateForwardStep i x) := by
  let w : (cubicGraph d).Walk x (coordinateForwardStep i x) :=
    SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x (i, true)) SimpleGraph.Walk.nil
  refine ⟨w, ?_, ?_⟩
  · intro e he
    have hew := he
    have he' : e = s(x, coordinateForwardStep i x) := by
      simpa [w, coordinateForwardStep] using he
    have heq : (⟨e, w.edges_subset_edgeSet hew⟩ : CubicEdge d) =
        coordinateForwardStepEdge i x := by
      apply Subtype.ext
      simpa [coordinateForwardStepEdge, cubicStepEdge] using he'
    simpa [heq] using hopen
  · intro z hz
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · change z ∈ [coordinateForwardStep i x] at hz
      have : z = coordinateForwardStep i x := by simpa using hz
      subst z
      exact hstep

/-- A fresh connection uses the two forward step edges and then connects their new endpoints
inside the next closed band.  The one-layer shift makes its edge support disjoint from the
entire explored closed band. -/
def freshForwardBandConnectionEvent
    (d n : ℕ) (i : Fin d) (r : ℤ) (L : ℕ) (u v : Cubic d) :
    Set (EdgeConfiguration d) :=
  {ω | coordinateForwardStepEdge i u ∈ ω} ∩
    {ω | coordinateForwardStepEdge i v ∈ ω} ∩
      connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i (r + 1) (r + L + 1) : Set (Cubic d))
        (coordinateForwardStep i u) (coordinateForwardStep i v)

/-- Explicit finite edge support of a fresh right-hand connection. -/
noncomputable def freshForwardBandEdges
    (d n : ℕ) (i : Fin d) (r : ℤ) (L : ℕ) (u v : Cubic d) :
    Finset (CubicEdge d) :=
  {coordinateForwardStepEdge i u, coordinateForwardStepEdge i v} ∪
    coordinateClosedBandEdges d n i (r + 1) (r + L + 1)

/-- A single edge-coordinate event depends on that edge. -/
theorem dependsOn_edgeOpenEvent {d : ℕ} (e : CubicEdge d) :
    DependsOn {e} {ω : EdgeConfiguration d | e ∈ ω} := by
  intro ω η hagree
  exact hagree e (by simp)

/-- The fresh connection event is a finite cylinder on its displayed support. -/
theorem dependsOn_freshForwardBandConnectionEvent
    {d n L : ℕ} {i : Fin d} {r : ℤ} {u v : Cubic d}
    (hu : u ∈ coordinateHyperplaneVertices d n i r)
    (hupper : r + L + 1 ≤ n) :
    DependsOn (freshForwardBandEdges d n i r L u v)
      (freshForwardBandConnectionEvent d n i r L u v) := by
  have huData := mem_coordinateHyperplaneVertices_iff.mp hu
  have huStepBox : coordinateForwardStep i u ∈ cubicMetricBox d cubicOrigin n :=
    coordinateForwardStep_mem_cubicMetricBox huData.1 (by omega)
  have huStepBand : coordinateForwardStep i u ∈
      coordinateClosedStripVertices d n i (r + 1) (r + L + 1) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨huStepBox, by simp [huData.2], by
      rw [coordinateForwardStep_apply_self, huData.2]
      omega⟩
  have heU : {coordinateForwardStepEdge i u} ⊆
      freshForwardBandEdges d n i r L u v := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    simp [freshForwardBandEdges]
  have heV : {coordinateForwardStepEdge i v} ⊆
      freshForwardBandEdges d n i r L u v := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    simp [freshForwardBandEdges]
  have hBand : coordinateClosedBandEdges d n i (r + 1) (r + L + 1) ⊆
      freshForwardBandEdges d n i r L u v := by
    exact Finset.subset_union_right
  exact (((dependsOn_edgeOpenEvent (coordinateForwardStepEdge i u)).mono heU).inter
    ((dependsOn_edgeOpenEvent (coordinateForwardStepEdge i v)).mono heV)).inter
      ((dependsOn_connectionEventWithinVertices_closedBand huStepBand).mono hBand)

/-- The explored closed-band support and the shifted fresh support are disjoint. -/
theorem coordinateClosedBandEdges_disjoint_freshForwardBandEdges
    {d n L : ℕ} {i : Fin d} {φ r : ℤ} {u v : Cubic d}
    (hu : u ∈ coordinateHyperplaneVertices d n i r)
    (hv : v ∈ coordinateHyperplaneVertices d n i r) :
    Disjoint (coordinateClosedBandEdges d n i φ r)
      (freshForwardBandEdges d n i r L u v) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOld heFresh
  have heOldData := mem_coordinateClosedBandEdges_iff.mp heOld
  simp only [freshForwardBandEdges, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at heFresh
  rcases heFresh with (rfl | rfl) | heFuture
  · have hle := (heOldData.2 (coordinateForwardStep i u) (by
      simp [coordinateForwardStepEdge, coordinateForwardStep, cubicStepEdge])).2
    have hucoord := (mem_coordinateHyperplaneVertices_iff.mp hu).2
    simp [hucoord] at hle
  · have hle := (heOldData.2 (coordinateForwardStep i v) (by
      simp [coordinateForwardStepEdge, coordinateForwardStep, cubicStepEdge])).2
    have hvcoord := (mem_coordinateHyperplaneVertices_iff.mp hv).2
    simp [hvcoord] at hle
  · have heFutureData := mem_coordinateClosedBandEdges_iff.mp heFuture
    let z := e.1.out.1
    have hzmem : z ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem e.1
    have hold := (heOldData.2 z hzmem).2
    have hfresh := (heFutureData.2 z hzmem).1
    omega

/-- FKG and the two connector-edge probabilities turn an inner-band connection bound into a
fresh-connection bound. -/
theorem mul_sq_le_freshForwardBandConnection_probability
    {d n L : ℕ} (p : I) {i : Fin d} {r : ℤ} {u v : Cubic d} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hinner : δ ≤ (bernoulliBondMeasure d p).real
      (connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i (r + 1) (r + L + 1) : Set (Cubic d))
        (coordinateForwardStep i u) (coordinateForwardStep i v))) :
    (p : ℝ) ^ 2 * δ ≤ (bernoulliBondMeasure d p).real
      (freshForwardBandConnectionEvent d n i r L u v) := by
  let U : Set (EdgeConfiguration d) := {ω | coordinateForwardStepEdge i u ∈ ω}
  let V : Set (EdgeConfiguration d) := {ω | coordinateForwardStepEdge i v ∈ ω}
  let C : Set (EdgeConfiguration d) := connectionEventWithinVertices d
    (coordinateClosedStripVertices d n i (r + 1) (r + L + 1) : Set (Cubic d))
    (coordinateForwardStep i u) (coordinateForwardStep i v)
  have hUm : MeasurableSet U := (dependsOn_edgeOpenEvent _).measurableSet
  have hVm : MeasurableSet V := (dependsOn_edgeOpenEvent _).measurableSet
  have hCm : MeasurableSet C := measurableSet_connectionEventWithinVertices d _ _ _
  have hUinc : IsIncreasingEvent U := by
    intro ω η hωη hω
    exact hωη hω
  have hVinc : IsIncreasingEvent V := by
    intro ω η hωη hω
    exact hωη hω
  have hCinc : IsIncreasingEvent C := isIncreasingEvent_connectionEventWithinVertices d _ _ _
  have hUV := bernoulliBondMeasure_real_fkg p hUinc hVinc hUm hVm
  have hUVC := bernoulliBondMeasure_real_fkg p (hUinc.inter hVinc) hCinc
    (hUm.inter hVm) hCm
  have hUprob : (bernoulliBondMeasure d p).real U = (p : ℝ) := by
    have h := bernoulliBondMeasure_real_openEdgeSetEvent d p
      ({coordinateForwardStepEdge i u} : Finset (CubicEdge d))
    simpa [U, openEdgeSetEvent] using h
  have hVprob : (bernoulliBondMeasure d p).real V = (p : ℝ) := by
    have h := bernoulliBondMeasure_real_openEdgeSetEvent d p
      ({coordinateForwardStepEdge i v} : Finset (CubicEdge d))
    simpa [V, openEdgeSetEvent] using h
  calc
    (p : ℝ) ^ 2 * δ =
        ((bernoulliBondMeasure d p).real U * (bernoulliBondMeasure d p).real V) * δ := by
      rw [hUprob, hVprob]
      ring
    _ ≤ (bernoulliBondMeasure d p).real (U ∩ V) *
        (bernoulliBondMeasure d p).real C := by
      exact mul_le_mul hUV hinner hδ0 measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real ((U ∩ V) ∩ C) := hUVC
    _ = (bernoulliBondMeasure d p).real
        (freshForwardBandConnectionEvent d n i r L u v) := rfl

/-- Coordinate-axis point at signed level `r`. -/
def coordinateLevelVertex {d : ℕ} (i : Fin d) (r : ℤ) : Cubic d :=
  fun j ↦ if j = i then r else 0

/-- Translate level `r` to zero and permute coordinate `i` into the final coordinate. -/
def coordinateBandToLastIso {d : ℕ} (hd : 1 ≤ d) (i : Fin d) (r : ℤ) :
    cubicGraph d ≃g cubicGraph d :=
  (cubicTranslationIso (coordinateLevelVertex i r) cubicOrigin).trans
    (cubicCoordinatePermutationIso (Equiv.swap i ⟨d - 1, by omega⟩))

@[simp]
theorem coordinateBandToLastIso_apply_last
    {d : ℕ} (hd : 1 ≤ d) (i : Fin d) (r : ℤ) (x : Cubic d) :
    coordinateBandToLastIso hd i r x ⟨d - 1, by omega⟩ = x i - r := by
  change cubicTranslate (coordinateLevelVertex i r) cubicOrigin x
      ((Equiv.swap i ⟨d - 1, by omega⟩).symm ⟨d - 1, by omega⟩) = x i - r
  simp [cubicTranslate, coordinateLevelVertex, cubicOrigin]
  ring

theorem coordinateBandToLastIso_apply_ne_last
    {d : ℕ} (hd : 1 ≤ d) (i j : Fin d) (r : ℤ)
    (hj : j ≠ ⟨d - 1, by omega⟩) (x : Cubic d) :
    coordinateBandToLastIso hd i r x j = x ((Equiv.swap i ⟨d - 1, by omega⟩).symm j) := by
  have hne : (Equiv.swap i ⟨d - 1, by omega⟩).symm j ≠ i := by
    intro h
    have := congrArg (Equiv.swap i ⟨d - 1, by omega⟩) h
    simp at this
    exact hj this
  have hne' : (Equiv.swap i ⟨d - 1, by omega⟩) j ≠ i := by simpa using hne
  change cubicTranslate (coordinateLevelVertex i r) cubicOrigin x
      ((Equiv.swap i ⟨d - 1, by omega⟩).symm j) =
    x ((Equiv.swap i ⟨d - 1, by omega⟩).symm j)
  simp [cubicTranslate, coordinateLevelVertex, cubicOrigin, hne']

/-- A full cross-section coordinate band is carried exactly to Grimmett's finite thick region
`T_n(L)`.  The endpoint assumptions make the ambient-box restriction in the band redundant in
the thickness coordinate. -/
theorem coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
    {d n L : ℕ} (hd : 1 ≤ d) (i : Fin d) (r : ℤ)
    (hrlower : -(n : ℤ) ≤ r) (hrupper : r + L ≤ n) (x : Cubic d) :
    coordinateBandToLastIso hd i r x ∈ finiteThickSlabTVertices d n L ↔
      x ∈ coordinateClosedStripVertices d n i r (r + L) := by
  let last : Fin d := ⟨d - 1, by omega⟩
  let e : Fin d ≃ Fin d := Equiv.swap i last
  rw [mem_finiteThickSlabTVertices_iff, mem_coordinateClosedStripVertices_iff]
  constructor
  · intro hT
    have hlast := hT last
    have hlastEq : last.val + 1 = d := by simp [last]; omega
    simp only [if_pos hlastEq] at hlast
    have hlastCoord := coordinateBandToLastIso_apply_last hd i r x
    change coordinateBandToLastIso hd i r x last = x i - r at hlastCoord
    rw [hlastCoord] at hlast
    refine ⟨?_, by omega, by omega⟩
    rw [mem_cubicMetricBox]
    intro j
    simp only [cubicOrigin, zero_sub, zero_add]
    by_cases hji : j = i
    · subst j
      exact ⟨by omega, by omega⟩
    · have hej : e j ≠ last := by
        intro h
        have := congrArg e.symm h
        simp [e, last] at this
        exact hji this
      have hcoord := coordinateBandToLastIso_apply_ne_last hd i (e j) r hej x
      have hcoord' : coordinateBandToLastIso hd i r x (e j) = x j := by
        rw [hcoord]
        congr 1
        simp [e, last]
      have hTj := hT (e j)
      have hnotlast : (e j).val + 1 ≠ d := by
        intro hval
        apply hej
        apply Fin.ext
        simp [last]
        omega
      simp only [if_neg hnotlast, hcoord'] at hTj
      have habs : |x j| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hTj
      exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
  · rintro ⟨hxBox, hxr, hxu⟩ j
    by_cases hj : j = last
    · subst j
      have hlastEq : last.val + 1 = d := by simp [last]; omega
      rw [if_pos hlastEq]
      rw [coordinateBandToLastIso_apply_last hd i r x]
      constructor <;> omega
    · have hnotlast : j.val + 1 ≠ d := by
        intro hval
        apply hj
        apply Fin.ext
        simp [last]
        omega
      simp only [if_neg hnotlast]
      rw [coordinateBandToLastIso_apply_ne_last hd i j r hj x]
      have hxj := mem_cubicMetricBox.mp hxBox (e.symm j)
      simp only [cubicOrigin, zero_sub, zero_add] at hxj
      have habs : |x (e.symm j)| ≤ (n : ℤ) := abs_le.mpr hxj
      rw [← Int.natCast_natAbs] at habs
      exact Int.ofNat_le.mp habs

theorem cubicGraphIsoRegion_coordinateClosedStrip_eq_finiteThickSlabT
    {d n L : ℕ} (hd : 1 ≤ d) (i : Fin d) (r : ℤ)
    (hrlower : -(n : ℤ) ≤ r) (hrupper : r + L ≤ n) :
    cubicGraphIsoRegion (coordinateBandToLastIso hd i r)
        (coordinateClosedStripVertices d n i r (r + L) : Set (Cubic d)) =
      (finiteThickSlabTVertices d n L : Set (Cubic d)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_coe.mpr <|
      (coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
        hd i r hrlower hrupper x).2 (Finset.mem_coe.mp hx)
  · intro hy
    let x := (coordinateBandToLastIso hd i r).symm y
    have hxT : coordinateBandToLastIso hd i r x ∈ finiteThickSlabTVertices d n L := by
      simpa [x] using Finset.mem_coe.mp hy
    have hxBand := (coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
      hd i r hrlower hrupper x).1 hxT
    exact ⟨x, Finset.mem_coe.mpr hxBand, by simp [x]⟩

/-- The `T_n(L)` half of Lemma 7.78 is invariant under translation and coordinate permutation,
so it applies to every full cross-section coordinate band. -/
theorem coordinateClosedStrip_connection_probability_ge_of_uniformFiniteSlab
    {d n L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ}
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hn : 1 ≤ n) (i : Fin d) (r : ℤ)
    (hrlower : -(n : ℤ) ≤ r) (hrupper : r + L ≤ n)
    {u v : Cubic d}
    (hu : u ∈ coordinateClosedStripVertices d n i r (r + L))
    (hv : v ∈ coordinateClosedStripVertices d n i r (r + L)) :
    δ ≤ (bernoulliBondMeasure d p).real
      (connectionEventWithinVertices d
        (coordinateClosedStripVertices d n i r (r + L) : Set (Cubic d)) u v) := by
  let F := coordinateBandToLastIso hd i r
  have huT : F u ∈ finiteThickSlabTVertices d n L :=
    (coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
      hd i r hrlower hrupper u).2 hu
  have hvT : F v ∈ finiteThickSlabTVertices d n L :=
    (coordinateBandToLastIso_mem_finiteThickSlabTVertices_iff
      hd i r hrlower hrupper v).2 hv
  have hlower := hslab.2 n hn (F u) huT (F v) hvT
  rw [finiteThickSlabTConnectionEvent] at hlower
  rw [bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso F
    (coordinateClosedStripVertices d n i r (r + L) : Set (Cubic d)) p u v,
    cubicGraphIsoRegion_coordinateClosedStrip_eq_finiteThickSlabT
      hd i r hrlower hrupper]
  exact hlower

/-- Uniform finite-thick-slab connectivity supplies the fresh-connection probability required
by one peeling step. -/
theorem mul_sq_le_freshForwardBandConnection_probability_of_uniformFiniteSlab
    {d n L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hn : 1 ≤ n) {i : Fin d} {r : ℤ} {u v : Cubic d}
    (hrlower : -(n : ℤ) ≤ r + 1) (hrupper : r + L + 1 ≤ n)
    (hu : u ∈ coordinateHyperplaneVertices d n i r)
    (hv : v ∈ coordinateHyperplaneVertices d n i r) :
    (p : ℝ) ^ 2 * δ ≤ (bernoulliBondMeasure d p).real
      (freshForwardBandConnectionEvent d n i r L u v) := by
  have huData := mem_coordinateHyperplaneVertices_iff.mp hu
  have hvData := mem_coordinateHyperplaneVertices_iff.mp hv
  have huStepBox : coordinateForwardStep i u ∈ cubicMetricBox d cubicOrigin n :=
    coordinateForwardStep_mem_cubicMetricBox huData.1 (by omega)
  have hvStepBox : coordinateForwardStep i v ∈ cubicMetricBox d cubicOrigin n :=
    coordinateForwardStep_mem_cubicMetricBox hvData.1 (by omega)
  have huStepBand : coordinateForwardStep i u ∈
      coordinateClosedStripVertices d n i (r + 1) (r + 1 + L) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨huStepBox, by rw [coordinateForwardStep_apply_self, huData.2], by
      rw [coordinateForwardStep_apply_self, huData.2]
      omega⟩
  have hvStepBand : coordinateForwardStep i v ∈
      coordinateClosedStripVertices d n i (r + 1) (r + 1 + L) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨hvStepBox, by rw [coordinateForwardStep_apply_self, hvData.2], by
      rw [coordinateForwardStep_apply_self, hvData.2]
      omega⟩
  have hinner := coordinateClosedStrip_connection_probability_ge_of_uniformFiniteSlab
    hd p hslab hn i (r + 1) hrlower (by omega) huStepBand hvStepBand
  apply mul_sq_le_freshForwardBandConnection_probability p hδ0
  simpa [add_assoc, add_left_comm, add_comm] using hinner

/-- A fresh right-hand connection joins the two explored arms inside the band enlarged by
`L+2`.  The extra final layer is deliberately unused and gives the clean block width used in
the probabilistic iteration. -/
theorem mem_connectionWithin_extendedBand_of_freshForwardBandConnection
    {d n L : ℕ} {i : Fin d} {φ r : ℤ} {x y u v : Cubic d}
    (hφr : φ ≤ r) (hupper : r + L + 2 ≤ n)
    (hu : u ∈ coordinateHyperplaneVertices d n i r)
    (hv : v ∈ coordinateHyperplaneVertices d n i r)
    {ω : EdgeConfiguration d}
    (hxu : ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ r : Set (Cubic d)) x u)
    (hyv : ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ r : Set (Cubic d)) y v)
    (hfresh : ω ∈ freshForwardBandConnectionEvent d n i r L u v) :
    ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ (r + L + 2) : Set (Cubic d)) x y := by
  have huData := mem_coordinateHyperplaneVertices_iff.mp hu
  have hvData := mem_coordinateHyperplaneVertices_iff.mp hv
  have huStepBox : coordinateForwardStep i u ∈ cubicMetricBox d cubicOrigin n :=
    coordinateForwardStep_mem_cubicMetricBox huData.1 (by omega)
  have hvStepBox : coordinateForwardStep i v ∈ cubicMetricBox d cubicOrigin n :=
    coordinateForwardStep_mem_cubicMetricBox hvData.1 (by omega)
  have huExt : u ∈ coordinateClosedStripVertices d n i φ (r + L + 2) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨huData.1, by omega, by omega⟩
  have hvExt : v ∈ coordinateClosedStripVertices d n i φ (r + L + 2) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨hvData.1, by omega, by omega⟩
  have huStepExt : coordinateForwardStep i u ∈
      coordinateClosedStripVertices d n i φ (r + L + 2) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨huStepBox, by simp [huData.2]; omega, by simp [huData.2]; omega⟩
  have hvStepExt : coordinateForwardStep i v ∈
      coordinateClosedStripVertices d n i φ (r + L + 2) := by
    rw [mem_coordinateClosedStripVertices_iff]
    exact ⟨hvStepBox, by simp [hvData.2]; omega, by simp [hvData.2]; omega⟩
  have holdSubset :
      (coordinateClosedStripVertices d n i φ r : Set (Cubic d)) ⊆
        coordinateClosedStripVertices d n i φ (r + L + 2) := by
    intro z hz
    have hz' := mem_coordinateClosedStripVertices_iff.mp (Finset.mem_coe.mp hz)
    exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
      ⟨hz'.1, hz'.2.1, by omega⟩
  have hfreshSubset :
      (coordinateClosedStripVertices d n i (r + 1) (r + L + 1) : Set (Cubic d)) ⊆
        coordinateClosedStripVertices d n i φ (r + L + 2) := by
    intro z hz
    have hz' := mem_coordinateClosedStripVertices_iff.mp (Finset.mem_coe.mp hz)
    exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
      ⟨hz'.1, by omega, by omega⟩
  have hxuExt := connectionEventWithinVertices_mono holdSubset x u hxu
  have hyvExt := connectionEventWithinVertices_mono holdSubset y v hyv
  have huStep : ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ (r + L + 2) : Set (Cubic d))
      u (coordinateForwardStep i u) :=
    mem_connectionEventWithinVertices_coordinateForwardStep huExt huStepExt hfresh.1.1
  have hvStep : ω ∈ connectionEventWithinVertices d
      (coordinateClosedStripVertices d n i φ (r + L + 2) : Set (Cubic d))
      v (coordinateForwardStep i v) :=
    mem_connectionEventWithinVertices_coordinateForwardStep hvExt hvStepExt hfresh.1.2
  have hmiddle := connectionEventWithinVertices_mono hfreshSubset
    (coordinateForwardStep i u) (coordinateForwardStep i v) hfresh.2
  exact connectionEventWithinVertices_trans_mem hxuExt <|
    connectionEventWithinVertices_trans_mem huStep <|
      connectionEventWithinVertices_trans_mem hmiddle <|
        connectionEventWithinVertices_trans_mem
          (connectionEventWithinVertices_symm_mem hvStep)
          (connectionEventWithinVertices_symm_mem hyvExt)

/-- Once a pair of old frontier vertices receives a fresh right-hand connection, the next
separation event is impossible. -/
theorem not_mem_next_forwardTwoArm_of_fresh_frontier_connection
    {d n k L : ℕ} {i : Fin d} {φ : ℤ} {x y u v : Cubic d}
    (hupper : φ + (k + L + 2 : ℕ) ≤ n)
    {ω : EdgeConfiguration d}
    (hu : u ∈ coordinateBandFrontierVertices d n i φ k x ω)
    (hv : v ∈ coordinateBandFrontierVertices d n i φ k y ω)
    (hfresh : ω ∈ freshForwardBandConnectionEvent d n i (φ + k) L u v) :
    ω ∉ forwardTwoArmSeparationEvent d n i φ (k + L + 2) x y := by
  intro hnext
  have hconn := mem_connectionWithin_extendedBand_of_freshForwardBandConnection
    (φ := φ) (r := φ + k) (by omega) (by omega)
    (mem_coordinateBandFrontierVertices_iff.mp hu).1
    (mem_coordinateBandFrontierVertices_iff.mp hv).1
    (mem_coordinateBandFrontierVertices_iff.mp hu).2
    (mem_coordinateBandFrontierVertices_iff.mp hv).2 hfresh
  exact hnext.2 (by simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hconn)

/-- A uniform lower bound on the shifted fresh connection gives one ratio-free peeling step.
This is the measure-theoretic core of (7.109): the proof conditions on the exact finite trace of
the explored band and never divides by a possibly null history. -/
theorem forwardTwoArmSeparation_probability_block_step_of_fresh_lowerBound
    {d n k L : ℕ} (p : I) {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ)
    {δ : ℝ} (hupper : φ + (k + L + 2 : ℕ) ≤ n)
    (hfreshLower : ∀ u ∈ coordinateHyperplaneVertices d n i (φ + k),
      ∀ v ∈ coordinateHyperplaneVertices d n i (φ + k),
        δ ≤ (bernoulliBondMeasure d p).real
          (freshForwardBandConnectionEvent d n i (φ + k) L u v)) :
    (bernoulliBondMeasure d p).real
        (forwardTwoArmSeparationEvent d n i φ (k + L + 2) x y) ≤
      (1 - δ) * (bernoulliBondMeasure d p).real
        (forwardTwoArmSeparationEvent d n i φ k x y) := by
  let E := coordinateClosedBandEdges d n i φ (φ + k)
  let A := forwardTwoArmSeparationEvent d n i φ k x y
  let B := forwardTwoArmSeparationEvent d n i φ (k + L + 2) x y
  have hAdep : DependsOn E A := dependsOn_forwardTwoArmSeparationEvent hx hy
  have hBA : B ⊆ A := by
    intro ω hω
    simp only [B, A, forwardTwoArmSeparationEvent, Set.mem_inter_iff,
      Set.mem_compl_iff] at hω ⊢
    refine ⟨⟨connectionAcrossCoordinateBandEvent_mono_width hx (by omega) hω.1.1,
      connectionAcrossCoordinateBandEvent_mono_width hy (by omega) hω.1.2⟩, ?_⟩
    intro hconn
    apply hω.2
    apply connectionEventWithinVertices_mono _ x y hconn
    intro z hz
    have hz' := mem_coordinateClosedStripVertices_iff.mp (Finset.mem_coe.mp hz)
    exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
      ⟨hz'.1, hz'.2.1, by omega⟩
  apply setBernoulli_real_le_mul_of_sliceProbability_le E p
    (measurableSet_forwardTwoArmSeparationEvent d n i φ k x y)
    (measurableSet_forwardTwoArmSeparationEvent d n i φ (k + L + 2) x y)
  intro ω
  have hsliceA := hAdep.sliceProbability_eq_indicator subset_rfl p ω
  by_cases hωA : ω ∈ A
  · obtain ⟨huNonempty, hvNonempty⟩ :=
      coordinateBandFrontierVertices_nonempty_of_mem_forwardTwoArm hωA
    obtain ⟨u, huFront⟩ := huNonempty
    obtain ⟨v, hvFront⟩ := hvNonempty
    have huPlane := (mem_coordinateBandFrontierVertices_iff.mp huFront).1
    have hvPlane := (mem_coordinateBandFrontierVertices_iff.mp hvFront).1
    let F := freshForwardBandConnectionEvent d n i (φ + k) L u v
    let EF := freshForwardBandEdges d n i (φ + k) L u v
    have hFdep : DependsOn EF F :=
      dependsOn_freshForwardBandConnectionEvent huPlane (by omega)
    have hdisj : Disjoint (E : Set (CubicEdge d)) (EF : Set (CubicEdge d)) := by
      exact_mod_cast coordinateClosedBandEdges_disjoint_freshForwardBandEdges
        (φ := φ) huPlane hvPlane
    have hpre :
        (fun η => spliceOn E (restrictTo E ω) η) ⁻¹' B ⊆ Fᶜ := by
      intro η hηB
      simp only [Set.mem_preimage] at hηB
      intro hηF
      let ζ := spliceOn E (restrictTo E ω) η
      have hagree : ∀ e ∈ coordinateClosedBandEdges d n i φ (φ + k),
          (e ∈ ω ↔ e ∈ ζ) := by
        intro e he
        have heE : e ∈ E := by simpa [E] using he
        change e ∈ ω ↔ e ∈ spliceOn E (restrictTo E ω) η
        rw [mem_spliceOn_of_mem heE, mem_restrictTo]
        simp [heE]
      have huζ : u ∈ coordinateBandFrontierVertices d n i φ k x ζ := by
        rw [← coordinateBandFrontierVertices_eq_of_agree hx hagree]
        exact huFront
      have hvζ : v ∈ coordinateBandFrontierVertices d n i φ k y ζ := by
        rw [← coordinateBandFrontierVertices_eq_of_agree hy hagree]
        exact hvFront
      have hζF : ζ ∈ F :=
        (hFdep.spliceOn_mem_iff_of_disjoint (restrictTo_subset E ω) hdisj η).mpr hηF
      exact (not_mem_next_forwardTwoArm_of_fresh_frontier_connection hupper huζ hvζ hζF) hηB
    have hFm : MeasurableSet F := hFdep.measurableSet
    have hδF : δ ≤ (bernoulliBondMeasure d p).real F := hfreshLower u huPlane v hvPlane
    have hsliceB : sliceProbability E p B ω ≤ 1 - δ := by
      calc
        sliceProbability E p B ω =
            (bernoulliBondMeasure d p).real
              ((fun η => spliceOn E (restrictTo E ω) η) ⁻¹' B) := rfl
        _ ≤ (bernoulliBondMeasure d p).real Fᶜ := measureReal_mono hpre
        _ = 1 - (bernoulliBondMeasure d p).real F := by
          rw [measureReal_compl hFm, probReal_univ]
        _ ≤ 1 - δ := by linarith
    rw [hsliceA, Set.indicator_of_mem hωA]
    simpa using hsliceB
  · have hsliceB_le_A : sliceProbability E p B ω ≤ sliceProbability E p A ω := by
      exact measureReal_mono (Set.preimage_mono hBA)
    rw [hsliceA, Set.indicator_of_notMem hωA] at hsliceB_le_A ⊢
    simpa [B] using hsliceB_le_A

/-- The strip-peeling events decrease with the explored width, as used before (7.109). -/
theorem forwardTwoArmSeparationEvent_anti_width
    {d n k l : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ) (hkl : k ≤ l) :
    forwardTwoArmSeparationEvent d n i φ l x y ⊆
      forwardTwoArmSeparationEvent d n i φ k x y := by
  intro ω hω
  simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff,
    Set.mem_compl_iff] at hω ⊢
  refine ⟨⟨connectionAcrossCoordinateBandEvent_mono_width hx hkl hω.1.1,
    connectionAcrossCoordinateBandEvent_mono_width hy hkl hω.1.2⟩, ?_⟩
  intro hconn
  exact hω.2 (connectionEventWithinVertices_mono
    (show (coordinateClosedStripVertices d n i φ (φ + k) : Set (Cubic d)) ⊆
        coordinateClosedStripVertices d n i φ (φ + l) by
      intro z hz
      have hz' := Finset.mem_coe.mp hz
      rw [mem_coordinateClosedStripVertices_iff] at hz'
      exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
        ⟨hz'.1, hz'.2.1, by omega⟩) x y hconn)

/-- Ratio-free block peeling for (7.108)--(7.109).  A one-block failure factor `q` iterates to
`q^(m/M)`; no conditional probability is divided by the mass of an earlier event. -/
theorem forwardTwoArmSeparation_probability_le_pow_of_block_step
    {d n m M : ℕ} (p : I) {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ)
    {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ j,
      (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ ((j + 1) * M) x y) ≤
        q * (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ (j * M) x y)) :
    (bernoulliBondMeasure d p).real
        (forwardTwoArmSeparationEvent d n i φ m x y) ≤ q ^ (m / M) := by
  apply measureReal_event_le_pow_of_peeling (bernoulliBondMeasure d p)
    (forwardTwoArmSeparationEvent d n i φ m x y)
    (fun j ↦ forwardTwoArmSeparationEvent d n i φ (j * M) x y)
    q hq (m / M)
  · exact forwardTwoArmSeparationEvent_anti_width hx hy (Nat.div_mul_le_self m M)
  · exact hstep

/-- For a genuine entrance vertex and a positive strip width, the two-arm event with identical
entrances is impossible.  This is an adversarial check on the non-coalescence clause. -/
@[simp]
theorem forwardTwoArmSeparationEvent_self_eq_empty
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x : Cubic d}
    (hk : 1 ≤ k) (hx : x ∈ coordinateHyperplaneVertices d n i φ) :
    forwardTwoArmSeparationEvent d n i φ k x x = ∅ := by
  apply Set.Subset.antisymm
  · intro ω hω
    simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff,
      Set.mem_compl_iff] at hω
    have hnot := hω.2
    exfalso
    apply hnot
    refine ⟨SimpleGraph.Walk.nil, by intro e he; simp at he, ?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    change x ∈ coordinateClosedStripVertices d n i φ (φ + k)
    rw [mem_coordinateClosedStripVertices_iff]
    have hx' := mem_coordinateHyperplaneVertices_iff.mp hx
    exact ⟨hx'.1, by omega, by omega⟩
  · exact Set.empty_subset _

/-- Once the requested target hyperplane lies beyond the positive face of `B(n)`, the forward
two-arm event is empty. -/
theorem forwardTwoArmSeparationEvent_eq_empty_of_nat_lt
    {d n k : ℕ} {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hfar : (n : ℤ) < φ + k) :
    forwardTwoArmSeparationEvent d n i φ k x y = ∅ := by
  have htarget : coordinateHyperplaneVertices d n i (φ + k) = ∅ := by
    ext z
    simp only [mem_coordinateHyperplaneVertices_iff, Finset.notMem_empty, iff_false]
    rintro ⟨hzbox, hzcoord⟩
    have hzle := cubicLInfDist_coord_le cubicOrigin z i
    have hbox := mem_cubicMetricBox_iff_lInfDist_le.mp hzbox
    simp [cubicOrigin, hzcoord] at hzle
    omega
  apply Set.Subset.antisymm
  · intro ω hω
    simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff,
      Set.mem_compl_iff, connectionAcrossCoordinateBandEvent,
      Set.mem_iUnion] at hω
    obtain ⟨z, hz, _hxz⟩ := hω.1.1
    rw [htarget] at hz
    simp at hz
  · exact Set.empty_subset _

/-- Lemma 7.78 supplies the uniform one-block contraction used in (7.109).  The block width is
`L+2`: one fresh connector layer, a translated `T_n(L)`, and one unused terminal layer. -/
theorem forwardTwoArmSeparation_uniform_block_step_of_uniformFiniteSlab
    {d n L : ℕ} (hd : 1 ≤ d) (p : I) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ)
    (hn : 1 ≤ n) {i : Fin d} {φ : ℤ} {x y : Cubic d}
    (hx : x ∈ coordinateHyperplaneVertices d n i φ)
    (hy : y ∈ coordinateHyperplaneVertices d n i φ) :
    ∀ j,
      (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ ((j + 1) * (L + 2)) x y) ≤
        (1 - (p : ℝ) ^ 2 * δ) * (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i φ (j * (L + 2)) x y) := by
  have hpSq : (p : ℝ) ^ 2 ≤ 1 := by
    nlinarith [p.2.1, p.2.2, sq_nonneg (p : ℝ), sq_nonneg (1 - (p : ℝ))]
  have hprodLe : (p : ℝ) ^ 2 * δ ≤ 1 := by
    calc
      (p : ℝ) ^ 2 * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hpSq hδ0
      _ ≤ 1 := by simpa using hδ1
  have hq0 : 0 ≤ 1 - (p : ℝ) ^ 2 * δ := sub_nonneg.mpr hprodLe
  intro j
  by_cases hfar : (n : ℤ) < φ + ((j + 1) * (L + 2) : ℕ)
  · rw [forwardTwoArmSeparationEvent_eq_empty_of_nat_lt hfar, measureReal_empty]
    exact mul_nonneg hq0 measureReal_nonneg
  · have hwidth : j * (L + 2) + L + 2 = (j + 1) * (L + 2) := by ring
    have hupper : φ + (j * (L + 2) + L + 2 : ℕ) ≤ n := by
      have hnear : φ + ((j + 1) * (L + 2) : ℕ) ≤ n := by omega
      simpa [hwidth] using hnear
    have hstep := forwardTwoArmSeparation_probability_block_step_of_fresh_lowerBound
      p hx hy hupper (δ := (p : ℝ) ^ 2 * δ) (fun u hu v hv ↦ by
        apply mul_sq_le_freshForwardBandConnection_probability_of_uniformFiniteSlab
          hd p hδ0 hslab hn
        · have hxbound := (mem_coordinateHyperplaneVertices_iff.mp hx).1
          have hxlower := mem_cubicMetricBox.mp hxbound i
          have hxcoord := (mem_coordinateHyperplaneVertices_iff.mp hx).2
          simp [cubicOrigin, hxcoord] at hxlower
          omega
        · omega
        · exact hu
        · exact hv)
    simpa [hwidth] using hstep

/-! ### Deterministic covering behind (7.105)--(7.107) -/

/-- A crossing component and a distinct diameter-`m` component produce a pair of separated
forward arms in some coordinate direction. -/
theorem exists_forwardTwoArmSeparationEvent_of_crossing_of_secondMacroscopic
    {d m n : ℕ} (hd : 1 ≤ d) {ω : EdgeConfiguration d}
    {C D : (finiteBoxOpenGraph d ω cubicOrigin n).ConnectedComponent}
    (hCD : C ≠ D) (hCcross : finiteBoxGraphComponentIsCrossing C)
    (hmD : m ≤ finiteBoxGraphComponentDiameter D) :
    ∃ i : Fin d, ∃ x ∈ cubicMetricBox d cubicOrigin n,
      ∃ y ∈ cubicMetricBox d cubicOrigin n,
        x i = y i ∧ ω ∈ forwardTwoArmSeparationEvent d n i (x i) m x y := by
  classical
  obtain ⟨i, u, huD, v, hvD, huv, hmuv⟩ :=
    exists_oriented_coordinate_span_of_le_finiteBoxGraphComponentDiameter hd D hmD
  have huData := huD
  have hvData := hvD
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at huData hvData
  have huBox : u ∈ cubicMetricBox d cubicOrigin n := huData.1
  have hvBox : v ∈ cubicMetricBox d cubicOrigin n := hvData.1
  have huBounds := mem_cubicMetricBox.mp huBox i
  have hvBounds := mem_cubicMetricBox.mp hvBox i
  simp [cubicOrigin] at huBounds hvBounds
  obtain ⟨a, haC, haFace⟩ := (hCcross i).1
  obtain ⟨b, hbC, hbFace⟩ := (hCcross i).2
  have haCoord : a i = -(n : ℤ) := by
    have h := (mem_cubicBoxFace.mp haFace).1
    simpa [cubicOrigin] using h
  have hbCoord : b i = (n : ℤ) := by
    have h := (mem_cubicBoxFace.mp hbFace).1
    simpa [cubicOrigin] using h
  obtain ⟨wC, hwCopen, hwCbox⟩ :=
    mem_connectionEventWithinVertices_of_mem_finiteBoxGraphComponent haC hbC
  obtain ⟨x, z, q, hxCoord, hzCoord, hqopen, hqband⟩ :=
    exists_open_cubicWalk_between_levels wC hwCopen i (u i) (u i + m)
      (by omega) (by omega) (by omega)
  obtain ⟨wD, hwDopen, hwDbox⟩ :=
    mem_connectionEventWithinVertices_of_mem_finiteBoxGraphComponent huD hvD
  obtain ⟨y, t, r, hyCoord, htCoord, hropen, hrband⟩ :=
    exists_open_cubicWalk_between_levels wD hwDopen i (u i) (u i + m)
      (by omega) (by omega) (by omega)
  have hxWC : x ∈ wC.support := (hqband x q.start_mem_support).2.2
  have hyWD : y ∈ wD.support := (hrband y r.start_mem_support).2.2
  have hxBox : x ∈ cubicMetricBox d cubicOrigin n := hwCbox x hxWC
  have hyBox : y ∈ cubicMetricBox d cubicOrigin n := hwDbox y hyWD
  have hxAcross : ω ∈ connectionAcrossCoordinateBandEvent d n i (u i) m x := by
    simp only [connectionAcrossCoordinateBandEvent, Set.mem_iUnion]
    refine ⟨z, ?_, q, hqopen, ?_⟩
    · exact mem_coordinateHyperplaneVertices_iff.mpr
        ⟨hwCbox z (hqband z q.end_mem_support).2.2, hzCoord⟩
    · intro s hs
      exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
        ⟨hwCbox s (hqband s hs).2.2, (hqband s hs).1, (hqband s hs).2.1⟩
  have hyAcross : ω ∈ connectionAcrossCoordinateBandEvent d n i (u i) m y := by
    simp only [connectionAcrossCoordinateBandEvent, Set.mem_iUnion]
    refine ⟨t, ?_, r, hropen, ?_⟩
    · exact mem_coordinateHyperplaneVertices_iff.mpr
        ⟨hwDbox t (hrband t r.end_mem_support).2.2, htCoord⟩
    · intro s hs
      exact Finset.mem_coe.mpr <| mem_coordinateClosedStripVertices_iff.mpr
        ⟨hwDbox s (hrband s hs).2.2, (hrband s hs).1, (hrband s hs).2.1⟩
  refine ⟨i, x, hxBox, y, hyBox, hxCoord.trans hyCoord.symm, ?_⟩
  simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff, Set.mem_compl_iff]
  refine ⟨⟨by simpa [hxCoord] using hxAcross, by simpa [hxCoord] using hyAcross⟩, ?_⟩
  intro hxyStrip
  have hstripBox :
      (coordinateClosedStripVertices d n i (x i) (x i + m) : Set (Cubic d)) ⊆
        (cubicMetricBox d cubicOrigin n : Set (Cubic d)) := by
    intro z hz
    exact Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp hz))
  have hxyBox := connectionEventWithinVertices_mono hstripBox x y hxyStrip
  have hax : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) a x := by
    refine ⟨wC.takeUntil x hxWC,
      walkIsOpen_of_edges_subset hwCopen (wC.edges_takeUntil_subset hxWC), ?_⟩
    intro s hs
    exact hwCbox s (wC.support_takeUntil_subset_support hxWC hs)
  have hyu : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) y u := by
    refine ⟨(wD.takeUntil y hyWD).reverse,
      walkIsOpen_reverse (walkIsOpen_of_edges_subset hwDopen
        (wD.edges_takeUntil_subset hyWD)), ?_⟩
    intro s hs
    apply hwDbox s
    apply wD.support_takeUntil_subset_support hyWD
    simpa using hs
  have hau := connectionEventWithinVertices_trans_mem hax
    (connectionEventWithinVertices_trans_mem hxyBox hyu)
  exact hCD (finiteBoxGraphComponents_eq_of_connectionWithinVertices haC huD hau)

/-- Finite union in (7.107), with the common entrance level determined by `x`. -/
def secondMacroscopicClusterStripCoverEvent (d m n : ℕ) : Set (EdgeConfiguration d) :=
  ⋃ i : Fin d, ⋃ x ∈ cubicMetricBox d cubicOrigin n,
    ⋃ y ∈ cubicMetricBox d cubicOrigin n,
      if x i = y i then forwardTwoArmSeparationEvent d n i (x i) m x y else ∅

theorem measurableSet_secondMacroscopicClusterStripCoverEvent (d m n : ℕ) :
    MeasurableSet (secondMacroscopicClusterStripCoverEvent d m n) := by
  apply MeasurableSet.iUnion
  intro i
  apply (cubicMetricBox d cubicOrigin n).measurableSet_biUnion
  intro x _hx
  apply (cubicMetricBox d cubicOrigin n).measurableSet_biUnion
  intro y _hy
  split
  · exact measurableSet_forwardTwoArmSeparationEvent d n i (x i) m x y
  · exact MeasurableSet.empty

/-- Deterministic event covering corresponding to (7.105)--(7.107). -/
theorem secondMacroscopicClusterEvent_subset_stripCover
    {d m n : ℕ} (hd : 1 ≤ d) :
    secondMacroscopicClusterEvent d m n cubicOrigin ⊆
      secondMacroscopicClusterStripCoverEvent d m n := by
  intro ω hω
  obtain ⟨C, D, hCD, hCcross, hmD⟩ := hω
  obtain ⟨i, x, hx, y, hy, hxy, hA⟩ :=
    exists_forwardTwoArmSeparationEvent_of_crossing_of_secondMacroscopic
      hd hCD hCcross hmD
  simp only [secondMacroscopicClusterStripCoverEvent, Set.mem_iUnion]
  refine ⟨i, x, hx, y, hy, ?_⟩
  rw [if_pos hxy]
  exact hA

/-- Union-bound form of (7.107), before replacing the box cardinality by `(2n+1)^d`. -/
theorem secondMacroscopicCluster_probability_le_card_sq_mul
    {d m n : ℕ} (hd : 1 ≤ d) (p : I) {q : ℝ} (hq : 0 ≤ q)
    (hpair : ∀ i : Fin d, ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n, x i = y i →
        (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i (x i) m x y) ≤ q) :
    (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
      d * ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 * q := by
  let μ := bernoulliBondMeasure d p
  calc
    μ.real (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        μ.real (secondMacroscopicClusterStripCoverEvent d m n) :=
      measureReal_mono (secondMacroscopicClusterEvent_subset_stripCover hd)
        (measure_ne_top _ _)
    _ ≤ ∑ i : Fin d, μ.real (⋃ x ∈ cubicMetricBox d cubicOrigin n,
        ⋃ y ∈ cubicMetricBox d cubicOrigin n,
          if x i = y i then forwardTwoArmSeparationEvent d n i (x i) m x y else ∅) := by
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin d, ∑ _x ∈ cubicMetricBox d cubicOrigin n,
        ∑ _y ∈ cubicMetricBox d cubicOrigin n, q := by
      apply Finset.sum_le_sum
      intro i _hi
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro x hx
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro y hy
      by_cases hxy : x i = y i
      · simpa [hxy] using hpair i x hx y hy hxy
      · simp [hxy, hq]
    _ = d * ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 * q := by
      simp
      ring

/-- Source-facing polynomial form of (7.107). -/
theorem secondMacroscopicCluster_probability_le_boxPolynomial_mul
    {d m n : ℕ} (hd : 1 ≤ d) (p : I) {q : ℝ} (hq : 0 ≤ q)
    (hpair : ∀ i : Fin d, ∀ x ∈ cubicMetricBox d cubicOrigin n,
      ∀ y ∈ cubicMetricBox d cubicOrigin n, x i = y i →
        (bernoulliBondMeasure d p).real
          (forwardTwoArmSeparationEvent d n i (x i) m x y) ≤ q) :
    (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
      d * (2 * n + 1 : ℝ) ^ (2 * d) * q := by
  calc
    (bernoulliBondMeasure d p).real
        (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        d * ((cubicMetricBox d cubicOrigin n).card : ℝ) ^ 2 * q :=
      secondMacroscopicCluster_probability_le_card_sq_mul hd p hq hpair
    _ = d * (2 * n + 1 : ℝ) ^ (2 * d) * q := by
      rw [cubicMetricBox_card]
      push_cast
      rw [pow_two, ← pow_add]
      congr 3
      omega

/-! ### Geometric-to-exponential conversion in Lemma 7.104 -/

/-- Above one block, the quotient `m/M` is at least half of the real ratio `m/M`. -/
theorem nat_le_two_mul_mul_div {m M : ℕ} (hM : 1 ≤ M) (hm : M ≤ m) :
    m ≤ 2 * M * (m / M) := by
  have hk : 1 ≤ m / M := (Nat.le_div_iff_mul_le hM).2 (by simpa using hm)
  have hMle : M ≤ M * (m / M) := by
    simpa using Nat.mul_le_mul_left M hk
  have hmod : m % M < M := Nat.mod_lt m hM
  calc
    m = M * (m / M) + m % M := (Nat.div_add_mod m M).symm
    _ ≤ M * (m / M) + M * (m / M) := Nat.add_le_add_left (hmod.le.trans hMle) _
    _ = 2 * M * (m / M) := by ring

/-- The positive rate used to absorb both the quotient-rounding loss and the finitely many
widths below one block. -/
noncomputable def secondClusterPeelingRate (q : ℝ) (M : ℕ) : ℝ :=
  min (-Real.log q / (2 * M)) (Real.log 2 / M)

theorem secondClusterPeelingRate_pos {q : ℝ} {M : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hM : 1 ≤ M) :
    0 < secondClusterPeelingRate q M := by
  rw [secondClusterPeelingRate, lt_min_iff]
  constructor
  · exact div_pos (neg_pos.mpr (Real.log_neg hq0 hq1)) (by positivity)
  · exact div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- For widths at least one block, the geometric factor is bounded by the selected exponential
rate. -/
theorem pow_natDiv_le_exp_neg_secondClusterPeelingRate
    {q : ℝ} {m M : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hM : 1 ≤ M) (hm : M ≤ m) :
    q ^ (m / M) ≤ Real.exp (-(secondClusterPeelingRate q M) * m) := by
  let k := m / M
  let a : ℝ := -Real.log q / (2 * M)
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hnat := nat_le_two_mul_mul_div hM hm
  have hcast : (m : ℝ) ≤ 2 * (M : ℝ) * (k : ℝ) := by
    exact_mod_cast hnat
  have hden : 0 < 2 * (M : ℝ) := by positivity
  have hratio : (m : ℝ) / (2 * M) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hexp : (k : ℝ) * Real.log q ≤ Real.log q * (m / (2 * M)) := by
    nlinarith
  have hgeom : q ^ k ≤ Real.exp (-a * m) := by
    calc
      q ^ k = (Real.exp (Real.log q)) ^ k := by rw [Real.exp_log hq0]
      _ = Real.exp ((k : ℝ) * Real.log q) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Real.log q * (m / (2 * M))) := Real.exp_le_exp.mpr hexp
      _ = Real.exp (-a * m) := by
        congr 1
        dsimp [a]
        field_simp
  exact hgeom.trans (Real.exp_le_exp.mpr <| by
    have hμa : secondClusterPeelingRate q M ≤ a := min_le_left _ _
    nlinarith)

/-- A uniform one-block failure factor proves the complete exponential estimate of Lemma 7.104.
The sole remaining source-specific input is the hypothesis `hstep`, obtained from Lemma 7.78. -/
theorem exists_secondMacroscopicCluster_probability_le_exp_of_block_step
    {d : ℕ} (hd : 1 ≤ d) (p : I) {q : ℝ} {M : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hM : 1 ≤ M)
    (hstep : ∀ n (i : Fin d) (x : Cubic d), x ∈ cubicMetricBox d cubicOrigin n →
      ∀ y : Cubic d, y ∈ cubicMetricBox d cubicOrigin n → x i = y i → ∀ j,
        (bernoulliBondMeasure d p).real
            (forwardTwoArmSeparationEvent d n i (x i) ((j + 1) * M) x y) ≤
          q * (bernoulliBondMeasure d p).real
            (forwardTwoArmSeparationEvent d n i (x i) (j * M) x y)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (bernoulliBondMeasure d p).real
          (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-μ * m) := by
  let μ := secondClusterPeelingRate q M
  refine ⟨μ, secondClusterPeelingRate_pos hq0 hq1 hM, ?_⟩
  intro m n hm hn
  by_cases hmM : M ≤ m
  · have hpair : ∀ i : Fin d, ∀ x ∈ cubicMetricBox d cubicOrigin n,
        ∀ y ∈ cubicMetricBox d cubicOrigin n, x i = y i →
          (bernoulliBondMeasure d p).real
            (forwardTwoArmSeparationEvent d n i (x i) m x y) ≤ Real.exp (-μ * m) := by
      intro i x hx y hy hxy
      exact (forwardTwoArmSeparation_probability_le_pow_of_block_step p
        (mem_coordinateHyperplaneVertices_iff.mpr ⟨hx, rfl⟩)
        (mem_coordinateHyperplaneVertices_iff.mpr ⟨hy, hxy.symm⟩) hq0.le
        (hstep n i x hx y hy hxy)).trans
          (pow_natDiv_le_exp_neg_secondClusterPeelingRate hq0 hq1 hM hmM)
    exact secondMacroscopicCluster_probability_le_boxPolynomial_mul hd p
      (Real.exp_pos _).le hpair
  · have hmLt : m < M := Nat.lt_of_not_ge hmM
    have hμle : μ ≤ Real.log 2 / M := min_le_right _ _
    have hμm : μ * m < Real.log 2 := by
      have hMpos : (0 : ℝ) < M := by positivity
      have hmcast : (m : ℝ) < M := by exact_mod_cast hmLt
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hμnonneg : 0 ≤ μ := (secondClusterPeelingRate_pos hq0 hq1 hM).le
      calc
        μ * m ≤ (Real.log 2 / M) * m :=
          mul_le_mul_of_nonneg_right hμle (by positivity)
        _ < (Real.log 2 / M) * M := by
          exact mul_lt_mul_of_pos_left hmcast (div_pos hlog2 hMpos)
        _ = Real.log 2 := by field_simp
    have hexpHalf : (1 / 2 : ℝ) ≤ Real.exp (-μ * m) := by
      have := Real.exp_le_exp.mpr (show -Real.log 2 ≤ -μ * m by linarith)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
      norm_num at this ⊢
      exact this
    have hbase : (3 : ℝ) ≤ 2 * n + 1 := by exact_mod_cast (show 3 ≤ 2 * n + 1 by omega)
    have hpow : (3 : ℝ) ≤ (2 * n + 1 : ℝ) ^ (2 * d) := by
      exact hbase.trans (le_self_pow₀ (by nlinarith) (by omega))
    have hfactor : (2 : ℝ) ≤ d * (2 * n + 1 : ℝ) ^ (2 * d) := by
      have hdcast : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [mul_le_mul hdcast hpow (by positivity) (by positivity)]
    calc
      (bernoulliBondMeasure d p).real
          (secondMacroscopicClusterEvent d m n cubicOrigin) ≤ 1 := measureReal_le_one
      _ ≤ (d * (2 * n + 1 : ℝ) ^ (2 * d)) * (1 / 2) := by nlinarith
      _ ≤ (d * (2 * n + 1 : ℝ) ^ (2 * d)) * Real.exp (-μ * m) :=
        mul_le_mul_of_nonneg_left hexpHalf (by positivity)
      _ = d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-μ * m) := rfl

/-- Lemma 7.104 from the exact conclusion of Lemma 7.78.  Unlike the lower-level analytic
adapter, this theorem has no unresolved one-block hypothesis: finite-slab connectivity is
transported, sprinkled by two fresh edges, conditioned through finite traces, and iterated
internally. -/
theorem exists_secondMacroscopicCluster_probability_le_exp_of_uniformFiniteSlab
    {d L : ℕ} (hd : 1 ≤ d) (p : I) (hp0 : 0 < (p : ℝ))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hslab : UniformFiniteSlabConnectionLowerBound d p L δ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (bernoulliBondMeasure d p).real
          (secondMacroscopicClusterEvent d m n cubicOrigin) ≤
        d * (2 * n + 1 : ℝ) ^ (2 * d) * Real.exp (-μ * m) := by
  let ε : ℝ := (p : ℝ) ^ 2 * δ / 2
  let q : ℝ := 1 - ε
  let M : ℕ := L + 2
  have hpSq0 : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hp0
  have hε0 : 0 < ε := by positivity
  have hpSqLe : (p : ℝ) ^ 2 ≤ 1 := by
    nlinarith [p.2.1, p.2.2, sq_nonneg (p : ℝ), sq_nonneg (1 - (p : ℝ))]
  have hprodLe : (p : ℝ) ^ 2 * δ ≤ 1 := by
    calc
      (p : ℝ) ^ 2 * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hpSqLe hδ0.le
      _ ≤ 1 := by simpa using hδ1
  have hεLeHalf : ε ≤ 1 / 2 := by dsimp [ε]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hM : 1 ≤ M := by dsimp [M]; omega
  apply exists_secondMacroscopicCluster_probability_le_exp_of_block_step hd p hq0 hq1 hM
  intro n i x hx y hy hxy j
  by_cases hn : 1 ≤ n
  · have hraw := forwardTwoArmSeparation_uniform_block_step_of_uniformFiniteSlab
      hd p hδ0.le hδ1 hslab hn
      (mem_coordinateHyperplaneVertices_iff.mpr ⟨hx, rfl⟩)
      (mem_coordinateHyperplaneVertices_iff.mpr ⟨hy, hxy.symm⟩) j
    have hcoef : 1 - (p : ℝ) ^ 2 * δ ≤ q := by
      dsimp [q, ε]
      linarith [mul_pos hpSq0 hδ0]
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoef measureReal_nonneg)
  · have hn0 : n = 0 := by omega
    subst n
    have hxi := mem_cubicMetricBox.mp hx i
    simp [cubicOrigin] at hxi
    have hxzero : x i = 0 := by omega
    have hfar : (0 : ℤ) < x i + ((j + 1) * M : ℕ) := by
      rw [hxzero]
      have hnat : 0 < (j + 1) * M := Nat.mul_pos (by omega) (by omega)
      have hz : (0 : ℤ) < ((j + 1) * M : ℕ) := by exact_mod_cast hnat
      omega
    rw [forwardTwoArmSeparationEvent_eq_empty_of_nat_lt hfar, measureReal_empty]
    exact mul_nonneg hq0.le measureReal_nonneg

end Percolation
