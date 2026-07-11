import Percolation.Critical.StaticCoalescence
import Percolation.Core.CubicWalkLevel
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

open MeasureTheory
open scoped unitInterval

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
  obtain ⟨z, q, hzcoord, _hqside, hqsupport, hqedges⟩ :=
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
  obtain ⟨z, q, hzcoord, _hqside, hqsupport, hqedges⟩ :=
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

/-- Grimmett's event `A_k(x,y)` from the proof of Lemma 7.104: both entrance vertices reach the
future hyperplane, but they have not coalesced inside the intervening half-open strip. -/
def forwardTwoArmSeparationEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x y : Cubic d) :
    Set (EdgeConfiguration d) :=
  connectionToCoordinateHyperplaneEvent d n i (φ + k) x ∩
    connectionToCoordinateHyperplaneEvent d n i (φ + k) y ∩
      (connectionEventWithinVertices d
        (coordinateHalfOpenStripVertices d n i φ (φ + k) : Set (Cubic d)) x y)ᶜ

theorem measurableSet_forwardTwoArmSeparationEvent
    (d n : ℕ) (i : Fin d) (φ : ℤ) (k : ℕ) (x y : Cubic d) :
    MeasurableSet (forwardTwoArmSeparationEvent d n i φ k x y) :=
  ((measurableSet_connectionToCoordinateHyperplaneEvent d n i (φ + k) x).inter
    (measurableSet_connectionToCoordinateHyperplaneEvent d n i (φ + k) y)).inter
      (measurableSet_connectionEventWithinVertices d _ x y).compl

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
  refine ⟨⟨connectionToCoordinateHyperplaneEvent_mono_width hx hkl hω.1.1,
    connectionToCoordinateHyperplaneEvent_mono_width hy hkl hω.1.2⟩, ?_⟩
  intro hconn
  exact hω.2 (connectionEventWithinVertices_mono
    (show (coordinateHalfOpenStripVertices d n i φ (φ + k) : Set (Cubic d)) ⊆
        coordinateHalfOpenStripVertices d n i φ (φ + l) by
      intro z hz
      exact Finset.mem_coe.mpr
        (coordinateHalfOpenStripVertices_mono_width hkl (Finset.mem_coe.mp hz))) x y hconn)

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
    change x ∈ coordinateHalfOpenStripVertices d n i φ (φ + k)
    rw [mem_coordinateHalfOpenStripVertices_iff]
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
      Set.mem_compl_iff, connectionToCoordinateHyperplaneEvent,
      Set.mem_iUnion] at hω
    obtain ⟨z, hz, _hxz⟩ := hω.1.1
    rw [htarget] at hz
    simp at hz
  · exact Set.empty_subset _

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
  have hab : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) a b :=
    mem_connectionEventWithinVertices_of_mem_finiteBoxGraphComponent haC hbC
  have haToU := mem_connectionToCoordinateHyperplaneEvent_of_connectionWithin
    hab (i := i) (r := u i) (by omega) (by omega)
  simp only [connectionToCoordinateHyperplaneEvent, Set.mem_iUnion] at haToU
  obtain ⟨x, hxPlane, hax⟩ := haToU
  have hxBox := (mem_coordinateHyperplaneVertices_iff.mp hxPlane).1
  have hxCoord := (mem_coordinateHyperplaneVertices_iff.mp hxPlane).2
  have hxb : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) x b :=
    connectionEventWithinVertices_trans_mem
      (connectionEventWithinVertices_symm_mem hax) hab
  have hxm : ω ∈ connectionToCoordinateHyperplaneEvent d n i (x i + m) x := by
    apply mem_connectionToCoordinateHyperplaneEvent_of_connectionWithin hxb
    · omega
    · omega
  have huvConn : ω ∈ connectionEventWithinVertices d
      (cubicMetricBox d cubicOrigin n : Set (Cubic d)) u v :=
    mem_connectionEventWithinVertices_of_mem_finiteBoxGraphComponent huD hvD
  have hum : ω ∈ connectionToCoordinateHyperplaneEvent d n i (u i + m) u := by
    apply mem_connectionToCoordinateHyperplaneEvent_of_connectionWithin huvConn
    · omega
    · omega
  refine ⟨i, x, hxBox, u, huBox, hxCoord, ?_⟩
  simp only [forwardTwoArmSeparationEvent, Set.mem_inter_iff, Set.mem_compl_iff]
  refine ⟨⟨by simpa [hxCoord] using hxm, by simpa [hxCoord] using hum⟩, ?_⟩
  intro hxuStrip
  have hstripBox :
      (coordinateHalfOpenStripVertices d n i (x i) (x i + m) : Set (Cubic d)) ⊆
        (cubicMetricBox d cubicOrigin n : Set (Cubic d)) := by
    intro z hz
    exact Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp hz))
  have hxuBox := connectionEventWithinVertices_mono hstripBox x u hxuStrip
  have hau := connectionEventWithinVertices_trans_mem hax hxuBox
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

end Percolation
