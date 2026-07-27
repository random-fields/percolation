import Percolation.Critical.RegionCoordinateSupport
import Percolation.Critical.RegionTranslation
import Percolation.Critical.RegionSymmetry

/-!
# Strip exploration for supercritical finite clusters

This file formalizes the fresh-strip mechanism in Grimmett, equations (8.44)--(8.48).  The
entrance to a strip is selected canonically using only bonds touching the strict past of the
entrance hyperplane.  Bonds internal to the new half-open strip are therefore independent of
the entire accumulated history.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

/-- The half-open coordinate strip `{x : a ≤ xᵢ < a+k}`. -/
def cubicCoordinateStrip (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) : Set (Cubic d) :=
  {x | a ≤ x i ∧ x i < a + k}

/-- The strict coordinate past `{x : xᵢ<a}` of an entrance hyperplane. -/
def cubicCoordinateStrictPast (d : ℕ) (i : Fin d) (a : ℤ) : Set (Cubic d) :=
  {x | x i < a}

/-- Bonds having at least one endpoint strictly before the entrance hyperplane. -/
def cubicEdgesTouchingCoordinateStrictPast
    (d : ℕ) (i : Fin d) (a : ℤ) : Set (CubicEdge d) :=
  {e | e.1.out.1 i < a ∨ e.1.out.2 i < a}

@[simp]
theorem mem_cubicCoordinateStrip {d : ℕ} {i : Fin d} {a : ℤ} {k : ℕ} {x : Cubic d} :
    x ∈ cubicCoordinateStrip d i a k ↔ a ≤ x i ∧ x i < a + k :=
  Iff.rfl

@[simp]
theorem mem_cubicCoordinateStrictPast {d : ℕ} {i : Fin d} {a : ℤ} {x : Cubic d} :
    x ∈ cubicCoordinateStrictPast d i a ↔ x i < a :=
  Iff.rfl

theorem cubicInternalEdgeSet_coordinateStrictPast_subset_touching
    (d : ℕ) (i : Fin d) (a : ℤ) :
    cubicInternalEdgeSet d (cubicCoordinateStrictPast d i a) ⊆
      cubicEdgesTouchingCoordinateStrictPast d i a := by
  intro e he
  exact Or.inl he.1

theorem disjoint_cubicEdgesTouchingCoordinateStrictPast_internalStrip
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) :
    Disjoint (cubicEdgesTouchingCoordinateStrictPast d i a)
      (cubicInternalEdgeSet d (cubicCoordinateStrip d i a k)) := by
  rw [Set.disjoint_left]
  intro e hpast hstrip
  rcases hpast with hleft | hright
  · exact (not_lt_of_ge hstrip.1.1) hleft
  · exact (not_lt_of_ge hstrip.2.1) hright

theorem cubicTranslateRegion_coordinateStrip_zero
    {d : ℕ} (i : Fin d) (v : Cubic d) (k : ℕ) :
    cubicTranslateRegion cubicOrigin v (cubicCoordinateStrip d i 0 k) =
      cubicCoordinateStrip d i (v i) k := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 ≤ z i ∧ z i < 0 + k at hz
    change v i ≤ cubicTranslate cubicOrigin v z i ∧
      cubicTranslate cubicOrigin v z i < v i + k
    simp only [cubicTranslate, cubicOrigin, sub_zero]
    constructor <;> omega
  · intro hx
    change v i ≤ x i ∧ x i < v i + k at hx
    let z := cubicTranslate v cubicOrigin x
    refine ⟨z, ?_, ?_⟩
    · change 0 ≤ z i ∧ z i < 0 + k
      simp only [z, cubicTranslate, cubicOrigin, zero_add]
      constructor <;> omega
    · ext j
      simp [z, cubicTranslate, cubicOrigin]

/-- Coordinate permutations carry a strip perpendicular to `i` to the strip perpendicular to
`e i`. -/
theorem cubicGraphIsoRegion_coordinatePermutation_coordinateStrip
    {d : ℕ} (e : Fin d ≃ Fin d) (i : Fin d) (a : ℤ) (k : ℕ) :
    cubicGraphIsoRegion (cubicCoordinatePermutationIso e)
        (cubicCoordinateStrip d i a k) =
      cubicCoordinateStrip d (e i) a k := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cubicCoordinateStrip] at hx ⊢
    change a ≤ cubicCoordinatePermutationEquiv e x (e i) ∧
      cubicCoordinatePermutationEquiv e x (e i) < a + k
    simpa using hx
  · intro hy
    let x := cubicCoordinatePermutationEquiv e.symm y
    refine ⟨x, ?_, ?_⟩
    · rw [mem_cubicCoordinateStrip] at hy ⊢
      simpa [x] using hy
    · ext j
      simp [x, cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]

theorem regionThetaFrom_coordinateStrip_eq
    {d : ℕ} (p : I) (i : Fin d) (v : Cubic d) (k : ℕ) :
    regionThetaFrom d (cubicCoordinateStrip d i (v i) k) p v =
      regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin := by
  rw [← cubicTranslateRegion_coordinateStrip_zero i v k]
  simpa [cubicOrigin] using
    (regionThetaFrom_translate (cubicCoordinateStrip d i 0 k) p cubicOrigin v cubicOrigin)

@[simp]
theorem cubicOrigin_mem_coordinateStrip_zero
    {d : ℕ} (i : Fin d) {k : ℕ} (hk : 0 < k) :
    cubicOrigin ∈ cubicCoordinateStrip d i 0 k := by
  simp [cubicOrigin, hk]

/-- A nonempty coordinate strip is connected.  This supplies the rooted form of positivity
above the strip's root-free critical probability. -/
theorem cubicRegionGraph_coordinateStrip_zero_connected
    {d : ℕ} (i : Fin d) {k : ℕ} (hk : 0 < k) :
    (cubicRegionGraph d (cubicCoordinateStrip d i 0 k)).Connected := by
  apply cubicRegionGraph_connected_of_coordinateConvex
  · exact ⟨cubicOrigin, cubicOrigin_mem_coordinateStrip_zero i hk⟩
  · intro x hx y hy z hz
    rw [mem_cubicCoordinateStrip] at hx hy ⊢
    rcases hz i with hxy | hyx
    · exact ⟨hx.1.trans hxy.1, hxy.2.trans_lt hy.2⟩
    · exact ⟨hy.1.trans hyx.1, hyx.2.trans_lt hx.2⟩

private def cubicEdgeOfAdj {d : ℕ} {u v : Cubic d}
    (h : (cubicGraph d).Adj u v) : CubicEdge d :=
  ⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).2 h⟩

/-- A fixed vertex `v` is an entrance reached for the first time from the strict past.  The
witnessing path stays strictly to the left of the hyperplane and then uses one crossing bond. -/
def coordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) : Set (EdgeConfiguration d) :=
  if _hv : v i = a then
    ⋃ (u : Cubic d) (_hu : u i < a) (huv : (cubicGraph d).Adj u v),
      connectionEventWithinVertices d (cubicCoordinateStrictPast d i a) cubicOrigin u ∩
        {ω | cubicEdgeOfAdj huv ∈ ω}
  else ∅

theorem measurableSet_coordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) :
    MeasurableSet (coordinateStripEntranceEvent d i a v) := by
  classical
  rw [coordinateStripEntranceEvent]
  split
  · exact MeasurableSet.iUnion fun u ↦ MeasurableSet.iUnion fun _hu ↦
      MeasurableSet.iUnion fun huv ↦
        (measurableSet_connectionEventWithinVertices d
          (cubicCoordinateStrictPast d i a) cubicOrigin u).inter <| by
            simpa [Set.singleton_subset_iff] using
              measurableSet_superset_finset ({cubicEdgeOfAdj huv} : Finset (CubicEdge d))
  · exact MeasurableSet.empty

theorem dependsOnCoordinates_coordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) :
    DependsOnCoordinates (cubicEdgesTouchingCoordinateStrictPast d i a)
      (coordinateStripEntranceEvent d i a v) := by
  classical
  rw [coordinateStripEntranceEvent]
  split
  · apply DependsOnCoordinates.iUnion
    intro u
    apply DependsOnCoordinates.iUnion
    intro hu
    apply DependsOnCoordinates.iUnion
    intro huv
    apply DependsOnCoordinates.inter
    · exact (dependsOnCoordinates_connectionEventWithinVertices d
        (cubicCoordinateStrictPast d i a) cubicOrigin u).mono
          (cubicInternalEdgeSet_coordinateStrictPast_subset_touching d i a)
    · apply dependsOnCoordinates_coordinateEvent
      change (s(u, v).out.1 i < a ∨ s(u, v).out.2 i < a)
      have hout : s(s(u, v).out.1, s(u, v).out.2) = s(u, v) := s(u, v).out_eq
      rcases Sym2.eq_iff.mp hout with hout | hout
      · rw [hout.1, hout.2]
        exact Or.inl hu
      · rw [hout.1, hout.2]
        exact Or.inr hu
  · intro _ω _η _h
    rfl

/-- A canonical entrance witness is an actual open connection from the origin. -/
theorem mem_connectionEvent_of_mem_coordinateStripEntranceEvent
    {d : ℕ} {i : Fin d} {a : ℤ} {v : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ coordinateStripEntranceEvent d i a v) :
    ω ∈ connectionEvent d cubicOrigin v := by
  classical
  rw [coordinateStripEntranceEvent] at hω
  split at hω
  · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
    obtain ⟨u, _hu, huv, ⟨w, hwopen, _hwPast⟩, hedge⟩ := hω
    let step : (cubicGraph d).Walk u v := SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
    have hstepOpen : walkIsOpen ω step := by
      intro e he
      simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_cons, List.not_mem_nil, or_false] at he
      subst e
      simpa [cubicEdgeOfAdj] using hedge
    exact ⟨w.append step, walkIsOpen_append hwopen hstepOpen⟩
  · exact False.elim hω

/-- First hit of a positive coordinate hyperplane by an open origin path.  The prefix before the
crossing is entirely in the strict past, so it produces an entrance event without revealing any
edge internal to the fresh strip. -/
theorem exists_coordinateStripEntrance_of_connection
    {d : ℕ} {i : Fin d} {a : ℤ} {x : Cubic d} {ω : EdgeConfiguration d}
    (ha : 0 < a) (hx : a ≤ x i) (hconn : ω ∈ connectionEvent d cubicOrigin x) :
    ∃ v, ω ∈ coordinateStripEntranceEvent d i a v := by
  classical
  obtain ⟨w, hwopen⟩ := hconn
  have hexit : ∃ m : ℕ, m ≤ w.length ∧ a ≤ w.getVert m i := by
    exact ⟨w.length, le_rfl, by simpa using hx⟩
  let m := Nat.find hexit
  have hm : m ≤ w.length ∧ a ≤ w.getVert m i := Nat.find_spec hexit
  have hmpos : 0 < m := by
    by_contra hnot
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
    have := hm.2
    simp [hm0, cubicOrigin] at this
    omega
  let j := m - 1
  have hmj : m = j + 1 := by omega
  have hjlt : w.getVert j i < a := by
    apply lt_of_not_ge
    intro hj
    exact Nat.find_min hexit (show j < m by omega) ⟨by omega, hj⟩
  have hjlen : j < w.length := by omega
  have hadj : (cubicGraph d).Adj (w.getVert j) (w.getVert m) := by
    simpa [hmj] using w.adj_getVert_succ hjlen
  have hmcoord : w.getVert m i = a := by
    obtain ⟨dir, hstep⟩ :=
      (cubicGraph_adj_iff_exists_stepFrom (w.getVert j) (w.getVert m)).mp hadj
    have hupper : w.getVert m i ≤ w.getVert j i + 1 := by
      simpa [hstep] using cubicStepFrom_coord_le_add_one (w.getVert j) dir i
    omega
  let q := w.take j
  have hqopen : walkIsOpen ω q := walkIsOpen_take w hwopen j
  have hqPast : ∀ z ∈ q.support, z ∈ cubicCoordinateStrictPast d i a := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨t, rfl, ht⟩ := hz
    have htj : t ≤ j := by
      simpa [q, Nat.min_eq_left (show j ≤ w.length by omega)] using ht
    have hget : q.getVert t = w.getVert t := by
      simp [q, Nat.min_eq_right htj]
    rw [hget]
    change w.getVert t i < a
    apply lt_of_not_ge
    intro htge
    exact Nat.find_min hexit (show t < m by omega) ⟨by omega, htge⟩
  have hedgeMem : s(w.getVert j, w.getVert m) ∈ w.edges := by
    have hjdarts : j < w.darts.length := by simpa using hjlen
    have hdart := w.darts_getElem_eq_getVert j hjdarts
    rw [SimpleGraph.Walk.edges, List.mem_map]
    refine ⟨w.darts[j]'hjdarts, List.getElem_mem _, ?_⟩
    have hedgeEq := congrArg SimpleGraph.Dart.edge hdart
    simpa [hmj] using hedgeEq
  have hedgeOpen := hwopen s(w.getVert j, w.getVert m) hedgeMem
  refine ⟨w.getVert m, ?_⟩
  rw [coordinateStripEntranceEvent, dif_pos hmcoord]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨w.getVert j, hjlt, hadj, ⟨q, hqopen, hqPast⟩, ?_⟩
  simpa [cubicEdgeOfAdj] using hedgeOpen

/-- The canonical entrance is the entrance vertex with least `Encodable.encode`. -/
def canonicalCoordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) : Set (EdgeConfiguration d) :=
  coordinateStripEntranceEvent d i a v ∩
    ⋂ (w : Cubic d) (_hw : Encodable.encode w < Encodable.encode v),
      (coordinateStripEntranceEvent d i a w)ᶜ

theorem measurableSet_canonicalCoordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) :
    MeasurableSet (canonicalCoordinateStripEntranceEvent d i a v) :=
  (measurableSet_coordinateStripEntranceEvent d i a v).inter <|
    MeasurableSet.iInter fun w ↦ MeasurableSet.iInter fun _hw ↦
      (measurableSet_coordinateStripEntranceEvent d i a w).compl

theorem dependsOnCoordinates_canonicalCoordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (v : Cubic d) :
    DependsOnCoordinates (cubicEdgesTouchingCoordinateStrictPast d i a)
      (canonicalCoordinateStripEntranceEvent d i a v) :=
  (dependsOnCoordinates_coordinateStripEntranceEvent d i a v).inter <|
    DependsOnCoordinates.iInter fun w ↦ DependsOnCoordinates.iInter fun _hw ↦
      (dependsOnCoordinates_coordinateStripEntranceEvent d i a w).compl

theorem pairwiseDisjoint_canonicalCoordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) :
    Set.PairwiseDisjoint Set.univ
      (canonicalCoordinateStripEntranceEvent d i a) := by
  intro v _hv w _hw hvw
  change Disjoint (canonicalCoordinateStripEntranceEvent d i a v)
    (canonicalCoordinateStripEntranceEvent d i a w)
  rw [Set.disjoint_left]
  intro ω hv hw
  have hcode : Encodable.encode v ≠ Encodable.encode w := fun h ↦
    hvw (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hcode with hvwCode | hwvCode
  · exact (Set.mem_iInter.mp (Set.mem_iInter.mp hw.2 v) hvwCode) hv.1
  · exact (Set.mem_iInter.mp (Set.mem_iInter.mp hv.2 w) hwvCode) hw.1

theorem iUnion_canonicalCoordinateStripEntranceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) :
    (⋃ v, canonicalCoordinateStripEntranceEvent d i a v) =
      ⋃ v, coordinateStripEntranceEvent d i a v := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun v ↦ Set.inter_subset_left
  · intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨v₀, hv₀⟩ := hω
    let P : ℕ → Prop := fun n ↦
      ∃ v : Cubic d, Encodable.encode v = n ∧
        ω ∈ coordinateStripEntranceEvent d i a v
    have hP : ∃ n, P n := ⟨Encodable.encode v₀, v₀, rfl, hv₀⟩
    let n := Nat.find hP
    obtain ⟨v, hvCode, hv⟩ := Nat.find_spec hP
    refine ⟨v, hv, ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro w hwCode hw
    have hPw : P (Encodable.encode w) := ⟨w, rfl, hw⟩
    have hle := Nat.find_min' hP hPw
    have hlt : Encodable.encode w < Nat.find hP := hwCode.trans_eq hvCode
    exact (not_lt_of_ge hle) hlt

/-- The selected entrance vertex does not lie in an infinite open cluster internal to the fresh
strip. -/
def coordinateStripAvoidanceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) (v : Cubic d) :
    Set (EdgeConfiguration d) :=
  {ω | ¬(cubicOpenClusterWithinVertices d (cubicCoordinateStrip d i a k) ω v).Infinite}

theorem measurableSet_coordinateStripAvoidanceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) (v : Cubic d) :
    MeasurableSet (coordinateStripAvoidanceEvent d i a k v) :=
  (measurableSet_cubicOpenClusterWithinVertices_infinite d
    (cubicCoordinateStrip d i a k) v).compl

theorem dependsOnCoordinates_coordinateStripAvoidanceEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) (v : Cubic d) :
    DependsOnCoordinates
      (cubicInternalEdgeSet d (cubicCoordinateStrip d i a k))
      (coordinateStripAvoidanceEvent d i a k v) :=
  (dependsOnCoordinates_cubicOpenClusterWithinVertices_infinite d
    (cubicCoordinateStrip d i a k) v).compl

theorem bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
    {d : ℕ} (p : I) (i : Fin d) {a : ℤ} (k : ℕ) {v : Cubic d}
    (hv : v i = a) :
    (bernoulliBondMeasure d p).real
        (coordinateStripAvoidanceEvent d i a k v) =
      1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin := by
  rw [show coordinateStripAvoidanceEvent d i a k v =
      {ω | (cubicOpenClusterWithinVertices d
        (cubicCoordinateStrip d i a k) ω v).Infinite}ᶜ by rfl,
    measureReal_compl
      (measurableSet_cubicOpenClusterWithinVertices_infinite d
        (cubicCoordinateStrip d i a k) v)]
  rw [show (bernoulliBondMeasure d p).real
      {ω | (cubicOpenClusterWithinVertices d
        (cubicCoordinateStrip d i a k) ω v).Infinite} =
      regionThetaFrom d (cubicCoordinateStrip d i a k) p v by rfl]
  rw [← hv, regionThetaFrom_coordinateStrip_eq p i v k]
  simp

/-- A canonical entrance lies on its defining hyperplane. -/
theorem coordinate_eq_of_mem_canonicalCoordinateStripEntranceEvent
    {d : ℕ} {i : Fin d} {a : ℤ} {v : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ canonicalCoordinateStripEntranceEvent d i a v) :
    v i = a := by
  have hEntrance := hω.1
  rw [coordinateStripEntranceEvent] at hEntrance
  split at hEntrance
  · assumption
  · exact False.elim hEntrance

/-- One exploration step: choose the canonical entrance using the past coordinates and require
that it avoid the infinite cluster made from the fresh strip coordinates. -/
def coordinateStripRestartEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) : Set (EdgeConfiguration d) :=
  ⋃ v : Cubic d,
    canonicalCoordinateStripEntranceEvent d i a v ∩
      coordinateStripAvoidanceEvent d i a k v

theorem measurableSet_coordinateStripRestartEvent
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) :
    MeasurableSet (coordinateStripRestartEvent d i a k) :=
  MeasurableSet.iUnion fun v ↦
    (measurableSet_canonicalCoordinateStripEntranceEvent d i a v).inter
      (measurableSet_coordinateStripAvoidanceEvent d i a k v)

/-- A finite origin cluster forces every strip cluster rooted at an origin-connected entrance
to be finite. -/
theorem mem_coordinateStripAvoidanceEvent_of_finiteCluster_of_connection
    {d : ℕ} {i : Fin d} {a : ℤ} {k : ℕ} {v : Cubic d}
    {ω : EdgeConfiguration d} (hfinite : ω ∈ finiteClusterEvent d)
    (hconn : ω ∈ connectionEvent d cubicOrigin v) :
    ω ∈ coordinateStripAvoidanceEvent d i a k v := by
  intro hinfinite
  apply hfinite.not_infinite
  apply hinfinite.mono
  intro y hy
  obtain ⟨_hyStrip, hvy⟩ := hy
  obtain ⟨w₀, hw₀⟩ := hconn
  obtain ⟨w₁, hw₁, _hw₁Strip⟩ := hvy
  exact ⟨w₀.append w₁, walkIsOpen_append hw₀ hw₁⟩

/-- If some entrance exists, the least encoded entrance exists and supplies the restart event. -/
theorem mem_coordinateStripRestartEvent_of_finiteCluster_of_exists_entrance
    {d : ℕ} {i : Fin d} {a : ℤ} {k : ℕ} {ω : EdgeConfiguration d}
    (hfinite : ω ∈ finiteClusterEvent d)
    (hEntrance : ∃ v, ω ∈ coordinateStripEntranceEvent d i a v) :
    ω ∈ coordinateStripRestartEvent d i a k := by
  have hCanonical : ω ∈ ⋃ v, canonicalCoordinateStripEntranceEvent d i a v := by
    rw [iUnion_canonicalCoordinateStripEntranceEvent]
    simpa only [Set.mem_iUnion] using hEntrance
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hCanonical
  apply Set.mem_iUnion.mpr
  refine ⟨v, hv, ?_⟩
  apply mem_coordinateStripAvoidanceEvent_of_finiteCluster_of_connection hfinite
  exact mem_connectionEvent_of_mem_coordinateStripEntranceEvent hv.1

/-- **Fresh-strip contraction (equations 8.46--8.47, one-step form).**  Any measurable history
determined by bonds touching the strict past loses at least the rooted strip-percolation
probability when the next canonical entrance is required to avoid the strip's infinite cluster.
-/
theorem bernoulliBondMeasure_real_history_inter_coordinateStripRestartEvent_le
    {d : ℕ} (p : I) (i : Fin d) (a : ℤ) (k : ℕ)
    {H : Set (EdgeConfiguration d)} (hHm : MeasurableSet H)
    (hH : DependsOnCoordinates (cubicEdgesTouchingCoordinateStrictPast d i a) H) :
    (bernoulliBondMeasure d p).real
        (H ∩ coordinateStripRestartEvent d i a k) ≤
      (1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin) *
        (bernoulliBondMeasure d p).real H := by
  classical
  let μ := bernoulliBondMeasure d p
  let C : Cubic d → Set (EdgeConfiguration d) :=
    canonicalCoordinateStripEntranceEvent d i a
  let F : Cubic d → Set (EdgeConfiguration d) :=
    coordinateStripAvoidanceEvent d i a k
  let D : Cubic d → Set (EdgeConfiguration d) := fun v ↦ H ∩ C v
  let E : Cubic d → Set (EdgeConfiguration d) := fun v ↦ D v ∩ F v
  let F₀ := coordinateStripAvoidanceEvent d i 0 k cubicOrigin
  have hCpair : Pairwise (Function.onFun Disjoint C) := by
    intro v w hvw
    exact pairwiseDisjoint_canonicalCoordinateStripEntranceEvent d i a
      (Set.mem_univ v) (Set.mem_univ w) hvw
  have hDpair : Pairwise (Function.onFun Disjoint D) := by
    intro v w hvw
    exact (hCpair hvw).mono Set.inter_subset_right Set.inter_subset_right
  have hEpair : Pairwise (Function.onFun Disjoint E) := by
    intro v w hvw
    exact (hDpair hvw).mono Set.inter_subset_left Set.inter_subset_left
  have hDm : ∀ v, MeasurableSet (D v) := fun v ↦
    hHm.inter (measurableSet_canonicalCoordinateStripEntranceEvent d i a v)
  have hEm : ∀ v, MeasurableSet (E v) := fun v ↦
    (hDm v).inter (measurableSet_coordinateStripAvoidanceEvent d i a k v)
  have hterm : ∀ v, μ (E v) = μ (D v) * μ F₀ := by
    intro v
    by_cases hv : v i = a
    · have hDdep : DependsOnCoordinates
          (cubicEdgesTouchingCoordinateStrictPast d i a) (D v) :=
        hH.inter (dependsOnCoordinates_canonicalCoordinateStripEntranceEvent d i a v)
      have hindep : IndepSet (D v) (F v) μ := by
        change IndepSet (D v) (F v) setBer((Set.univ : Set (CubicEdge d)), p)
        exact setBernoulli_indepSet_of_dependsOnCoordinates p
          (disjoint_cubicEdgesTouchingCoordinateStrictPast_internalStrip d i a k)
          hDdep (dependsOnCoordinates_coordinateStripAvoidanceEvent d i a k v)
          (hDm v) (measurableSet_coordinateStripAvoidanceEvent d i a k v)
      have hFreal : μ.real (F v) = μ.real F₀ := by
        rw [bernoulliBondMeasure_real_coordinateStripAvoidanceEvent p i k hv]
        exact (bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
          p i k (v := cubicOrigin) rfl).symm
      have hFmeasure : μ (F v) = μ F₀ := by
        apply (ENNReal.toReal_eq_toReal_iff'
          (measure_ne_top μ (F v)) (measure_ne_top μ F₀)).mp
        simpa [Measure.real] using hFreal
      rw [show E v = D v ∩ F v by rfl, hindep.measure_inter_eq_mul, hFmeasure]
    · have hCempty : C v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        exact hv (coordinate_eq_of_mem_canonicalCoordinateStripEntranceEvent hω)
      simp [E, D, hCempty]
  have hevent : H ∩ coordinateStripRestartEvent d i a k = ⋃ v, E v := by
    ext ω
    simp only [coordinateStripRestartEvent, Set.mem_inter_iff, Set.mem_iUnion, E, D, C, F]
    aesop
  have hmeasureUnionE : μ (⋃ v, E v) = ∑' v, μ (E v) :=
    measure_iUnion hEpair hEm
  have hmeasureUnionD : μ (⋃ v, D v) = ∑' v, μ (D v) :=
    measure_iUnion hDpair hDm
  have hUnionDsub : (⋃ v, D v) ⊆ H := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    exact hω.choose_spec.1
  have hENN : μ (H ∩ coordinateStripRestartEvent d i a k) ≤ μ H * μ F₀ := by
    rw [hevent, hmeasureUnionE, tsum_congr hterm, ENNReal.tsum_mul_right,
      ← hmeasureUnionD]
    gcongr
  calc
    μ.real (H ∩ coordinateStripRestartEvent d i a k) ≤
        (μ H * μ F₀).toReal := by
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top (measure_ne_top μ H) (measure_ne_top μ F₀)) hENN
    _ = μ.real H * μ.real F₀ := by
      rw [ENNReal.toReal_mul]
      rfl
    _ = (1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin) *
        μ.real H := by
      change (bernoulliBondMeasure d p).real H *
          (bernoulliBondMeasure d p).real
            (coordinateStripAvoidanceEvent d i 0 k cubicOrigin) = _
      rw [bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
        p i (a := 0) k (v := cubicOrigin) rfl]
      ring

/-- Entrance hyperplane of the `r`-th width-`k` strip. -/
def coordinateStripBoundary (k r : ℕ) : ℤ :=
  (r : ℤ) * k

@[simp]
theorem coordinateStripBoundary_zero (k : ℕ) : coordinateStripBoundary k 0 = 0 := by
  simp [coordinateStripBoundary]

theorem coordinateStripBoundary_succ (k r : ℕ) :
    coordinateStripBoundary k (r + 1) = coordinateStripBoundary k r + k := by
  simp only [coordinateStripBoundary, Nat.cast_add, Nat.cast_one]
  ring

theorem cubicEdgesTouchingCoordinateStrictPast_mono
    {d : ℕ} (i : Fin d) {a b : ℤ} (hab : a ≤ b) :
    cubicEdgesTouchingCoordinateStrictPast d i a ⊆
      cubicEdgesTouchingCoordinateStrictPast d i b := by
  intro e he
  exact he.elim (fun h ↦ Or.inl (h.trans_le hab))
    (fun h ↦ Or.inr (h.trans_le hab))

theorem cubicInternalEdgeSet_coordinateStrip_subset_touching_next
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) :
    cubicInternalEdgeSet d (cubicCoordinateStrip d i a k) ⊆
      cubicEdgesTouchingCoordinateStrictPast d i (a + k) := by
  intro e he
  exact Or.inl he.1.2

theorem dependsOnCoordinates_coordinateStripRestartEvent_nextPast
    (d : ℕ) (i : Fin d) (a : ℤ) (k : ℕ) :
    DependsOnCoordinates (cubicEdgesTouchingCoordinateStrictPast d i (a + k))
      (coordinateStripRestartEvent d i a k) := by
  apply DependsOnCoordinates.iUnion
  intro v
  apply DependsOnCoordinates.inter
  · exact (dependsOnCoordinates_canonicalCoordinateStripEntranceEvent d i a v).mono
      (cubicEdgesTouchingCoordinateStrictPast_mono i (by omega))
  · exact (dependsOnCoordinates_coordinateStripAvoidanceEvent d i a k v).mono
      (cubicInternalEdgeSet_coordinateStrip_subset_touching_next d i a k)

/-- Grimmett's accumulated avoidance history `A_r`.  The first strip is rooted at the origin;
each later strip uses its canonical entrance from the already explored strict past. -/
def coordinateStripAvoidanceHistory
    (d : ℕ) (i : Fin d) (k : ℕ) : ℕ → Set (EdgeConfiguration d)
  | 0 => Set.univ
  | 1 => coordinateStripAvoidanceEvent d i 0 k cubicOrigin
  | r + 2 =>
      coordinateStripAvoidanceHistory d i k (r + 1) ∩
        coordinateStripRestartEvent d i (coordinateStripBoundary k (r + 1)) k

theorem measurableSet_coordinateStripAvoidanceHistory
    (d : ℕ) (i : Fin d) (k r : ℕ) :
    MeasurableSet (coordinateStripAvoidanceHistory d i k r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [coordinateStripAvoidanceHistory]
  | one =>
      exact measurableSet_coordinateStripAvoidanceEvent d i 0 k cubicOrigin
  | more r _hr hr1 =>
      exact hr1.inter <|
        measurableSet_coordinateStripRestartEvent d i
          (coordinateStripBoundary k (r + 1)) k

theorem dependsOnCoordinates_coordinateStripAvoidanceHistory
    (d : ℕ) (i : Fin d) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    DependsOnCoordinates
      (cubicEdgesTouchingCoordinateStrictPast d i (coordinateStripBoundary k r))
      (coordinateStripAvoidanceHistory d i k r) := by
  induction r using Nat.twoStepInduction with
  | zero => omega
  | one =>
      exact (dependsOnCoordinates_coordinateStripAvoidanceEvent d i 0 k cubicOrigin).mono <| by
        simpa [coordinateStripBoundary] using
          (cubicInternalEdgeSet_coordinateStrip_subset_touching_next d i 0 k)
  | more r _hr hr1 =>
      rw [coordinateStripAvoidanceHistory]
      apply DependsOnCoordinates.inter
      · apply (hr1 (by omega)).mono
        apply cubicEdgesTouchingCoordinateStrictPast_mono i
        simp only [coordinateStripBoundary, Nat.cast_add, Nat.cast_one]
        have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
        apply mul_le_mul_of_nonneg_right _ hk0
        norm_num
      · simpa [coordinateStripBoundary_succ] using
          (dependsOnCoordinates_coordinateStripRestartEvent_nextPast d i
            (coordinateStripBoundary k (r + 1)) k)

/-- **Iterated strip contraction (equation 8.47).** -/
theorem bernoulliBondMeasure_real_coordinateStripAvoidanceHistory_le_pow
    {d : ℕ} (p : I) (i : Fin d) (k r : ℕ) :
    (bernoulliBondMeasure d p).real
        (coordinateStripAvoidanceHistory d i k r) ≤
      (1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin) ^ r := by
  let q := 1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin
  have hq : 0 ≤ q := by
    change 0 ≤ 1 - regionThetaFrom d (cubicCoordinateStrip d i 0 k) p cubicOrigin
    rw [← bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
      p i (a := 0) k (v := cubicOrigin) rfl]
    exact measureReal_nonneg
  induction r using Nat.twoStepInduction with
  | zero => simp [coordinateStripAvoidanceHistory]
  | one =>
      rw [show coordinateStripAvoidanceHistory d i k 1 =
        coordinateStripAvoidanceEvent d i 0 k cubicOrigin by rfl,
        bernoulliBondMeasure_real_coordinateStripAvoidanceEvent
          p i (a := 0) k (v := cubicOrigin) rfl]
      simp
  | more r _hr hr1 =>
      have hstep :=
        bernoulliBondMeasure_real_history_inter_coordinateStripRestartEvent_le
          p i (coordinateStripBoundary k (r + 1)) k
          (measurableSet_coordinateStripAvoidanceHistory d i k (r + 1))
          (dependsOnCoordinates_coordinateStripAvoidanceHistory d i k (by omega))
      rw [show coordinateStripAvoidanceHistory d i k (r + 2) =
          coordinateStripAvoidanceHistory d i k (r + 1) ∩
            coordinateStripRestartEvent d i (coordinateStripBoundary k (r + 1)) k by rfl]
      calc
        (bernoulliBondMeasure d p).real
            (coordinateStripAvoidanceHistory d i k (r + 1) ∩
              coordinateStripRestartEvent d i (coordinateStripBoundary k (r + 1)) k) ≤
            q * (bernoulliBondMeasure d p).real
              (coordinateStripAvoidanceHistory d i k (r + 1)) := hstep
        _ ≤ q * q ^ (r + 1) := by gcongr
        _ = q ^ (r + 2) := by rw [pow_succ']; ring

end Percolation
