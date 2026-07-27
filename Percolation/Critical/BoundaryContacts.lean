import Percolation.Critical.InfiniteClusterZeroOne
import Percolation.Critical.Seeds
import Percolation.Critical.StaticCoalescence
import Percolation.Critical.ConcreteAnimals

/-!
# Boundary contacts for Grimmett Lemma 7.9

The first step in the seed amplification argument is elementary but logically important: once
the root-free infinite-cluster event has probability one, expanding central boxes meet an
infinite cluster with probability tending to one.  This file packages that approximation before
introducing the finite boundary-contact counts `U(n)` and `V(n)` from pp. 151--152.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

/-- The event that some vertex of the central box `B(m)` belongs to an infinite open cluster. -/
def centralBoxMeetsInfiniteClusterEvent (d m : ℕ) : Set (EdgeConfiguration d) :=
  {omega | ∃ x ∈ cubicMetricBox d cubicOrigin m,
    hasInfiniteOpenClusterFrom d omega x}

theorem measurableSet_centralBoxMeetsInfiniteClusterEvent (d m : ℕ) :
    MeasurableSet (centralBoxMeetsInfiniteClusterEvent d m) := by
  have hrepr : centralBoxMeetsInfiniteClusterEvent d m =
      ⋃ x ∈ cubicMetricBox d cubicOrigin m,
        {omega | hasInfiniteOpenClusterFrom d omega x} := by
    ext omega
    simp [centralBoxMeetsInfiniteClusterEvent]
  rw [hrepr]
  exact (cubicMetricBox d cubicOrigin m).measurableSet_biUnion fun x _hx =>
    measurableSet_hasInfiniteOpenClusterFrom d x

theorem centralBoxMeetsInfiniteClusterEvent_mono {d m n : ℕ} (hmn : m ≤ n) :
    centralBoxMeetsInfiniteClusterEvent d m ⊆ centralBoxMeetsInfiniteClusterEvent d n := by
  rintro omega ⟨x, hx, hinf⟩
  exact ⟨x, mem_cubicMetricBox_iff_lInfDist_le.mpr
    ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans hmn), hinf⟩

theorem monotone_centralBoxMeetsInfiniteClusterEvent (d : ℕ) :
    Monotone (centralBoxMeetsInfiniteClusterEvent d) :=
  fun _m _n hmn => centralBoxMeetsInfiniteClusterEvent_mono hmn

/-- Expanding central boxes exhaust the event that some infinite open component exists. -/
theorem iUnion_centralBoxMeetsInfiniteClusterEvent (d : ℕ) :
    (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) =
      {omega | hasInfiniteOpenClusterInVertices d Set.univ omega} := by
  ext omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, x, _hx, hinf⟩
    exact ⟨x, Set.mem_univ x, by
      simpa [cubicOpenClusterWithinVertices_univ, hasInfiniteOpenClusterFrom] using hinf⟩
  · rintro ⟨x, _hx, hinf⟩
    refine ⟨cubicLInfDist cubicOrigin x, x, ?_, ?_⟩
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr le_rfl
    · simpa [cubicOpenClusterWithinVertices_univ, hasInfiniteOpenClusterFrom] using hinf

/-- If rooted percolation is positive, expanding central boxes meet an infinite cluster with
probability tending to one.  This is the formal version of the first sentence of the proof of
Lemma 7.9. -/
theorem centralBoxMeetsInfiniteCluster_probability_tendsto_one
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p) :
    Tendsto
      (fun m : ℕ =>
        (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m))
      atTop (nhds 1) := by
  let mu := bernoulliBondMeasure d p
  have hcont : Tendsto
      (fun m : ℕ => mu (centralBoxMeetsInfiniteClusterEvent d m)) atTop
      (nhds (mu (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m))) :=
    tendsto_measure_iUnion_atTop (μ := mu) (monotone_centralBoxMeetsInfiniteClusterEvent d)
  have hne : mu (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) ≠ ∞ :=
    measure_ne_top mu _
  have hreal : Tendsto
      (fun m : ℕ => mu.real (centralBoxMeetsInfiniteClusterEvent d m)) atTop
      (nhds (mu.real (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m))) := by
    simpa [Measure.real] using (ENNReal.tendsto_toReal hne).comp hcont
  have hglobal :
      mu.real (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) = 1 := by
    rw [iUnion_centralBoxMeetsInfiniteClusterEvent]
    exact regionHasInfiniteClusterProbability_univ_eq_one_of_theta_pos d p htheta
  simpa [hglobal] using hreal

theorem exists_centralBoxMeetsInfiniteCluster_probability_gt
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ,
      1 - epsilon <
        (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m) := by
  have hnhds : Set.Ioi (1 - epsilon) ∈ nhds (1 : ℝ) :=
    Ioi_mem_nhds (sub_lt_self 1 hepsilon)
  have heventually :=
    (centralBoxMeetsInfiniteCluster_probability_tendsto_one d p htheta).eventually hnhds
  obtain ⟨m, hm⟩ := eventually_atTop.1 heventually
  exact ⟨m, hm m le_rfl⟩

/-! ## Finite boundary-contact sets -/

/-- Grimmett's `U(n)`: surface vertices of `B(n)` connected inside `B(n)` to the central
box `B(m)`. -/
noncomputable def boxBoundaryContacts
    (d m n : ℕ) (omega : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (cubicBoxSurface d cubicOrigin n).filter fun y =>
    ∃ x ∈ cubicMetricBox d cubicOrigin m,
      omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y

@[simp]
theorem mem_boxBoundaryContacts_iff {d m n : ℕ} {omega : EdgeConfiguration d}
    {y : Cubic d} :
    y ∈ boxBoundaryContacts d m n omega ↔
      y ∈ cubicBoxSurface d cubicOrigin n ∧
        ∃ x ∈ cubicMetricBox d cubicOrigin m,
          omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y := by
  classical
  simp [boxBoundaryContacts]

/-- The contact-count event `|U(n)| < ell`. -/
def boundaryContactCardLtEvent (d m n ell : ℕ) : Set (EdgeConfiguration d) :=
  {omega | (boxBoundaryContacts d m n omega).card < ell}

/-- The complementary event `ell ≤ |U(n)|`. -/
def boundaryContactCardGeEvent (d m n ell : ℕ) : Set (EdgeConfiguration d) :=
  {omega | ell ≤ (boxBoundaryContacts d m n omega).card}

theorem dependsOn_boundaryContactCardLtEvent (d m n ell : ℕ) :
    DependsOn (cubicBoxEdges d cubicOrigin n) (boundaryContactCardLtEvent d m n ell) := by
  classical
  intro omega eta hagree
  have hcontacts : boxBoundaryContacts d m n omega = boxBoundaryContacts d m n eta := by
    ext y
    simp only [mem_boxBoundaryContacts_iff]
    apply and_congr_right
    intro _hy
    apply exists_congr
    intro x
    apply and_congr_right
    intro _hx
    exact dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y hagree
  simp [boundaryContactCardLtEvent, hcontacts]

theorem measurableSet_boundaryContactCardLtEvent (d m n ell : ℕ) :
    MeasurableSet (boundaryContactCardLtEvent d m n ell) :=
  (dependsOn_boundaryContactCardLtEvent d m n ell).measurableSet

theorem boundaryContactCardGeEvent_eq_compl (d m n ell : ℕ) :
    boundaryContactCardGeEvent d m n ell =
      (boundaryContactCardLtEvent d m n ell)ᶜ := by
  ext omega
  simp [boundaryContactCardGeEvent, boundaryContactCardLtEvent]

theorem measurableSet_boundaryContactCardGeEvent (d m n ell : ℕ) :
    MeasurableSet (boundaryContactCardGeEvent d m n ell) := by
  rw [boundaryContactCardGeEvent_eq_compl]
  exact (measurableSet_boundaryContactCardLtEvent d m n ell).compl

/-- An infinite-cluster vertex in `B(m)` supplies at least one contact on every later surface. -/
theorem boxBoundaryContacts_nonempty_of_centralBoxMeetsInfiniteCluster
    {d m n : ℕ} {omega : EdgeConfiguration d} (hmn : m ≤ n)
    (hinf : omega ∈ centralBoxMeetsInfiniteClusterEvent d m) :
    (boxBoundaryContacts d m n omega).Nonempty := by
  obtain ⟨x, hxBox, hxInf⟩ := hinf
  have hxOuter : x ∈ cubicMetricBox d cubicOrigin n :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hxBox).trans hmn)
  have hsurface := hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent hxOuter hxInf
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion] at hsurface
  obtain ⟨y, hySurface, hyConnection⟩ := hsurface
  exact ⟨y, mem_boxBoundaryContacts_iff.mpr
    ⟨hySurface, x, hxBox, hyConnection⟩⟩

theorem centralBoxMeetsInfiniteClusterEvent_subset_one_le_contactCard
    {d m n : ℕ} (hmn : m ≤ n) :
    centralBoxMeetsInfiniteClusterEvent d m ⊆
      {omega | 1 ≤ (boxBoundaryContacts d m n omega).card} := by
  intro omega hinf
  exact Finset.one_le_card.mpr
    (boxBoundaryContacts_nonempty_of_centralBoxMeetsInfiniteCluster hmn hinf)

theorem centralBoxMeetsInfiniteCluster_probability_le_one_le_contactCard
    (d : ℕ) (p : I) {m n : ℕ} (hmn : m ≤ n) :
    (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m) ≤
      (bernoulliBondMeasure d p).real (boundaryContactCardGeEvent d m n 1) := by
  exact measureReal_mono
    (centralBoxMeetsInfiniteClusterEvent_subset_one_le_contactCard hmn)
    (measure_ne_top _ _)

/-! ## Unrevealed exit bonds -/

/-- Edges incident to a proposed contact set `S` which are not internal edges of `B(n)`.
These coordinates are disjoint from the information defining `U(n)`. -/
noncomputable def boxBoundaryExitEdges
    (d n : ℕ) (S : Finset (Cubic d)) : Finset (CubicEdge d) :=
  cubicIncidentEdges d S \ cubicBoxEdges d cubicOrigin n

theorem boxBoundaryExitEdges_card_le (d n : ℕ) (S : Finset (Cubic d)) :
    (boxBoundaryExitEdges d n S).card ≤ S.card * (2 * d) := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (cubicIncidentEdges_card_le d S)

theorem disjoint_cubicBoxEdges_boxBoundaryExitEdges
    (d n : ℕ) (S : Finset (Cubic d)) :
    Disjoint (cubicBoxEdges d cubicOrigin n : Set (CubicEdge d))
      (boxBoundaryExitEdges d n S : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heBox heExit
  exact (Finset.mem_sdiff.mp heExit).2 heBox

theorem mem_boxBoundaryExitEdges_of_incident_of_not_internal
    {d n : ℕ} {S : Finset (Cubic d)} {e : CubicEdge d} {x : Cubic d}
    (hxS : x ∈ S) (hxe : x ∈ (e : Sym2 (Cubic d)))
    (heNot : e ∉ cubicBoxEdges d cubicOrigin n) :
    e ∈ boxBoundaryExitEdges d n S := by
  exact Finset.mem_sdiff.mpr
    ⟨mem_cubicIncidentEdges_of_endpoint hxS hxe, heNot⟩

/-- The finite event that the entire contact set at radius `n` is exactly `S`. -/
def boundaryContactSetEvent
    (d m n : ℕ) (S : Finset (Cubic d)) : Set (EdgeConfiguration d) :=
  {omega | boxBoundaryContacts d m n omega = S}

theorem dependsOn_boundaryContactSetEvent
    (d m n : ℕ) (S : Finset (Cubic d)) :
    DependsOn (cubicBoxEdges d cubicOrigin n) (boundaryContactSetEvent d m n S) := by
  classical
  intro omega eta hagree
  have hcontacts : boxBoundaryContacts d m n omega = boxBoundaryContacts d m n eta := by
    ext y
    simp only [mem_boxBoundaryContacts_iff]
    apply and_congr_right
    intro _hy
    apply exists_congr
    intro x
    apply and_congr_right
    intro _hx
    exact dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y hagree
  simp [boundaryContactSetEvent, hcontacts]

theorem measurableSet_boundaryContactSetEvent
    (d m n : ℕ) (S : Finset (Cubic d)) :
    MeasurableSet (boundaryContactSetEvent d m n S) :=
  (dependsOn_boundaryContactSetEvent d m n S).measurableSet

theorem measurableSet_boundaryContactSetEvent_edgeCoordinates
    (d m n : ℕ) (S : Finset (Cubic d)) :
    MeasurableSet[edgeCoordinateMeasurableSpace d (cubicBoxEdges d cubicOrigin n)]
      (boundaryContactSetEvent d m n S) := by
  simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
    (dependsOn_boundaryContactSetEvent d m n S).measurableSet_generateFrom_coordinateEvents
      (S := (cubicBoxEdges d cubicOrigin n : Set (CubicEdge d))) (by simp)

theorem boundaryContactSetEvent_indep_closedExitEdges
    (d m n : ℕ) (p : I) (S : Finset (Cubic d)) :
    IndepSet (boundaryContactSetEvent d m n S)
      (closedEdgeSetEvent d (boxBoundaryExitEdges d n S))
      (bernoulliBondMeasure d p) := by
  exact bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace
    d p (cubicBoxEdges d cubicOrigin n) (boxBoundaryExitEdges d n S)
    (disjoint_cubicBoxEdges_boxBoundaryExitEdges d n S)
    (measurableSet_boundaryContactSetEvent_edgeCoordinates d m n S)
    (measurableSet_closedEdgeSetEvent_edgeCoordinateMeasurableSpace d
      (boxBoundaryExitEdges d n S))

/-- A cubic edge leaving `B(n)` from a vertex in `B(n)` starts on its surface. -/
theorem mem_cubicBoxSurface_of_adj_mem_notMem
    {d n : ℕ} {u v : Cubic d} (hu : u ∈ cubicMetricBox d cubicOrigin n)
    (huv : (cubicGraph d).Adj u v) (hv : v ∉ cubicMetricBox d cubicOrigin n) :
    u ∈ cubicBoxSurface d cubicOrigin n := by
  obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom u v).mp huv
  have huDist : cubicLInfDist cubicOrigin u ≤ n :=
    mem_cubicMetricBox_iff_lInfDist_le.mp hu
  have hvDist : n < cubicLInfDist cubicOrigin v := by
    exact lt_of_not_ge fun hle => hv (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
  have huvDist : cubicLInfDist cubicOrigin v ≤ cubicLInfDist cubicOrigin u + 1 := by
    calc
      cubicLInfDist cubicOrigin v ≤
          cubicLInfDist cubicOrigin u + cubicLInfDist u v :=
        cubicLInfDist_triangle cubicOrigin u v
      _ ≤ cubicLInfDist cubicOrigin u + 1 := by
        gcongr
        simpa [ha] using cubicLInfDist_stepFrom_le_one u a
  exact mem_cubicBoxSurface.mpr (by omega)

/-- Extend an in-box connection by one open cubic edge whose two endpoints remain in the box. -/
theorem mem_connectionEventIn_of_mem_of_adj
    {d n : ℕ} {omega : EdgeConfiguration d} {x u v : Cubic d}
    (hxu : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x u)
    (hu : u ∈ cubicMetricBox d cubicOrigin n)
    (hv : v ∈ cubicMetricBox d cubicOrigin n)
    (huv : (cubicGraph d).Adj u v)
    (hopen :
      (⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huv⟩ : CubicEdge d) ∈ omega) :
    omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x v := by
  obtain ⟨q, hqOpen, hqEdges⟩ := hxu
  let step : (cubicGraph d).Walk u v := SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
  have hstepOpen : walkIsOpen omega step := by
    intro e he
    have heq : e = s(u, v) := by
      simpa [step, SimpleGraph.Walk.edges_cons] using he
    subst e
    simpa using hopen
  have hstepEdges : walkEdgeFinset step ⊆ cubicBoxEdges d cubicOrigin n :=
    walkEdgeFinset_subset_cubicBoxEdges_of_support step (by
      intro z hz
      simp [step] at hz
      rcases hz with rfl | rfl
      · exact hu
      · exact hv)
  refine ⟨q.append step, walkIsOpen_append hqOpen hstepOpen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · exact hqEdges ((mem_walkEdgeFinset_iff q e).mpr he)
  · exact hstepEdges ((mem_walkEdgeFinset_iff step e).mpr he)

/-- If all unrevealed exit bonds of the exact contact set are closed, an open walk which has
already reached the box through its internal edges can never leave the box. -/
theorem walk_support_subset_box_of_closed_contact_exits
    {d m n : ℕ} {omega : EdgeConfiguration d} {S : Finset (Cubic d)}
    {x u y : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin m)
    (hS : boxBoundaryContacts d m n omega = S)
    (hclosed : omega ∈ closedEdgeSetEvent d (boxBoundaryExitEdges d n S))
    (w : (cubicGraph d).Walk u y) (hwOpen : walkIsOpen omega w)
    (hu : u ∈ cubicMetricBox d cubicOrigin n)
    (hxu : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x u) :
    ∀ z ∈ w.support, z ∈ cubicMetricBox d cubicOrigin n := by
  induction w with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hu
  | @cons u v y huv p ih =>
      have heOpen :
          (⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huv⟩ : CubicEdge d) ∈
            omega := by
        apply hwOpen
        simp [SimpleGraph.Walk.edges_cons]
      have hv : v ∈ cubicMetricBox d cubicOrigin n := by
        by_contra hvNot
        have huSurface : u ∈ cubicBoxSurface d cubicOrigin n :=
          mem_cubicBoxSurface_of_adj_mem_notMem hu huv hvNot
        have huContact : u ∈ boxBoundaryContacts d m n omega :=
          mem_boxBoundaryContacts_iff.mpr ⟨huSurface, x, hx, hxu⟩
        have huS : u ∈ S := by simpa [hS] using huContact
        let e : CubicEdge d :=
          ⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr huv⟩
        have heNotInternal : e ∉ cubicBoxEdges d cubicOrigin n := by
          intro heInternal
          exact hvNot (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heInternal (by
            simp [e]))
        have heExit : e ∈ boxBoundaryExitEdges d n S :=
          mem_boxBoundaryExitEdges_of_incident_of_not_internal huS (by simp [e]) heNotInternal
        exact Set.disjoint_left.mp (mem_closedEdgeSetEvent d _ omega |>.mp hclosed)
          heExit (by simpa [e] using heOpen)
      have hxu' : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x v :=
        mem_connectionEventIn_of_mem_of_adj hxu hu hv huv heOpen
      have hpOpen : walkIsOpen omega p := by
        intro e he
        exact hwOpen e (by simp [SimpleGraph.Walk.edges_cons, he])
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · exact ih hpOpen hv hxu' z hz

/-- Closing the unrevealed exit bonds of the exact nonempty contact set makes the next contact
set empty.  This is the deterministic map behind equation (7.16). -/
theorem boundaryContactSet_inter_closedExit_subset_next_empty
    {d m n : ℕ} (hmn : m ≤ n) (S : Finset (Cubic d)) :
    boundaryContactSetEvent d m n S ∩
        closedEdgeSetEvent d (boxBoundaryExitEdges d n S) ⊆
      boundaryContactSetEvent d m (n + 1) ∅ := by
  intro omega homega
  rcases homega with ⟨hS, hclosed⟩
  change boxBoundaryContacts d m n omega = S at hS
  change boxBoundaryContacts d m (n + 1) omega = ∅
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨y, hy⟩
  obtain ⟨hySurface, x, hx, hxy⟩ := mem_boxBoundaryContacts_iff.mp hy
  obtain ⟨w, hwOpen, _hwEdges⟩ := hxy
  have hxOuter : x ∈ cubicMetricBox d cubicOrigin n :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans hmn)
  have hxx : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x x := by
    refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
    · intro e he
      simp at he
    · intro e he
      rw [mem_walkEdgeFinset_iff] at he
      simp at he
  have hyInner := walk_support_subset_box_of_closed_contact_exits hx hS hclosed
    w hwOpen hxOuter hxx y (by simp)
  have hyDist : cubicLInfDist cubicOrigin y = n + 1 :=
    mem_cubicBoxSurface.mp hySurface
  exact (not_lt_of_ge (mem_cubicMetricBox_iff_lInfDist_le.mp hyInner)) (by omega)

/-- The event that the contact set is nonempty at radius `n` but empty at radius `n+1`. -/
def boundaryContactsDieNextEvent (d m n : ℕ) : Set (EdgeConfiguration d) :=
  boundaryContactCardGeEvent d m n 1 ∩ boundaryContactCardLtEvent d m (n + 1) 1

theorem measurableSet_boundaryContactsDieNextEvent (d m n : ℕ) :
    MeasurableSet (boundaryContactsDieNextEvent d m n) :=
  (measurableSet_boundaryContactCardGeEvent d m n 1).inter
    (measurableSet_boundaryContactCardLtEvent d m (n + 1) 1)

theorem boundaryContactSet_inter_closedExit_subset_dieNext
    {d m n : ℕ} (hmn : m ≤ n) {S : Finset (Cubic d)} (hSnonempty : S.Nonempty) :
    boundaryContactSetEvent d m n S ∩
        closedEdgeSetEvent d (boxBoundaryExitEdges d n S) ⊆
      boundaryContactsDieNextEvent d m n := by
  intro omega homega
  have hnext := boundaryContactSet_inter_closedExit_subset_next_empty hmn S homega
  constructor
  · change 1 ≤ (boxBoundaryContacts d m n omega).card
    rw [show boxBoundaryContacts d m n omega = S from homega.1]
    exact Finset.one_le_card.mpr hSnonempty
  · change (boxBoundaryContacts d m (n + 1) omega).card < 1
    rw [show boxBoundaryContacts d m (n + 1) omega = ∅ from hnext]
    simp

theorem boundaryContactSet_inter_closedExit_probability
    (d m n : ℕ) (p : I) (S : Finset (Cubic d)) :
    (bernoulliBondMeasure d p).real
        (boundaryContactSetEvent d m n S ∩
          closedEdgeSetEvent d (boxBoundaryExitEdges d n S)) =
      (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
        (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card := by
  have hind := (boundaryContactSetEvent_indep_closedExitEdges d m n p S).measure_inter_eq_mul
  have hreal := congrArg ENNReal.toReal hind
  rw [ENNReal.toReal_mul, ← Measure.real, ← Measure.real] at hreal
  rw [hreal]
  change (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
      (bernoulliBondMeasure d p).real
        (closedEdgeSetEvent d (boxBoundaryExitEdges d n S)) = _
  rw [bernoulliBondMeasure_real_closedEdgeSetEvent]

theorem boundaryContactSet_mul_closedExitProbability_le_dieNext
    {d m n : ℕ} (hmn : m ≤ n) (p : I) {S : Finset (Cubic d)}
    (hSnonempty : S.Nonempty) :
    (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
        (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card ≤
      (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n) := by
  rw [← boundaryContactSet_inter_closedExit_probability]
  exact measureReal_mono
    (boundaryContactSet_inter_closedExit_subset_dieNext hmn hSnonempty)
    (measure_ne_top _ _)

/-- A uniform version of the preceding estimate for all nonempty contact sets of cardinality
strictly below `ell`.  The exponent `2d(ell-1)` is a safe incidence bound; a later refinement
to the `d(ell-1)` outward-direction count recovers Grimmett's displayed `3 ell` exponent in
dimension three. -/
theorem boundaryContactSet_mul_uniformClosedFactor_le_dieNext
    {d m n ell : ℕ} (hmn : m ≤ n) (p : I) {S : Finset (Cubic d)}
    (hSnonempty : S.Nonempty) (hScard : S.card < ell) :
    (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
        (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
      (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n) := by
  have hcard : (boxBoundaryExitEdges d n S).card ≤ (ell - 1) * (2 * d) := by
    refine (boxBoundaryExitEdges_card_le d n S).trans ?_
    exact Nat.mul_le_mul_right (2 * d) (by omega)
  have hbase0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hbase1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
  have hpow :
      (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
        (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card :=
    pow_le_pow_of_le_one hbase0 hbase1 hcard
  calc
    (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
          (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
        (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
          (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card :=
      mul_le_mul_of_nonneg_left hpow measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n) :=
      boundaryContactSet_mul_closedExitProbability_le_dieNext hmn p hSnonempty

/-- All possible nonempty contact sets of cardinality strictly below `ell`. -/
noncomputable def smallNonemptyBoundaryContactSets
    (d n ell : ℕ) : Finset (Finset (Cubic d)) := by
  classical
  exact (cubicBoxSurface d cubicOrigin n).powerset.filter fun S =>
    S.Nonempty ∧ S.card < ell

@[simp]
theorem mem_smallNonemptyBoundaryContactSets_iff
    {d n ell : ℕ} {S : Finset (Cubic d)} :
    S ∈ smallNonemptyBoundaryContactSets d n ell ↔
      S ⊆ cubicBoxSurface d cubicOrigin n ∧ S.Nonempty ∧ S.card < ell := by
  classical
  simp [smallNonemptyBoundaryContactSets]

/-- The event `1 ≤ |U(n)| < ell`. -/
def smallNonemptyBoundaryContactEvent (d m n ell : ℕ) : Set (EdgeConfiguration d) :=
  boundaryContactCardGeEvent d m n 1 ∩ boundaryContactCardLtEvent d m n ell

theorem measurableSet_smallNonemptyBoundaryContactEvent (d m n ell : ℕ) :
    MeasurableSet (smallNonemptyBoundaryContactEvent d m n ell) :=
  (measurableSet_boundaryContactCardGeEvent d m n 1).inter
    (measurableSet_boundaryContactCardLtEvent d m n ell)

theorem smallNonemptyBoundaryContactEvent_eq_biUnion (d m n ell : ℕ) :
    smallNonemptyBoundaryContactEvent d m n ell =
      ⋃ S ∈ smallNonemptyBoundaryContactSets d n ell,
        boundaryContactSetEvent d m n S := by
  classical
  ext omega
  simp only [smallNonemptyBoundaryContactEvent, Set.mem_inter_iff,
    boundaryContactCardGeEvent, boundaryContactCardLtEvent, Set.mem_setOf_eq,
    Set.mem_iUnion, boundaryContactSetEvent]
  constructor
  · rintro ⟨hne, hlt⟩
    let S := boxBoundaryContacts d m n omega
    have hsubset : S ⊆ cubicBoxSurface d cubicOrigin n := by
      intro y hy
      exact (mem_boxBoundaryContacts_iff.mp hy).1
    have hSnonempty : S.Nonempty := Finset.one_le_card.mp hne
    exact ⟨S, mem_smallNonemptyBoundaryContactSets_iff.mpr
      ⟨hsubset, hSnonempty, hlt⟩, rfl⟩
  · rintro ⟨S, hScandidate, hS⟩
    have hcandidate := mem_smallNonemptyBoundaryContactSets_iff.mp hScandidate
    rw [hS]
    exact ⟨Finset.one_le_card.mpr hcandidate.2.1, hcandidate.2.2⟩

theorem pairwiseDisjoint_boundaryContactSetEvent (d m n ell : ℕ) :
    Set.PairwiseDisjoint (smallNonemptyBoundaryContactSets d n ell : Set (Finset (Cubic d)))
      (boundaryContactSetEvent d m n) := by
  intro S _hS T _hT hST
  change Disjoint (boundaryContactSetEvent d m n S) (boundaryContactSetEvent d m n T)
  rw [Set.disjoint_left]
  intro omega homegaS homegaT
  exact hST (homegaS.symm.trans homegaT)

theorem pairwiseDisjoint_boundaryContactSet_inter_closedExit (d m n ell : ℕ) :
    Set.PairwiseDisjoint (smallNonemptyBoundaryContactSets d n ell : Set (Finset (Cubic d)))
      (fun S => boundaryContactSetEvent d m n S ∩
        closedEdgeSetEvent d (boxBoundaryExitEdges d n S)) :=
  (pairwiseDisjoint_boundaryContactSetEvent d m n ell).mono fun _S => Set.inter_subset_left

/-- Finite-energy estimate behind (7.16), with the safe `2d` incidence exponent.  The events are
partitioned by the exact value of `U(n)` before the still-unrevealed exit bonds are closed. -/
theorem smallNonemptyBoundaryContact_probability_mul_pow_le_dieNext
    {d m n ell : ℕ} (hmn : m ≤ n) (p : I) :
    (bernoulliBondMeasure d p).real (smallNonemptyBoundaryContactEvent d m n ell) *
        (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
      (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n) := by
  classical
  let C := smallNonemptyBoundaryContactSets d n ell
  let paired : Finset (Cubic d) → Set (EdgeConfiguration d) := fun S =>
    boundaryContactSetEvent d m n S ∩
      closedEdgeSetEvent d (boxBoundaryExitEdges d n S)
  have hsmall :
      (bernoulliBondMeasure d p).real (smallNonemptyBoundaryContactEvent d m n ell) =
        ∑ S ∈ C,
          (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) := by
    rw [smallNonemptyBoundaryContactEvent_eq_biUnion]
    exact measureReal_biUnion_finset
      (pairwiseDisjoint_boundaryContactSetEvent d m n ell)
      (fun S _hS => measurableSet_boundaryContactSetEvent d m n S)
  have hpaired :
      (bernoulliBondMeasure d p).real (⋃ S ∈ C, paired S) =
        ∑ S ∈ C, (bernoulliBondMeasure d p).real (paired S) := by
    exact measureReal_biUnion_finset
      (pairwiseDisjoint_boundaryContactSet_inter_closedExit d m n ell)
      (fun S _hS => (measurableSet_boundaryContactSetEvent d m n S).inter
        (measurableSet_closedEdgeSetEvent d (boxBoundaryExitEdges d n S)))
  have hpairedSubset : (⋃ S ∈ C, paired S) ⊆ boundaryContactsDieNextEvent d m n := by
    intro omega homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨S, hSC, hpair⟩ := homega
    have hSnonempty := (mem_smallNonemptyBoundaryContactSets_iff.mp hSC).2.1
    exact boundaryContactSet_inter_closedExit_subset_dieNext hmn hSnonempty hpair
  have hterm : ∀ S ∈ C,
      (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
          (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
        (bernoulliBondMeasure d p).real (paired S) := by
    intro S hSC
    have hcandidate := mem_smallNonemptyBoundaryContactSets_iff.mp hSC
    have hcard : (boxBoundaryExitEdges d n S).card ≤ (ell - 1) * (2 * d) := by
      refine (boxBoundaryExitEdges_card_le d n S).trans ?_
      exact Nat.mul_le_mul_right (2 * d) (by omega)
    have hpow :
        (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
          (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card :=
      pow_le_pow_of_le_one (sub_nonneg.mpr p.2.2) (by linarith [p.2.1]) hcard
    calc
      (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
            (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
          (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
            (1 - (p : ℝ)) ^ (boxBoundaryExitEdges d n S).card :=
        mul_le_mul_of_nonneg_left hpow measureReal_nonneg
      _ = (bernoulliBondMeasure d p).real (paired S) := by
        exact (boundaryContactSet_inter_closedExit_probability d m n p S).symm
  rw [hsmall, Finset.sum_mul]
  calc
    ∑ S ∈ C,
        (bernoulliBondMeasure d p).real (boundaryContactSetEvent d m n S) *
          (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d)) ≤
      ∑ S ∈ C, (bernoulliBondMeasure d p).real (paired S) :=
        Finset.sum_le_sum fun S hS => hterm S hS
    _ = (bernoulliBondMeasure d p).real (⋃ S ∈ C, paired S) := hpaired.symm
    _ ≤ (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n) :=
      measureReal_mono hpairedSubset (measure_ne_top _ _)

/-- A contact at a farther surface yields a contact at every intermediate surface. -/
theorem boxBoundaryContacts_nonempty_mono_radius
    {d m r R : ℕ} {omega : EdgeConfiguration d} (hmr : m ≤ r) (hrR : r ≤ R)
    (hR : (boxBoundaryContacts d m R omega).Nonempty) :
    (boxBoundaryContacts d m r omega).Nonempty := by
  obtain ⟨y, hy⟩ := hR
  obtain ⟨hySurface, x, hx, hxy⟩ := mem_boxBoundaryContacts_iff.mp hy
  obtain ⟨w, hwOpen, _hwEdges⟩ := hxy
  have hxInner : x ∈ cubicMetricBox d cubicOrigin r :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans hmr)
  have hyFar : r ≤ cubicLInfDist cubicOrigin y := by
    rw [mem_cubicBoxSurface.mp hySurface]
    exact hrR
  obtain ⟨z, hzSurface, hzConnection⟩ :=
    exists_open_walk_to_cubicBoxSurface_in_box_of_mem hxInner w hwOpen hyFar
  exact ⟨z, mem_boxBoundaryContacts_iff.mpr
    ⟨hzSurface, x, hx, hzConnection⟩⟩

theorem pairwiseDisjoint_boundaryContactsDieNextEvent
    (d m : ℕ) :
    Pairwise fun n k : ℕ =>
      Disjoint (boundaryContactsDieNextEvent d m (m + n))
        (boundaryContactsDieNextEvent d m (m + k)) := by
  intro n k hnk
  wlog hnklt : n < k generalizing n k
  · exact (this (n := k) (k := n) hnk.symm
      (lt_of_le_of_ne (not_lt.mp hnklt) hnk.symm)).symm
  rw [Set.disjoint_left]
  intro omega hn hk
  have hnEmpty : boxBoundaryContacts d m (m + n + 1) omega = ∅ := by
    apply Finset.card_eq_zero.mp
    have := hn.2
    change (boxBoundaryContacts d m (m + n + 1) omega).card < 1 at this
    omega
  have hkNonempty : (boxBoundaryContacts d m (m + k) omega).Nonempty := by
    apply Finset.one_le_card.mp
    exact hk.1
  have hnNonempty : (boxBoundaryContacts d m (m + n + 1) omega).Nonempty :=
    boxBoundaryContacts_nonempty_mono_radius (by omega) (by omega) hkNonempty
  exact hnNonempty.ne_empty hnEmpty

/-- The probability of losing the contact set at exactly the next radius tends to zero.  These
events are pairwise disjoint after the harmless finite shift by `m`. -/
theorem boundaryContactsDieNext_probability_tendsto_zero
    (d m : ℕ) (p : I) :
    Tendsto
      (fun n : ℕ =>
        (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m n))
      atTop (nhds 0) := by
  let mu := bernoulliBondMeasure d p
  let D : ℕ → Set (EdgeConfiguration d) := fun n =>
    boundaryContactsDieNextEvent d m (m + n)
  have htailENN : Tendsto
      (mu ∘ fun n => ⋃ i ≥ n, D i) atTop (nhds 0) :=
    tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (fun i => (measurableSet_boundaryContactsDieNextEvent d m (m + i)).nullMeasurableSet)
      (pairwiseDisjoint_boundaryContactsDieNextEvent d m)
  have htailReal : Tendsto
      (fun n => mu.real (⋃ i ≥ n, D i)) atTop (nhds 0) := by
    simpa [Measure.real, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp)).comp htailENN
  have hshift : Tendsto (fun n => mu.real (D n)) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) htailReal
    apply measureReal_mono
    · intro omega homega
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨le_rfl, homega⟩⟩
    · exact measure_ne_top _ _
  apply (tendsto_add_atTop_iff_nat m).mp
  simpa [mu, D, Nat.add_comm] using hshift

/-- For fixed `m` and `ell`, the probability of a nonempty but smaller-than-`ell` contact set
tends to zero. -/
theorem smallNonemptyBoundaryContact_probability_tendsto_zero
    (d m ell : ℕ) (p : I) (hp1 : (p : ℝ) < 1) :
    Tendsto
      (fun n : ℕ =>
        (bernoulliBondMeasure d p).real (smallNonemptyBoundaryContactEvent d m n ell))
      atTop (nhds 0) := by
  let c : ℝ := (1 - (p : ℝ)) ^ ((ell - 1) * (2 * d))
  have hc : 0 < c := pow_pos (sub_pos.mpr hp1) _
  have hupper : Tendsto
      (fun n : ℕ =>
        (bernoulliBondMeasure d p).real (boundaryContactsDieNextEvent d m (n + m)) / c)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((boundaryContactsDieNext_probability_tendsto_zero d m p).comp
        (tendsto_add_atTop_nat m)).div_const c
  have hshift : Tendsto
      (fun n : ℕ =>
        (bernoulliBondMeasure d p).real
          (smallNonemptyBoundaryContactEvent d m (n + m) ell))
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hupper
    apply (le_div_iff₀ hc).2
    simpa [c] using
      (smallNonemptyBoundaryContact_probability_mul_pow_le_dieNext
        (d := d) (m := m) (n := n + m) (ell := ell) (by omega) p)
  exact (tendsto_add_atTop_iff_nat m).mp hshift

theorem boundaryContactCardLtEvent_subset_empty_union_small
    (d m n ell : ℕ) :
    boundaryContactCardLtEvent d m n ell ⊆
      boundaryContactCardLtEvent d m n 1 ∪
        smallNonemptyBoundaryContactEvent d m n ell := by
  intro omega homega
  change (boxBoundaryContacts d m n omega).card < ell at homega
  by_cases hempty : (boxBoundaryContacts d m n omega).card = 0
  · left
    change (boxBoundaryContacts d m n omega).card < 1
    omega
  · right
    exact ⟨by
      change 1 ≤ (boxBoundaryContacts d m n omega).card
      omega, homega⟩

theorem boundaryContactCardLt_probability_le_empty_add_small
    (d m n ell : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real (boundaryContactCardLtEvent d m n ell) ≤
      (bernoulliBondMeasure d p).real (boundaryContactCardLtEvent d m n 1) +
        (bernoulliBondMeasure d p).real (smallNonemptyBoundaryContactEvent d m n ell) := by
  exact (measureReal_mono
    (boundaryContactCardLtEvent_subset_empty_union_small d m n ell)
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)

theorem emptyBoundaryContact_probability_le_one_sub_central
    (d : ℕ) (p : I) {m n : ℕ} (hmn : m ≤ n) :
    (bernoulliBondMeasure d p).real (boundaryContactCardLtEvent d m n 1) ≤
      1 - (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m) := by
  let mu := bernoulliBondMeasure d p
  have hmono := centralBoxMeetsInfiniteCluster_probability_le_one_le_contactCard d p hmn
  have hcompl :
      mu.real (boundaryContactCardLtEvent d m n 1) +
          mu.real (boundaryContactCardGeEvent d m n 1) = 1 := by
    have h := probReal_add_probReal_compl
      (μ := mu) (measurableSet_boundaryContactCardLtEvent d m n 1)
    rwa [← boundaryContactCardGeEvent_eq_compl] at h
  dsimp [mu] at hcompl
  linarith

/-- Quantitative boundary-contact conclusion used before seed amplification: for any prescribed
number of contacts, some central box and later surface have that many contacts with probability
greater than `1-epsilon`. -/
theorem exists_boundaryContactCardGe_probability_gt
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p) (hp1 : (p : ℝ) < 1)
    (ell : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, m ≤ n ∧
      1 - epsilon <
        (bernoulliBondMeasure d p).real (boundaryContactCardGeEvent d m n ell) := by
  obtain ⟨m, hm⟩ := exists_centralBoxMeetsInfiniteCluster_probability_gt
    d p htheta (half_pos hepsilon)
  have hsmallT := smallNonemptyBoundaryContact_probability_tendsto_zero d m ell p hp1
  have hsmallEventually : ∀ᶠ n : ℕ in atTop,
      (bernoulliBondMeasure d p).real
          (smallNonemptyBoundaryContactEvent d m n ell) < epsilon / 2 :=
    hsmallT.eventually (Iio_mem_nhds (half_pos hepsilon))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEventually
  let n := max N m
  have hmn : m ≤ n := le_max_right _ _
  have hsmall :
      (bernoulliBondMeasure d p).real
          (smallNonemptyBoundaryContactEvent d m n ell) < epsilon / 2 :=
    hN n (le_max_left _ _)
  have hempty := emptyBoundaryContact_probability_le_one_sub_central d p hmn
  have hbad := boundaryContactCardLt_probability_le_empty_add_small d m n ell p
  have hbadlt :
      (bernoulliBondMeasure d p).real (boundaryContactCardLtEvent d m n ell) < epsilon := by
    linarith
  have hcompl :
      (bernoulliBondMeasure d p).real (boundaryContactCardLtEvent d m n ell) +
          (bernoulliBondMeasure d p).real (boundaryContactCardGeEvent d m n ell) = 1 := by
    have h := probReal_add_probReal_compl
      (μ := bernoulliBondMeasure d p)
      (measurableSet_boundaryContactCardLtEvent d m n ell)
    rwa [← boundaryContactCardGeEvent_eq_compl] at h
  exact ⟨m, n, hmn, by linarith⟩

end Percolation
