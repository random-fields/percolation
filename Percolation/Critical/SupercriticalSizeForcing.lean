import Percolation.Critical.BoxSurfaceConnectivity
import Percolation.Critical.BoundaryContacts
import Percolation.Critical.StaticCoalescence
import Percolation.Critical.SupercriticalClusterSize
import Percolation.Critical.SupercriticalSizeLowerBound

/-!
# Surface-order finite-energy forcing for supercritical cluster sizes

This file formalizes the box-surface surgery in Grimmett (8.69)--(8.78).  A deterministic
surface shell and one radial path are resampled.  The shell joins the many infinite-cluster
vertices inside the box into one finite origin cluster, while the number of resampled edges is
of surface order.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

/-- A fixed shortest origin-to-surface walk used to attach the forced surface component to the
origin. -/
noncomputable def supercriticalSurfaceAxisWalk
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    (cubicGraph d).Walk cubicOrigin (cubicAxisVertex d m) :=
  Classical.choose
    (exists_cubicWalk_length_eq_l1Dist_support_between
      d cubicOrigin (cubicAxisVertex d m))

theorem supercriticalSurfaceAxisWalk_length
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    (supercriticalSurfaceAxisWalk d hd m).length = m := by
  rw [show (supercriticalSurfaceAxisWalk d hd m).length =
      cubicL1Dist cubicOrigin (cubicAxisVertex d m) from
    (Classical.choose_spec
      (exists_cubicWalk_length_eq_l1Dist_support_between
        d cubicOrigin (cubicAxisVertex d m))).1]
  exact cubicL1Dist_origin_axisVertex hd

theorem supercriticalSurfaceAxisWalk_support_between
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    ∀ z ∈ (supercriticalSurfaceAxisWalk d hd m).support,
      CubicCoordinateBetween cubicOrigin (cubicAxisVertex d m) z :=
  (Classical.choose_spec
    (exists_cubicWalk_length_eq_l1Dist_support_between
      d cubicOrigin (cubicAxisVertex d m))).2

theorem supercriticalSurfaceAxisWalk_support_subset_box
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    ∀ z ∈ (supercriticalSurfaceAxisWalk d hd m).support,
      z ∈ cubicMetricBox d cubicOrigin m := by
  intro z hz
  rw [mem_cubicMetricBox]
  intro i
  have hbetween := supercriticalSurfaceAxisWalk_support_between d hd m z hz i
  rcases hbetween with hbetween | hbetween <;>
    simp [cubicOrigin, cubicAxisVertex] at hbetween ⊢ <;> omega

theorem supercriticalSurfaceAxisWalk_edges_subset_box
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    walkEdgeFinset (supercriticalSurfaceAxisWalk d hd m) ⊆
      cubicBoxEdges d cubicOrigin m :=
  walkEdgeFinset_subset_cubicBoxEdges_of_support _
    (supercriticalSurfaceAxisWalk_support_subset_box d hd m)

theorem supercriticalSurfaceAxisWalk_edge_card_le
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    (walkEdgeFinset (supercriticalSurfaceAxisWalk d hd m)).card ≤ m := by
  have hpath : (supercriticalSurfaceAxisWalk d hd m).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [cubicGraph_dist_eq_l1Dist,
      supercriticalSurfaceAxisWalk_length d hd m,
      cubicL1Dist_origin_axisVertex hd]
  rw [walkEdgeFinset_card_of_isTrail hpath.isTrail,
    supercriticalSurfaceAxisWalk_length d hd m]

/-- The finite set of coordinates changed by the surface surgery. -/
noncomputable def supercriticalSurfaceForcingEdges
    (d : ℕ) (hd : 0 < d) (m : ℕ) : Finset (CubicEdge d) :=
  cubicIncidentEdges d (cubicBoxSurface d cubicOrigin m) ∪
    walkEdgeFinset (supercriticalSurfaceAxisWalk d hd m)

/-- Inside-box forcing coordinates are opened; all other incident surface coordinates are
closed. -/
noncomputable def supercriticalSurfaceForcingTrace
    (d : ℕ) (hd : 0 < d) (m : ℕ) : Finset (CubicEdge d) :=
  supercriticalSurfaceForcingEdges d hd m ∩ cubicBoxEdges d cubicOrigin m

theorem supercriticalSurfaceForcingTrace_subset
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    supercriticalSurfaceForcingTrace d hd m ⊆
      supercriticalSurfaceForcingEdges d hd m :=
  Finset.inter_subset_left

theorem supercriticalSurfaceAxisWalk_edges_subset_trace
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    walkEdgeFinset (supercriticalSurfaceAxisWalk d hd m) ⊆
      supercriticalSurfaceForcingTrace d hd m := by
  intro e he
  exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ he,
    supercriticalSurfaceAxisWalk_edges_subset_box d hd m he⟩

/-- A convenient surface-order cardinality bound for the surgery support. -/
theorem supercriticalSurfaceForcingEdges_card_le
    {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (supercriticalSurfaceForcingEdges d (by omega) m).card ≤
      (4 * d * d + 1) * (2 * m + 1) ^ (d - 1) := by
  calc
    (supercriticalSurfaceForcingEdges d (by omega) m).card ≤
        (cubicIncidentEdges d (cubicBoxSurface d cubicOrigin m)).card +
          (walkEdgeFinset
            (supercriticalSurfaceAxisWalk d (by omega) m)).card := Finset.card_union_le _ _
    _ ≤ (cubicBoxSurface d cubicOrigin m).card * (2 * d) + m :=
      Nat.add_le_add (cubicIncidentEdges_card_le d _) <|
        supercriticalSurfaceAxisWalk_edge_card_le d (by omega) m
    _ ≤ (2 * d * (2 * m + 1) ^ (d - 1)) * (2 * d) + m := by
      gcongr
      exact cubicBoxSurface_card_le (by omega) cubicOrigin
    _ ≤ (4 * d * d + 1) * (2 * m + 1) ^ (d - 1) := by
      have hbase : m ≤ (2 * m + 1) ^ (d - 1) := by
        have hdm : 1 ≤ d - 1 := by omega
        exact (show m ≤ 2 * m + 1 by omega).trans
          (le_self_pow (by omega : 1 ≤ 2 * m + 1) (Nat.ne_of_gt hdm))
      nlinarith

/-! ### A quantitative finite-energy lemma -/

/-- If forcing one prescribed trace on a finite coordinate set sends every configuration in
`A` into `T`, then the probability of `T` is at least the Bernoulli weight of that trace times
the probability of `A`.  This ratio-free form is valid even when `A` is null. -/
theorem finiteBernoulliWeight_mul_measureReal_le_of_spliceOn
    {d : ℕ} (p : I) (E s : Finset (CubicEdge d)) {A T : Set (EdgeConfiguration d)}
    (hs : s ⊆ E) (hT : MeasurableSet T)
    (hmap : A ⊆ (fun omega ↦ spliceOn E s omega) ⁻¹' T) :
    finiteBernoulliWeight E (p : ℝ) s *
        (bernoulliBondMeasure d p).real A ≤
      (bernoulliBondMeasure d p).real T := by
  classical
  have hdecomp := setBernoulli_real_eq_sum_splice
    (ι := CubicEdge d) p E hT
  change (bernoulliBondMeasure d p).real T = _ at hdecomp
  calc
    finiteBernoulliWeight E (p : ℝ) s *
        (bernoulliBondMeasure d p).real A ≤
        finiteBernoulliWeight E (p : ℝ) s *
          (bernoulliBondMeasure d p).real
            ((fun omega ↦ spliceOn E s omega) ⁻¹' T) := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hmap)
        (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)
    _ ≤ ∑ t ∈ E.powerset, finiteBernoulliWeight E (p : ℝ) t *
          (bernoulliBondMeasure d p).real
            ((fun omega ↦ spliceOn E t omega) ⁻¹' T) := by
      apply Finset.single_le_sum (f := fun t ↦
        finiteBernoulliWeight E (p : ℝ) t *
          (bernoulliBondMeasure d p).real
            ((fun omega ↦ spliceOn E t omega) ⁻¹' T))
      · intro t ht
        exact mul_nonneg
          (finiteBernoulliWeight_nonneg p.2.1 p.2.2 t)
          measureReal_nonneg
      · exact Finset.mem_powerset.mpr hs
    _ = (bernoulliBondMeasure d p).real T := hdecomp.symm

/-- Every prescribed trace has probability at least the smaller one-edge probability raised
to the number of resampled coordinates. -/
theorem min_density_pow_card_le_finiteBernoulliWeight
    {d : ℕ} (p : I) (E s : Finset (CubicEdge d)) (hs : s ⊆ E) :
    (min (p : ℝ) (1 - (p : ℝ))) ^ E.card ≤
      finiteBernoulliWeight E (p : ℝ) s := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hcard : s.card + (E.card - s.card) = E.card :=
    Nat.add_sub_of_le (Finset.card_le_card hs)
  have hmin0 : 0 ≤ min (p : ℝ) (1 - (p : ℝ)) := le_min hp0 hp1
  rw [finiteBernoulliWeight]
  calc
    min (p : ℝ) (1 - (p : ℝ)) ^ E.card =
        min (p : ℝ) (1 - (p : ℝ)) ^
          (s.card + (E.card - s.card)) := by rw [hcard]
    _ = min (p : ℝ) (1 - (p : ℝ)) ^ s.card *
        min (p : ℝ) (1 - (p : ℝ)) ^ (E.card - s.card) := pow_add _ _ _
    _ ≤ (p : ℝ) ^ s.card * (1 - (p : ℝ)) ^ (E.card - s.card) :=
      mul_le_mul
        (pow_le_pow_left₀ hmin0 (min_le_left _ _) _)
        (pow_le_pow_left₀ hmin0 (min_le_right _ _) _)
        (pow_nonneg hmin0 _)
        (pow_nonneg hp0 _)

/-! ### Deterministic effect of the forcing trace -/

/-- An originally open walk contained in the box remains open after the surface forcing. -/
theorem walkIsOpen_spliceOn_surfaceForcing_of_edges_subset_box
    {d m : ℕ} (hd : 0 < d) {omega : EdgeConfiguration d}
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hopen : walkIsOpen omega w)
    (hbox : walkEdgeFinset w ⊆ cubicBoxEdges d cubicOrigin m) :
    walkIsOpen
      (spliceOn (supercriticalSurfaceForcingEdges d hd m)
        (supercriticalSurfaceForcingTrace d hd m) omega) w := by
  intro e he
  let ce : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have hceWalk : ce ∈ walkEdgeFinset w := (mem_walkEdgeFinset_iff w ce).mpr he
  have hceBox : ce ∈ cubicBoxEdges d cubicOrigin m := hbox hceWalk
  by_cases hceE : ce ∈ supercriticalSurfaceForcingEdges d hd m
  · unfold edgeOpen
    simpa only [ce, mem_spliceOn] using
      (Or.inl (Finset.mem_inter.mpr ⟨hceE, hceBox⟩) :
        ce ∈ supercriticalSurfaceForcingTrace d hd m ∨
          (ce ∈ omega ∧ ce ∉ supercriticalSurfaceForcingEdges d hd m))
  · unfold edgeOpen
    simpa only [ce, mem_spliceOn] using
      (Or.inr ⟨hopen e he, hceE⟩ :
        ce ∈ supercriticalSurfaceForcingTrace d hd m ∨
          (ce ∈ omega ∧ ce ∉ supercriticalSurfaceForcingEdges d hd m))

/-- A walk all of whose edges belong to the open part of the forcing trace is open after the
splice, independently of the original configuration. -/
theorem walkIsOpen_spliceOn_surfaceForcing_of_edges_subset_trace
    {d m : ℕ} (hd : 0 < d) {omega : EdgeConfiguration d}
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (htrace : walkEdgeFinset w ⊆ supercriticalSurfaceForcingTrace d hd m) :
    walkIsOpen
      (spliceOn (supercriticalSurfaceForcingEdges d hd m)
        (supercriticalSurfaceForcingTrace d hd m) omega) w := by
  intro e he
  let ce : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have hce : ce ∈ supercriticalSurfaceForcingTrace d hd m :=
    htrace ((mem_walkEdgeFinset_iff w ce).mpr he)
  unfold edgeOpen
  simpa only [ce, mem_spliceOn] using
    (Or.inl hce : ce ∈ supercriticalSurfaceForcingTrace d hd m ∨
      (ce ∈ omega ∧ ce ∉ supercriticalSurfaceForcingEdges d hd m))

/-- The forcing trace opens a connection from every surface vertex to the fixed axis vertex. -/
theorem exists_open_surfaceWalk_after_supercriticalSurfaceForcing
    {d m : ℕ} (hd : 2 ≤ d) (omega : EdgeConfiguration d)
    {y : Cubic d} (hy : y ∈ cubicBoxSurface d cubicOrigin m) :
    ∃ w : (cubicGraph d).Walk y (cubicAxisVertex d m),
      walkIsOpen
        (spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
          (supercriticalSurfaceForcingTrace d (by omega) m) omega) w := by
  obtain ⟨w, hwSurface⟩ := exists_cubicWalk_support_in_boxSurface hd hy
    (cubicAxisVertex_mem_boxSurface (by omega))
  have hwIncident : walkEdgeFinset w ⊆
      cubicIncidentEdges d (cubicBoxSurface d cubicOrigin m) := by
    rintro ⟨e, heGraph⟩ heWalk
    rw [mem_walkEdgeFinset_iff] at heWalk
    induction e using Sym2.ind with
    | _ a b =>
        have haSupport : a ∈ w.support := w.fst_mem_support_of_mem_edges heWalk
        exact mem_cubicIncidentEdges_of_endpoint (hwSurface a haSupport) (by simp)
  refine ⟨w, walkIsOpen_spliceOn_surfaceForcing_of_edges_subset_trace
    (by omega) w ?_⟩
  intro e he
  exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hwIncident he),
    walkEdgeFinset_subset_cubicBoxEdges_of_support w
      (fun z hz ↦ (mem_cubicBoxSurface.mp (hwSurface z hz)) ▸
        mem_cubicMetricBox_iff_lInfDist_le.mpr le_rfl) he⟩

/-- The fixed radial walk is opened by the forcing trace. -/
theorem supercriticalSurfaceAxisWalk_open_after_forcing
    {d m : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d) :
    walkIsOpen
      (spliceOn (supercriticalSurfaceForcingEdges d hd m)
        (supercriticalSurfaceForcingTrace d hd m) omega)
      (supercriticalSurfaceAxisWalk d hd m) :=
  walkIsOpen_spliceOn_surfaceForcing_of_edges_subset_trace hd _
    (supercriticalSurfaceAxisWalk_edges_subset_trace d hd m)

/-- Every infinite-cluster vertex in the box is joined to the origin after the surface
surgery.  The original first-hit path reaches the forced shell, and the shell plus radial path
then reaches the origin. -/
theorem mem_cubicOpenCluster_after_surfaceForcing_of_infinite
    {d m : ℕ} (hd : 2 ≤ d) {omega : EdgeConfiguration d} {x : Cubic d}
    (hxBox : x ∈ cubicMetricBox d cubicOrigin m)
    (hxInf : hasInfiniteOpenClusterFrom d omega x) :
    x ∈ cubicOpenCluster d
      (spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
        (supercriticalSurfaceForcingTrace d (by omega) m) omega) := by
  have hxSurface :=
    hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent hxBox hxInf
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion] at hxSurface
  obtain ⟨y, hySurface, q, hqOpen, hqBox⟩ := hxSurface
  obtain ⟨r, hrOpen⟩ :=
    exists_open_surfaceWalk_after_supercriticalSurfaceForcing hd omega hySurface
  let eta := spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
    (supercriticalSurfaceForcingTrace d (by omega) m) omega
  have hqOpenEta : walkIsOpen eta q :=
    walkIsOpen_spliceOn_surfaceForcing_of_edges_subset_box (by omega) q hqOpen hqBox
  have haxisOpen : walkIsOpen eta (supercriticalSurfaceAxisWalk d (by omega) m) :=
    supercriticalSurfaceAxisWalk_open_after_forcing (by omega) omega
  change ∃ w : (cubicGraph d).Walk cubicOrigin x, walkIsOpen eta w
  exact ⟨(supercriticalSurfaceAxisWalk d (by omega) m).append
      (r.reverse.append q.reverse),
    walkIsOpen_append haxisOpen
      (walkIsOpen_append (walkIsOpen_reverse hrOpen) (walkIsOpen_reverse hqOpenEta))⟩

/-- No open walk in the forced configuration can cross from the box to its complement: every
edge incident to the surface but not internal to the box was closed by the splice. -/
theorem walk_support_subset_box_after_supercriticalSurfaceForcing
    {d m : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d)
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hopen : walkIsOpen
      (spliceOn (supercriticalSurfaceForcingEdges d hd m)
        (supercriticalSurfaceForcingTrace d hd m) omega) w)
    (hu : u ∈ cubicMetricBox d cubicOrigin m) :
    ∀ z ∈ w.support, z ∈ cubicMetricBox d cubicOrigin m := by
  let eta := spliceOn (supercriticalSurfaceForcingEdges d hd m)
    (supercriticalSurfaceForcingTrace d hd m) omega
  let P : {a b : Cubic d} → (cubicGraph d).Walk a b → Prop :=
    fun {a _} q ↦ walkIsOpen eta q →
      a ∈ cubicMetricBox d cubicOrigin m →
        ∀ z ∈ q.support, z ∈ cubicMetricBox d cubicOrigin m
  have hP : ∀ {a b : Cubic d} (q : (cubicGraph d).Walk a b), P q := by
    intro a b q
    apply @SimpleGraph.Walk.rec (Cubic d) (cubicGraph d)
      (fun a b q ↦ P q) _ _ a b q
    · intro a
      dsimp [P]
      intro _ ha z hz
      have hza : z = a := by simpa using hz
      exact hza ▸ ha
    · intro a b c hab q ih
      dsimp [P] at ih ⊢
      intro hqConsOpen ha
      let ce : CubicEdge d :=
        ⟨s(a, b), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hab⟩
      have hceOpen : ce ∈ eta := by
        apply hqConsOpen
        simp [SimpleGraph.Walk.edges_cons]
      have hb : b ∈ cubicMetricBox d cubicOrigin m := by
        by_contra hbNot
        have haSurface : a ∈ cubicBoxSurface d cubicOrigin m :=
          mem_cubicBoxSurface_of_adj_mem_notMem ha hab hbNot
        have hceE : ce ∈ supercriticalSurfaceForcingEdges d hd m := by
          apply Finset.mem_union_left
          exact mem_cubicIncidentEdges_of_endpoint haSurface (by simp [ce])
        have hceNotBox : ce ∉ cubicBoxEdges d cubicOrigin m := by
          intro hceBox
          exact hbNot (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
            hceBox (by simp [ce]))
        have hceNotTrace : ce ∉ supercriticalSurfaceForcingTrace d hd m := by
          intro hceTrace
          exact hceNotBox (Finset.mem_inter.mp hceTrace).2
        exact hceNotTrace ((mem_spliceOn_of_mem hceE).mp hceOpen)
      have hqOpen : walkIsOpen eta q := by
        intro e he
        exact hqConsOpen e (by simp [SimpleGraph.Walk.edges_cons, he])
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      exact hz.elim (fun h ↦ h ▸ ha) (ih hqOpen hb z)
  exact hP w hopen hu

/-- The origin cluster produced by the surface forcing is contained in the finite box. -/
theorem cubicOpenCluster_after_surfaceForcing_subset_box
    {d m : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d) :
    cubicOpenCluster d
        (spliceOn (supercriticalSurfaceForcingEdges d hd m)
          (supercriticalSurfaceForcingTrace d hd m) omega) ⊆
      cubicMetricBox d cubicOrigin m := by
  intro x hx
  obtain ⟨w, hwOpen⟩ := hx
  exact walk_support_subset_box_after_supercriticalSurfaceForcing hd omega w hwOpen
    (mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)) x (by simp)

/-- In particular the forced origin cluster is finite. -/
theorem cubicOpenCluster_after_surfaceForcing_finite
    {d m : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d) :
    (cubicOpenCluster d
      (spliceOn (supercriticalSurfaceForcingEdges d hd m)
        (supercriticalSurfaceForcingTrace d hd m) omega)).Finite :=
  (cubicMetricBox d cubicOrigin m).finite_toSet.subset
    (cubicOpenCluster_after_surfaceForcing_subset_box hd omega)

/-- Every infinite-cluster vertex in the box belongs to the finite origin cluster created by
the surgery. -/
theorem infiniteClusterVerticesIn_subset_cluster_after_surfaceForcing
    {d m : ℕ} (hd : 2 ≤ d) (omega : EdgeConfiguration d) :
    (infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin m) omega :
        Set (Cubic d)) ⊆
      cubicOpenCluster d
        (spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
          (supercriticalSurfaceForcingTrace d (by omega) m) omega) := by
  intro x hx
  have hxFin : x ∈ infiniteClusterVerticesIn d
      (cubicMetricBox d cubicOrigin m) omega := hx
  have hxData := mem_infiniteClusterVerticesIn.mp hxFin
  exact mem_cubicOpenCluster_after_surfaceForcing_of_infinite hd hxData.1 hxData.2

/-- The size of the forced finite cluster lies between the number of original infinite-cluster
vertices in the box and the box volume. -/
theorem surfaceForcing_cluster_ncard_bounds
    {d m : ℕ} (hd : 2 ≤ d) (omega : EdgeConfiguration d) :
    (infiniteClusterVerticesIn d (cubicMetricBox d cubicOrigin m) omega).card ≤
        (cubicOpenCluster d
          (spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
            (supercriticalSurfaceForcingTrace d (by omega) m) omega)).ncard ∧
      (cubicOpenCluster d
          (spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
            (supercriticalSurfaceForcingTrace d (by omega) m) omega)).ncard ≤
        (2 * m + 1) ^ d := by
  let eta := spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
    (supercriticalSurfaceForcingTrace d (by omega) m) omega
  have hfinite : (cubicOpenCluster d eta).Finite :=
    cubicOpenCluster_after_surfaceForcing_finite (by omega) omega
  have hsubset : (infiniteClusterVerticesIn d
      (cubicMetricBox d cubicOrigin m) omega : Set (Cubic d)) ⊆
      cubicOpenCluster d eta :=
    infiniteClusterVerticesIn_subset_cluster_after_surfaceForcing hd omega
  have hbox : cubicOpenCluster d eta ⊆
      (cubicMetricBox d cubicOrigin m : Set (Cubic d)) :=
    cubicOpenCluster_after_surfaceForcing_subset_box (by omega) omega
  constructor
  · simpa using Set.ncard_le_ncard hsubset hfinite
  · simpa [cubicMetricBox_card] using
      Set.ncard_le_ncard hbox (cubicMetricBox d cubicOrigin m).finite_toSet

/-! ### The surface-order cluster-size window -/

/-- Candidate sizes produced by the surgery at box radius `m`. -/
noncomputable def supercriticalSurfaceSizeWindowIndices
    (d : ℕ) (p : I) (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ((2 * m + 1) ^ d)).filter fun n ↦
    theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤ (n : ℝ)

/-- The finite union of exact-size events in the surgery window. -/
def supercriticalSurfaceSizeWindowEvent
    (d : ℕ) (p : I) (m : ℕ) : Set (EdgeConfiguration d) :=
  ⋃ n ∈ supercriticalSurfaceSizeWindowIndices d p m,
    finiteClusterSizeEvent d n

theorem measurableSet_supercriticalSurfaceSizeWindowEvent
    (d : ℕ) (p : I) (m : ℕ) :
    MeasurableSet (supercriticalSurfaceSizeWindowEvent d p m) := by
  apply (supercriticalSurfaceSizeWindowIndices d p m).measurableSet_biUnion
  intro n hn
  exact measurableSet_finiteClusterSizeEvent d n

/-- A configuration with at least half the expected number of infinite-cluster vertices is
sent by the surface splice into the exact-size window. -/
theorem denseInfiniteVertices_spliceOn_mem_surfaceSizeWindow
    {d m : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    {omega : EdgeConfiguration d}
    (hdense : theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤
      ((infiniteClusterVerticesIn d
        (cubicMetricBox d cubicOrigin m) omega).card : ℝ)) :
    spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
        (supercriticalSurfaceForcingTrace d (by omega) m) omega ∈
      supercriticalSurfaceSizeWindowEvent d p m := by
  let eta := spliceOn (supercriticalSurfaceForcingEdges d (by omega) m)
    (supercriticalSurfaceForcingTrace d (by omega) m) omega
  let n := (cubicOpenCluster d eta).ncard
  have hbounds := surfaceForcing_cluster_ncard_bounds (m := m) hd omega
  have hlower : theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤ (n : ℝ) := by
    exact hdense.trans (by exact_mod_cast hbounds.1)
  have hvolumePos : 0 < (((2 * m + 1) ^ d : ℕ) : ℝ) := by positivity
  have hnPos : 0 < n := by
    have : 0 < (n : ℝ) := (div_pos (mul_pos htheta hvolumePos) (by norm_num)).trans_le hlower
    exact_mod_cast this
  have hnWindow : n ∈ supercriticalSurfaceSizeWindowIndices d p m := by
    rw [supercriticalSurfaceSizeWindowIndices, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hnPos, hbounds.2⟩, hlower⟩
  have hfinite : (cubicOpenCluster d eta).Finite :=
    cubicOpenCluster_after_surfaceForcing_finite (by omega) omega
  have hsize : eta ∈ finiteClusterSizeEvent d n := by
    change clusterSizeENNReal d eta = (n : ℝ≥0∞)
    exact clusterSizeENNReal_eq_ncard_of_finite hfinite
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hnWindow, hsize⟩⟩

/-- Quantitative finite-energy lower bound for the total mass of the size window.  This is the
formal version of Grimmett (8.77). -/
theorem surfaceSizeWindow_probability_lower_bound
    {d m : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) :
    finiteBernoulliWeight
        (supercriticalSurfaceForcingEdges d (by omega) m) (p : ℝ)
        (supercriticalSurfaceForcingTrace d (by omega) m) * (theta d p / 2) ≤
      (bernoulliBondMeasure d p).real
        (supercriticalSurfaceSizeWindowEvent d p m) := by
  let A : Set (EdgeConfiguration d) :=
    {omega | theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤
      ((infiniteClusterVerticesIn d
        (cubicMetricBox d cubicOrigin m) omega).card : ℝ)}
  have hmap : A ⊆
      (fun omega ↦ spliceOn
        (supercriticalSurfaceForcingEdges d (by omega) m)
        (supercriticalSurfaceForcingTrace d (by omega) m) omega) ⁻¹'
          supercriticalSurfaceSizeWindowEvent d p m := by
    intro omega homega
    exact denseInfiniteVertices_spliceOn_mem_surfaceSizeWindow hd p htheta homega
  have henergy := finiteBernoulliWeight_mul_measureReal_le_of_spliceOn p
    (supercriticalSurfaceForcingEdges d (by omega) m)
    (supercriticalSurfaceForcingTrace d (by omega) m)
    (A := A) (T := supercriticalSurfaceSizeWindowEvent d p m)
    (supercriticalSurfaceForcingTrace_subset d (by omega) m)
    (measurableSet_supercriticalSurfaceSizeWindowEvent d p m) hmap
  have hdense : theta d p / 2 ≤ (bernoulliBondMeasure d p).real A := by
    simpa [A, cubicMetricBox_card] using
      infiniteClusterVertexCount_ge_half_probability_ge d p m
  exact (mul_le_mul_of_nonneg_left hdense
    (finiteBernoulliWeight_nonneg p.2.1 p.2.2 _)).trans henergy

theorem surfaceSizeWindow_probability_eq_sum
    (d : ℕ) (p : I) (m : ℕ) :
    (bernoulliBondMeasure d p).real
        (supercriticalSurfaceSizeWindowEvent d p m) =
      ∑ n ∈ supercriticalSurfaceSizeWindowIndices d p m,
        finiteClusterSizeProbability d p n := by
  rw [supercriticalSurfaceSizeWindowEvent]
  exact measureReal_biUnion_finset
    (fun n hn k hk hnk ↦ pairwiseDisjoint_finiteClusterSizeEvent d hnk)
    (fun n hn ↦ measurableSet_finiteClusterSizeEvent d n)

/-- The forcing trace has a uniform surface-order weight lower bound. -/
theorem surfaceForcing_weight_lower_bound
    {d m : ℕ} (hd : 2 ≤ d) (p : I) :
    (min (p : ℝ) (1 - (p : ℝ))) ^
        ((4 * d * d + 1) * (2 * m + 1) ^ (d - 1)) ≤
      finiteBernoulliWeight
        (supercriticalSurfaceForcingEdges d (by omega) m) (p : ℝ)
        (supercriticalSurfaceForcingTrace d (by omega) m) := by
  let ell : ℝ := min (p : ℝ) (1 - (p : ℝ))
  have hell0 : 0 ≤ ell := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hell1 : ell ≤ 1 := (min_le_left _ _).trans p.2.2
  calc
    ell ^ ((4 * d * d + 1) * (2 * m + 1) ^ (d - 1)) ≤
        ell ^ (supercriticalSurfaceForcingEdges d (by omega) m).card :=
      pow_le_pow_of_le_one hell0 hell1 (supercriticalSurfaceForcingEdges_card_le hd m)
    _ ≤ finiteBernoulliWeight
        (supercriticalSurfaceForcingEdges d (by omega) m) (p : ℝ)
        (supercriticalSurfaceForcingTrace d (by omega) m) :=
      min_density_pow_card_le_finiteBernoulliWeight p _ _
        (supercriticalSurfaceForcingTrace_subset d (by omega) m)

/-- Grimmett (8.78): at every box scale, some finite cluster size in the macroscopic window
has probability at least a surface-order finite-energy factor divided by the box volume. -/
theorem exists_finiteClusterSizeProbability_ge_surface_forcing
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (m : ℕ) :
    ∃ n : ℕ,
      theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤ (n : ℝ) ∧
      n ≤ (2 * m + 1) ^ d ∧
      (min (p : ℝ) (1 - (p : ℝ))) ^
          ((4 * d * d + 1) * (2 * m + 1) ^ (d - 1)) * (theta d p / 2) /
            (((2 * m + 1) ^ d : ℕ) : ℝ) ≤
        finiteClusterSizeProbability d p n := by
  let s := supercriticalSurfaceSizeWindowIndices d p m
  let ell : ℝ := min (p : ℝ) (1 - (p : ℝ))
  let V : ℕ := (2 * m + 1) ^ d
  let L : ℝ := ell ^ ((4 * d * d + 1) * (2 * m + 1) ^ (d - 1)) *
    (theta d p / 2)
  have hell : 0 < ell := lt_min hp0 (sub_pos.mpr hp1)
  have hLpos : 0 < L := mul_pos (pow_pos hell _) (div_pos htheta (by norm_num))
  have hLsum : L ≤ ∑ n ∈ s, finiteClusterSizeProbability d p n := by
    have hweight := surfaceForcing_weight_lower_bound hd p (m := m)
    have hwindow := surfaceSizeWindow_probability_lower_bound hd p htheta (m := m)
    have hmul : L ≤
        finiteBernoulliWeight
          (supercriticalSurfaceForcingEdges d (by omega) m) (p : ℝ)
          (supercriticalSurfaceForcingTrace d (by omega) m) * (theta d p / 2) := by
      exact mul_le_mul_of_nonneg_right hweight (div_nonneg (le_of_lt htheta) (by norm_num))
    rw [surfaceSizeWindow_probability_eq_sum] at hwindow
    exact hmul.trans hwindow
  have hsNonempty : s.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty] at hLsum
    exact (not_le_of_gt hLpos) hLsum
  obtain ⟨n, hnS, hnMax⟩ := Finset.exists_max_image s
    (finiteClusterSizeProbability d p) hsNonempty
  have hnWindow :
      theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤ (n : ℝ) ∧
        n ≤ (2 * m + 1) ^ d := by
    have hn := Finset.mem_filter.mp hnS
    exact ⟨hn.2, (Finset.mem_Icc.mp hn.1).2⟩
  have hsCard : s.card ≤ V := by
    have hsub : s ⊆ Finset.Icc 1 V := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    calc
      s.card ≤ (Finset.Icc 1 V).card := Finset.card_le_card hsub
      _ = V := by
        rw [Nat.card_Icc]
        have hV : 1 ≤ V := by
          dsimp [V]
          exact one_le_pow₀ (by omega)
        omega
  have hsumMax : (∑ k ∈ s, finiteClusterSizeProbability d p k) ≤
      (s.card : ℝ) * finiteClusterSizeProbability d p n := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s
      (finiteClusterSizeProbability d p)
      (finiteClusterSizeProbability d p n) hnMax
  have hVpos : (0 : ℝ) < V := by positivity
  have hLV : L / (V : ℝ) ≤ finiteClusterSizeProbability d p n := by
    apply (div_le_iff₀ hVpos).2
    calc
      L ≤ ∑ k ∈ s, finiteClusterSizeProbability d p k := hLsum
      _ ≤ (s.card : ℝ) * finiteClusterSizeProbability d p n := hsumMax
      _ ≤ (V : ℝ) * finiteClusterSizeProbability d p n := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsCard)
          (finiteClusterSizeProbability_nonneg d p n)
      _ = finiteClusterSizeProbability d p n * (V : ℝ) := by ring
  exact ⟨n, hnWindow.1, hnWindow.2, by simpa [L, ell, V] using hLV⟩

/-! ### A canonical selected size at each box scale -/

/-- One deterministic choice of the size furnished by (8.78). -/
noncomputable def supercriticalSelectedClusterSize
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (m : ℕ) : ℕ :=
  Classical.choose
    (exists_finiteClusterSizeProbability_ge_surface_forcing
      hd p hp0 hp1 htheta m)

theorem supercriticalSelectedClusterSize_lower
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (m : ℕ) :
    theta d p * (((2 * m + 1) ^ d : ℕ) : ℝ) / 2 ≤
      (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m : ℝ) :=
  (Classical.choose_spec
    (exists_finiteClusterSizeProbability_ge_surface_forcing
      hd p hp0 hp1 htheta m)).1

theorem supercriticalSelectedClusterSize_upper
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (m : ℕ) :
    supercriticalSelectedClusterSize hd p hp0 hp1 htheta m ≤ (2 * m + 1) ^ d :=
  (Classical.choose_spec
    (exists_finiteClusterSizeProbability_ge_surface_forcing
      hd p hp0 hp1 htheta m)).2.1

theorem supercriticalSelectedClusterSize_probability_lower
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (m : ℕ) :
    (min (p : ℝ) (1 - (p : ℝ))) ^
          ((4 * d * d + 1) * (2 * m + 1) ^ (d - 1)) * (theta d p / 2) /
            (((2 * m + 1) ^ d : ℕ) : ℝ) ≤
      finiteClusterSizeProbability d p
        (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m) :=
  (Classical.choose_spec
    (exists_finiteClusterSizeProbability_ge_surface_forcing
      hd p hp0 hp1 htheta m)).2.2

/-- The surface power of a cubic box volume is exactly its coordinate surface power. -/
theorem cubicBoxVolume_rpow_supercriticalClusterSizeExponent
    {d m : ℕ} (hd : 0 < d) :
    ((((2 * m + 1) ^ d : ℕ) : ℝ) ^ supercriticalClusterSizeExponent d) =
      (((2 * m + 1) ^ (d - 1) : ℕ) : ℝ) := by
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  let b : ℝ := 2 * (m : ℝ) + 1
  have hb : 0 ≤ b := by positivity
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hexp : (d : ℝ) * (((d : ℝ) - 1) * (d : ℝ)⁻¹) = (d : ℝ) - 1 := by
    calc
      (d : ℝ) * (((d : ℝ) - 1) * (d : ℝ)⁻¹) =
          ((d : ℝ) - 1) * ((d : ℝ) * (d : ℝ)⁻¹) := by ring
      _ = (d : ℝ) - 1 := by rw [mul_inv_cancel₀ hdR, mul_one]
  have h : (b ^ d) ^ supercriticalClusterSizeExponent d = b ^ (d - 1) := by
    rw [← Real.rpow_natCast b (d - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    rw [supercriticalClusterSizeExponent, div_eq_mul_inv]
    rw [← Real.rpow_natCast b d]
    rw [← Real.rpow_mul hb]
    rw [hexp]
  simpa [b] using h

/-- Elementary analytic estimate turning a surface-order finite-energy expression into the
`k exp (-η k^α)` form used in Lemma 8.72. -/
private theorem mul_exp_neg_rpow_le_of_surface_energy
    {α q ell V k P : ℝ} {N C : ℕ}
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (hV : 1 ≤ V)
    (hk0 : q * V ≤ k) (hkV : k ≤ V)
    (hN : (N : ℝ) = (C : ℝ) * V ^ α)
    (hprob : ell ^ N * q / V ≤ P) :
    let eta := (-(C : ℝ) * Real.log ell - Real.log q + 2 / α) / q ^ α
    k * Real.exp (-eta * k ^ α) ≤ P := by
  let eta := (-(C : ℝ) * Real.log ell - Real.log q + 2 / α) / q ^ α
  have hα0 : 0 ≤ α := hα.le
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hqlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
  have helllog : Real.log ell ≤ 0 := Real.log_nonpos hell.le hell1
  have hS1 : 1 ≤ V ^ α := Real.one_le_rpow hV hα0
  have hkpow : q ^ α * V ^ α ≤ k ^ α := by
    rw [← Real.mul_rpow hq.le hV0]
    exact Real.rpow_le_rpow (mul_nonneg hq.le hV0) hk0 hα0
  have hcoeff0 : 0 ≤ -(C : ℝ) * Real.log ell - Real.log q + 2 / α := by
    have h1 : 0 ≤ -(C : ℝ) * Real.log ell :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg C)) helllog
    have h2 : 0 ≤ -Real.log q := neg_nonneg.mpr hqlog
    have h3 : 0 ≤ 2 / α := div_nonneg (by norm_num) hα.le
    linarith
  have heta0 : 0 ≤ eta := div_nonneg hcoeff0 (Real.rpow_nonneg hq.le _)
  have hetaMain :
      -(N : ℝ) * Real.log ell - Real.log q + 2 * Real.log V ≤
        eta * k ^ α := by
    have hlogV := Real.log_le_rpow_div hV0 hα
    have hqterm : -Real.log q ≤ (-Real.log q) * V ^ α := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hqlog) (sub_nonneg.mpr hS1)]
    have hleft : -(N : ℝ) * Real.log ell - Real.log q + 2 * Real.log V ≤
        (-(C : ℝ) * Real.log ell - Real.log q + 2 / α) * V ^ α := by
      rw [hN]
      calc
        -((C : ℝ) * V ^ α) * Real.log ell - Real.log q + 2 * Real.log V =
            (-(C : ℝ) * Real.log ell) * V ^ α + (-Real.log q) +
              2 * Real.log V := by ring
        _ ≤ (-(C : ℝ) * Real.log ell) * V ^ α +
              ((-Real.log q) * V ^ α) + 2 * (V ^ α / α) := by
          gcongr
        _ = (-(C : ℝ) * Real.log ell - Real.log q + 2 / α) * V ^ α := by ring
    calc
      -(N : ℝ) * Real.log ell - Real.log q + 2 * Real.log V ≤
          (-(C : ℝ) * Real.log ell - Real.log q + 2 / α) * V ^ α := hleft
      _ = eta * (q ^ α * V ^ α) := by
        dsimp [eta]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hq α)]
      _ ≤ eta * k ^ α := mul_le_mul_of_nonneg_left hkpow heta0
  have hrhs : ell ^ N * q / V =
      Real.exp ((N : ℝ) * Real.log ell + Real.log q - Real.log V) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_log hell,
      Real.exp_log hq, Real.exp_log (zero_lt_one.trans_le hV)]
  have hexp : V * Real.exp (-eta * k ^ α) ≤ ell ^ N * q / V := by
    rw [hrhs, ← Real.exp_log (zero_lt_one.trans_le hV), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_exp]
    nlinarith
  exact ((mul_le_mul_of_nonneg_right hkV (Real.exp_nonneg _)).trans hexp).trans hprob

/-- Equation (8.79), uniformly over the canonical sizes selected from all box scales. -/
theorem exists_eta_supercriticalSelectedClusterSize_probability_lower
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    ∃ eta : ℝ, 0 ≤ eta ∧ ∀ m : ℕ,
      (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m : ℝ) *
          Real.exp (-eta *
            (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m : ℝ) ^
              supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p
          (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m) := by
  let alpha := supercriticalClusterSizeExponent d
  let q := theta d p / 2
  let ell := min (p : ℝ) (1 - (p : ℝ))
  let C : ℕ := 4 * d * d + 1
  let eta := (-(C : ℝ) * Real.log ell - Real.log q + 2 / alpha) / q ^ alpha
  have halpha : 0 < alpha := by
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (half_le_supercriticalClusterSizeExponent hd)
  have hq : 0 < q := div_pos htheta (by norm_num)
  have hthetaOne : theta d p ≤ 1 := by
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hell : 0 < ell := lt_min hp0 (sub_pos.mpr hp1)
  have hell1 : ell ≤ 1 := (min_le_left _ _).trans p.2.2
  have hcoeff0 : 0 ≤ -(C : ℝ) * Real.log ell - Real.log q + 2 / alpha := by
    have helllog : Real.log ell ≤ 0 := Real.log_nonpos hell.le hell1
    have hqlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
    have h1 : 0 ≤ -(C : ℝ) * Real.log ell :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg C)) helllog
    have h2 : 0 ≤ -Real.log q := neg_nonneg.mpr hqlog
    have h3 : 0 ≤ 2 / alpha := div_nonneg (by norm_num) halpha.le
    linarith
  refine ⟨eta, div_nonneg hcoeff0 (Real.rpow_nonneg hq.le _), ?_⟩
  intro m
  let V : ℝ := (((2 * m + 1) ^ d : ℕ) : ℝ)
  let k : ℝ :=
    (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m : ℝ)
  have hV : 1 ≤ V := by
    dsimp [V]
    have hVnat : 1 ≤ (2 * m + 1) ^ d := one_le_pow₀ (by omega)
    exact_mod_cast hVnat
  have hk0 : q * V ≤ k := by
    dsimp [q, V, k]
    convert supercriticalSelectedClusterSize_lower hd p hp0 hp1 htheta m using 1 <;> ring
  have hkV : k ≤ V := by
    dsimp [k, V]
    exact_mod_cast supercriticalSelectedClusterSize_upper hd p hp0 hp1 htheta m
  have hN : ((C * (2 * m + 1) ^ (d - 1) : ℕ) : ℝ) =
      (C : ℝ) * V ^ alpha := by
    simp only [Nat.cast_mul]
    dsimp [V, alpha]
    rw [cubicBoxVolume_rpow_supercriticalClusterSizeExponent (by omega)]
  have hprob : ell ^ (C * (2 * m + 1) ^ (d - 1)) * q / V ≤
      finiteClusterSizeProbability d p
        (supercriticalSelectedClusterSize hd p hp0 hp1 htheta m) := by
    simpa [ell, C, q, V] using
      supercriticalSelectedClusterSize_probability_lower hd p hp0 hp1 htheta m
  have hmain := mul_exp_neg_rpow_le_of_surface_energy
    halpha hq hq1 hell hell1 hV hk0 hkV hN hprob
  simpa [eta, alpha, q, ell, C, V, k] using hmain

/-! ### Scale selection for Lemma 8.72 -/

private theorem exists_nat_scaled_cubicBoxVolume
    {d : ℕ} (hd : 1 ≤ d) {q A : ℝ} (hq : 0 < q) :
    ∃ m : ℕ, 1 ≤ m ∧ A ≤ q * (((2 * m + 1) ^ d : ℕ) : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (max 1 (A / q))
  have hm1R : (1 : ℝ) ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by exact_mod_cast hm1R
  have hAdiv : A / q ≤ (m : ℝ) := (le_max_right _ _).trans hm
  have hAm : A ≤ q * (m : ℝ) := by
    apply (div_le_iff₀ hq).mp at hAdiv
    simpa [mul_comm] using hAdiv
  have hmV : m ≤ (2 * m + 1) ^ d := by
    exact (show m ≤ 2 * m + 1 by omega).trans
      (le_self_pow (by omega : 1 ≤ 2 * m + 1) (by omega : d ≠ 0))
  exact ⟨m, hm1, hAm.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hmV) hq.le)⟩

/-- First box index whose selected-size lower window has reached size two. -/
noncomputable def supercriticalInitialBoxIndex
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) : ℕ :=
  Nat.find (exists_nat_scaled_cubicBoxVolume (d := d) (by omega)
    (q := theta d p / 2) (A := 2) (div_pos htheta (by norm_num)))

theorem supercriticalInitialBoxIndex_spec
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) :
    1 ≤ supercriticalInitialBoxIndex hd p htheta ∧
      (2 : ℝ) ≤ theta d p / 2 *
        ((((2 * supercriticalInitialBoxIndex hd p htheta + 1) ^ d : ℕ) : ℝ)) :=
  Nat.find_spec (exists_nat_scaled_cubicBoxVolume (d := d) (by omega)
    (q := theta d p / 2) (A := 2) (div_pos htheta (by norm_num)))

/-- The next source-box index in Grimmett's subsequence construction. -/
noncomputable def supercriticalNextBoxIndex
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    (j : ℕ) : ℕ :=
  Nat.find (exists_nat_scaled_cubicBoxVolume (d := d) (by omega)
    (q := theta d p / 4)
    (A := (((2 * j + 1) ^ d : ℕ) : ℝ))
    (div_pos htheta (by norm_num)))

theorem supercriticalNextBoxIndex_spec
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    (j : ℕ) :
    1 ≤ supercriticalNextBoxIndex hd p htheta j ∧
      ((((2 * j + 1) ^ d : ℕ) : ℝ)) ≤ theta d p / 4 *
        ((((2 * supercriticalNextBoxIndex hd p htheta j + 1) ^ d : ℕ) : ℝ)) :=
  Nat.find_spec (exists_nat_scaled_cubicBoxVolume (d := d) (by omega)
    (q := theta d p / 4)
    (A := (((2 * j + 1) ^ d : ℕ) : ℝ))
    (div_pos htheta (by norm_num)))

theorem supercriticalNextBoxIndex_gt
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    (j : ℕ) :
    j < supercriticalNextBoxIndex hd p htheta j := by
  let l := supercriticalNextBoxIndex hd p htheta j
  have hspec := (supercriticalNextBoxIndex_spec hd p htheta j).2
  have hthetaOne : theta d p ≤ 1 :=
    (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hfactor : theta d p / 4 < 1 := by linarith
  by_contra hnot
  have hlj : l ≤ j := Nat.le_of_not_gt hnot
  have hvol : (2 * l + 1) ^ d ≤ (2 * j + 1) ^ d := by gcongr
  have hvolPos : (0 : ℝ) < (((2 * j + 1) ^ d : ℕ) : ℝ) := by positivity
  have hspec' : (((2 * j + 1) ^ d : ℕ) : ℝ) ≤
      theta d p / 4 * (((2 * j + 1) ^ d : ℕ) : ℝ) := by
    exact hspec.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hvol)
      (div_nonneg (le_of_lt htheta) (by norm_num)))
  nlinarith

/-- Minimality of the next index gives the failed inequality at the preceding box. -/
theorem supercriticalNextBoxIndex_pred_failure
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    {j : ℕ} (hj : 1 ≤ j) :
    theta d p / 4 *
        ((((2 * (supercriticalNextBoxIndex hd p htheta j - 1) + 1) ^ d : ℕ) : ℝ)) <
      (((2 * j + 1) ^ d : ℕ) : ℝ) := by
  let l := supercriticalNextBoxIndex hd p htheta j
  have hl : 0 < l := (supercriticalNextBoxIndex_spec hd p htheta j).1
  have hlj : j < l := supercriticalNextBoxIndex_gt hd p htheta j
  have hl2 : 2 ≤ l := by omega
  apply lt_of_not_ge
  intro hprev
  have hfind : l ≤ l - 1 := by
    apply Nat.find_min'
      (exists_nat_scaled_cubicBoxVolume (d := d) (by omega)
        (q := theta d p / 4)
        (A := (((2 * j + 1) ^ d : ℕ) : ℝ))
        (div_pos htheta (by norm_num)))
    exact ⟨by omega, hprev⟩
  omega

/-- The volume growth estimate used in the upper half of (8.74). -/
theorem supercriticalNextBoxVolume_le
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p)
    {j : ℕ} (hj : 1 ≤ j) :
    ((((2 * supercriticalNextBoxIndex hd p htheta j + 1) ^ d : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (d + 2) / theta d p *
        ((((2 * j + 1) ^ d : ℕ) : ℝ)) := by
  let l := supercriticalNextBoxIndex hd p htheta j
  have hlj : j < l := supercriticalNextBoxIndex_gt hd p htheta j
  have hl2 : 2 ≤ l := by omega
  have hbase : 2 * l + 1 ≤ 2 * (2 * (l - 1) + 1) := by omega
  have hpow : (2 * l + 1) ^ d ≤ 2 ^ d * (2 * (l - 1) + 1) ^ d := by
    calc
      (2 * l + 1) ^ d ≤ (2 * (2 * (l - 1) + 1)) ^ d := Nat.pow_le_pow_left hbase d
      _ = 2 ^ d * (2 * (l - 1) + 1) ^ d := by rw [Nat.mul_pow]
  have hfailure := supercriticalNextBoxIndex_pred_failure hd p htheta hj
  have htheta0 : 0 < theta d p := htheta
  have hpred : ((((2 * (l - 1) + 1) ^ d : ℕ) : ℝ)) <
      4 / theta d p * ((((2 * j + 1) ^ d : ℕ) : ℝ)) := by
    change theta d p / 4 *
        ((((2 * (l - 1) + 1) ^ d : ℕ) : ℝ)) <
      (((2 * j + 1) ^ d : ℕ) : ℝ) at hfailure
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ htheta0).2
    nlinarith
  have hpowR : ((((2 * l + 1) ^ d : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ d * ((((2 * (l - 1) + 1) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast hpow
  calc
    ((((2 * l + 1) ^ d : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ d * ((((2 * (l - 1) + 1) ^ d : ℕ) : ℝ)) := hpowR
    _ ≤ (2 : ℝ) ^ d *
        (4 / theta d p * ((((2 * j + 1) ^ d : ℕ) : ℝ))) := by
      gcongr
    _ = (2 : ℝ) ^ (d + 2) / theta d p *
        ((((2 * j + 1) ^ d : ℕ) : ℝ)) := by
      rw [pow_add]
      norm_num
      ring

/-- Iteration of the source's minimal-next-box rule. -/
noncomputable def supercriticalSelectedBoxIndex
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) : ℕ → ℕ
  | 0 => supercriticalInitialBoxIndex hd p htheta
  | i + 1 => supercriticalNextBoxIndex hd p htheta
      (supercriticalSelectedBoxIndex hd p htheta i)

theorem supercriticalSelectedBoxIndex_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) :
    ∀ i, 1 ≤ supercriticalSelectedBoxIndex hd p htheta i := by
  intro i
  cases i with
  | zero => exact (supercriticalInitialBoxIndex_spec hd p htheta).1
  | succ i => exact (supercriticalNextBoxIndex_spec hd p htheta _).1

theorem supercriticalSelectedBoxIndex_strictMono
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) :
    StrictMono (supercriticalSelectedBoxIndex hd p htheta) := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact supercriticalNextBoxIndex_gt hd p htheta _

/-- The selected exact cluster sizes along the recursively chosen source boxes. -/
noncomputable def supercriticalSelectedTailScale
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) : ℕ :=
  supercriticalSelectedClusterSize hd p hp0 hp1 htheta
    (supercriticalSelectedBoxIndex hd p htheta i)

theorem supercriticalSelectedTailScale_two_mul_le
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) :
    2 * supercriticalSelectedTailScale hd p hp0 hp1 htheta i ≤
      supercriticalSelectedTailScale hd p hp0 hp1 htheta (i + 1) := by
  let j := supercriticalSelectedBoxIndex hd p htheta i
  let l := supercriticalNextBoxIndex hd p htheta j
  let kj := supercriticalSelectedTailScale hd p hp0 hp1 htheta i
  let kl := supercriticalSelectedTailScale hd p hp0 hp1 htheta (i + 1)
  have hkj := supercriticalSelectedClusterSize_upper hd p hp0 hp1 htheta j
  have hbox := (supercriticalNextBoxIndex_spec hd p htheta j).2
  have hkl := supercriticalSelectedClusterSize_lower hd p hp0 hp1 htheta l
  have hjnext : supercriticalSelectedBoxIndex hd p htheta (i + 1) = l := rfl
  have hreal : (2 : ℝ) * kj ≤ kl := by
    dsimp [kj, kl, supercriticalSelectedTailScale]
    rw [hjnext]
    have hkjR : (supercriticalSelectedClusterSize hd p hp0 hp1 htheta j : ℝ) ≤
        (((2 * j + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hkj
    nlinarith
  exact_mod_cast hreal

theorem supercriticalSelectedTailScale_le_delta_mul
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) :
    (supercriticalSelectedTailScale hd p hp0 hp1 htheta (i + 1) : ℝ) ≤
      ((2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2) *
        supercriticalSelectedTailScale hd p hp0 hp1 htheta i := by
  let j := supercriticalSelectedBoxIndex hd p htheta i
  let l := supercriticalNextBoxIndex hd p htheta j
  let kj := supercriticalSelectedTailScale hd p hp0 hp1 htheta i
  let kl := supercriticalSelectedTailScale hd p hp0 hp1 htheta (i + 1)
  have hj : 1 ≤ j := supercriticalSelectedBoxIndex_pos hd p htheta i
  have hvolume := supercriticalNextBoxVolume_le hd p htheta hj
  have hklUpper := supercriticalSelectedClusterSize_upper hd p hp0 hp1 htheta l
  have hkjLower := supercriticalSelectedClusterSize_lower hd p hp0 hp1 htheta j
  have hjnext : supercriticalSelectedBoxIndex hd p htheta (i + 1) = l := rfl
  have hVj : ((((2 * j + 1) ^ d : ℕ) : ℝ)) ≤
      2 / theta d p * (kj : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ htheta).2
    dsimp [kj, supercriticalSelectedTailScale]
    nlinarith
  have hklR : (kl : ℝ) ≤
      ((((2 * l + 1) ^ d : ℕ) : ℝ)) := by
    dsimp [kl, supercriticalSelectedTailScale]
    rw [hjnext]
    exact_mod_cast hklUpper
  calc
    (kl : ℝ) ≤ ((((2 * l + 1) ^ d : ℕ) : ℝ)) := hklR
    _ ≤ (2 : ℝ) ^ (d + 2) / theta d p *
        ((((2 * j + 1) ^ d : ℕ) : ℝ)) := hvolume
    _ ≤ (2 : ℝ) ^ (d + 2) / theta d p *
        (2 / theta d p * (kj : ℝ)) := by gcongr
    _ = ((2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2) * (kj : ℝ) := by
      rw [pow_succ]
      field_simp [ne_of_gt htheta]
      ring

theorem supercriticalSelectedTailScale_probability_lower
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    ∃ eta : ℝ, 0 ≤ eta ∧ ∀ i : ℕ,
      (supercriticalSelectedTailScale hd p hp0 hp1 htheta i : ℝ) *
          Real.exp (-eta *
            (supercriticalSelectedTailScale hd p hp0 hp1 htheta i : ℝ) ^
              supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p
          (supercriticalSelectedTailScale hd p hp0 hp1 htheta i) := by
  obtain ⟨eta, heta, hscale⟩ :=
    exists_eta_supercriticalSelectedClusterSize_probability_lower hd p hp0 hp1 htheta
  exact ⟨eta, heta, fun i ↦ hscale (supercriticalSelectedBoxIndex hd p htheta i)⟩

theorem supercriticalSelectedTailScale_zero_ge_two
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    2 ≤ supercriticalSelectedTailScale hd p hp0 hp1 htheta 0 := by
  have hinitial := (supercriticalInitialBoxIndex_spec hd p htheta).2
  have hselected := supercriticalSelectedClusterSize_lower hd p hp0 hp1 htheta
    (supercriticalInitialBoxIndex hd p htheta)
  have hreal : (2 : ℝ) ≤
      supercriticalSelectedTailScale hd p hp0 hp1 htheta 0 := by
    exact hinitial.trans (by
      simpa [supercriticalSelectedTailScale, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm] using hselected)
  exact_mod_cast hreal

/-- Number of initial dyadic steps needed to reach the first selected tail scale. -/
noncomputable def supercriticalScaleBridgeLength
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) : ℕ :=
  Nat.log 2 (supercriticalSelectedTailScale hd p hp0 hp1 htheta 0)

theorem supercriticalScaleBridgeLength_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    0 < supercriticalScaleBridgeLength hd p hp0 hp1 htheta := by
  exact Nat.log_pos (by norm_num)
    (supercriticalSelectedTailScale_zero_ge_two hd p hp0 hp1 htheta)

/-- The complete Lemma 8.72 scale: a finite dyadic bridge from `1`, followed by the selected
box-scale subsequence. -/
noncomputable def supercriticalLemma872Scale
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) : ℕ :=
  let A := supercriticalScaleBridgeLength hd p hp0 hp1 htheta
  if i < A then 2 ^ i
  else supercriticalSelectedTailScale hd p hp0 hp1 htheta (i - A)

@[simp]
theorem supercriticalLemma872Scale_zero
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    supercriticalLemma872Scale hd p hp0 hp1 htheta 0 = 1 := by
  rw [supercriticalLemma872Scale, if_pos
    (supercriticalScaleBridgeLength_pos hd p hp0 hp1 htheta)]
  simp

private theorem four_le_supercriticalScaleDelta
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) :
    (4 : ℝ) ≤ (2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2 := by
  have hthetaOne : theta d p ≤ 1 :=
    (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hinv : (1 : ℝ) ≤ (theta d p)⁻¹ := (one_le_inv₀ htheta).2 hthetaOne
  have hinvSq : (1 : ℝ) ≤ (theta d p)⁻¹ ^ 2 := by nlinarith
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (d + 3) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (d + 3) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (4 : ℝ) ≤ (2 : ℝ) ^ (d + 3) := hpow
    _ = (2 : ℝ) ^ (d + 3) * 1 := by ring
    _ ≤ (2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hinvSq (pow_nonneg (by norm_num) _)

theorem supercriticalLemma872Scale_two_mul_le
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) :
    2 * supercriticalLemma872Scale hd p hp0 hp1 htheta i ≤
      supercriticalLemma872Scale hd p hp0 hp1 htheta (i + 1) := by
  let A := supercriticalScaleBridgeLength hd p hp0 hp1 htheta
  let K := supercriticalSelectedTailScale hd p hp0 hp1 htheta 0
  by_cases hnext : i + 1 < A
  · have hi : i < A := lt_trans (Nat.lt_succ_self i) hnext
    simp [supercriticalLemma872Scale, A, hi, hnext, pow_succ, Nat.mul_comm]
  · by_cases hi : i < A
    · have hiA : i + 1 = A := by omega
      have hKne : K ≠ 0 := by
        have hKge : 2 ≤ K := by
          simpa [K] using
            supercriticalSelectedTailScale_zero_ge_two hd p hp0 hp1 htheta
        omega
      have hpowK : 2 ^ A ≤ K := Nat.pow_log_le_self 2 hKne
      simp only [supercriticalLemma872Scale, A, if_pos hi, if_neg hnext]
      rw [show i + 1 - A = 0 by omega]
      simpa [← hiA, pow_succ, Nat.mul_comm, K] using hpowK
    · have hi1 : ¬ i + 1 < A := by omega
      simp only [supercriticalLemma872Scale, A, if_neg hi, if_neg hi1]
      have hoffset : i + 1 - A = (i - A) + 1 := by omega
      rw [hoffset]
      exact supercriticalSelectedTailScale_two_mul_le hd p hp0 hp1 htheta (i - A)

theorem supercriticalLemma872Scale_le_delta_mul
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) (i : ℕ) :
    (supercriticalLemma872Scale hd p hp0 hp1 htheta (i + 1) : ℝ) ≤
      ((2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2) *
        supercriticalLemma872Scale hd p hp0 hp1 htheta i := by
  let A := supercriticalScaleBridgeLength hd p hp0 hp1 htheta
  let K := supercriticalSelectedTailScale hd p hp0 hp1 htheta 0
  let delta := (2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2
  have hdelta4 : (4 : ℝ) ≤ delta := four_le_supercriticalScaleDelta hd p htheta
  by_cases hnext : i + 1 < A
  · have hi : i < A := lt_trans (Nat.lt_succ_self i) hnext
    simp only [supercriticalLemma872Scale, A, if_pos hi, if_pos hnext]
    change (((2 ^ (i + 1) : ℕ) : ℝ)) ≤ delta * (((2 ^ i : ℕ) : ℝ))
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
    calc
      (2 : ℝ) ^ i * 2 ≤ (2 : ℝ) ^ i * 4 :=
        mul_le_mul_of_nonneg_left (by norm_num) hpow0
      _ ≤ (2 : ℝ) ^ i * delta :=
        mul_le_mul_of_nonneg_left hdelta4 hpow0
      _ = delta * (2 : ℝ) ^ i := by ring
      _ = delta * (((2 ^ i : ℕ) : ℝ)) := by norm_cast
  · by_cases hi : i < A
    · have hiA : i + 1 = A := by omega
      have hKlt : K < 2 ^ (A + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) K
      have hpow : (K : ℝ) ≤ 4 * (2 ^ i : ℕ) := by
        have hpowNat : K ≤ 4 * 2 ^ i := by
          rw [← hiA] at hKlt
          simp only [pow_succ] at hKlt
          omega
        exact_mod_cast hpowNat
      simp only [supercriticalLemma872Scale, A, if_pos hi, if_neg hnext]
      rw [hiA, Nat.sub_self]
      change (K : ℝ) ≤ delta * (2 ^ i : ℕ)
      exact hpow.trans (by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hdelta4
            (show (0 : ℝ) ≤ (2 ^ i : ℕ) by positivity))
    · have hi1 : ¬ i + 1 < A := by omega
      simp only [supercriticalLemma872Scale, A, if_neg hi, if_neg hi1]
      have hoffset : i + 1 - A = (i - A) + 1 := by omega
      rw [hoffset]
      exact supercriticalSelectedTailScale_le_delta_mul hd p hp0 hp1 htheta (i - A)

/-- The finite dyadic bridge can be absorbed into the exponential constant, so the complete
scale satisfies the probability lower bound in (8.75). -/
theorem supercriticalLemma872Scale_probability_lower
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p) :
    ∃ eta : ℝ, 0 ≤ eta ∧ ∀ i : ℕ,
      (supercriticalLemma872Scale hd p hp0 hp1 htheta i : ℝ) *
          Real.exp (-eta *
            (supercriticalLemma872Scale hd p hp0 hp1 htheta i : ℝ) ^
              supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p
          (supercriticalLemma872Scale hd p hp0 hp1 htheta i) := by
  obtain ⟨etaTail, hetaTail, htail⟩ :=
    supercriticalSelectedTailScale_probability_lower hd p hp0 hp1 htheta
  let A := supercriticalScaleBridgeLength hd p hp0 hp1 htheta
  let alpha := supercriticalClusterSizeExponent d
  let required : ℕ → ℝ := fun i ↦
    max 0 (Real.log (((2 ^ i : ℕ) : ℝ) /
      finiteClusterSizeProbability d p (2 ^ i)) /
        (((2 ^ i : ℕ) : ℝ) ^ alpha))
  let etaPrefix := ∑ i ∈ Finset.range A, required i
  let eta := max etaTail etaPrefix
  have hrequired0 : ∀ i, 0 ≤ required i := fun i ↦ by
    exact le_max_left _ _
  have hetaPrefix : 0 ≤ etaPrefix := Finset.sum_nonneg fun i hi ↦ hrequired0 i
  have heta : 0 ≤ eta := le_max_of_le_left hetaTail
  refine ⟨eta, heta, ?_⟩
  intro i
  by_cases hi : i < A
  · have hnpos : 0 < 2 ^ i := pow_pos (by omega) _
    let n : ℕ := 2 ^ i
    let P : ℝ := finiteClusterSizeProbability d p n
    have hP : 0 < P := CubicBondAnimal.finiteClusterSizeProbability_pos d n p
      (by omega) hnpos hp0 hp1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnPow : 0 < (n : ℝ) ^ alpha :=
      Real.rpow_pos_of_pos hnR alpha
    have hterm : required i ≤ etaPrefix := by
      apply Finset.single_le_sum (f := required)
      · intro j hj
        exact hrequired0 j
      · exact Finset.mem_range.mpr hi
    have hlog : Real.log ((n : ℝ) / P) / (n : ℝ) ^ alpha ≤ required i := by
      dsimp [required, n, P]
      exact le_max_right _ _
    have hetaReq : Real.log ((n : ℝ) / P) / (n : ℝ) ^ alpha ≤ eta :=
      hlog.trans (hterm.trans (le_max_right _ _))
    have hexp : Real.exp (-eta * (n : ℝ) ^ alpha) ≤ P / n := by
      rw [← Real.exp_log (div_pos hP hnR)]
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hnPow).mp at hetaReq
      have hlogSwap : Real.log (P / (n : ℝ)) =
          -Real.log ((n : ℝ) / P) := by
        rw [Real.log_div hP.ne' hnR.ne', Real.log_div hnR.ne' hP.ne']
        ring
      rw [hlogSwap]
      nlinarith
    have hr : supercriticalLemma872Scale hd p hp0 hp1 htheta i = n := by
      simp [supercriticalLemma872Scale, A, hi, n]
    rw [hr]
    change (n : ℝ) * Real.exp (-eta * (n : ℝ) ^ alpha) ≤ P
    exact (mul_le_mul_of_nonneg_left hexp hnR.le).trans_eq (by field_simp)
  · have hr : supercriticalLemma872Scale hd p hp0 hp1 htheta i =
        supercriticalSelectedTailScale hd p hp0 hp1 htheta (i - A) := by
      simp [supercriticalLemma872Scale, A, hi]
    rw [hr]
    let n := supercriticalSelectedTailScale hd p hp0 hp1 htheta (i - A)
    have hnpos : 0 < n := by
      have hlower := supercriticalSelectedClusterSize_lower hd p hp0 hp1 htheta
        (supercriticalSelectedBoxIndex hd p htheta (i - A))
      have hvol : (0 : ℝ) <
          ((((2 * supercriticalSelectedBoxIndex hd p htheta (i - A) + 1) ^ d : ℕ) : ℝ)) :=
        by positivity
      have hnreal : (0 : ℝ) < n := by
        dsimp [n, supercriticalSelectedTailScale]
        exact (div_pos (mul_pos htheta hvol) (by norm_num)).trans_le hlower
      exact_mod_cast hnreal
    have hnPow : 0 ≤ (n : ℝ) ^ alpha := Real.rpow_nonneg (by positivity) _
    have hetaComp : -eta * (n : ℝ) ^ alpha ≤
        -etaTail * (n : ℝ) ^ alpha := by
      have : etaTail ≤ eta := le_max_left _ _
      nlinarith
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hetaComp) (by positivity)).trans (htail (i - A))

/-- **Grimmett Lemma 8.72.**  Above criticality there is a scale beginning at one, growing by
factors between two and `δ = 2^(d+3) θ(p)\u207b²`, on which the exact finite-cluster probabilities
have the required surface-order lower bound. -/
theorem exists_supercriticalClusterSize_scale
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hpc : cubicCriticalProbability d < p) (hp1 : (p : ℝ) < 1) :
    ∃ eta : ℝ, 0 ≤ eta ∧
      let r := supercriticalLemma872Scale hd p
        ((cubicCriticalProbability_pos_lt_one hd).1.trans hpc) hp1
        (theta_pos_of_criticalProbability_lt hpc)
      r 0 = 1 ∧
      (∀ i, 2 * r i ≤ r (i + 1)) ∧
      (∀ i, (r (i + 1) : ℝ) ≤
        ((2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2) * r i) ∧
      ∀ i, (r i : ℝ) * Real.exp
        (-eta * (r i : ℝ) ^ supercriticalClusterSizeExponent d) ≤
          finiteClusterSizeProbability d p (r i) := by
  have hp0 : 0 < (p : ℝ) := (cubicCriticalProbability_pos_lt_one hd).1.trans hpc
  have htheta : 0 < theta d p := theta_pos_of_criticalProbability_lt hpc
  obtain ⟨eta, heta, hprob⟩ :=
    supercriticalLemma872Scale_probability_lower hd p hp0 hp1 htheta
  refine ⟨eta, heta, ?_, ?_, ?_, hprob⟩
  · exact supercriticalLemma872Scale_zero hd p hp0 hp1 htheta
  · exact supercriticalLemma872Scale_two_mul_le hd p hp0 hp1 htheta
  · exact supercriticalLemma872Scale_le_delta_mul hd p hp0 hp1 htheta

/-- **Grimmett Theorem 8.61.**  In the supercritical phase, every positive exact finite-cluster
size has a surface-order stretched-exponential lower bound. -/
theorem finiteClusterSizeProbability_ge_exp_neg_surface_of_critical_lt
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hpc : cubicCriticalProbability d < p) (hp1 : (p : ℝ) < 1) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ ∀ n : ℕ, 0 < n →
      Real.exp (-gamma * (n : ℝ) ^ supercriticalClusterSizeExponent d) ≤
        finiteClusterSizeProbability d p n := by
  have hp0 : 0 < (p : ℝ) := (cubicCriticalProbability_pos_lt_one hd).1.trans hpc
  have htheta : 0 < theta d p := theta_pos_of_criticalProbability_lt hpc
  obtain ⟨eta, heta, hr0, hrLower, hrUpper, hscale⟩ :=
    exists_supercriticalClusterSize_scale hd p hpc hp1
  let delta : ℝ := (2 : ℝ) ^ (d + 3) * (theta d p)⁻¹ ^ 2
  have hdelta : 0 ≤ delta := mul_nonneg (by positivity) (pow_nonneg (by positivity) _)
  exact finiteClusterSizeProbability_ge_exp_neg_surface_of_scale
    hd p hp0 hp1 hdelta hr0 hrLower hrUpper heta hscale

end Percolation
