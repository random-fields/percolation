import Percolation.Bernoulli.DisjointConnections
import Percolation.Bernoulli.Coupling
import Percolation.Critical.VertexIndependence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Radius events and susceptibility on the cubic lattice

This file supplies the geometric and probabilistic vocabulary used in both proofs of
Grimmett's Chapter 5 exponential-decay theorem.  The finite event `radiusConnectionEvent`
is the event called `Aₙ(x)` in §5.2.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal unitInterval BigOperators

/-! ### Finite metric balls -/

/-- The coordinate box of radius `n` centered at `x`.  It is an enumerable ambient set for
the graph-metric ball. -/
noncomputable def cubicMetricBox (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  Fintype.piFinset fun i : Fin d ↦ Finset.Icc (x i - n) (x i + n)

@[simp]
theorem mem_cubicMetricBox {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricBox d x n ↔ ∀ i, x i - n ≤ y i ∧ y i ≤ x i + n := by
  simp [cubicMetricBox]

/-- The closed graph-metric ball `S(n,x)` in the cubic lattice. -/
noncomputable def cubicMetricBall (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d x n).filter fun y ↦ cubicL1Dist x y ≤ n

/-- The graph-metric sphere `∂S(n,x)` in the cubic lattice. -/
noncomputable def cubicMetricSphere (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d x n).filter fun y ↦ cubicL1Dist x y = n

@[simp]
theorem mem_cubicMetricBall {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricBall d x n ↔ y ∈ cubicMetricBox d x n ∧ cubicL1Dist x y ≤ n := by
  simp [cubicMetricBall]

@[simp]
theorem mem_cubicMetricSphere {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricSphere d x n ↔ y ∈ cubicMetricBox d x n ∧ cubicL1Dist x y = n := by
  simp [cubicMetricSphere]

/-- The coordinate box in the definition of `cubicMetricBall` is only an enumeration device:
membership is exactly the Manhattan-distance inequality. -/
theorem mem_cubicMetricBall_iff_l1Dist_le {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricBall d x n ↔ cubicL1Dist x y ≤ n := by
  rw [mem_cubicMetricBall]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  rw [mem_cubicMetricBox]
  intro i
  have hi := (cubicL1Dist_coord_le x y i).trans h
  by_cases hz : 0 ≤ y i - x i
  · have hiz : ((y i - x i).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
    rw [Int.natAbs_of_nonneg hz] at hiz
    constructor <;> omega
  · have hz' : 0 ≤ -(y i - x i) := by omega
    rw [← Int.natAbs_neg] at hi
    have hiz : ((-(y i - x i)).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
    rw [Int.natAbs_of_nonneg hz'] at hiz
    constructor <;> omega

theorem mem_cubicMetricSphere_iff_l1Dist_eq {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricSphere d x n ↔ cubicL1Dist x y = n := by
  rw [mem_cubicMetricSphere]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  rw [mem_cubicMetricBox]
  intro i
  have hi := (cubicL1Dist_coord_le x y i).trans h.le
  by_cases hz : 0 ≤ y i - x i
  · have hiz : ((y i - x i).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
    rw [Int.natAbs_of_nonneg hz] at hiz
    constructor <;> omega
  · have hz' : 0 ≤ -(y i - x i) := by omega
    rw [← Int.natAbs_neg] at hi
    have hiz : ((-(y i - x i)).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
    rw [Int.natAbs_of_nonneg hz'] at hiz
    constructor <;> omega

theorem cubicMetricBox_card (d : ℕ) (x : Cubic d) (n : ℕ) :
    (cubicMetricBox d x n).card = (2 * n + 1) ^ d := by
  classical
  simp only [cubicMetricBox, Fintype.card_piFinset, Int.card_Icc]
  have hterm : ∀ i : Fin d,
      (x i + (n : ℤ) + 1 - (x i - (n : ℤ))).toNat = 2 * n + 1 := by
    intro i
    omega
  simp_rw [hterm]
  simp

/-- Grimmett's elementary volume estimate `|S(n,x)| ≤ 3ᵈ(n+1)ᵈ`. -/
theorem cubicMetricBall_card_le (d : ℕ) (x : Cubic d) (n : ℕ) :
    (cubicMetricBall d x n).card ≤ 3 ^ d * (n + 1) ^ d := by
  calc
    (cubicMetricBall d x n).card ≤ (cubicMetricBox d x n).card := Finset.card_filter_le _ _
    _ = (2 * n + 1) ^ d := cubicMetricBox_card d x n
    _ ≤ (3 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
    _ = 3 ^ d * (n + 1) ^ d := by rw [mul_pow]

theorem cubicMetricSphere_subset_ball (d : ℕ) (x : Cubic d) (n : ℕ) :
    cubicMetricSphere d x n ⊆ cubicMetricBall d x n := by
  intro y hy
  rw [mem_cubicMetricSphere] at hy
  rw [mem_cubicMetricBall]
  exact ⟨hy.1, hy.2.le⟩

@[simp]
theorem cubicMetricSphere_zero (d : ℕ) (x : Cubic d) :
    cubicMetricSphere d x 0 = {x} := by
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy
    exact (cubicL1Dist_eq_zero_iff.mp (mem_cubicMetricSphere.mp hy).2).symm
  · intro hy
    subst y
    exact mem_cubicMetricSphere.mpr ⟨by simp, by simp⟩

/-- The undirected cubic edge traversed by a signed step. -/
def cubicStepEdge {d : ℕ} (y : Cubic d) (a : CubicDirection d) : CubicEdge d :=
  ⟨s(y, cubicStepFrom y a), by
    rw [SimpleGraph.mem_edgeSet]
    exact cubicGraph_adj_stepFrom y a⟩

/-- All nearest-neighbor edges whose two endpoints lie in `S(n,x)`. -/
noncomputable def cubicMetricBallEdges (d : ℕ) (x : Cubic d) (n : ℕ) :
    Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBall d x n).biUnion fun y ↦
    ((Finset.univ.filter fun a : CubicDirection d ↦
        cubicStepFrom y a ∈ cubicMetricBall d x n).image fun a ↦
      cubicStepEdge y a)

theorem cubicStepEdge_mem_cubicMetricBallEdges {d n : ℕ} {x y : Cubic d}
    {a : CubicDirection d} (hy : y ∈ cubicMetricBall d x n)
    (hya : cubicStepFrom y a ∈ cubicMetricBall d x n) :
    cubicStepEdge y a ∈ cubicMetricBallEdges d x n := by
  classical
  simp only [cubicMetricBallEdges, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨y, hy, a, hya, rfl⟩

theorem endpoint_mem_cubicMetricBall_of_edge_mem {d n : ℕ} {x z : Cubic d}
    {e : CubicEdge d} (he : e ∈ cubicMetricBallEdges d x n)
    (hz : z ∈ (e : Sym2 (Cubic d))) : z ∈ cubicMetricBall d x n := by
  classical
  simp only [cubicMetricBallEdges, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨y, hy, a, hya, rfl⟩ := he
  rw [cubicStepEdge, Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hy
  · exact hya

theorem walk_support_subset_cubicMetricBall_of_edges {d n : ℕ} {x u v : Cubic d}
    (hu : u ∈ cubicMetricBall d x n) (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ cubicMetricBallEdges d x n) :
    ∀ z ∈ w.support, z ∈ cubicMetricBall d x n := by
  induction w with
  | nil => simpa using hu
  | @cons u y v huy p ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · let e : CubicEdge d := ⟨s(u, y), by
          rw [SimpleGraph.mem_edgeSet]
          exact huy⟩
        have hew : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huy p) := by
          rw [mem_walkEdgeFinset_iff]
          simp [e]
        have hy : y ∈ cubicMetricBall d x n :=
          endpoint_mem_cubicMetricBall_of_edge_mem (hw hew) (by simp [e])
        have hp : walkEdgeFinset p ⊆ cubicMetricBallEdges d x n := by
          intro f hf
          apply hw
          rw [mem_walkEdgeFinset_iff] at hf ⊢
          simp [hf]
        exact ih hy hp z hz

/-- If every vertex of a walk lies in a metric ball, every traversed edge belongs to the
finite edge set of that ball. -/
theorem walkEdgeFinset_subset_cubicMetricBallEdges_of_support {d n : ℕ}
    {x u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hball : ∀ z ∈ w.support, z ∈ cubicMetricBall d x n) :
    walkEdgeFinset w ⊆ cubicMetricBallEdges d x n := by
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  induction w with
  | nil => simp at he
  | @cons u v z huv p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨a, ha⟩
        have hu : u ∈ cubicMetricBall d x n := hball u (by simp)
        have hv : v ∈ cubicMetricBall d x n := hball v (by simp)
        have hedge : e = cubicStepEdge u a := by
          apply Subtype.ext
          simpa [cubicStepEdge, ha] using he
        rw [hedge]
        exact cubicStepEdge_mem_cubicMetricBallEdges hu (by simpa [ha] using hv)
      · apply ih
        · intro q hq
          exact hball q (by simp [hq])
        · exact he

/-- First-hitting construction: an open walk whose endpoint is at distance at least `n` has
an open prefix ending on the sphere of radius `n`, and that prefix stays in the ball. -/
theorem exists_open_walk_to_cubicMetricSphere_in_ball {d n : ℕ}
    {ω : EdgeConfiguration d} {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hopen : walkIsOpen ω w) (hy : n ≤ cubicL1Dist x y) :
    ∃ z, z ∈ cubicMetricSphere d x n ∧
      ω ∈ connectionEventIn d (cubicMetricBallEdges d x n) x z := by
  classical
  have hexit : ∃ k : ℕ,
      k ≤ w.length ∧ n ≤ cubicL1Dist x (w.getVert k) := by
    exact ⟨w.length, le_rfl, by simpa using hy⟩
  let k := Nat.find hexit
  have hk : k ≤ w.length ∧ n ≤ cubicL1Dist x (w.getVert k) := Nat.find_spec hexit
  have hkdist : cubicL1Dist x (w.getVert k) = n := by
    by_cases hkzero : k = 0
    · have hn : n = 0 := by
        simpa [hkzero] using hk.2
      simp [hkzero, hn]
    · let j := k - 1
      have hksucc : k = j + 1 := by omega
      have hjfind : j < Nat.find hexit := by
        change j < k
        omega
      have hjlt : cubicL1Dist x (w.getVert j) < n := by
        apply lt_of_not_ge
        intro hj
        exact Nat.find_min hexit hjfind ⟨by omega, hj⟩
      have hjlen : j < w.length := by omega
      have hadj := w.adj_getVert_succ hjlen
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
      have hupper : cubicL1Dist x (w.getVert (j + 1)) ≤ n := by
        calc
          cubicL1Dist x (w.getVert (j + 1)) ≤
              cubicL1Dist x (w.getVert j) +
                cubicL1Dist (w.getVert j) (w.getVert (j + 1)) :=
            cubicL1Dist_triangle _ _ _
          _ = cubicL1Dist x (w.getVert j) + 1 := by
            rw [ha, cubicL1Dist_stepFrom]
          _ ≤ n := by omega
      rw [hksucc]
      exact le_antisymm hupper (by simpa [hksucc] using hk.2)
  let q := w.take k
  have hq_length : q.length = k := by
    simp [q, Nat.min_eq_left hk.1]
  have hq_support : ∀ z ∈ q.support, z ∈ cubicMetricBall d x n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    rcases hz with ⟨m, hm, hmle⟩
    subst z
    have hmk : m ≤ k := by omega
    have hget : q.getVert m = w.getVert m := by
      simp [q, Nat.min_eq_right hmk]
    rw [hget, mem_cubicMetricBall_iff_l1Dist_le]
    by_cases hmk' : m = k
    · simpa [hmk'] using hkdist.le
    · have hmlt : m < k := lt_of_le_of_ne hmk hmk'
      apply le_of_lt
      apply lt_of_not_ge
      intro hmge
      exact Nat.find_min hexit hmlt ⟨(hmle.trans_eq hq_length).trans hk.1, hmge⟩
  have hqopen : walkIsOpen ω q := by
    intro e he
    apply hopen e
    have he' : e ∈ (w.take k).edges := by simpa [q] using he
    rw [SimpleGraph.Walk.edges_take] at he'
    exact List.Sublist.subset (List.take_sublist k w.edges) he'
  refine ⟨w.getVert k, ?_, q, hqopen, ?_⟩
  · rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    exact hkdist
  · exact walkEdgeFinset_subset_cubicMetricBallEdges_of_support q hq_support

/-! ### The finite radius event -/

/-- `Aₙ(x)`: there is an open path from `x` to the metric sphere of radius `n`, using only
edges of the finite metric ball. -/
def radiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ y, y ∈ cubicMetricSphere d x n ∧
    ω ∈ connectionEventIn d (cubicMetricBallEdges d x n) x y}

/-- The finite-support definition of `Aₙ(x)` is equivalent to ordinary open connection from
`x` to the metric sphere. -/
theorem mem_radiusConnectionEvent_iff_exists_connection {d n : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d} :
    ω ∈ radiusConnectionEvent d x n ↔
      ∃ y, y ∈ cubicMetricSphere d x n ∧ ω ∈ connectionEvent d x y := by
  constructor
  · rintro ⟨y, hy, hconn⟩
    exact ⟨y, hy, connectionEventIn_subset d _ x y hconn⟩
  · rintro ⟨y, hy, w, hopen⟩
    exact exists_open_walk_to_cubicMetricSphere_in_ball w hopen
      (mem_cubicMetricSphere_iff_l1Dist_eq.mp hy).ge

theorem dependsOn_radiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    DependsOn (cubicMetricBallEdges d x n) (radiusConnectionEvent d x n) := by
  intro ω η hagree
  constructor
  · rintro ⟨y, hy, hω⟩
    exact ⟨y, hy, (dependsOn_connectionEventIn d _ x y hagree).mp hω⟩
  · rintro ⟨y, hy, hη⟩
    exact ⟨y, hy, (dependsOn_connectionEventIn d _ x y hagree).mpr hη⟩

theorem measurableSet_radiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    MeasurableSet (radiusConnectionEvent d x n) :=
  (dependsOn_radiusConnectionEvent d x n).measurableSet

theorem isIncreasingEvent_radiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    IsIncreasingEvent (radiusConnectionEvent d x n) := by
  rintro ω η hωη ⟨y, hy, hconn⟩
  exact ⟨y, hy, isIncreasingEvent_connectionEventIn d _ x y hωη hconn⟩

/-- Larger-radius connection events are nested inside smaller-radius ones. -/
theorem radiusConnectionEvent_antitone (d : ℕ) (x : Cubic d) :
    Antitone (radiusConnectionEvent d x) := by
  intro m n hmn ω hω
  rcases hω with ⟨y, hy, w, hopen, _hsupport⟩
  exact exists_open_walk_to_cubicMetricSphere_in_ball w hopen <|
    hmn.trans_eq (mem_cubicMetricSphere_iff_l1Dist_eq.mp hy).symm

@[simp]
theorem radiusConnectionEvent_zero (d : ℕ) (x : Cubic d) :
    radiusConnectionEvent d x 0 = Set.univ := by
  ext ω
  constructor
  · intro _h
    trivial
  · intro _h
    refine ⟨x, by simp, SimpleGraph.Walk.nil, ?_, ?_⟩
    · intro e he
      simp at he
    · simp [walkEdgeFinset, walkEdgeList]

/-- Grimmett's radius tail `gₚ(n) = Pₚ(Aₙ)`, rooted at the origin. -/
noncomputable def radiusTail (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (radiusConnectionEvent d cubicOrigin n)

@[simp]
theorem radiusTail_zero (d : ℕ) (p : I) : radiusTail d p 0 = 1 := by
  simp [radiusTail, radiusConnectionEvent_zero]

theorem radiusTail_antitone (d : ℕ) (p : I) : Antitone (radiusTail d p) := by
  intro m n hmn
  exact measureReal_mono (radiusConnectionEvent_antitone d cubicOrigin hmn)

theorem radiusTail_mono_density (d : ℕ) (n : ℕ) : Monotone fun p : I ↦ radiusTail d p n := by
  intro p q hpq
  exact (isIncreasingEvent_radiusConnectionEvent d cubicOrigin n).setBernoulli_real_mono
    (measurableSet_radiusConnectionEvent d cubicOrigin n) hpq

/-- The intersection of all finite radius events is exactly the infinite-cluster event. -/
theorem iInter_radiusConnectionEvent (d : ℕ) (x : Cubic d) :
    (⋂ n : ℕ, radiusConnectionEvent d x n) =
      {ω : EdgeConfiguration d | hasInfiniteOpenClusterFrom d ω x} := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom]
    intro n
    rcases h n with ⟨y, hy, w, hopen, _hsupport⟩
    refine ⟨y, (w.toPath : (cubicGraph d).Walk x y), w.toPath.2, ?_,
      walkIsOpen_toPath w hopen⟩
    rw [← mem_cubicMetricSphere_iff_l1Dist_eq.mp hy]
    exact cubicL1Dist_le_walk_length (w.toPath : (cubicGraph d).Walk x y)
  · intro hinfinite n
    have hcluster : (cubicOpenClusterFrom d ω x).Infinite := hinfinite
    obtain ⟨y, hy, hynot⟩ := hcluster.exists_notMem_finset (cubicMetricBall d x n)
    have hydist : n ≤ cubicL1Dist x y := by
      by_contra hnot
      have hlt : cubicL1Dist x y < n := Nat.lt_of_not_ge hnot
      exact hynot (mem_cubicMetricBall_iff_l1Dist_le.mpr hlt.le)
    rcases hy with ⟨w, hopen⟩
    exact exists_open_walk_to_cubicMetricSphere_in_ball w hopen hydist

/-- The radius tails decrease to the percolation probability. -/
theorem radiusTail_tendsto_theta (d : ℕ) (p : I) :
    Tendsto (radiusTail d p) Filter.atTop (nhds (theta d p)) := by
  let μ := bernoulliBondMeasure d p
  have hμ : Tendsto (fun n : ℕ ↦ μ (radiusConnectionEvent d cubicOrigin n))
      Filter.atTop (nhds (μ (⋂ n : ℕ, radiusConnectionEvent d cubicOrigin n))) :=
    tendsto_measure_iInter_atTop
      (fun n ↦ (measurableSet_radiusConnectionEvent d cubicOrigin n).nullMeasurableSet)
      (radiusConnectionEvent_antitone d cubicOrigin) ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hμ
  rw [iInter_radiusConnectionEvent] at hreal
  simpa [radiusTail, theta, μ, measureReal_def, Function.comp_def,
    hasInfiniteOpenClusterFrom_origin] using hreal

/-! ### Cluster radius, cluster size, and susceptibility -/

/-- The radius of the origin cluster as an extended natural number. -/
noncomputable def clusterRadius (d : ℕ) (ω : EdgeConfiguration d) : ℕ∞ :=
  by
    classical
    exact ⨆ y : Cubic d,
      if y ∈ cubicOpenCluster d ω then (cubicL1Dist cubicOrigin y : ℕ∞) else 0

/-- The extended cardinality of the origin cluster.  The sum is `⊤` precisely for an infinite
cluster, unlike `Set.ncard`, whose infinite-set convention is zero. -/
noncomputable def clusterSizeENNReal (d : ℕ) (ω : EdgeConfiguration d) : ℝ≥0∞ :=
  by
    classical
    exact ∑' y : Cubic d, if y ∈ cubicOpenCluster d ω then 1 else 0

theorem clusterSizeENNReal_eq_encard (d : ℕ) (ω : EdgeConfiguration d) :
    clusterSizeENNReal d ω = (cubicOpenCluster d ω).encard := by
  classical
  rw [← ENNReal.tsum_set_one]
  change (∑' y : Cubic d,
    (cubicOpenCluster d ω).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
      ∑' _ : cubicOpenCluster d ω, (1 : ℝ≥0∞)
  exact (tsum_subtype (cubicOpenCluster d ω) fun _ ↦ (1 : ℝ≥0∞)).symm

/-- The extended cardinality of the origin cluster is a measurable random variable. -/
theorem measurable_clusterSizeENNReal (d : ℕ) :
    Measurable (clusterSizeENNReal d) := by
  classical
  unfold clusterSizeENNReal
  apply Measurable.tsum
  intro y
  have hevent : {ω : EdgeConfiguration d | y ∈ cubicOpenCluster d ω} =
      connectionEvent d cubicOrigin y := by
    rfl
  rw [show (fun ω : EdgeConfiguration d ↦
      if y ∈ cubicOpenCluster d ω then (1 : ℝ≥0∞) else 0) =
      (connectionEvent d cubicOrigin y).indicator (fun _ ↦ 1) by
    funext ω
    simp only [Set.indicator, connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq]
    rfl]
  exact measurable_const.indicator (measurableSet_connectionEvent d cubicOrigin y)

theorem clusterSizeENNReal_eq_top_iff (d : ℕ) (ω : EdgeConfiguration d) :
    clusterSizeENNReal d ω = ⊤ ↔ hasInfiniteOpenCluster d ω := by
  rw [clusterSizeENNReal_eq_encard, ENat.toENNReal_eq_top, Set.encard_eq_top_iff]
  rfl

/-- The susceptibility `χ(p) = Eₚ|C|`. -/
noncomputable def susceptibility (d : ℕ) (p : I) : ℝ≥0∞ :=
  ∫⁻ ω, clusterSizeENNReal d ω ∂bernoulliBondMeasure d p

/-- The susceptibility is the sum of the two-point connection probabilities. -/
theorem susceptibility_eq_tsum_connection (d : ℕ) (p : I) :
    susceptibility d p =
      ∑' y : Cubic d, bernoulliBondMeasure d p (connectionEvent d cubicOrigin y) := by
  classical
  let μ := bernoulliBondMeasure d p
  have hmeas : ∀ y : Cubic d, Measurable fun ω : EdgeConfiguration d ↦
      if y ∈ cubicOpenCluster d ω then (1 : ℝ≥0∞) else 0 := by
    intro y
    have hevent : {ω : EdgeConfiguration d | y ∈ cubicOpenCluster d ω} =
        connectionEvent d cubicOrigin y := by
      rfl
    rw [show (fun ω : EdgeConfiguration d ↦
        if y ∈ cubicOpenCluster d ω then (1 : ℝ≥0∞) else 0) =
        (connectionEvent d cubicOrigin y).indicator (fun _ ↦ 1) by
      funext ω
      simp only [Set.indicator, connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
        Set.mem_setOf_eq]
      rfl]
    exact measurable_const.indicator (measurableSet_connectionEvent d cubicOrigin y)
  unfold susceptibility clusterSizeENNReal
  rw [lintegral_tsum fun y ↦ (hmeas y).aemeasurable]
  apply tsum_congr
  intro y
  have hevent : {ω : EdgeConfiguration d | y ∈ cubicOpenCluster d ω} =
      connectionEvent d cubicOrigin y := by
    rfl
  rw [show (fun ω : EdgeConfiguration d ↦
      if y ∈ cubicOpenCluster d ω then (1 : ℝ≥0∞) else 0) =
      (connectionEvent d cubicOrigin y).indicator (fun _ ↦ 1) by
    funext ω
    simp only [Set.indicator, connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq]
    rfl]
  simp [measurableSet_connectionEvent]

theorem susceptibility_mono (d : ℕ) : Monotone (susceptibility d) := by
  intro p q hpq
  rw [susceptibility_eq_tsum_connection, susceptibility_eq_tsum_connection]
  exact ENNReal.tsum_le_tsum fun y ↦
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp <|
      (isIncreasingEvent_connectionEvent d cubicOrigin y).setBernoulli_real_mono
        (measurableSet_connectionEvent d cubicOrigin y) hpq

theorem susceptibility_eq_top_of_theta_pos {d : ℕ} {p : I} (hp : 0 < theta d p) :
    susceptibility d p = ⊤ := by
  let μ := bernoulliBondMeasure d p
  let A : Set (EdgeConfiguration d) := {ω | hasInfiniteOpenCluster d ω}
  have hA : MeasurableSet A := measurableSet_hasInfiniteOpenClusterFrom d cubicOrigin
  have hμA : μ A ≠ 0 := by
    intro hzero
    have htheta : theta d p = 0 := by
      simp [theta, μ, A, measureReal_def, hzero]
    linarith
  have hpoint : A.indicator (fun _ ↦ (⊤ : ℝ≥0∞)) ≤ clusterSizeENNReal d := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      exact (clusterSizeENNReal_eq_top_iff d ω).mpr hω |>.ge
    · simp [Set.indicator, hω]
  have hle : (∫⁻ ω, A.indicator (fun _ ↦ (⊤ : ℝ≥0∞)) ω ∂μ) ≤
      susceptibility d p := by
    exact (lintegral_mono hpoint).trans_eq rfl
  have hleft : (∫⁻ ω, A.indicator (fun _ ↦ (⊤ : ℝ≥0∞)) ω ∂μ) = ⊤ := by
    rw [lintegral_indicator_const hA]
    simp [hμA]
  exact top_unique (hleft ▸ hle)

/-- The susceptibility threshold `p_T = sup {p : χ(p) < ∞}`. -/
noncomputable def susceptibilityThreshold (d : ℕ) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | susceptibility d p < ⊤}) : Set ℝ)

/-! ### Critical-point adapters -/

private theorem theta_zero_density (d : ℕ) :
    theta d (⟨0, by simp⟩ : I) = 0 := by
  apply le_antisymm
  · exact (theta_le_selfAvoidingWalkCount_mul_pow d 1 (⟨0, by simp⟩ : I)).trans_eq (by simp)
  · exact measureReal_nonneg

private theorem criticalZeroSet_nonempty (d : ℕ) :
    (((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0}) : Set ℝ).Nonempty := by
  exact ⟨0, ⟨(⟨0, by simp⟩ : I), theta_zero_density d, rfl⟩⟩

private theorem criticalZeroSet_bddAbove (d : ℕ) :
    BddAbove (((fun p : I ↦ (p : ℝ)) '' {p : I | theta d p = 0}) : Set ℝ) := by
  refine ⟨1, ?_⟩
  rintro q ⟨p, _hp, rfl⟩
  exact p.2.2

/-- The defining supremum for `p_c` implies vanishing of `θ` strictly below `p_c`. -/
theorem theta_eq_zero_of_lt_criticalProbability {d : ℕ} {p : I}
    (hp : (p : ℝ) < cubicCriticalProbability d) : theta d p = 0 := by
  rw [cubicCriticalProbability] at hp
  obtain ⟨q, ⟨qI, hqzero, rfl⟩, hpq⟩ :=
    exists_lt_of_lt_csSup (criticalZeroSet_nonempty d) hp
  apply le_antisymm
  · exact (theta_mono d (show p ≤ qI by exact_mod_cast hpq.le)).trans_eq hqzero
  · exact measureReal_nonneg

/-- Above the defining critical probability, the percolation probability is positive. -/
theorem theta_pos_of_criticalProbability_lt {d : ℕ} {p : I}
    (hp : cubicCriticalProbability d < (p : ℝ)) : 0 < theta d p := by
  apply lt_of_le_of_ne measureReal_nonneg
  intro htheta
  have hp_mem : (p : ℝ) ∈
      (((fun q : I ↦ (q : ℝ)) '' {q : I | theta d q = 0}) : Set ℝ) :=
    ⟨p, htheta.symm, rfl⟩
  have hle : (p : ℝ) ≤ cubicCriticalProbability d := by
    rw [cubicCriticalProbability]
    exact le_csSup (criticalZeroSet_bddAbove d) hp_mem
  exact not_lt_of_ge hle hp

end Percolation
