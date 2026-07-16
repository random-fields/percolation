import Percolation.Critical.RadiusDecay
import Percolation.Critical.Translation
import Percolation.Planar.Crossings

/-!
# The square-lattice critical probability

This file formalizes the finite rectangle used in Grimmett, Lemma 11.21, and the analytic
implication from its half-density crossing probability to the upper bound `p_c ≤ 1 / 2`.
The planar crossing alternative itself is developed in the duality layer.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval

/-- The density `1 / 2`, packaged in the unit interval. -/
noncomputable def squareHalfDensity : I :=
  ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem coe_squareHalfDensity : (squareHalfDensity : ℝ) = 1 / 2 :=
  rfl

/-- The vertex set `[0, n + 1] × [0, n]` from Grimmett, Lemma 11.21. -/
noncomputable def grimmettRectangleVertices (n : ℕ) : Finset SquareVertex :=
  ((Finset.Icc (0 : ℤ) (n + 1)).product (Finset.Icc (0 : ℤ) n)).map
    squareVertexEmbedding

/-- The left side of the rectangle in Lemma 11.21. -/
noncomputable def grimmettRectangleLeft (n : ℕ) : Finset SquareVertex :=
  (Finset.Icc (0 : ℤ) n).map
    ⟨fun y ↦ squareVertex 0 y, fun _ _ h ↦ congrFun h 1⟩

/-- The right side of the rectangle in Lemma 11.21. -/
noncomputable def grimmettRectangleRight (n : ℕ) : Finset SquareVertex :=
  (Finset.Icc (0 : ℤ) n).map
    ⟨fun y ↦ squareVertex (n + 1) y, fun _ _ h ↦ congrFun h 1⟩

@[simp]
theorem mem_grimmettRectangleVertices_iff {n : ℕ} {x : SquareVertex} :
    x ∈ grimmettRectangleVertices n ↔
      0 ≤ x 0 ∧ x 0 ≤ (n + 1 : ℕ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, habx⟩ := Finset.mem_map.mp hx
    have hab' : 0 ≤ a ∧ a ≤ (n + 1 : ℕ) ∧ 0 ≤ b ∧ b ≤ (n : ℤ) := by
      have h := by simpa [Finset.mem_Icc] using hab
      exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
    have ha : a = x 0 := by
      simpa [squareVertexEmbedding] using congrFun habx 0
    have hb : b = x 1 := by
      simpa [squareVertexEmbedding] using congrFun habx 1
    simpa [ha, hb] using hab'
  · intro hx
    refine Finset.mem_map.mpr ⟨(x 0, x 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hx.1, hx.2.1⟩, Finset.mem_Icc.mpr hx.2.2⟩
    · exact squareVertex_eta x

@[simp]
theorem mem_grimmettRectangleLeft_iff {n : ℕ} {x : SquareVertex} :
    x ∈ grimmettRectangleLeft n ↔ x 0 = 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hy' : 0 ≤ y ∧ y ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using hy
    have hx0 : x 0 = 0 := by
      simpa using (congrFun hyx 0).symm
    have hy1 : y = x 1 := by
      simpa using congrFun hyx 1
    exact ⟨hx0, by simpa [hy1] using hy'.1, by simpa [hy1] using hy'.2⟩
  · rintro ⟨hx0, hx1, hx1'⟩
    refine Finset.mem_map.mpr ⟨x 1, by simp [Finset.mem_Icc, hx1, hx1'], ?_⟩
    rw [← squareVertex_eta x]
    simp [hx0]

@[simp]
theorem mem_grimmettRectangleRight_iff {n : ℕ} {x : SquareVertex} :
    x ∈ grimmettRectangleRight n ↔
      x 0 = (n + 1 : ℕ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hy' : 0 ≤ y ∧ y ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using hy
    have hx0 : x 0 = (n + 1 : ℕ) := by
      simpa using (congrFun hyx 0).symm
    have hy1 : y = x 1 := by
      simpa using congrFun hyx 1
    exact ⟨hx0, by simpa [hy1] using hy'.1, by simpa [hy1] using hy'.2⟩
  · rintro ⟨hx0, hx1, hx1'⟩
    refine Finset.mem_map.mpr ⟨x 1, by simp [Finset.mem_Icc, hx1, hx1'], ?_⟩
    rw [← squareVertex_eta x]
    simp [hx0]

@[simp]
theorem card_grimmettRectangleLeft (n : ℕ) :
    (grimmettRectangleLeft n).card = n + 1 := by
  simp [grimmettRectangleLeft]

/-- All square-lattice edges with both endpoints in the rectangle from Lemma 11.21. -/
noncomputable def grimmettRectangleEdges (n : ℕ) : Finset SquareEdge :=
  (cubicBoxEdges 2 cubicOrigin (n + 1)).filter fun e ↦
    e.1.out.1 ∈ grimmettRectangleVertices n ∧
      e.1.out.2 ∈ grimmettRectangleVertices n

/-- Every endpoint of an edge in Grimmett's finite rectangle belongs to its vertex set. -/
theorem endpoint_mem_grimmettRectangleVertices_of_edge_mem
    {n : ℕ} {e : SquareEdge} (he : e ∈ grimmettRectangleEdges n)
    {x : SquareVertex} (hx : x ∈ (e : Sym2 SquareVertex)) :
    x ∈ grimmettRectangleVertices n := by
  have hend := (Finset.mem_filter.mp he).2
  rw [← e.1.out_eq] at hx
  change x ∈ s(e.1.out.1, e.1.out.2) at hx
  rw [Sym2.mem_iff] at hx
  exact hx.elim (fun h ↦ h ▸ hend.1) (fun h ↦ h ▸ hend.2)

/-- A walk which starts in Grimmett's rectangle and uses only its internal edges remains in
the rectangle. -/
theorem walk_support_subset_grimmettRectangleVertices_of_edges
    {n : ℕ} {u v : SquareVertex} (hu : u ∈ grimmettRectangleVertices n)
    (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ grimmettRectangleEdges n) :
    ∀ z ∈ w.support, z ∈ grimmettRectangleVertices n := by
  induction w with
  | nil => simpa using hu
  | @cons u y v huy q ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · let e : SquareEdge := ⟨s(u, y), by
          rw [SimpleGraph.mem_edgeSet]
          exact huy⟩
        have hew : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huy q) := by
          rw [mem_walkEdgeFinset_iff]
          simp [e]
        have hy : y ∈ grimmettRectangleVertices n :=
          endpoint_mem_grimmettRectangleVertices_of_edge_mem (hw hew) (by simp [e])
        have hq : walkEdgeFinset q ⊆ grimmettRectangleEdges n := by
          intro f hf
          apply hw
          rw [mem_walkEdgeFinset_iff] at hf ⊢
          simp [hf]
        exact ih hy hq z hz

/-- The left-right crossing event `A_n` from Grimmett, Lemma 11.21. -/
def grimmettRectangleCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ grimmettRectangleLeft n, ⋃ y ∈ grimmettRectangleRight n,
    connectionEventIn 2 (grimmettRectangleEdges n) x y

/-- Finite edge traces on the source rectangle which contain a left-right crossing. -/
noncomputable def grimmettRectangleCrossingTraces (n : ℕ) : Finset (Finset SquareEdge) := by
  classical
  exact (grimmettRectangleEdges n).powerset.filter fun s ↦
    s ∈ eventTrace (grimmettRectangleCrossingEvent n)

/-- Finite edge traces on the source rectangle which do not contain a left-right crossing. -/
noncomputable def grimmettRectangleNoncrossingTraces (n : ℕ) : Finset (Finset SquareEdge) := by
  classical
  exact (grimmettRectangleEdges n).powerset.filter fun s ↦
    s ∉ eventTrace (grimmettRectangleCrossingEvent n)

theorem dependsOn_grimmettRectangleCrossingEvent (n : ℕ) :
    DependsOn (grimmettRectangleEdges n) (grimmettRectangleCrossingEvent n) := by
  intro ω η hωη
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (grimmettRectangleEdges n) x y hωη).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (grimmettRectangleEdges n) x y hωη).mpr hxy⟩

theorem measurableSet_grimmettRectangleCrossingEvent (n : ℕ) :
    MeasurableSet (grimmettRectangleCrossingEvent n) :=
  (dependsOn_grimmettRectangleCrossingEvent n).measurableSet

theorem isIncreasingEvent_grimmettRectangleCrossingEvent (n : ℕ) :
    IsIncreasingEvent (grimmettRectangleCrossingEvent n) := by
  intro ω η hωη
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2 (grimmettRectangleEdges n) x y hωη hxy⟩

/-- A left-right crossing of Grimmett's rectangle reaches graph radius at least `n + 1` from
its left endpoint. -/
theorem grimmettRectangleCrossingEvent_subset_biUnion_radiusConnectionEvent (n : ℕ) :
    grimmettRectangleCrossingEvent n ⊆
      ⋃ x ∈ grimmettRectangleLeft n, radiusConnectionEvent 2 x (n + 1) := by
  intro ω hω
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion] at hω
  obtain ⟨x, hx, y, hy, hxy⟩ := hω
  refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
  obtain ⟨w, hwOpen, _hwEdges⟩ := hxy
  have hx0 := (mem_grimmettRectangleLeft_iff.mp hx).1
  have hy0 := (mem_grimmettRectangleRight_iff.mp hy).1
  have hcoord : n + 1 ≤ cubicL1Dist x y := by
    have hle := cubicL1Dist_coord_le x y (0 : Fin 2)
    rw [hx0, hy0] at hle
    simpa using hle
  exact exists_open_walk_to_cubicMetricSphere_in_ball w hwOpen hcoord

/-- Union-bound estimate used in the second proof of Grimmett, Theorem 11.11. -/
theorem grimmettRectangleCrossingProbability_le (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (grimmettRectangleCrossingEvent n) ≤
      (n + 1 : ℝ) * radiusTail 2 p (n + 1) := by
  let μ := bernoulliBondMeasure 2 p
  have hcover :=
    grimmettRectangleCrossingEvent_subset_biUnion_radiusConnectionEvent n
  calc
    μ.real (grimmettRectangleCrossingEvent n) ≤
        μ.real (⋃ x ∈ grimmettRectangleLeft n,
          radiusConnectionEvent 2 x (n + 1)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ x ∈ grimmettRectangleLeft n,
        μ.real (radiusConnectionEvent 2 x (n + 1)) :=
      measureReal_biUnion_finset_le _ _
    _ = (n + 1 : ℝ) * radiusTail 2 p (n + 1) := by
      dsimp [μ]
      simp_rw [bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail]
      simp [card_grimmettRectangleLeft]

/-- The vanishing half-density conclusion of Grimmett, Lemma 11.12 gives the lower half of the
exact critical-probability calculation. -/
theorem half_le_cubicCriticalProbability_two_of_theta_half_eq_zero
    (hθ : theta 2 squareHalfDensity = 0) :
    1 / 2 ≤ cubicCriticalProbability 2 := by
  simpa using coe_le_cubicCriticalProbability_of_theta_eq_zero hθ

private theorem tendsto_nat_succ_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * Real.exp (-c * (n + 1))) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscale : Tendsto (fun n : ℕ ↦ c * (n + 1 : ℝ)) atTop atTop :=
    hcast.const_mul_atTop hc
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hmul : Tendsto
      (fun n : ℕ ↦ c⁻¹ * ((c * (n + 1 : ℝ)) ^ 1 * Real.exp (-(c * (n + 1)))))
      atTop (nhds (c⁻¹ * 0)) :=
    tendsto_const_nhds.mul hbase
  convert hmul using 1
  · funext n
    field_simp [hc.ne']
  · simp

/-- If Grimmett's finite rectangles have a uniform half-density crossing lower bound, then the
square-lattice critical probability is at most `1 / 2`. This is the analytic half of the second
proof of Theorem 11.11; planar duality supplies the hypothesis with equality. -/
theorem cubicCriticalProbability_two_le_half_of_crossingProbability
    (hcross : ∀ n : ℕ,
      1 / 2 ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n)) :
    cubicCriticalProbability 2 ≤ 1 / 2 := by
  by_contra hpc
  have hhalfpc : (squareHalfDensity : ℝ) < cubicCriticalProbability 2 := by
    rw [coe_squareHalfDensity]
    exact lt_of_not_ge hpc
  obtain ⟨c, hc, hdecay⟩ :=
    radiusTail_exponential_decay_of_lt_critical 2 (by omega) squareHalfDensity hhalfpc
  have hlim := tendsto_nat_succ_mul_exp_neg_mul c hc
  have hevent : ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ) * Real.exp (-c * (n + 1)) < 1 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have hN' := hN N le_rfl
  have htail := hdecay (N + 1)
  have htail' :
      radiusTail 2 squareHalfDensity (N + 1) ≤ Real.exp (-c * (N + 1 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htail
  have hcontra : (1 / 2 : ℝ) < 1 / 2 := by
    calc
      (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (grimmettRectangleCrossingEvent N) := hcross N
      _ ≤ (N + 1 : ℝ) * radiusTail 2 squareHalfDensity (N + 1) :=
        grimmettRectangleCrossingProbability_le squareHalfDensity N
      _ ≤ (N + 1 : ℝ) * Real.exp (-c * (N + 1)) := by
        exact mul_le_mul_of_nonneg_left htail' (by positivity)
      _ < 1 / 2 := hN'
  exact (lt_irrefl _ hcontra)

end Percolation
