import Percolation.Extensions.ContinuumCubes
import Percolation.Extensions.ContinuumGeometry
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# A concrete marked Poisson construction of the Boolean model

Independent Poisson counts on unit cubes, together with independent uniform marks inside each
cube, give a literal homogeneous Poisson point process.  Unlike the occupation-only
discretization, this sample space retains the point locations needed by the Boolean graph.

The endpoint `1` of the unit-interval mark has probability zero.  We send that single value to
the left face of the half-open cube, making cube membership true for every sample rather than
only almost surely.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal unitInterval

/-- One uniform coordinate vector in the unit cube. -/
abbrev ContinuumUnitMark (d : ℕ) := Fin d → I

/-- An infinite supply of marks, of which the first Poisson-many are active. -/
abbrev ContinuumMarkStream (d : ℕ) := ℕ → ContinuumUnitMark d

/-- A unit-cube sample consists of its Poisson count and an independent mark stream. -/
abbrev ContinuumCubeSample (d : ℕ) := ℕ × ContinuumMarkStream d

/-- One marked unit-cube sample at every integer cube. -/
abbrev ContinuumPoissonConfiguration (d : ℕ) := Cubic d → ContinuumCubeSample d

/-- Product Lebesgue law on a finite-dimensional unit cube. -/
noncomputable def continuumUnitMarkMeasure (d : ℕ) : Measure (ContinuumUnitMark d) :=
  Measure.infinitePi fun _ : Fin d ↦ (volume : Measure I)

instance continuumUnitMarkMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (continuumUnitMarkMeasure d) := by
  unfold continuumUnitMarkMeasure
  infer_instance

/-- Iid uniform unit-cube marks. -/
noncomputable def continuumMarkStreamMeasure (d : ℕ) : Measure (ContinuumMarkStream d) :=
  Measure.infinitePi fun _ : ℕ ↦ continuumUnitMarkMeasure d

instance continuumMarkStreamMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (continuumMarkStreamMeasure d) := by
  unfold continuumMarkStreamMeasure
  infer_instance

/-- A Poisson count of rate `lambda`, independent of its mark stream. -/
noncomputable def continuumCubeSampleMeasure (d : ℕ) (intensity : ℝ≥0) :
    Measure (ContinuumCubeSample d) :=
  (poissonMeasure intensity).prod (continuumMarkStreamMeasure d)

instance continuumCubeSampleMeasure_isProbabilityMeasure (d : ℕ) (intensity : ℝ≥0) :
    IsProbabilityMeasure (continuumCubeSampleMeasure d intensity) := by
  unfold continuumCubeSampleMeasure
  infer_instance

/-- The concrete homogeneous marked Poisson law of intensity `lambda`. -/
noncomputable def continuumPoissonMeasure (d : ℕ) (intensity : ℝ≥0) :
    Measure (ContinuumPoissonConfiguration d) :=
  Measure.infinitePi fun _ : Cubic d ↦ continuumCubeSampleMeasure d intensity

instance continuumPoissonMeasure_isProbabilityMeasure (d : ℕ) (intensity : ℝ≥0) :
    IsProbabilityMeasure (continuumPoissonMeasure d intensity) := by
  unfold continuumPoissonMeasure
  infer_instance

/-- Forget the marks and retain the unit-cube Poisson counts. -/
def continuumPoissonCubeCounts {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : PoissonCubeConfiguration d :=
  fun x ↦ (Xi x).1

theorem measurable_continuumPoissonCubeCounts {d : ℕ} :
    Measurable (continuumPoissonCubeCounts :
      ContinuumPoissonConfiguration d → PoissonCubeConfiguration d) := by
  exact measurable_pi_lambda _ fun x ↦
    measurable_fst.comp (measurable_pi_apply x)

/-- The count marginal of the marked construction is exactly the cube-count law already used
for (12.38), at unit mesh. -/
theorem continuumPoissonMeasure_map_cubeCounts (d : ℕ) (intensity : ℝ≥0) :
    (continuumPoissonMeasure d intensity).map continuumPoissonCubeCounts =
      poissonCubeMeasure d intensity 1 := by
  unfold continuumPoissonMeasure continuumPoissonCubeCounts poissonCubeMeasure
  rw [Measure.infinitePi_map_pi]
  · congrm Measure.infinitePi fun x ↦ ?_
    simp [continuumCubeSampleMeasure, continuumCubeRate]
  · intro x
    fun_prop

/-- A unit-interval mark represented in the half-open centered interval `[-1/2,1/2)`. -/
noncomputable def continuumCenteredUnitMark (a : I) : ℝ :=
  if (a : ℝ) = 1 then -1 / 2 else (a : ℝ) - 1 / 2

theorem continuumCenteredUnitMark_mem_Ico (a : I) :
    continuumCenteredUnitMark a ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  unfold continuumCenteredUnitMark
  split_ifs with ha
  · constructor <;> norm_num
  · have ha0 : 0 ≤ (a : ℝ) := a.2.1
    have ha1 : (a : ℝ) < 1 := lt_of_le_of_ne a.2.2 ha
    constructor <;> linarith

theorem measurable_continuumCenteredUnitMark : Measurable continuumCenteredUnitMark := by
  unfold continuumCenteredUnitMark
  apply Measurable.ite
  · have hset : {a : I | (a : ℝ) = 1} = {1} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro ha
        apply Subtype.ext
        simpa using ha
      · rintro rfl
        norm_num
    rw [hset]
    exact measurableSet_singleton 1
  · exact measurable_const
  · exact continuous_subtype_val.measurable.sub measurable_const

/-- Spatial location of a potential marked point. -/
noncomputable def continuumPoissonPoint {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) (a : Cubic d × ℕ) : ContinuumPoint d :=
  fun i ↦ (a.1 i : ℝ) + continuumCenteredUnitMark ((Xi a.1).2 a.2 i)

theorem measurable_continuumPoissonPoint {d : ℕ} (a : Cubic d × ℕ) :
    Measurable (fun Xi : ContinuumPoissonConfiguration d ↦ continuumPoissonPoint Xi a) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.add <| measurable_continuumCenteredUnitMark.comp <|
    measurable_pi_apply i |>.comp <| measurable_pi_apply a.2 |>.comp <|
      measurable_snd.comp (measurable_pi_apply a.1)

/-- A potential mark is active exactly when its index is below the cube's Poisson count. -/
def continuumPoissonPointActive {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) (a : Cubic d × ℕ) : Prop :=
  a.2 < (Xi a.1).1

theorem measurableSet_continuumPoissonPointActive {d : ℕ} (a : Cubic d × ℕ) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d |
      continuumPoissonPointActive Xi a} := by
  exact (measurable_fst.comp (measurable_pi_apply a.1))
    (measurableSet_Ioi : MeasurableSet (Set.Ioi a.2))

/-- Countable active index set of the Poisson realization. -/
def continuumActivePointIndices {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : Set (Cubic d × ℕ) :=
  {a | continuumPoissonPointActive Xi a}

/-- Spatial point set of the realization.  The indexed graph below remains the primary object,
so the null event of two identical marks does not silently merge vertices. -/
noncomputable def continuumPoissonPointSet {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : Set (ContinuumPoint d) :=
  continuumPoissonPoint Xi '' continuumActivePointIndices Xi

/-- Every potential point is placed in the half-open unit cube recorded by its first index. -/
theorem continuumPoissonPoint_mem_unitCube {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) (a : Cubic d × ℕ) :
    continuumPoissonPoint Xi a ∈ continuumElementaryCube 1 a.1 := by
  intro i
  obtain ⟨hi0, hi1⟩ := continuumCenteredUnitMark_mem_Ico ((Xi a.1).2 a.2 i)
  simp only [continuumCubeCenter, continuumPoissonPoint, Nat.cast_one, div_one,
    mul_one]
  constructor <;> linarith

/-- The radius-one Boolean graph on active marked indices. -/
noncomputable def continuumPoissonGraph {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) :
    SimpleGraph (continuumActivePointIndices Xi) where
  Adj a b := a ≠ b ∧
    coordinateEuclideanDist (continuumPoissonPoint Xi a.1)
      (continuumPoissonPoint Xi b.1) ≤ 2
  symm := by
    rintro a b ⟨hab, hdist⟩
    exact ⟨hab.symm, (coordinateEuclideanDist_comm _ _).le.trans hdist⟩
  loopless := ⟨fun a h ↦ h.1 rfl⟩

@[simp]
theorem continuumPoissonGraph_adj {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    {a b : continuumActivePointIndices Xi} :
    (continuumPoissonGraph Xi).Adj a b ↔ a ≠ b ∧
      coordinateEuclideanDist (continuumPoissonPoint Xi a.1)
        (continuumPoissonPoint Xi b.1) ≤ 2 :=
  Iff.rfl

/-- The same Boolean graph on the fixed countable type of all potential indices.  Inactive
indices are isolated.  This encoding is used for event measurability. -/
noncomputable def continuumPoissonAmbientGraph {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) : SimpleGraph (Cubic d × ℕ) where
  Adj a b := a ≠ b ∧ continuumPoissonPointActive Xi a ∧
    continuumPoissonPointActive Xi b ∧
      coordinateEuclideanDist (continuumPoissonPoint Xi a)
        (continuumPoissonPoint Xi b) ≤ 2
  symm := by
    rintro a b ⟨hab, ha, hb, hdist⟩
    exact ⟨hab.symm, hb, ha, (coordinateEuclideanDist_comm _ _).le.trans hdist⟩
  loopless := ⟨fun a h ↦ h.1 rfl⟩

@[simp]
theorem continuumPoissonAmbientGraph_adj {d : ℕ}
    {Xi : ContinuumPoissonConfiguration d} {a b : Cubic d × ℕ} :
    (continuumPoissonAmbientGraph Xi).Adj a b ↔
      a ≠ b ∧ continuumPoissonPointActive Xi a ∧
        continuumPoissonPointActive Xi b ∧
          coordinateEuclideanDist (continuumPoissonPoint Xi a)
            (continuumPoissonPoint Xi b) ≤ 2 :=
  Iff.rfl

theorem measurable_coordinateEuclideanDist_continuumPoissonPoint {d : ℕ}
    (a b : Cubic d × ℕ) :
    Measurable (fun Xi : ContinuumPoissonConfiguration d ↦
      coordinateEuclideanDist (continuumPoissonPoint Xi a)
        (continuumPoissonPoint Xi b)) := by
  unfold coordinateEuclideanDist
  apply Measurable.sqrt
  simpa using Finset.measurable_sum Finset.univ fun i _hi ↦
    (((measurable_pi_apply i).comp (measurable_continuumPoissonPoint a)).sub
      ((measurable_pi_apply i).comp (measurable_continuumPoissonPoint b))).pow_const 2

theorem measurableSet_continuumPoissonAmbientGraph_adj {d : ℕ}
    (a b : Cubic d × ℕ) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d |
      (continuumPoissonAmbientGraph Xi).Adj a b} := by
  by_cases hab : a = b
  · subst b
    simp
  · rw [show {Xi : ContinuumPoissonConfiguration d |
        (continuumPoissonAmbientGraph Xi).Adj a b} =
        {Xi | continuumPoissonPointActive Xi a} ∩
          {Xi | continuumPoissonPointActive Xi b} ∩
            {Xi | coordinateEuclideanDist (continuumPoissonPoint Xi a)
              (continuumPoissonPoint Xi b) ≤ 2} by
      ext Xi
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
        continuumPoissonAmbientGraph_adj, hab, not_false_eq_true, true_and]
      tauto]
    exact (measurableSet_continuumPoissonPointActive a).inter
      (measurableSet_continuumPoissonPointActive b) |>.inter
        (measurable_coordinateEuclideanDist_continuumPoissonPoint a b measurableSet_Iic)

/-- Fixed-endpoint connectivity event in the marked Boolean graph. -/
def continuumPoissonConnectionEvent {d : ℕ} (a b : Cubic d × ℕ) :
    Set (ContinuumPoissonConfiguration d) :=
  {Xi | (continuumPoissonAmbientGraph Xi).Reachable a b}

private theorem measurableSet_continuumPoissonListIsChain {d : ℕ}
    (l : List (Cubic d × ℕ)) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d |
      l.IsChain (continuumPoissonAmbientGraph Xi).Adj} := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          simp only [List.isChain_cons_cons]
          exact (measurableSet_continuumPoissonAmbientGraph_adj a b).inter ih

theorem measurableSet_continuumPoissonConnectionEvent {d : ℕ}
    (a b : Cubic d × ℕ) :
    MeasurableSet (continuumPoissonConnectionEvent a b) := by
  classical
  have hrepr : continuumPoissonConnectionEvent a b =
      ⋃ l : List (Cubic d × ℕ),
        if ∃ hne : l ≠ [], l.head hne = a ∧ l.getLast hne = b then
          {Xi | l.IsChain (continuumPoissonAmbientGraph Xi).Adj}
        else ∅ := by
    ext Xi
    constructor
    · rintro ⟨w⟩
      refine Set.mem_iUnion.mpr ⟨w.support, ?_⟩
      have hne : w.support ≠ [] := w.support_ne_nil
      rw [if_pos]
      · exact w.isChain_adj_support
      · exact ⟨hne, w.head_support, w.getLast_support⟩
    · intro hXi
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hXi
      split_ifs at hl with hgood
      · obtain ⟨hne, hhead, hlast⟩ := hgood
        exact ⟨(SimpleGraph.Walk.ofSupport l hne hl).copy hhead hlast⟩
      · exact hl.elim
  rw [hrepr]
  exact MeasurableSet.iUnion fun l ↦ by
    split_ifs
    · exact measurableSet_continuumPoissonListIsChain l
    · exact MeasurableSet.empty

/-- Existence of an infinite component in the concrete Boolean graph. -/
def continuumPoissonPercolates {d : ℕ} (Xi : ContinuumPoissonConfiguration d) : Prop :=
  ∃ a : Cubic d × ℕ,
    {b | (continuumPoissonAmbientGraph Xi).Reachable a b}.Infinite

theorem measurableSet_continuumPoissonPercolates (d : ℕ) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d | continuumPoissonPercolates Xi} := by
  classical
  have hrepr : {Xi : ContinuumPoissonConfiguration d | continuumPoissonPercolates Xi} =
      ⋃ a : Cubic d × ℕ, ⋂ s : Finset (Cubic d × ℕ),
        ⋃ b : Cubic d × ℕ, ⋃ (_hb : b ∉ s), continuumPoissonConnectionEvent a b := by
    ext Xi
    simp only [Set.mem_setOf_eq, continuumPoissonPercolates, Set.mem_iUnion,
      Set.mem_iInter, continuumPoissonConnectionEvent]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, fun s ↦ ?_⟩
      obtain ⟨b, hbReach, hbNot⟩ := ha.exists_notMem_finset s
      exact ⟨b, hbNot, hbReach⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨b, hbNot, hbReach⟩ := ha hfinite.toFinset
      exact hbNot (hfinite.mem_toFinset.mpr hbReach)
  rw [hrepr]
  exact MeasurableSet.iUnion fun a ↦ MeasurableSet.iInter fun s ↦
    MeasurableSet.iUnion fun b ↦ MeasurableSet.iUnion fun _hb ↦
      measurableSet_continuumPoissonConnectionEvent a b

/-- The spatial origin in the coordinate representation. -/
def continuumSpatialOrigin (d : ℕ) : ContinuumPoint d := fun _ ↦ 0

/-- A marked sphere belongs to the Boolean cluster at the spatial origin when its centre is at
distance at most one from the origin. -/
def continuumPoissonPointCoversOrigin {d : ℕ}
    (Xi : ContinuumPoissonConfiguration d) (a : Cubic d × ℕ) : Prop :=
  continuumPoissonPointActive Xi a ∧
    coordinateEuclideanDist (continuumPoissonPoint Xi a)
      (continuumSpatialOrigin d) ≤ 1

theorem measurable_coordinateEuclideanDist_continuumPoissonPoint_origin {d : ℕ}
    (a : Cubic d × ℕ) :
    Measurable (fun Xi : ContinuumPoissonConfiguration d ↦
      coordinateEuclideanDist (continuumPoissonPoint Xi a)
        (continuumSpatialOrigin d)) := by
  unfold coordinateEuclideanDist
  apply Measurable.sqrt
  simpa using Finset.measurable_sum Finset.univ fun i _hi ↦
    (((measurable_pi_apply i).comp (measurable_continuumPoissonPoint a)).sub
      measurable_const).pow_const 2

theorem measurableSet_continuumPoissonPointCoversOrigin {d : ℕ}
    (a : Cubic d × ℕ) :
    MeasurableSet {Xi : ContinuumPoissonConfiguration d |
      continuumPoissonPointCoversOrigin Xi a} := by
  exact (measurableSet_continuumPoissonPointActive a).inter
    (measurable_coordinateEuclideanDist_continuumPoissonPoint_origin a measurableSet_Iic)

/-- Event that a fixed potential point is active and lies in an infinite Boolean component. -/
def continuumPoissonInfiniteClusterAt {d : ℕ} (a : Cubic d × ℕ) :
    Set (ContinuumPoissonConfiguration d) :=
  {Xi | continuumPoissonPointActive Xi a ∧
    {b | (continuumPoissonAmbientGraph Xi).Reachable a b}.Infinite}

theorem measurableSet_continuumPoissonInfiniteClusterAt {d : ℕ}
    (a : Cubic d × ℕ) :
    MeasurableSet (continuumPoissonInfiniteClusterAt a) := by
  classical
  have hrepr : continuumPoissonInfiniteClusterAt a =
      {Xi | continuumPoissonPointActive Xi a} ∩
        ⋂ s : Finset (Cubic d × ℕ),
          ⋃ b : Cubic d × ℕ, ⋃ (_hb : b ∉ s),
            continuumPoissonConnectionEvent a b := by
    ext Xi
    simp only [continuumPoissonInfiniteClusterAt, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
      continuumPoissonConnectionEvent]
    constructor
    · rintro ⟨ha, hinfinite⟩
      refine ⟨ha, fun s ↦ ?_⟩
      obtain ⟨b, hbReach, hbNot⟩ := hinfinite.exists_notMem_finset s
      exact ⟨b, hbNot, hbReach⟩
    · rintro ⟨ha, houtside⟩
      refine ⟨ha, ?_⟩
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨b, hbNot, hbReach⟩ := houtside hfinite.toFinset
      exact hbNot (hfinite.mem_toFinset.mpr hbReach)
  rw [hrepr]
  exact (measurableSet_continuumPoissonPointActive a).inter <|
    MeasurableSet.iInter fun s ↦ MeasurableSet.iUnion fun b ↦
      MeasurableSet.iUnion fun _hb ↦
        measurableSet_continuumPoissonConnectionEvent a b

/-- Event `|W(0)| = ∞` from (12.34): some sphere covering the spatial origin belongs to an
infinite cluster.  Any two spheres covering the origin intersect, so this is exactly the
infinite-cluster event for the cluster `W(0)` defined in the source. -/
def continuumOriginPercolatesEvent (d : ℕ) :
    Set (ContinuumPoissonConfiguration d) :=
  {Xi | ∃ a : Cubic d × ℕ,
    continuumPoissonPointCoversOrigin Xi a ∧
      Xi ∈ continuumPoissonInfiniteClusterAt a}

theorem measurableSet_continuumOriginPercolatesEvent (d : ℕ) :
    MeasurableSet (continuumOriginPercolatesEvent d) := by
  rw [show continuumOriginPercolatesEvent d =
      ⋃ a : Cubic d × ℕ,
        {Xi | continuumPoissonPointCoversOrigin Xi a} ∩
          continuumPoissonInfiniteClusterAt a by
    ext Xi
    simp [continuumOriginPercolatesEvent]]
  exact MeasurableSet.iUnion fun a ↦
    (measurableSet_continuumPoissonPointCoversOrigin a).inter
      (measurableSet_continuumPoissonInfiniteClusterAt a)

theorem continuumPoissonPercolates_of_mem_continuumOriginPercolatesEvent
    {d : ℕ} {Xi : ContinuumPoissonConfiguration d}
    (hXi : Xi ∈ continuumOriginPercolatesEvent d) :
    continuumPoissonPercolates Xi := by
  obtain ⟨a, _haCover, _haActive, haInfinite⟩ := hXi
  exact ⟨a, haInfinite⟩

/-- Boolean-model percolation probability, equation (12.34), for the concrete marked Poisson
construction. -/
noncomputable def continuumTheta (d : ℕ) (intensity : ℝ≥0) : ℝ :=
  (continuumPoissonMeasure d intensity).real
    (continuumOriginPercolatesEvent d)

end Percolation
