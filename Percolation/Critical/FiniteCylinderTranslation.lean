import Percolation.Critical.Translation
import Percolation.Critical.BoxRadius
import Percolation.Bernoulli.FKGInfinite

/-!
# Translated supports of finite bond cylinders

Every finite set of cubic edges fits in a coordinate box.  Translating such a support from the
origin to `x` keeps it inside the box with the same radius centered at `x`.  These facts are the
geometric input for finite-range covariance estimates of translated cylinder events.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The least convenient box radius obtained by taking the supremum of the distances of both
endpoints of every edge in `E`. -/
noncomputable def cubicEdgeSetRadius {d : ℕ} (E : Finset (CubicEdge d)) : ℕ :=
  E.sup fun e ↦ max (cubicLInfDist cubicOrigin e.1.out.1)
    (cubicLInfDist cubicOrigin e.1.out.2)

theorem endpoint_mem_cubicMetricBox_edgeSetRadius {d : ℕ}
    (E : Finset (CubicEdge d)) {e : CubicEdge d} (he : e ∈ E)
    {z : Cubic d} (hz : z ∈ (e : Sym2 (Cubic d))) :
    z ∈ cubicMetricBox d cubicOrigin (cubicEdgeSetRadius E) := by
  rw [mem_cubicMetricBox_iff_lInfDist_le]
  rw [← e.1.out_eq] at hz
  change z ∈ s(e.1.out.1, e.1.out.2) at hz
  rw [Sym2.mem_iff] at hz
  have hsup : max (cubicLInfDist cubicOrigin e.1.out.1)
      (cubicLInfDist cubicOrigin e.1.out.2) ≤ cubicEdgeSetRadius E := by
    exact Finset.le_sup (f := fun f : CubicEdge d ↦
      max (cubicLInfDist cubicOrigin f.1.out.1)
        (cubicLInfDist cubicOrigin f.1.out.2)) he
  rcases hz with rfl | rfl
  · exact (Nat.le_max_left _ _).trans hsup
  · exact (Nat.le_max_right _ _).trans hsup

/-- An edge whose two endpoints lie in a coordinate box belongs to the explicit internal edge
support of that box. -/
theorem mem_cubicBoxEdges_of_endpoints {d n : ℕ} {x : Cubic d}
    {e : CubicEdge d}
    (hends : ∀ z ∈ (e : Sym2 (Cubic d)), z ∈ cubicMetricBox d x n) :
    e ∈ cubicBoxEdges d x n := by
  let u := e.1.out.1
  let v := e.1.out.2
  have hadj : (cubicGraph d).Adj u v := by
    change (cubicGraph d).Adj e.1.out.1 e.1.out.2
    exact (SimpleGraph.mem_edgeSet (cubicGraph d)).mp (by simpa [e.1.out_eq] using e.2)
  obtain ⟨a, hva⟩ := (cubicGraph_adj_iff_exists_stepFrom u v).mp hadj
  have hu : u ∈ cubicMetricBox d x n := hends u (by
    change e.1.out.1 ∈ (e : Sym2 (Cubic d))
    exact Sym2.out_fst_mem e.1)
  have hv : v ∈ cubicMetricBox d x n := hends v (by
    change e.1.out.2 ∈ (e : Sym2 (Cubic d))
    exact Sym2.out_snd_mem e.1)
  have heq : e = cubicStepEdge u a := by
    apply Subtype.ext
    change (e : Sym2 (Cubic d)) = s(u, cubicStepFrom u a)
    rw [← hva]
    exact e.1.out_eq.symm
  rw [heq]
  exact cubicStepEdge_mem_cubicBoxEdges hu (by simpa [hva] using hv)

theorem cubicEdgeSet_subset_cubicBoxEdges_radius {d : ℕ}
    (E : Finset (CubicEdge d)) :
    E ⊆ cubicBoxEdges d cubicOrigin (cubicEdgeSetRadius E) := by
  intro e he
  exact mem_cubicBoxEdges_of_endpoints fun z hz ↦
    endpoint_mem_cubicMetricBox_edgeSetRadius E he hz

theorem cubicTranslate_mem_cubicMetricBox_iff {d n : ℕ}
    (x y z : Cubic d) :
    cubicTranslate x y z ∈ cubicMetricBox d y n ↔
      z ∈ cubicMetricBox d x n := by
  rw [mem_cubicMetricBox_iff_lInfDist_le, mem_cubicMetricBox_iff_lInfDist_le]
  rw [show cubicLInfDist y (cubicTranslate x y z) = cubicLInfDist x z by
    simpa using cubicLInfDist_translate x y x z]

/-- The image of an internal box edge under a cubic translation remains an internal edge of
the translated box. -/
theorem cubicTranslation_mapEdgeSet_mem_cubicBoxEdges {d n : ℕ}
    (x y : Cubic d) {e : CubicEdge d}
    (he : e ∈ cubicBoxEdges d x n) :
    (cubicTranslationIso x y).mapEdgeSet e ∈ cubicBoxEdges d y n := by
  apply mem_cubicBoxEdges_of_endpoints
  intro z hz
  have hzImage : ∃ w ∈ (e : Sym2 (Cubic d)), z = cubicTranslate x y w := by
    change z ∈ Sym2.map (cubicTranslate x y) (e : Sym2 (Cubic d)) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    exact ⟨w, hw, hwz.symm⟩
  obtain ⟨w, hw, rfl⟩ := hzImage
  apply (cubicTranslate_mem_cubicMetricBox_iff x y w).2
  exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges he hw

/-- The translated image of an arbitrary finite support lies in a same-radius translated box. -/
theorem cubicTranslation_image_edgeSet_subset_box {d : ℕ}
    (E : Finset (CubicEdge d)) (x : Cubic d) :
    E.image (cubicTranslationIso cubicOrigin x).mapEdgeSet ⊆
      cubicBoxEdges d x (cubicEdgeSetRadius E) := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact cubicTranslation_mapEdgeSet_mem_cubicBoxEdges cubicOrigin x
    (cubicEdgeSet_subset_cubicBoxEdges_radius E hf)

/-- Coordinate boxes whose centers are more than twice the radius apart have disjoint internal
edge supports. -/
theorem disjoint_cubicBoxEdges_of_two_mul_lt_lInfDist {d n : ℕ}
    {x y : Cubic d} (hxy : 2 * n < cubicLInfDist x y) :
    Disjoint (cubicBoxEdges d x n) (cubicBoxEdges d y n) := by
  classical
  rw [Finset.disjoint_left]
  intro e hex hey
  let z := e.1.out.1
  have hzx : z ∈ cubicMetricBox d x n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hex (by
      change e.1.out.1 ∈ (e : Sym2 (Cubic d))
      exact Sym2.out_fst_mem e.1)
  have hzy : z ∈ cubicMetricBox d y n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hey (by
      change e.1.out.1 ∈ (e : Sym2 (Cubic d))
      exact Sym2.out_fst_mem e.1)
  have hdist := cubicLInfDist_triangle x z y
  have hxz := mem_cubicMetricBox_iff_lInfDist_le.mp hzx
  have hzy' := mem_cubicMetricBox_iff_lInfDist_le.mp hzy
  have hzy'' : cubicLInfDist z y ≤ n := by
    rw [cubicLInfDist_comm]
    exact hzy'
  omega

theorem disjoint_cubicTranslation_image_edgeSets_of_far {d : ℕ}
    (E : Finset (CubicEdge d)) {x y : Cubic d}
    (hxy : 2 * cubicEdgeSetRadius E < cubicLInfDist x y) :
    Disjoint
      (E.image (cubicTranslationIso cubicOrigin x).mapEdgeSet)
      (E.image (cubicTranslationIso cubicOrigin y).mapEdgeSet) := by
  apply Disjoint.mono
    (cubicTranslation_image_edgeSet_subset_box E x)
    (cubicTranslation_image_edgeSet_subset_box E y)
  exact disjoint_cubicBoxEdges_of_two_mul_lt_lInfDist hxy

/-- Translate an origin-based bond event to the box centered at `x`. -/
def translatedCylinderEvent {d : ℕ} (x : Cubic d)
    (A : Set (EdgeConfiguration d)) : Set (EdgeConfiguration d) :=
  cubicTranslationConfigurationPullback cubicOrigin x ⁻¹' A

theorem dependsOn_translatedCylinderEvent {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (x : Cubic d) :
    DependsOn (E.image (cubicTranslationIso cubicOrigin x).mapEdgeSet)
      (translatedCylinderEvent x A) := by
  intro ω η hagree
  apply hA
  intro e he
  apply hagree ((cubicTranslationIso cubicOrigin x).mapEdgeSet e)
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem measurableSet_translatedCylinderEvent {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (x : Cubic d) :
    MeasurableSet (translatedCylinderEvent x A) :=
  (dependsOn_translatedCylinderEvent hA x).measurableSet

/-- Translation preserves measurability even when the event is not finitely supported. -/
theorem measurableSet_translatedCylinderEvent_of_measurable {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (x : Cubic d) :
    MeasurableSet (translatedCylinderEvent x A) :=
  hA.preimage (measurable_cubicTranslationConfigurationPullback cubicOrigin x)

/-- Bernoulli bond measure is invariant under translating any measurable event.  The
finite-cylinder theorem below is the specialization used by the finite-range field. -/
theorem bernoulliBondMeasure_real_translatedEvent {d : ℕ}
    {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A) (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (translatedCylinderEvent x A) =
      (bernoulliBondMeasure d p).real A := by
  let T := cubicTranslationConfigurationPullback cubicOrigin x
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ.real A)
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p cubicOrigin x)
  change (Measure.map T (bernoulliBondMeasure d p)).real A =
    (bernoulliBondMeasure d p).real A at hmap
  rw [map_measureReal_apply
    (measurable_cubicTranslationConfigurationPullback cubicOrigin x) hA] at hmap
  exact hmap

/-- Every translate of a finite cylinder has the same Bernoulli probability. -/
theorem bernoulliBondMeasure_real_translatedCylinderEvent {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (translatedCylinderEvent x A) =
    (bernoulliBondMeasure d p).real A :=
  bernoulliBondMeasure_real_translatedEvent hA.measurableSet p x

theorem dependsOn_translatedCylinderEvent_box {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (x : Cubic d) :
    DependsOn (cubicBoxEdges d x (cubicEdgeSetRadius E))
      (translatedCylinderEvent x A) :=
  (dependsOn_translatedCylinderEvent hA x).mono
    (cubicTranslation_image_edgeSet_subset_box E x)

end Percolation
