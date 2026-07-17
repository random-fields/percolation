import Percolation.Bernoulli.FKGInfinite
import Percolation.Critical.SupercriticalTruncatedConnectivity

/-!
# Gluing finite clusters into a truncated axis connection

This file formalizes the local finite-energy surgery in equations (8.58)--(8.60) of
Grimmett.  The surgery is represented by `spliceOn`: on the finite star of the separating
vertex, two axial edges are prescribed open and all remaining incident edges are prescribed
closed.  The first lemma below isolates the measure-theoretic comparison, independently of
the later cubic geometry.
-/

namespace Percolation

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval BigOperators

/-- Finite-energy overwrite comparison.  If overwriting the coordinates in `E` with trace
`s` sends every configuration in `A` into `B`, then the Bernoulli weight of that trace times
`P(A)` is at most `P(B)`.

This is the rigorous product-measure form of the local-modification arguments used throughout
Grimmett.  It is deliberately ratio-free, so it also behaves correctly at zero-probability
events. -/
theorem finiteBernoulliWeight_mul_measureReal_le_of_splice_subset
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (p : I) {E s : Finset ι} (hs : s ⊆ E)
    {A B : Set (Set ι)} (hB : MeasurableSet B)
    (hsplice : A ⊆ (fun omega => spliceOn E s omega) ⁻¹' B) :
    finiteBernoulliWeight E (p : ℝ) s *
        setBer((Set.univ : Set ι), p).real A ≤
      setBer((Set.univ : Set ι), p).real B := by
  have hmono :
      setBer((Set.univ : Set ι), p).real A ≤
        setBer((Set.univ : Set ι), p).real
          ((fun omega => spliceOn E s omega) ⁻¹' B) :=
    measureReal_mono hsplice
  have hfactor := setBernoulli_real_inter_finiteCylinder
    (ι := ι) p hs hB
  calc
    finiteBernoulliWeight E (p : ℝ) s *
        setBer((Set.univ : Set ι), p).real A ≤
        finiteBernoulliWeight E (p : ℝ) s *
          setBer((Set.univ : Set ι), p).real
            ((fun omega => spliceOn E s omega) ⁻¹' B) := by
      exact mul_le_mul_of_nonneg_left hmono
        (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)
    _ = setBer((Set.univ : Set ι), p).real
          (B ∩ finiteCylinder E s) := by
      rw [hfactor, mul_comm]
    _ ≤ setBer((Set.univ : Set ι), p).real B :=
      measureReal_mono Set.inter_subset_left

/-! ### The two separated endpoint events -/

/-- Vertices in the origin box lying on or to the positive side of the first-coordinate
hyperplane through the origin.  An anchored animal of first-coordinate span `m` is contained
in this finite region. -/
noncomputable def firstCoordinateAnchoredBox
    (d : ℕ) (hd : 0 < d) (m : ℕ) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBox d cubicOrigin m).filter
    (fun x => 0 ≤ x ⟨0, hd⟩)

/-- All bonds incident to the finite positive-first-coordinate box. -/
noncomputable def firstCoordinateAnchoredSupport
    (d : ℕ) (hd : 0 < d) (m : ℕ) : Finset (CubicEdge d) :=
  cubicIncidentEdges d (firstCoordinateAnchoredBox d hd m)

/-- Reflection of the first coordinate followed by translation to `(2m+2)e₁`.  It maps
`0` to `(2m+2)e₁` and a rightmost point `x` with `x₁=m` to `x+2e₁`. -/
def finiteClusterAxisMirrorIso
    (d : ℕ) (hd : 0 < d) (m : ℕ) : cubicGraph d ≃g cubicGraph d :=
  (cubicCoordinateReflectionIso (⟨0, hd⟩ : Fin d)).trans
    (cubicTranslationIso cubicOrigin (cubicAxisVertex d (2 * m + 2)))

theorem finiteClusterAxisMirrorIso_apply
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) (j : Fin d) :
    finiteClusterAxisMirrorIso d hd m x j =
      if j = (⟨0, hd⟩ : Fin d) then (2 * m + 2 : ℤ) - x j else x j := by
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisMirrorIso, cubicCoordinateReflectionIso,
      cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateReflectionEquiv, cubicAxisVertex, cubicOrigin]
    ring
  · have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      simpa using h0
    simp [finiteClusterAxisMirrorIso, cubicCoordinateReflectionIso,
      cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateReflectionEquiv, cubicAxisVertex, cubicOrigin, hj, hj0]

@[simp]
theorem finiteClusterAxisMirrorIso_origin
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    finiteClusterAxisMirrorIso d hd m cubicOrigin =
      cubicAxisVertex d (2 * m + 2) := by
  ext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisMirrorIso_apply, cubicAxisVertex, cubicOrigin]
  · have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      simpa using h0
    simp [finiteClusterAxisMirrorIso_apply, cubicAxisVertex, cubicOrigin, hj, hj0]

theorem finiteClusterAxisMirrorIso_rightEndpoint
    {d m : ℕ} (hd : 0 < d) {x : Cubic d}
    (hx : x ⟨0, hd⟩ = (m : ℤ)) :
    finiteClusterAxisMirrorIso d hd m x =
      cubicStepFrom (cubicStepFrom x ((⟨0, hd⟩ : Fin d), true))
        ((⟨0, hd⟩ : Fin d), true) := by
  ext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisMirrorIso_apply, cubicStepFrom,
      cubicDirectionIncrement, hx]
    omega
  · simp [finiteClusterAxisMirrorIso_apply, cubicStepFrom,
      cubicDirectionIncrement, hj]

/-- Extract the concrete animal from the bounded variable-size anchored family. -/
abbrev FirstDirectionAnchoredAnimal.animal
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    CubicBondAnimal d X.1.1 :=
  X.2.1.1

theorem FirstDirectionAnchoredAnimal.animal_anchored
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    X.animal.IsBottomLeftAnchored :=
  X.2.1.2

theorem FirstDirectionAnchoredAnimal.animal_direction
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    X.animal.IsFirstDirectionMaximal hd m :=
  X.2.2

/-- The finite union of exact-cluster cylinders for anchored diameter-`m` animals whose
canonical rightmost vertex is `x`. -/
def anchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    Set (EdgeConfiguration d) :=
  ⋃ X : {X : FirstDirectionAnchoredAnimal d hd m // X.animal.topRight = x},
    X.1.animal.clusterCylinder

theorem FirstDirectionAnchoredAnimal.vertices_subset_anchoredBox
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    X.animal.vertices ⊆ firstCoordinateAnchoredBox d hd m := by
  intro x hx
  rw [firstCoordinateAnchoredBox, Finset.mem_filter]
  refine ⟨?_, X.animal.coordinate_zero_nonneg_of_anchored
    X.animal_anchored hx hd⟩
  have hsub := X.animal.vertices_subset_metricBox_lInfDiameter hx
  simpa [X.animal_direction.1] using hsub

/-- Every exact-cluster cylinder in the left endpoint event is supported on the common finite
incident-edge set. -/
theorem CubicBondAnimal.dependsOn_clusterCylinder_of_vertices_subset
    {d s : ℕ} (A : CubicBondAnimal d s) {V : Finset (Cubic d)}
    (hV : A.vertices ⊆ V) :
    DependsOn (cubicIncidentEdges d V) A.clusterCylinder := by
  intro omega eta hagree
  simp only [clusterCylinder, Set.mem_inter_iff, mem_openEdgeSetEvent,
    mem_closedEdgeSetEvent]
  apply and_congr
  · constructor <;> intro hopen e heA
    · exact (hagree e (mem_cubicIncidentEdges_of_endpoint
        (hV (A.edge_endpoints e heA e.1.out.1 (Sym2.out_fst_mem e.1)))
        (Sym2.out_fst_mem e.1))).mp (hopen heA)
    · exact (hagree e (mem_cubicIncidentEdges_of_endpoint
        (hV (A.edge_endpoints e heA e.1.out.1 (Sym2.out_fst_mem e.1)))
        (Sym2.out_fst_mem e.1))).mpr (hopen heA)
  · rw [Set.disjoint_left, Set.disjoint_left]
    apply forall_congr'
    intro e
    apply imp_congr_right
    intro heBoundary
    have heSupport : e ∈ cubicIncidentEdges d V := by
      obtain ⟨v, hvA, hve⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp
        (Finset.mem_sdiff.mp heBoundary).1
      exact mem_cubicIncidentEdges_iff_exists_endpoint.mpr ⟨v, hV hvA, hve⟩
    exact not_congr (hagree e heSupport)

theorem dependsOn_anchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    DependsOn (firstCoordinateAnchoredSupport d hd m)
      (anchoredEndpointClusterEvent d hd m x) := by
  intro omega eta hagree
  simp only [anchoredEndpointClusterEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, (X.1.animal.dependsOn_clusterCylinder_of_vertices_subset
      X.1.vertices_subset_anchoredBox hagree).mp hX⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, (X.1.animal.dependsOn_clusterCylinder_of_vertices_subset
      X.1.vertices_subset_anchoredBox hagree).mpr hX⟩

theorem measurableSet_anchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    MeasurableSet (anchoredEndpointClusterEvent d hd m x) :=
  (dependsOn_anchoredEndpointClusterEvent d hd m x).measurableSet

/-- Bernoulli mass of the endpoint-conditioned anchored animals. -/
noncomputable def anchoredEndpointMass
    (d : ℕ) (p : ℝ) (hd : 0 < d) (m : ℕ) (x : Cubic d) : ℝ :=
  ∑ X : {X : FirstDirectionAnchoredAnimal d hd m // X.animal.topRight = x},
    X.1.animal.weight p

theorem anchoredEndpointMass_eq_sum_ite
    (d : ℕ) (p : ℝ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    anchoredEndpointMass d p hd m x =
      ∑ X : FirstDirectionAnchoredAnimal d hd m,
        if X.animal.topRight = x then X.animal.weight p else 0 := by
  classical
  unfold anchoredEndpointMass
  have h :
      (∑ X ∈ (Finset.univ : Finset (FirstDirectionAnchoredAnimal d hd m)).filter
          (fun X => X.animal.topRight = x), X.animal.weight p) =
        ∑ X : {X : FirstDirectionAnchoredAnimal d hd m // X.animal.topRight = x},
          X.1.animal.weight p :=
    Finset.sum_subtype
      ((Finset.univ : Finset (FirstDirectionAnchoredAnimal d hd m)).filter
        (fun X => X.animal.topRight = x))
      (fun X => by simp) (fun X => X.animal.weight p)
  rw [Finset.sum_filter] at h
  simpa using h.symm

theorem anchoredEndpointMass_eq_probability
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    anchoredEndpointMass d p hd m x =
      (bernoulliBondMeasure d p).real
        (anchoredEndpointClusterEvent d hd m x) := by
  let T := {X : FirstDirectionAnchoredAnimal d hd m // X.animal.topRight = x}
  let F : T → Set (EdgeConfiguration d) := fun X => X.1.animal.clusterCylinder
  have hpair : Pairwise (Function.onFun Disjoint F) := by
    classical
    intro X Y hXY
    change Disjoint (F X) (F Y)
    rw [Set.disjoint_left]
    intro omega hX hY
    apply hXY
    rcases X with ⟨⟨sx, AX⟩, hx⟩
    rcases Y with ⟨⟨sy, AY⟩, hy⟩
    dsimp [F] at hX hY hx hy ⊢
    have hvertices : AX.1.1.vertices = AY.1.1.vertices := by
      apply Finset.coe_injective
      exact (AX.1.1.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hX).symm.trans
        (AY.1.1.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hY)
    have hsval : sx.1 = sy.1 := by
      rw [← AX.1.1.vertices_card, ← AY.1.1.vertices_card, hvertices]
    have hs : sx = sy := Fin.ext hsval
    subst sy
    have hanimal : AX.1.1 = AY.1.1 :=
      CubicBondAnimal.eq_of_mem_clusterCylinder _ _ hX hY
    have hAX : AX = AY := Subtype.ext (Subtype.ext hanimal)
    subst AY
    rfl
  have hsum := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p) hpair
    (fun X : T => X.1.animal.measurableSet_clusterCylinder)
  change (∑ X : T, X.1.animal.weight p) = _
  rw [show anchoredEndpointClusterEvent d hd m x = ⋃ X : T, F X by rfl,
    hsum]
  apply Finset.sum_congr rfl
  intro X _hX
  simpa [F, CubicBondAnimal.weight] using
    (X.1.animal.bernoulliBondMeasure_real_clusterCylinder p).symm

theorem FirstDirectionAnchoredAnimal.topRight_coordinate_zero
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    X.animal.topRight ⟨0, hd⟩ = (m : ℤ) := by
  have hnonneg := X.animal.coordinate_zero_nonneg_of_anchored
    X.animal_anchored X.animal.topRight_mem hd
  have hspan := X.animal_direction.2
  rw [X.animal.firstCoordinateSpan_eq_toNat_sub hd,
    X.animal_anchored] at hspan
  simp only [cubicOrigin, sub_zero] at hspan
  calc
    X.animal.topRight ⟨0, hd⟩ =
        (X.animal.topRight ⟨0, hd⟩).toNat :=
      (Int.toNat_of_nonneg hnonneg).symm
    _ = (m : ℤ) := by exact_mod_cast hspan

theorem FirstDirectionAnchoredAnimal.topRight_mem_boxSurface
    {d : ℕ} {hd : 0 < d} {m : ℕ}
    (X : FirstDirectionAnchoredAnimal d hd m) :
    X.animal.topRight ∈ cubicBoxSurface d cubicOrigin m := by
  rw [mem_cubicBoxSurface]
  apply le_antisymm
  · exact (X.animal.cubicLInfDist_le_lInfDiameter
      X.animal.origin_mem X.animal.topRight_mem).trans_eq X.animal_direction.1
  · have hcoord := cubicLInfDist_coord_le cubicOrigin X.animal.topRight ⟨0, hd⟩
    simpa [X.topRight_coordinate_zero, cubicOrigin] using hcoord

theorem firstDirectionAnchoredTotalMass_eq_sum_animal
    (d : ℕ) (p : ℝ) (hd : 0 < d) (m : ℕ) :
    CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m =
      ∑ X : FirstDirectionAnchoredAnimal d hd m, X.animal.weight p := by
  classical
  unfold CubicBondAnimal.firstDirectionAnchoredTotalMass
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  rfl

/-- The endpoint-conditioned probabilities partition the total anchored directional animal
mass.  This is the finite pigeonhole decomposition in (8.58). -/
theorem sum_boxSurface_anchoredEndpointMass
    (d : ℕ) (p : ℝ) (hd : 0 < d) (m : ℕ) :
    ∑ x ∈ cubicBoxSurface d cubicOrigin m,
        anchoredEndpointMass d p hd m x =
      CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m := by
  classical
  rw [firstDirectionAnchoredTotalMass_eq_sum_animal]
  simp_rw [anchoredEndpointMass_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _hX
  simp [eq_comm, X.topRight_mem_boxSurface]

/-- A fixed right endpoint captures at least the average anchored mass over the box surface. -/
theorem exists_boxSurface_mul_anchoredEndpointMass_ge_total
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) :
    ∃ x ∈ cubicBoxSurface d cubicOrigin m,
      CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m ≤
        ((cubicBoxSurface d cubicOrigin m).card : ℝ) *
          anchoredEndpointMass d p hd m x := by
  have hsurface : (cubicBoxSurface d cubicOrigin m).Nonempty :=
    ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image
    (cubicBoxSurface d cubicOrigin m)
    (anchoredEndpointMass d p hd m) hsurface
  refine ⟨x, hx, ?_⟩
  rw [← sum_boxSurface_anchoredEndpointMass d p hd m]
  have hsum := Finset.sum_le_card_nsmul
    (cubicBoxSurface d cubicOrigin m)
    (anchoredEndpointMass d p hd m)
    (anchoredEndpointMass d p hd m x) hmax
  simpa [nsmul_eq_mul] using hsum

/-- The reflected/translated copy of the endpoint event. -/
def mirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    Set (EdgeConfiguration d) :=
  cubicGraphIsoEvent (finiteClusterAxisMirrorIso d hd m)
    (anchoredEndpointClusterEvent d hd m x)

theorem measurableSet_mirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    MeasurableSet (mirroredAnchoredEndpointClusterEvent d hd m x) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_anchoredEndpointClusterEvent d hd m x)

theorem mirroredAnchoredEndpointClusterEvent_probability
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (mirroredAnchoredEndpointClusterEvent d hd m x) =
      anchoredEndpointMass d p hd m x := by
  unfold mirroredAnchoredEndpointClusterEvent
  rw [bernoulliBondMeasure_real_cubicGraphIsoEvent p _
      (measurableSet_anchoredEndpointClusterEvent d hd m x),
    anchoredEndpointMass_eq_probability]

theorem DependsOn.cubicGraphIsoEvent
    {d : ℕ} {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (F : cubicGraph d ≃g cubicGraph d) :
    DependsOn (E.image F.mapEdgeSet) (cubicGraphIsoEvent F A) := by
  intro omega eta hagree
  apply hA
  intro e heE
  exact hagree (F.mapEdgeSet e) (Finset.mem_image.mpr ⟨e, heE, rfl⟩)

theorem dependsOn_mirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    DependsOn
      ((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisMirrorIso d hd m).mapEdgeSet)
      (mirroredAnchoredEndpointClusterEvent d hd m x) :=
  (dependsOn_anchoredEndpointClusterEvent d hd m x).cubicGraphIsoEvent _

theorem mem_firstCoordinateAnchoredBox_coordinate_bounds
    {d m : ℕ} {hd : 0 < d} {x : Cubic d}
    (hx : x ∈ firstCoordinateAnchoredBox d hd m) :
    0 ≤ x ⟨0, hd⟩ ∧ x ⟨0, hd⟩ ≤ (m : ℤ) := by
  rw [firstCoordinateAnchoredBox, Finset.mem_filter,
    mem_cubicMetricBox] at hx
  exact ⟨hx.2, by simpa [cubicOrigin] using (hx.1 ⟨0, hd⟩).2⟩

theorem cubicEdge_endpoint_coordinate_natAbs_sub_le_one
    {d : ℕ} (e : CubicEdge d) {x y : Cubic d}
    (hx : x ∈ (e : Sym2 (Cubic d))) (hy : y ∈ (e : Sym2 (Cubic d)))
    (i : Fin d) :
    (y i - x i).natAbs ≤ 1 := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hedge : e.1 = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
    have hadj : (cubicGraph d).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact hedge ▸ e.2
    have hl1 : cubicL1Dist x y = 1 := by
      rw [← cubicGraph_dist_eq_l1Dist, SimpleGraph.dist_eq_one_iff_adj]
      exact hadj
    exact (cubicL1Dist_coord_le x y i).trans_eq hl1

/-- The two finite endpoint events use disjoint coordinate blocks: their vertex regions are
separated by the middle hyperplane by two lattice steps. -/
theorem disjoint_firstCoordinateAnchoredSupport_axisMirror
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    Disjoint
      (firstCoordinateAnchoredSupport d hd m : Set (CubicEdge d))
      (((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisMirrorIso d hd m).mapEdgeSet :
          Finset (CubicEdge d)) : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heLeft heRight
  obtain ⟨x, hxBox, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heLeft
  obtain ⟨f, hfSupport, hfe⟩ := Finset.mem_image.mp heRight
  obtain ⟨y, hyBox, hyf⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp hfSupport
  have hFy : finiteClusterAxisMirrorIso d hd m y ∈ (e : Sym2 (Cubic d)) := by
    rw [← hfe, SimpleGraph.Iso.mapEdgeSet_apply]
    exact Sym2.mem_map.mpr ⟨y, hyf, rfl⟩
  have hxBounds := mem_firstCoordinateAnchoredBox_coordinate_bounds hxBox
  have hyBounds := mem_firstCoordinateAnchoredBox_coordinate_bounds hyBox
  have hmirror := finiteClusterAxisMirrorIso_apply d hd m y ⟨0, hd⟩
  simp at hmirror
  have hcoord := cubicEdge_endpoint_coordinate_natAbs_sub_le_one e hxe hFy ⟨0, hd⟩
  have hnonneg :
      0 ≤ finiteClusterAxisMirrorIso d hd m y ⟨0, hd⟩ - x ⟨0, hd⟩ := by
    omega
  have hcoordZ :
      (((finiteClusterAxisMirrorIso d hd m y ⟨0, hd⟩ -
        x ⟨0, hd⟩).natAbs : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hcoord
  rw [Int.natAbs_of_nonneg hnonneg] at hcoordZ
  omega

theorem indepSet_anchoredEndpoint_mirrored
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    IndepSet
      (anchoredEndpointClusterEvent d hd m x)
      (mirroredAnchoredEndpointClusterEvent d hd m x)
      (bernoulliBondMeasure d p) := by
  apply bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace
    d p (firstCoordinateAnchoredSupport d hd m)
      ((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisMirrorIso d hd m).mapEdgeSet)
    (disjoint_firstCoordinateAnchoredSupport_axisMirror d hd m)
  · simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
      (dependsOn_anchoredEndpointClusterEvent d hd m x).measurableSet_generateFrom_coordinateEvents
        (S := (firstCoordinateAnchoredSupport d hd m : Set (CubicEdge d))) (by simp)
  · simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
      (dependsOn_mirroredAnchoredEndpointClusterEvent d hd m x).measurableSet_generateFrom_coordinateEvents
        (S := (((firstCoordinateAnchoredSupport d hd m).image
          (finiteClusterAxisMirrorIso d hd m).mapEdgeSet :
            Finset (CubicEdge d)) : Set (CubicEdge d))) (by simp)

theorem bernoulliBondMeasure_real_endpoint_inter_mirrored
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (anchoredEndpointClusterEvent d hd m x ∩
          mirroredAnchoredEndpointClusterEvent d hd m x) =
      anchoredEndpointMass d p hd m x ^ 2 := by
  have hindep := indepSet_anchoredEndpoint_mirrored d p hd m x
  have hprod := hindep.measure_inter_eq_mul
  rw [measureReal_def, hprod, ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def, ← anchoredEndpointMass_eq_probability,
    mirroredAnchoredEndpointClusterEvent_probability]
  ring

/-! ### The finite star overwritten by the surgery -/

/-- The separating vertex `x+e₁`. -/
def finiteClusterGlueCenter {d : ℕ} (hd : 0 < d) (x : Cubic d) : Cubic d :=
  cubicStepFrom x ((⟨0, hd⟩ : Fin d), true)

/-- Every bond incident to the separating vertex. -/
noncomputable def finiteClusterGlueStar
    {d : ℕ} (hd : 0 < d) (x : Cubic d) : Finset (CubicEdge d) := by
  classical
  exact Finset.univ.image (cubicStepEdge (finiteClusterGlueCenter hd x))

/-- The two axial bonds retained open by the surgery. -/
noncomputable def finiteClusterGlueOpenTrace
    {d : ℕ} (hd : 0 < d) (x : Cubic d) : Finset (CubicEdge d) :=
  {cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), false),
    cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), true)}

private theorem cubicStepEdge_fixed_injective_for_glue
    {d : ℕ} (x : Cubic d) :
    Function.Injective (cubicStepEdge x : CubicDirection d → CubicEdge d) := by
  intro u v huv
  have hs : s(x, cubicStepFrom x u) = s(x, cubicStepFrom x v) :=
    congrArg Subtype.val huv
  rcases Sym2.eq_iff.mp hs with h | h
  · exact cubicStepFrom_injective x h.2
  · exfalso
    exact (cubicGraph_adj_stepFrom x v).ne h.1

theorem finiteClusterGlueStar_card
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (finiteClusterGlueStar hd x).card = 2 * d := by
  classical
  rw [finiteClusterGlueStar,
    Finset.card_image_iff.mpr
      (cubicStepEdge_fixed_injective_for_glue
        (finiteClusterGlueCenter hd x)).injOn]
  simp [CubicDirection, Fintype.card_prod, Nat.mul_comm]

theorem finiteClusterGlueOpenTrace_card
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (finiteClusterGlueOpenTrace hd x).card = 2 := by
  classical
  rw [finiteClusterGlueOpenTrace, Finset.card_pair]
  intro heq
  have hdir := cubicStepEdge_fixed_injective_for_glue
    (finiteClusterGlueCenter hd x) heq
  simp at hdir

theorem finiteClusterGlueOpenTrace_subset_star
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    finiteClusterGlueOpenTrace hd x ⊆ finiteClusterGlueStar hd x := by
  classical
  intro e he
  rw [finiteClusterGlueOpenTrace, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl <;>
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The exact local-modification cost in (8.59). -/
theorem finiteBernoulliWeight_glueOpenTrace
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (p : ℝ) :
    finiteBernoulliWeight (finiteClusterGlueStar hd x) p
        (finiteClusterGlueOpenTrace hd x) =
      p ^ 2 * (1 - p) ^ (2 * d - 2) := by
  rw [finiteBernoulliWeight, finiteClusterGlueOpenTrace_card,
    finiteClusterGlueStar_card]

theorem finiteClusterGlueCenter_coordinate_zero
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    finiteClusterGlueCenter hd x ⟨0, hd⟩ = x ⟨0, hd⟩ + 1 := by
  simp [finiteClusterGlueCenter, cubicStepFrom, cubicDirectionIncrement]

theorem finiteClusterAxisMirrorIso_glueCenter
    {d m : ℕ} (hd : 0 < d) {x : Cubic d}
    (hx : x ⟨0, hd⟩ = (m : ℤ)) :
    finiteClusterAxisMirrorIso d hd m (finiteClusterGlueCenter hd x) =
      finiteClusterGlueCenter hd x := by
  ext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    rw [finiteClusterAxisMirrorIso_apply, if_pos rfl,
      finiteClusterGlueCenter_coordinate_zero]
    omega
  · rw [finiteClusterAxisMirrorIso_apply, if_neg hj]

theorem mem_finiteClusterGlueStar_iff
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (e : CubicEdge d) :
    e ∈ finiteClusterGlueStar hd x ↔
      ∃ a : CubicDirection d,
        cubicStepEdge (finiteClusterGlueCenter hd x) a = e := by
  classical
  simp [finiteClusterGlueStar]

theorem glueCenter_mem_edge_of_mem_star
    {d : ℕ} {hd : 0 < d} {x : Cubic d} {e : CubicEdge d}
    (he : e ∈ finiteClusterGlueStar hd x) :
    finiteClusterGlueCenter hd x ∈ (e : Sym2 (Cubic d)) := by
  obtain ⟨a, rfl⟩ := (mem_finiteClusterGlueStar_iff hd x e).mp he
  simp [cubicStepEdge]

theorem CubicBondAnimal.edges_disjoint_glueStar_of_endpoint
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x) :
    Disjoint (A.edges : Set (CubicEdge d))
      (finiteClusterGlueStar hd x : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heA heStar
  have hcenterA : finiteClusterGlueCenter hd x ∈ A.vertices :=
    A.edge_endpoints e heA _ (glueCenter_mem_edge_of_mem_star heStar)
  have hupper := A.coordinate_zero_le_topRight' hd hcenterA
  have htop : A.topRight ⟨0, hd⟩ = (m : ℤ) := by
    have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
    have hspan := hdir.2
    rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
    simp only [cubicOrigin, sub_zero] at hspan
    calc
      A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
        (Int.toNat_of_nonneg hnonneg).symm
      _ = (m : ℤ) := by exact_mod_cast hspan
  rw [hx, finiteClusterGlueCenter_coordinate_zero, ← hx, htop] at hupper
  omega

theorem CubicBondAnimal.mappedEdges_disjoint_glueStar_of_endpoint
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x) :
    Disjoint
      ((A.edges.image (finiteClusterAxisMirrorIso d hd m).mapEdgeSet :
        Finset (CubicEdge d)) : Set (CubicEdge d))
      (finiteClusterGlueStar hd x : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heMap heStar
  obtain ⟨f, hfA, hfe⟩ := Finset.mem_image.mp heMap
  have hcenterMap : finiteClusterGlueCenter hd x ∈
      ((finiteClusterAxisMirrorIso d hd m).mapEdgeSet f : Sym2 (Cubic d)) := by
    rw [hfe]
    exact glueCenter_mem_edge_of_mem_star heStar
  rw [SimpleGraph.Iso.mapEdgeSet_apply] at hcenterMap
  obtain ⟨y, hyf, hycenter⟩ := Sym2.mem_map.mp hcenterMap
  have htop : A.topRight ⟨0, hd⟩ = (m : ℤ) := by
    have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
    have hspan := hdir.2
    rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
    simp only [cubicOrigin, sub_zero] at hspan
    calc
      A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
        (Int.toNat_of_nonneg hnonneg).symm
      _ = (m : ℤ) := by exact_mod_cast hspan
  have hfix := finiteClusterAxisMirrorIso_glueCenter hd (x := x) (hx ▸ htop)
  have hy : y = finiteClusterGlueCenter hd x := by
    apply (finiteClusterAxisMirrorIso d hd m).injective
    exact hycenter.trans hfix.symm
  have hcenterA : finiteClusterGlueCenter hd x ∈ A.vertices := by
    rw [← hy]
    exact A.edge_endpoints f hfA y hyf
  have hupper := A.coordinate_zero_le_topRight' hd hcenterA
  rw [hx, finiteClusterGlueCenter_coordinate_zero, ← hx, htop] at hupper
  omega

theorem walkIsOpen_splice_glueStar_of_animal
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x)
    {omega : EdgeConfiguration d} (homega : omega ∈ A.clusterCylinder)
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ A.edges) :
    walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega) w := by
  intro e he
  let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have heA : e' ∈ A.edges := hw ((mem_walkEdgeFinset_iff w e').mpr he)
  have heNot : e' ∉ finiteClusterGlueStar hd x :=
    Set.disjoint_left.mp (A.edges_disjoint_glueStar_of_endpoint hA hdir hx) heA
  change e' ∈ spliceOn (finiteClusterGlueStar hd x)
    (finiteClusterGlueOpenTrace hd x) omega
  rw [mem_spliceOn_of_notMem (finiteClusterGlueOpenTrace_subset_star hd x) heNot]
  exact (mem_openEdgeSetEvent d A.edges omega).mp homega.1 heA

theorem walkIsOpen_splice_glueStar_of_mappedAnimal
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x)
    {omega : EdgeConfiguration d}
    (homega : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisMirrorIso d hd m) omega ∈ A.clusterCylinder)
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ A.edges) :
    walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega)
      (w.map (finiteClusterAxisMirrorIso d hd m).toHom) := by
  have hwOpenPull : walkIsOpen
      (cubicGraphIsoConfigurationPullback
        (finiteClusterAxisMirrorIso d hd m) omega) w := by
    intro e he
    let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
    exact (mem_openEdgeSetEvent d A.edges _).mp homega.1
      (hw ((mem_walkEdgeFinset_iff w e').mpr he))
  have hopenOmega := walkIsOpen_map_cubicGraphIso
    (finiteClusterAxisMirrorIso d hd m) w hwOpenPull
  intro e he
  have heList : e ∈ (w.map (finiteClusterAxisMirrorIso d hd m).toHom).edges := he
  rw [SimpleGraph.Walk.edges_map] at heList
  obtain ⟨f, hfw, hfe⟩ := List.mem_map.mp heList
  let f' : CubicEdge d := ⟨f, w.edges_subset_edgeSet hfw⟩
  have hfA : f' ∈ A.edges := hw ((mem_walkEdgeFinset_iff w f').mpr hfw)
  let e' : CubicEdge d := ⟨e,
    (w.map (finiteClusterAxisMirrorIso d hd m).toHom).edges_subset_edgeSet he⟩
  have heEq : (finiteClusterAxisMirrorIso d hd m).mapEdgeSet f' = e' := by
    apply Subtype.ext
    exact hfe
  have heMap : e' ∈ A.edges.image
      (finiteClusterAxisMirrorIso d hd m).mapEdgeSet :=
    Finset.mem_image.mpr ⟨f', hfA, heEq⟩
  have heNot : e' ∉ finiteClusterGlueStar hd x :=
    Set.disjoint_left.mp
      (A.mappedEdges_disjoint_glueStar_of_endpoint hA hdir hx) heMap
  change e' ∈ spliceOn (finiteClusterGlueStar hd x)
    (finiteClusterGlueOpenTrace hd x) omega
  rw [mem_spliceOn_of_notMem (finiteClusterGlueOpenTrace_subset_star hd x) heNot]
  exact hopenOmega e he

theorem finiteClusterGlue_leftEdge_sym2
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), false)).1 =
        s(x, finiteClusterGlueCenter hd x) := by
  change s(finiteClusterGlueCenter hd x,
    cubicStepFrom (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), false)) = s(x, finiteClusterGlueCenter hd x)
  rw [show cubicStepFrom (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), false) = x by
    ext j
    by_cases hj : j = (⟨0, hd⟩ : Fin d)
    · subst j
      simp [finiteClusterGlueCenter, cubicStepFrom, cubicDirectionIncrement]
    · simp [finiteClusterGlueCenter, cubicStepFrom, cubicDirectionIncrement, hj]]
  exact Sym2.eq_swap

theorem finiteClusterGlue_rightEdge_sym2
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), true)).1 =
        s(finiteClusterGlueCenter hd x,
          cubicStepFrom (finiteClusterGlueCenter hd x)
            ((⟨0, hd⟩ : Fin d), true)) := rfl

/-- The two-edge bridge through the separating vertex is open after the splice. -/
theorem walkIsOpen_glueBridge_splice
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (omega : EdgeConfiguration d) :
    let center := finiteClusterGlueCenter hd x
    let right := cubicStepFrom center ((⟨0, hd⟩ : Fin d), true)
    let hleft : (cubicGraph d).Adj x center := cubicGraph_adj_stepFrom x _
    let hright : (cubicGraph d).Adj center right := cubicGraph_adj_stepFrom center _
    walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega)
      (SimpleGraph.Walk.cons hleft
        (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil)) := by
  let center := finiteClusterGlueCenter hd x
  let right := cubicStepFrom center ((⟨0, hd⟩ : Fin d), true)
  let hleft : (cubicGraph d).Adj x center := cubicGraph_adj_stepFrom x _
  let hright : (cubicGraph d).Adj center right := cubicGraph_adj_stepFrom center _
  let bridge : (cubicGraph d).Walk x right :=
    SimpleGraph.Walk.cons hleft
      (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil)
  change walkIsOpen
    (spliceOn (finiteClusterGlueStar hd x)
      (finiteClusterGlueOpenTrace hd x) omega) bridge
  intro e he
  let ew : CubicEdge d := ⟨e, bridge.edges_subset_edgeSet he⟩
  have heCases :
      e = s(x, finiteClusterGlueCenter hd x) ∨
      e = s(finiteClusterGlueCenter hd x,
        cubicStepFrom (finiteClusterGlueCenter hd x)
          ((⟨0, hd⟩ : Fin d), true)) := by
    simpa [bridge, hleft, hright, center, right] using he
  rcases heCases with heLeft | heRight
  · let e' : CubicEdge d :=
      cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), false)
    have heq : e = e'.1 := by
      simpa [e', finiteClusterGlue_leftEdge_sym2] using heLeft
    change ew ∈ spliceOn (finiteClusterGlueStar hd x)
      (finiteClusterGlueOpenTrace hd x) omega
    rw [show ew = e' by exact Subtype.ext heq]
    rw [mem_spliceOn_of_mem]
    · simp [finiteClusterGlueOpenTrace, e']
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · let e' : CubicEdge d :=
      cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), true)
    have heq : e = e'.1 := by
      simpa [e', finiteClusterGlue_rightEdge_sym2] using heRight
    change ew ∈ spliceOn (finiteClusterGlueStar hd x)
      (finiteClusterGlueOpenTrace hd x) omega
    rw [show ew = e' by exact Subtype.ext heq]
    rw [mem_spliceOn_of_mem]
    · simp [finiteClusterGlueOpenTrace, e']
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The splice joins the selected left and mirrored right finite clusters along the axis. -/
theorem splice_endpoint_inter_mem_connectionEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      mirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega ∈
      connectionEvent d cubicOrigin (cubicAxisVertex d (2 * m + 2)) := by
  rcases homega with ⟨hleftEvent, hrightEvent⟩
  obtain ⟨X, hXcyl⟩ := Set.mem_iUnion.mp hleftEvent
  change cubicGraphIsoConfigurationPullback
      (finiteClusterAxisMirrorIso d hd m) omega ∈
    anchoredEndpointClusterEvent d hd m x at hrightEvent
  obtain ⟨Y, hYcyl⟩ := Set.mem_iUnion.mp hrightEvent
  let A := X.1.animal
  let B := Y.1.animal
  have hAx : A.topRight = x := X.2
  have hBx : B.topRight = x := Y.2
  obtain ⟨wA, hwA⟩ := A.connected A.topRight A.topRight_mem
  obtain ⟨wB, hwB⟩ := B.connected B.topRight B.topRight_mem
  have hwAOpen := walkIsOpen_splice_glueStar_of_animal A
    X.1.animal_anchored X.1.animal_direction hAx hXcyl wA hwA
  have hwBMapOpen := walkIsOpen_splice_glueStar_of_mappedAnimal B
    Y.1.animal_anchored Y.1.animal_direction hBx hYcyl wB hwB
  let center := finiteClusterGlueCenter hd x
  let right := cubicStepFrom center ((⟨0, hd⟩ : Fin d), true)
  have hxcoord : x ⟨0, hd⟩ = (m : ℤ) := by
    rw [← hAx]
    exact X.1.topRight_coordinate_zero
  have hFright : finiteClusterAxisMirrorIso d hd m x = right := by
    simpa [center, right, finiteClusterGlueCenter] using
      finiteClusterAxisMirrorIso_rightEndpoint hd hxcoord
  let wBMap0 := wB.map (finiteClusterAxisMirrorIso d hd m).toHom
  let wBMap : (cubicGraph d).Walk (cubicAxisVertex d (2 * m + 2)) right :=
    wBMap0.copy (by simp [wBMap0]) (by simp [wBMap0, hBx, hFright])
  have hwBOpen : walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega) wBMap := by
    exact (walkIsOpen_copy wBMap0 (by simp [wBMap0])
      (by simp [wBMap0, hBx, hFright])).mpr hwBMapOpen
  let hleft : (cubicGraph d).Adj x center := cubicGraph_adj_stepFrom x _
  let hright : (cubicGraph d).Adj center right := cubicGraph_adj_stepFrom center _
  let bridge : (cubicGraph d).Walk x right :=
    SimpleGraph.Walk.cons hleft
      (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil)
  have hbridgeOpen : walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega) bridge := by
    simpa [bridge, center, right, hleft, hright] using
      walkIsOpen_glueBridge_splice hd x omega
  let w : (cubicGraph d).Walk cubicOrigin (cubicAxisVertex d (2 * m + 2)) :=
    (wA.copy rfl hAx).append (bridge.append wBMap.reverse)
  refine ⟨w, ?_⟩
  apply walkIsOpen_append
  · exact (walkIsOpen_copy wA rfl hAx).mpr hwAOpen
  · exact walkIsOpen_append hbridgeOpen (walkIsOpen_reverse hwBOpen)

/-! ### Finiteness of the glued cluster -/

/-- The finite vertex set containing the cluster after the star overwrite. -/
noncomputable def finiteClusterGluedVertices
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t) : Finset (Cubic d) := by
  classical
  exact A.vertices ∪ {finiteClusterGlueCenter hd x} ∪
    B.vertices.map (finiteClusterAxisMirrorIso d hd m).toEquiv.toEmbedding

theorem finiteClusterGlueOpenTrace_edge_cases
    {d : ℕ} (hd : 0 < d) (x : Cubic d) {e : CubicEdge d}
    (he : e ∈ finiteClusterGlueOpenTrace hd x) :
    e = cubicStepEdge (finiteClusterGlueCenter hd x)
          ((⟨0, hd⟩ : Fin d), false) ∨
      e = cubicStepEdge (finiteClusterGlueCenter hd x)
          ((⟨0, hd⟩ : Fin d), true) := by
  simpa [finiteClusterGlueOpenTrace] using he

theorem mem_finiteClusterGluedVertices_of_mem_openTrace_endpoint
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    (hxcoord : x ⟨0, hd⟩ = (m : ℤ))
    {e : CubicEdge d} (heTrace : e ∈ finiteClusterGlueOpenTrace hd x)
    {v : Cubic d} (hve : v ∈ (e : Sym2 (Cubic d))) :
    v ∈ finiteClusterGluedVertices (m := m) hd x A B := by
  classical
  rcases finiteClusterGlueOpenTrace_edge_cases hd x heTrace with rfl | rfl
  · rw [finiteClusterGlue_leftEdge_sym2] at hve
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · simp [finiteClusterGluedVertices, ← hAx, A.topRight_mem]
    · simp [finiteClusterGluedVertices]
  · rw [finiteClusterGlue_rightEdge_sym2] at hve
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | hvRight
    · simp [finiteClusterGluedVertices]
    · have hFright := finiteClusterAxisMirrorIso_rightEndpoint hd hxcoord
      have hvF :
          cubicStepFrom (finiteClusterGlueCenter hd x)
              ((⟨0, hd⟩ : Fin d), true) =
            finiteClusterAxisMirrorIso d hd m x := by
        simpa [finiteClusterGlueCenter] using hFright.symm
      rw [hvRight, hvF]
      rw [finiteClusterGluedVertices, Finset.mem_union]
      right
      apply Finset.mem_map.mpr
      refine ⟨B.topRight, B.topRight_mem, ?_⟩
      change finiteClusterAxisMirrorIso d hd m B.topRight =
        finiteClusterAxisMirrorIso d hd m x
      rw [hBx]

/-- One open step in the spliced configuration cannot leave the finite union of the two animal
vertex sets and the separating vertex. -/
theorem finiteClusterGluedVertices_step_closed
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored)
    (hAdir : A.IsFirstDirectionMaximal hd m)
    (hBdir : B.IsFirstDirectionMaximal hd m)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    {omega : EdgeConfiguration d}
    (hAcyl : omega ∈ A.clusterCylinder)
    (hBcyl : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisMirrorIso d hd m) omega ∈ B.clusterCylinder)
    {u v : Cubic d} (hu : u ∈ finiteClusterGluedVertices (m := m) hd x A B)
    (huv : (cubicGraph d).Adj u v)
    (hopen : (⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩ : CubicEdge d) ∈
      spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega) :
    v ∈ finiteClusterGluedVertices (m := m) hd x A B := by
  classical
  let e : CubicEdge d :=
    ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩
  have huve : u ∈ (e : Sym2 (Cubic d)) := by simp [e]
  have hvve : v ∈ (e : Sym2 (Cubic d)) := by simp [e]
  by_cases heStar : e ∈ finiteClusterGlueStar hd x
  · have heTrace : e ∈ finiteClusterGlueOpenTrace hd x := by
      exact (mem_spliceOn_of_mem heStar).mp hopen
    have hxcoord : x ⟨0, hd⟩ = (m : ℤ) := by
      rw [← hAx]
      have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
      have hspan := hAdir.2
      rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
      simp only [cubicOrigin, sub_zero] at hspan
      calc
        A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
          (Int.toNat_of_nonneg hnonneg).symm
        _ = (m : ℤ) := by exact_mod_cast hspan
    exact mem_finiteClusterGluedVertices_of_mem_openTrace_endpoint
      hd x A B hAx hBx hxcoord heTrace hvve
  · have heOmega : e ∈ omega := by
      exact (mem_spliceOn_of_notMem
        (finiteClusterGlueOpenTrace_subset_star hd x) heStar).mp hopen
    simp only [finiteClusterGluedVertices, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_map] at hu ⊢
    rcases hu with (huA | huCenter) | huB
    · apply Or.inl
      apply Or.inl
      let q : (cubicGraph d).Walk u v :=
        SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
      have hqOpen : walkIsOpen omega q := by
        intro f hf
        simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.mem_singleton] at hf
        have hfe : f = e.1 := by simpa [e] using hf
        simpa [hfe] using heOmega
      exact A.endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder
        hAcyl huA q hqOpen
    · subst u
      exfalso
      apply heStar
      obtain ⟨a, ha⟩ :=
        (cubicGraph_adj_iff_exists_stepFrom (finiteClusterGlueCenter hd x) v).mp huv
      rw [mem_finiteClusterGlueStar_iff]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change s(finiteClusterGlueCenter hd x,
        cubicStepFrom (finiteClusterGlueCenter hd x) a) =
          s(finiteClusterGlueCenter hd x, v)
      rw [← ha]
    · right
      obtain ⟨b, hbB, hbu⟩ := huB
      let q : (cubicGraph d).Walk u v :=
        SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
      have hqOpen : walkIsOpen omega q := by
        intro f hf
        simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.mem_singleton] at hf
        have hfe : f = e.1 := by simpa [e] using hf
        simpa [hfe] using heOmega
      have hqBackOpen : walkIsOpen
          (cubicGraphIsoConfigurationPullback
            (finiteClusterAxisMirrorIso d hd m) omega)
          (q.map (finiteClusterAxisMirrorIso d hd m).symm.toHom) := by
        have h := walkIsOpen_map_cubicGraphIso
          (finiteClusterAxisMirrorIso d hd m).symm q
          (show walkIsOpen
            (cubicGraphIsoConfigurationPullback
              (finiteClusterAxisMirrorIso d hd m).symm
              (cubicGraphIsoConfigurationPullback
                (finiteClusterAxisMirrorIso d hd m) omega)) q by
              simpa using hqOpen)
        simpa using h
      let qBack0 := q.map (finiteClusterAxisMirrorIso d hd m).symm.toHom
      have hstart : (finiteClusterAxisMirrorIso d hd m).symm u = b := by
        rw [← hbu]
        simp
      let qBack : (cubicGraph d).Walk b
          ((finiteClusterAxisMirrorIso d hd m).symm v) :=
        qBack0.copy (by simpa [qBack0] using hstart) rfl
      have hqBackOpen' : walkIsOpen
          (cubicGraphIsoConfigurationPullback
            (finiteClusterAxisMirrorIso d hd m) omega) qBack := by
        exact (walkIsOpen_copy qBack0
          (by simpa [qBack0] using hstart) rfl).mpr hqBackOpen
      have hvB : (finiteClusterAxisMirrorIso d hd m).symm v ∈ B.vertices :=
        B.endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder
          hBcyl hbB qBack hqBackOpen'
      exact ⟨(finiteClusterAxisMirrorIso d hd m).symm v, hvB, by simp⟩

theorem endpoint_mem_finiteClusterGluedVertices_of_walkIsOpen
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored)
    (hAdir : A.IsFirstDirectionMaximal hd m)
    (hBdir : B.IsFirstDirectionMaximal hd m)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    {omega : EdgeConfiguration d}
    (hAcyl : omega ∈ A.clusterCylinder)
    (hBcyl : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisMirrorIso d hd m) omega ∈ B.clusterCylinder)
    {u v : Cubic d} (hu : u ∈ finiteClusterGluedVertices (m := m) hd x A B)
    (w : (cubicGraph d).Walk u v)
    (hopen : walkIsOpen
      (spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega) w) :
    v ∈ finiteClusterGluedVertices (m := m) hd x A B := by
  induction w with
  | nil => exact hu
  | @cons u z v huz w ih =>
      have heOpen :
          (⟨s(u, z), by simpa [SimpleGraph.mem_edgeSet] using huz⟩ : CubicEdge d) ∈
            spliceOn (finiteClusterGlueStar hd x)
              (finiteClusterGlueOpenTrace hd x) omega := by
        apply hopen
        simp
      have hz := finiteClusterGluedVertices_step_closed hd x A B hA hB
        hAdir hBdir hAx hBx hAcyl hBcyl hu huz heOpen
      apply ih hz
      intro e he
      exact hopen e (by simp [he])

theorem splice_endpoint_inter_mem_finiteClusterEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      mirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega ∈ finiteClusterEvent d := by
  rcases homega with ⟨hleftEvent, hrightEvent⟩
  obtain ⟨X, hXcyl⟩ := Set.mem_iUnion.mp hleftEvent
  change cubicGraphIsoConfigurationPullback
      (finiteClusterAxisMirrorIso d hd m) omega ∈
    anchoredEndpointClusterEvent d hd m x at hrightEvent
  obtain ⟨Y, hYcyl⟩ := Set.mem_iUnion.mp hrightEvent
  let A := X.1.animal
  let B := Y.1.animal
  have hAx : A.topRight = x := X.2
  have hBx : B.topRight = x := Y.2
  change (cubicOpenCluster d
    (spliceOn (finiteClusterGlueStar hd x)
      (finiteClusterGlueOpenTrace hd x) omega)).Finite
  apply Set.Finite.subset
    (finiteClusterGluedVertices (m := m) hd x A B).finite_toSet
  intro z hz
  rcases hz with ⟨w, hwOpen⟩
  exact endpoint_mem_finiteClusterGluedVertices_of_walkIsOpen
    hd x A B X.1.animal_anchored Y.1.animal_anchored
    X.1.animal_direction Y.1.animal_direction hAx hBx
    hXcyl hYcyl
    (by simp [finiteClusterGluedVertices, A, B, A.origin_mem]) w hwOpen

theorem splice_endpoint_inter_mem_truncatedConnectionEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      mirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterGlueStar hd x)
        (finiteClusterGlueOpenTrace hd x) omega ∈
      truncatedConnectionEvent d (cubicAxisVertex d (2 * m + 2)) :=
  ⟨splice_endpoint_inter_mem_connectionEvent hd x homega,
    splice_endpoint_inter_mem_finiteClusterEvent hd x homega⟩

/-! ### The lower gluing inequality -/

/-- Endpoint-conditioned form of (8.59), before the two pigeonhole estimates. -/
theorem gluePenalty_mul_anchoredEndpointMass_sq_le_truncatedAxisConnectivity
    {d m : ℕ} (hd : 0 < d) (p : I) (x : Cubic d) :
    (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        anchoredEndpointMass d p hd m x ^ 2 ≤
      truncatedAxisConnectivity d p (2 * m + 2) := by
  have hoverwrite := finiteBernoulliWeight_mul_measureReal_le_of_splice_subset
    (ι := CubicEdge d) p
    (finiteClusterGlueOpenTrace_subset_star hd x)
    (measurableSet_truncatedConnectionEvent d
      (cubicAxisVertex d (2 * m + 2)))
    (fun _omega homega =>
      splice_endpoint_inter_mem_truncatedConnectionEvent hd x homega)
  rw [finiteBernoulliWeight_glueOpenTrace,
    show setBer((Set.univ : Set (CubicEdge d)), p).real
        (anchoredEndpointClusterEvent d hd m x ∩
          mirroredAnchoredEndpointClusterEvent d hd m x) =
        anchoredEndpointMass d p hd m x ^ 2 by
      simpa [bernoulliBondMeasure] using
        bernoulliBondMeasure_real_endpoint_inter_mirrored d p hd m x] at hoverwrite
  simpa [bernoulliBondMeasure, truncatedAxisConnectivity,
    truncatedTwoPointConnectivity] using hoverwrite

/-- Combined direction and anchoring pigeonhole estimate used in both Lemma 8.27 and
Theorem 8.53. -/
theorem finiteClusterLInfDiameterProbability_le_directionAnchorMass
    {d m : ℕ} (hd : 0 < d) (p : I) :
    finiteClusterLInfDiameterProbability d p m ≤
      (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m := by
  let Q := finiteClusterLInfDiameterProbability d p m
  let P := (bernoulliBondMeasure d p).real
    (finiteClusterFirstDirectionDiameterEvent d hd m)
  let M := CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m
  have hdir : Q ≤ (d : ℝ) * P := by
    simpa [Q, P] using
      finiteClusterLInfDiameterProbability_le_card_mul_firstDirection hd p
  have hanchor : P ≤ (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := by
    simpa [P, M, Nat.cast_pow] using
      firstDirectionDiameter_probability_le_boxCard_mul_anchoredTotalMass d m p hd
  calc
    Q ≤ (d : ℝ) * P := hdir
    _ ≤ (d : ℝ) * ((((2 * m + 1 : ℕ) : ℝ) ^ d) * M) := by
      gcongr
    _ = (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := by ring

/-- Denominator-free form of equation (8.59).  It is convenient for endpoint and
zero-probability checks. -/
theorem gluePenalty_mul_diameterProbability_sq_le_prefactor_mul_truncatedAxis
    {d m : ℕ} (hd : 0 < d) (p : I) :
    (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        finiteClusterLInfDiameterProbability d p m ^ 2 ≤
      ((d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
          ((cubicBoxSurface d cubicOrigin m).card : ℝ)) ^ 2 *
        truncatedAxisConnectivity d p (2 * m + 2) := by
  obtain ⟨x, hxSurface, hxMass⟩ :=
    exists_boxSurface_mul_anchoredEndpointMass_ge_total d p hd m
  let Q := finiteClusterLInfDiameterProbability d p m
  let M := CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m
  let R := anchoredEndpointMass d p hd m x
  let D := (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
    ((cubicBoxSurface d cubicOrigin m).card : ℝ)
  let c := (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)
  let T := truncatedAxisConnectivity d p (2 * m + 2)
  have hQM : Q ≤
      (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := by
    simpa [Q, M] using
      finiteClusterLInfDiameterProbability_le_directionAnchorMass hd p
  have hMR : M ≤ ((cubicBoxSurface d cubicOrigin m).card : ℝ) * R := by
    simpa [M, R] using hxMass
  have hQD : Q ≤ D * R := by
    calc
      Q ≤ (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := hQM
      _ ≤ (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
          (((cubicBoxSurface d cubicOrigin m).card : ℝ) * R) := by
        gcongr
      _ = D * R := by ring
  have hQ0 : 0 ≤ Q := finiteClusterLInfDiameterProbability_nonneg d p m
  have hD0 : 0 ≤ D := by positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    rw [anchoredEndpointMass_eq_probability]
    exact measureReal_nonneg
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (sq_nonneg (p : ℝ))
      (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hsq : Q ^ 2 ≤ D ^ 2 * R ^ 2 := by nlinarith
  have hlocal : c * R ^ 2 ≤ T := by
    simpa [c, R, T] using
      gluePenalty_mul_anchoredEndpointMass_sq_le_truncatedAxisConnectivity
        hd p x
  calc
    c * Q ^ 2 ≤ c * (D ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hc0
    _ = D ^ 2 * (c * R ^ 2) := by ring
    _ ≤ D ^ 2 * T := mul_le_mul_of_nonneg_left hlocal (sq_nonneg D)

/-- Equation (8.59), with the exact source polynomial prefactor. -/
theorem truncatedAxisConnectivity_even_glue_lower_bound
    {d m : ℕ} (hd : 0 < d) (p : I) :
    ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        finiteClusterLInfDiameterProbability d p m ^ 2) /
        ((d : ℝ) ^ 2 *
          ((cubicBoxSurface d cubicOrigin m).card : ℝ) ^ 2 *
          ((((2 * m + 1 : ℕ) : ℝ) ^ d) ^ 2)) ≤
      truncatedAxisConnectivity d p (2 * m + 2) := by
  have hden :=
    gluePenalty_mul_diameterProbability_sq_le_prefactor_mul_truncatedAxis
      (m := m) hd p
  let D := (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
    ((cubicBoxSurface d cubicOrigin m).card : ℝ)
  have hsurface : 0 < ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hform :
      (d : ℝ) ^ 2 * ((cubicBoxSurface d cubicOrigin m).card : ℝ) ^ 2 *
          ((((2 * m + 1 : ℕ) : ℝ) ^ d) ^ 2) = D ^ 2 := by
    dsimp [D]
    ring
  rw [hform]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).2
  convert hden using 1 <;> dsimp [D] <;> ring

/-! ### Odd axis distances -/

/-- First-coordinate reflection followed by translation to `(2m+3)e₁`. -/
def finiteClusterAxisOddMirrorIso
    (d : ℕ) (hd : 0 < d) (m : ℕ) : cubicGraph d ≃g cubicGraph d :=
  (cubicCoordinateReflectionIso (⟨0, hd⟩ : Fin d)).trans
    (cubicTranslationIso cubicOrigin (cubicAxisVertex d (2 * m + 3)))

theorem finiteClusterAxisOddMirrorIso_apply
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) (j : Fin d) :
    finiteClusterAxisOddMirrorIso d hd m x j =
      if j = (⟨0, hd⟩ : Fin d) then (2 * m + 3 : ℤ) - x j else x j := by
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisOddMirrorIso, cubicCoordinateReflectionIso,
      cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateReflectionEquiv, cubicAxisVertex, cubicOrigin]
    ring
  · have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      simpa using h0
    simp [finiteClusterAxisOddMirrorIso, cubicCoordinateReflectionIso,
      cubicTranslationIso_apply, cubicTranslate,
      cubicCoordinateReflectionEquiv, cubicAxisVertex, cubicOrigin, hj, hj0]

@[simp]
theorem finiteClusterAxisOddMirrorIso_origin
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    finiteClusterAxisOddMirrorIso d hd m cubicOrigin =
      cubicAxisVertex d (2 * m + 3) := by
  ext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisOddMirrorIso_apply, cubicAxisVertex, cubicOrigin]
  · have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      simpa using h0
    simp [finiteClusterAxisOddMirrorIso_apply, cubicAxisVertex, cubicOrigin, hj, hj0]

theorem finiteClusterAxisOddMirrorIso_rightEndpoint
    {d m : ℕ} (hd : 0 < d) {x : Cubic d}
    (hx : x ⟨0, hd⟩ = (m : ℤ)) :
    finiteClusterAxisOddMirrorIso d hd m x =
      cubicStepFrom
        (cubicStepFrom (cubicStepFrom x ((⟨0, hd⟩ : Fin d), true))
          ((⟨0, hd⟩ : Fin d), true))
        ((⟨0, hd⟩ : Fin d), true) := by
  ext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [finiteClusterAxisOddMirrorIso_apply, cubicStepFrom,
      cubicDirectionIncrement, hx]
    omega
  · simp [finiteClusterAxisOddMirrorIso_apply, cubicStepFrom,
      cubicDirectionIncrement, hj]

def oddMirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    Set (EdgeConfiguration d) :=
  cubicGraphIsoEvent (finiteClusterAxisOddMirrorIso d hd m)
    (anchoredEndpointClusterEvent d hd m x)

theorem measurableSet_oddMirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    MeasurableSet (oddMirroredAnchoredEndpointClusterEvent d hd m x) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_anchoredEndpointClusterEvent d hd m x)

theorem oddMirroredAnchoredEndpointClusterEvent_probability
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (oddMirroredAnchoredEndpointClusterEvent d hd m x) =
      anchoredEndpointMass d p hd m x := by
  unfold oddMirroredAnchoredEndpointClusterEvent
  rw [bernoulliBondMeasure_real_cubicGraphIsoEvent p _
      (measurableSet_anchoredEndpointClusterEvent d hd m x),
    anchoredEndpointMass_eq_probability]

theorem dependsOn_oddMirroredAnchoredEndpointClusterEvent
    (d : ℕ) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    DependsOn
      ((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet)
      (oddMirroredAnchoredEndpointClusterEvent d hd m x) :=
  (dependsOn_anchoredEndpointClusterEvent d hd m x).cubicGraphIsoEvent _

theorem disjoint_firstCoordinateAnchoredSupport_axisOddMirror
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    Disjoint
      (firstCoordinateAnchoredSupport d hd m : Set (CubicEdge d))
      (((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet :
          Finset (CubicEdge d)) : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heLeft heRight
  obtain ⟨x, hxBox, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heLeft
  obtain ⟨f, hfSupport, hfe⟩ := Finset.mem_image.mp heRight
  obtain ⟨y, hyBox, hyf⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp hfSupport
  have hFy : finiteClusterAxisOddMirrorIso d hd m y ∈ (e : Sym2 (Cubic d)) := by
    rw [← hfe, SimpleGraph.Iso.mapEdgeSet_apply]
    exact Sym2.mem_map.mpr ⟨y, hyf, rfl⟩
  have hxBounds := mem_firstCoordinateAnchoredBox_coordinate_bounds hxBox
  have hyBounds := mem_firstCoordinateAnchoredBox_coordinate_bounds hyBox
  have hmirror := finiteClusterAxisOddMirrorIso_apply d hd m y ⟨0, hd⟩
  simp at hmirror
  have hcoord := cubicEdge_endpoint_coordinate_natAbs_sub_le_one e hxe hFy ⟨0, hd⟩
  have hnonneg :
      0 ≤ finiteClusterAxisOddMirrorIso d hd m y ⟨0, hd⟩ - x ⟨0, hd⟩ := by
    omega
  have hcoordZ :
      (((finiteClusterAxisOddMirrorIso d hd m y ⟨0, hd⟩ -
        x ⟨0, hd⟩).natAbs : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hcoord
  rw [Int.natAbs_of_nonneg hnonneg] at hcoordZ
  omega

theorem indepSet_anchoredEndpoint_oddMirrored
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    IndepSet
      (anchoredEndpointClusterEvent d hd m x)
      (oddMirroredAnchoredEndpointClusterEvent d hd m x)
      (bernoulliBondMeasure d p) := by
  apply bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace
    d p (firstCoordinateAnchoredSupport d hd m)
      ((firstCoordinateAnchoredSupport d hd m).image
        (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet)
    (disjoint_firstCoordinateAnchoredSupport_axisOddMirror d hd m)
  · simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
      (dependsOn_anchoredEndpointClusterEvent d hd m x).measurableSet_generateFrom_coordinateEvents
        (S := (firstCoordinateAnchoredSupport d hd m : Set (CubicEdge d))) (by simp)
  · simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
      (dependsOn_oddMirroredAnchoredEndpointClusterEvent d hd m x).measurableSet_generateFrom_coordinateEvents
        (S := (((firstCoordinateAnchoredSupport d hd m).image
          (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet :
            Finset (CubicEdge d)) : Set (CubicEdge d))) (by simp)

theorem bernoulliBondMeasure_real_endpoint_inter_oddMirrored
    (d : ℕ) (p : I) (hd : 0 < d) (m : ℕ) (x : Cubic d) :
    (bernoulliBondMeasure d p).real
        (anchoredEndpointClusterEvent d hd m x ∩
          oddMirroredAnchoredEndpointClusterEvent d hd m x) =
      anchoredEndpointMass d p hd m x ^ 2 := by
  have hprod := (indepSet_anchoredEndpoint_oddMirrored d p hd m x).measure_inter_eq_mul
  rw [measureReal_def, hprod, ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def, ← anchoredEndpointMass_eq_probability,
    oddMirroredAnchoredEndpointClusterEvent_probability]
  ring

/-- The second separating vertex `x+2e₁` in the odd bridge. -/
def finiteClusterOddGlueCenterTwo
    {d : ℕ} (hd : 0 < d) (x : Cubic d) : Cubic d :=
  cubicStepFrom (finiteClusterGlueCenter hd x)
    ((⟨0, hd⟩ : Fin d), true)

/-- The union of the two incident-edge stars overwritten by the odd bridge. -/
noncomputable def finiteClusterOddGlueStar
    {d : ℕ} (hd : 0 < d) (x : Cubic d) : Finset (CubicEdge d) :=
  finiteClusterGlueStar hd x ∪
    Finset.univ.image (cubicStepEdge (finiteClusterOddGlueCenterTwo hd x))

/-- The three axial edges retained open in the odd bridge. -/
noncomputable def finiteClusterOddGlueOpenTrace
    {d : ℕ} (hd : 0 < d) (x : Cubic d) : Finset (CubicEdge d) :=
  {cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), false),
    cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), true),
    cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
      ((⟨0, hd⟩ : Fin d), true)}

theorem finiteClusterOddGlueOpenTrace_subset_star
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    finiteClusterOddGlueOpenTrace hd x ⊆ finiteClusterOddGlueStar hd x := by
  classical
  intro e he
  simp only [finiteClusterOddGlueOpenTrace, Finset.mem_insert,
    Finset.mem_singleton] at he
  rw [finiteClusterOddGlueStar, Finset.mem_union]
  rcases he with rfl | rfl | rfl
  · left
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · left
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · right
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem finiteClusterOddGlueStar_card_le
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (finiteClusterOddGlueStar hd x).card ≤ 4 * d := by
  classical
  calc
    (finiteClusterOddGlueStar hd x).card ≤
        (finiteClusterGlueStar hd x).card +
          (Finset.univ.image
            (cubicStepEdge (finiteClusterOddGlueCenterTwo hd x))).card :=
      Finset.card_union_le _ _
    _ = 2 * d + 2 * d := by
      rw [finiteClusterGlueStar_card]
      rw [Finset.card_image_iff.mpr
        (cubicStepEdge_fixed_injective_for_glue
          (finiteClusterOddGlueCenterTwo hd x)).injOn]
      simp [CubicDirection, Fintype.card_prod, Nat.mul_comm]
    _ = 4 * d := by omega

theorem finiteClusterGlueStar_inter_secondStar
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    finiteClusterGlueStar hd x ∩
        Finset.univ.image (cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)) =
      {cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), true)} := by
  classical
  ext e
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨heOne, heTwo⟩
    have hcOne : finiteClusterGlueCenter hd x ∈ (e : Sym2 (Cubic d)) :=
      glueCenter_mem_edge_of_mem_star heOne
    obtain ⟨a, _ha, hae⟩ := Finset.mem_image.mp heTwo
    have hcTwo : finiteClusterOddGlueCenterTwo hd x ∈ (e : Sym2 (Cubic d)) := by
      rw [← hae]
      simp [cubicStepEdge]
    apply Subtype.ext
    exact Sym2.eq_of_ne_mem (cubicGraph_adj_stepFrom
      (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), true)).ne hcOne hcTwo
      (by simp [cubicStepEdge]) (by simp [cubicStepEdge, finiteClusterOddGlueCenterTwo])
  · rintro rfl
    constructor
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_image.mpr
      refine ⟨((⟨0, hd⟩ : Fin d), false), Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change s(finiteClusterOddGlueCenterTwo hd x,
          cubicStepFrom (finiteClusterOddGlueCenterTwo hd x)
            ((⟨0, hd⟩ : Fin d), false)) =
        s(finiteClusterGlueCenter hd x,
          cubicStepFrom (finiteClusterGlueCenter hd x)
            ((⟨0, hd⟩ : Fin d), true))
      have hback : cubicStepFrom (finiteClusterOddGlueCenterTwo hd x)
          ((⟨0, hd⟩ : Fin d), false) = finiteClusterGlueCenter hd x := by
        ext j
        by_cases hj : j = (⟨0, hd⟩ : Fin d)
        · subst j
          simp [finiteClusterOddGlueCenterTwo, cubicStepFrom, cubicDirectionIncrement]
        · simp [finiteClusterOddGlueCenterTwo, cubicStepFrom,
            cubicDirectionIncrement, hj]
      rw [hback]
      exact Sym2.eq_swap

/-- The two degree-`2d` stars overlap in exactly their common axial edge. -/
theorem finiteClusterOddGlueStar_card
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (finiteClusterOddGlueStar hd x).card = 4 * d - 1 := by
  classical
  have hcard := Finset.card_union_add_card_inter
    (finiteClusterGlueStar hd x)
    (Finset.univ.image (cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)))
  rw [finiteClusterGlueStar_inter_secondStar, Finset.card_singleton,
    finiteClusterGlueStar_card,
    Finset.card_image_iff.mpr
      (cubicStepEdge_fixed_injective_for_glue
        (finiteClusterOddGlueCenterTwo hd x)).injOn] at hcard
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, mul_comm] at hcard
  change (finiteClusterOddGlueStar hd x).card = 4 * d - 1
  rw [finiteClusterOddGlueStar]
  omega

private theorem finiteClusterOddGlue_edge01_ne
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), false) ≠
      cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), true) := by
  intro h
  have := cubicStepEdge_fixed_injective_for_glue
    (finiteClusterGlueCenter hd x) h
  simp at this

private theorem finiteClusterOddGlue_edge12_ne
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), true) ≠
      cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
        ((⟨0, hd⟩ : Fin d), true) := by
  intro h
  have hs := congrArg (fun e : CubicEdge d => e.1) h
  have hcoord := congrArg
    (fun z : Sym2 (Cubic d) => z.map (fun y => y ⟨0, hd⟩)) hs
  simp [finiteClusterOddGlueCenterTwo, finiteClusterGlueCenter,
    cubicStepEdge, cubicStepFrom, cubicDirectionIncrement] at hcoord
  omega

private theorem finiteClusterOddGlue_edge02_ne
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), false) ≠
      cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
        ((⟨0, hd⟩ : Fin d), true) := by
  intro h
  have hs := congrArg (fun e : CubicEdge d => e.1) h
  have hcoord := congrArg
    (fun z : Sym2 (Cubic d) => z.map (fun y => y ⟨0, hd⟩)) hs
  simp [finiteClusterOddGlueCenterTwo, finiteClusterGlueCenter,
    cubicStepEdge, cubicStepFrom, cubicDirectionIncrement] at hcoord
  omega

theorem finiteClusterOddGlueOpenTrace_card
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (finiteClusterOddGlueOpenTrace hd x).card = 3 := by
  classical
  rw [finiteClusterOddGlueOpenTrace]
  simp [finiteClusterOddGlue_edge01_ne hd x,
    finiteClusterOddGlue_edge12_ne hd x,
    finiteClusterOddGlue_edge02_ne hd x]

theorem finiteBernoulliWeight_oddGlueOpenTrace_lower
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (p : I) :
    (p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d) ≤
      finiteBernoulliWeight (finiteClusterOddGlueStar hd x) (p : ℝ)
        (finiteClusterOddGlueOpenTrace hd x) := by
  rw [finiteBernoulliWeight, finiteClusterOddGlueOpenTrace_card]
  have hcard := finiteClusterOddGlueStar_card_le hd x
  have hexp : (finiteClusterOddGlueStar hd x).card - 3 ≤ 4 * d := by omega
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hq1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
  have hpow := pow_le_pow_of_le_one hq0 hq1 hexp
  exact mul_le_mul_of_nonneg_left hpow (pow_nonneg p.2.1 3)

/-- The exact local-modification cost in equation (8.60). -/
theorem finiteBernoulliWeight_oddGlueOpenTrace
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (p : ℝ) :
    finiteBernoulliWeight (finiteClusterOddGlueStar hd x) p
        (finiteClusterOddGlueOpenTrace hd x) =
      p ^ 3 * (1 - p) ^ (4 * d - 4) := by
  rw [finiteBernoulliWeight, finiteClusterOddGlueOpenTrace_card,
    finiteClusterOddGlueStar_card]
  have : 3 ≤ 4 * d - 1 := by omega
  congr 1

theorem finiteClusterOddGlueCenterTwo_coordinate_zero
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    finiteClusterOddGlueCenterTwo hd x ⟨0, hd⟩ = x ⟨0, hd⟩ + 2 := by
  simp [finiteClusterOddGlueCenterTwo, finiteClusterGlueCenter,
    cubicStepFrom, cubicDirectionIncrement]
  ring

theorem mem_finiteClusterOddGlueStar_of_centerOne_incident
    {d : ℕ} {hd : 0 < d} {x : Cubic d} {e : CubicEdge d}
    (he : finiteClusterGlueCenter hd x ∈ (e : Sym2 (Cubic d))) :
    e ∈ finiteClusterOddGlueStar hd x := by
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp he
  have hadj : (cubicGraph d).Adj (finiteClusterGlueCenter hd x) y := by
    rw [← SimpleGraph.mem_edgeSet]
    exact hey ▸ e.2
  obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
  rw [finiteClusterOddGlueStar, Finset.mem_union]
  left
  rw [mem_finiteClusterGlueStar_iff]
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa [cubicStepEdge, ha] using hey.symm

theorem mem_finiteClusterOddGlueStar_of_centerTwo_incident
    {d : ℕ} {hd : 0 < d} {x : Cubic d} {e : CubicEdge d}
    (he : finiteClusterOddGlueCenterTwo hd x ∈ (e : Sym2 (Cubic d))) :
    e ∈ finiteClusterOddGlueStar hd x := by
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp he
  have hadj : (cubicGraph d).Adj (finiteClusterOddGlueCenterTwo hd x) y := by
    rw [← SimpleGraph.mem_edgeSet]
    exact hey ▸ e.2
  obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
  rw [finiteClusterOddGlueStar, Finset.mem_union]
  right
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  simpa [cubicStepEdge, ha] using hey.symm

theorem CubicBondAnimal.edges_disjoint_oddGlueStar_of_endpoint
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x) :
    Disjoint (A.edges : Set (CubicEdge d))
      (finiteClusterOddGlueStar hd x : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heA heStar
  change e ∈ finiteClusterOddGlueStar hd x at heStar
  rw [finiteClusterOddGlueStar, Finset.mem_union] at heStar
  rcases heStar with heOne | heTwo
  · exact Set.disjoint_left.mp
      (A.edges_disjoint_glueStar_of_endpoint hA hdir hx) heA heOne
  · obtain ⟨a, _ha, hae⟩ := Finset.mem_image.mp heTwo
    have hcenterA : finiteClusterOddGlueCenterTwo hd x ∈ A.vertices :=
      A.edge_endpoints e heA _ (by
        rw [← hae]
        simp [cubicStepEdge])
    have hupper := A.coordinate_zero_le_topRight' hd hcenterA
    have htop : A.topRight ⟨0, hd⟩ = (m : ℤ) := by
      have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
      have hspan := hdir.2
      rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
      simp only [cubicOrigin, sub_zero] at hspan
      calc
        A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
          (Int.toNat_of_nonneg hnonneg).symm
        _ = (m : ℤ) := by exact_mod_cast hspan
    rw [hx, finiteClusterOddGlueCenterTwo_coordinate_zero, ← hx, htop] at hupper
    omega

theorem CubicBondAnimal.oddMappedEdges_disjoint_glueStar_of_endpoint
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x) :
    Disjoint
      ((A.edges.image (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet :
        Finset (CubicEdge d)) : Set (CubicEdge d))
      (finiteClusterOddGlueStar hd x : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heMap heStar
  obtain ⟨f, hfA, hfe⟩ := Finset.mem_image.mp heMap
  have htop : A.topRight ⟨0, hd⟩ = (m : ℤ) := by
    have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
    have hspan := hdir.2
    rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
    simp only [cubicOrigin, sub_zero] at hspan
    calc
      A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
        (Int.toNat_of_nonneg hnonneg).symm
      _ = (m : ℤ) := by exact_mod_cast hspan
  have hpreimageCenter (z : Cubic d) (hz : z ∈ (e : Sym2 (Cubic d)))
      (hzlower : (m : ℤ) + 1 ≤ z ⟨0, hd⟩)
      (hzupper : z ⟨0, hd⟩ ≤ (m : ℤ) + 2) : False := by
    have hzMap : z ∈
        ((finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet f : Sym2 (Cubic d)) := by
      rwa [hfe]
    rw [SimpleGraph.Iso.mapEdgeSet_apply] at hzMap
    obtain ⟨y, hyf, hyz⟩ := Sym2.mem_map.mp hzMap
    have hyA := A.edge_endpoints f hfA y hyf
    have hyUpper := A.coordinate_zero_le_topRight' hd hyA
    have happly := finiteClusterAxisOddMirrorIso_apply d hd m y ⟨0, hd⟩
    simp at happly
    have hyEq : finiteClusterAxisOddMirrorIso d hd m y = z := hyz
    have hcoordEq := congrFun hyEq ⟨0, hd⟩
    rw [happly] at hcoordEq
    omega
  change e ∈ finiteClusterOddGlueStar hd x at heStar
  rw [finiteClusterOddGlueStar, Finset.mem_union] at heStar
  rcases heStar with heOne | heTwo
  · exact hpreimageCenter (finiteClusterGlueCenter hd x)
      (glueCenter_mem_edge_of_mem_star heOne)
      (by rw [finiteClusterGlueCenter_coordinate_zero, ← hx, htop])
      (by rw [finiteClusterGlueCenter_coordinate_zero, ← hx, htop]; omega)
  · obtain ⟨a, _ha, hae⟩ := Finset.mem_image.mp heTwo
    exact hpreimageCenter (finiteClusterOddGlueCenterTwo hd x)
      (by rw [← hae]; simp [cubicStepEdge])
      (by rw [finiteClusterOddGlueCenterTwo_coordinate_zero, ← hx, htop]; omega)
      (by rw [finiteClusterOddGlueCenterTwo_coordinate_zero, ← hx, htop])

theorem walkIsOpen_splice_oddGlueStar_of_animal
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x)
    {omega : EdgeConfiguration d} (homega : omega ∈ A.clusterCylinder)
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ A.edges) :
    walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega) w := by
  intro e he
  let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have heA : e' ∈ A.edges := hw ((mem_walkEdgeFinset_iff w e').mpr he)
  have heNot : e' ∉ finiteClusterOddGlueStar hd x :=
    Set.disjoint_left.mp (A.edges_disjoint_oddGlueStar_of_endpoint hA hdir hx) heA
  change e' ∈ spliceOn (finiteClusterOddGlueStar hd x)
    (finiteClusterOddGlueOpenTrace hd x) omega
  rw [mem_spliceOn_of_notMem (finiteClusterOddGlueOpenTrace_subset_star hd x) heNot]
  exact (mem_openEdgeSetEvent d A.edges omega).mp homega.1 heA

theorem walkIsOpen_splice_oddGlueStar_of_mappedAnimal
    {d s m : ℕ} {hd : 0 < d} (A : CubicBondAnimal d s)
    (hA : A.IsBottomLeftAnchored) (hdir : A.IsFirstDirectionMaximal hd m)
    {x : Cubic d} (hx : A.topRight = x)
    {omega : EdgeConfiguration d}
    (homega : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisOddMirrorIso d hd m) omega ∈ A.clusterCylinder)
    {u v : Cubic d} (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ A.edges) :
    walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega)
      (w.map (finiteClusterAxisOddMirrorIso d hd m).toHom) := by
  have hwOpenPull : walkIsOpen
      (cubicGraphIsoConfigurationPullback
        (finiteClusterAxisOddMirrorIso d hd m) omega) w := by
    intro e he
    let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
    exact (mem_openEdgeSetEvent d A.edges _).mp homega.1
      (hw ((mem_walkEdgeFinset_iff w e').mpr he))
  have hopenOmega := walkIsOpen_map_cubicGraphIso
    (finiteClusterAxisOddMirrorIso d hd m) w hwOpenPull
  intro e he
  have heList : e ∈ (w.map (finiteClusterAxisOddMirrorIso d hd m).toHom).edges := he
  rw [SimpleGraph.Walk.edges_map] at heList
  obtain ⟨f, hfw, hfe⟩ := List.mem_map.mp heList
  let f' : CubicEdge d := ⟨f, w.edges_subset_edgeSet hfw⟩
  have hfA : f' ∈ A.edges := hw ((mem_walkEdgeFinset_iff w f').mpr hfw)
  let e' : CubicEdge d := ⟨e,
    (w.map (finiteClusterAxisOddMirrorIso d hd m).toHom).edges_subset_edgeSet he⟩
  have heEq : (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet f' = e' := by
    apply Subtype.ext
    exact hfe
  have heMap : e' ∈ A.edges.image
      (finiteClusterAxisOddMirrorIso d hd m).mapEdgeSet :=
    Finset.mem_image.mpr ⟨f', hfA, heEq⟩
  have heNot : e' ∉ finiteClusterOddGlueStar hd x :=
    Set.disjoint_left.mp
      (A.oddMappedEdges_disjoint_glueStar_of_endpoint hA hdir hx) heMap
  change e' ∈ spliceOn (finiteClusterOddGlueStar hd x)
    (finiteClusterOddGlueOpenTrace hd x) omega
  rw [mem_spliceOn_of_notMem (finiteClusterOddGlueOpenTrace_subset_star hd x) heNot]
  exact hopenOmega e he

theorem finiteClusterOddGlue_middleEdge_sym2
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (cubicStepEdge (finiteClusterGlueCenter hd x)
      ((⟨0, hd⟩ : Fin d), true)).1 =
        s(finiteClusterGlueCenter hd x, finiteClusterOddGlueCenterTwo hd x) := by
  rfl

theorem finiteClusterOddGlue_rightEdge_sym2
    {d : ℕ} (hd : 0 < d) (x : Cubic d) :
    (cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
      ((⟨0, hd⟩ : Fin d), true)).1 =
        s(finiteClusterOddGlueCenterTwo hd x,
          cubicStepFrom (finiteClusterOddGlueCenterTwo hd x)
            ((⟨0, hd⟩ : Fin d), true)) := rfl

/-- The three-edge bridge through the two separating vertices is open after the odd splice. -/
theorem walkIsOpen_oddGlueBridge_splice
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (omega : EdgeConfiguration d) :
    let centerOne := finiteClusterGlueCenter hd x
    let centerTwo := finiteClusterOddGlueCenterTwo hd x
    let right := cubicStepFrom centerTwo ((⟨0, hd⟩ : Fin d), true)
    let hleft : (cubicGraph d).Adj x centerOne := cubicGraph_adj_stepFrom x _
    let hmiddle : (cubicGraph d).Adj centerOne centerTwo := cubicGraph_adj_stepFrom centerOne _
    let hright : (cubicGraph d).Adj centerTwo right := cubicGraph_adj_stepFrom centerTwo _
    walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega)
      (SimpleGraph.Walk.cons hleft
        (SimpleGraph.Walk.cons hmiddle
          (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil))) := by
  let centerOne := finiteClusterGlueCenter hd x
  let centerTwo := finiteClusterOddGlueCenterTwo hd x
  let right := cubicStepFrom centerTwo ((⟨0, hd⟩ : Fin d), true)
  let hleft : (cubicGraph d).Adj x centerOne := cubicGraph_adj_stepFrom x _
  let hmiddle : (cubicGraph d).Adj centerOne centerTwo := cubicGraph_adj_stepFrom centerOne _
  let hright : (cubicGraph d).Adj centerTwo right := cubicGraph_adj_stepFrom centerTwo _
  let bridge : (cubicGraph d).Walk x right :=
    SimpleGraph.Walk.cons hleft
      (SimpleGraph.Walk.cons hmiddle
        (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil))
  change walkIsOpen
    (spliceOn (finiteClusterOddGlueStar hd x)
      (finiteClusterOddGlueOpenTrace hd x) omega) bridge
  intro e he
  let ew : CubicEdge d := ⟨e, bridge.edges_subset_edgeSet he⟩
  have heCases :
      e = s(x, finiteClusterGlueCenter hd x) ∨
      e = s(finiteClusterGlueCenter hd x, finiteClusterOddGlueCenterTwo hd x) ∨
      e = s(finiteClusterOddGlueCenterTwo hd x,
        cubicStepFrom (finiteClusterOddGlueCenterTwo hd x)
          ((⟨0, hd⟩ : Fin d), true)) := by
    simpa [bridge, hleft, hmiddle, hright, centerOne, centerTwo, right] using he
  rcases heCases with heLeft | heMiddle | heRight
  · let e' : CubicEdge d :=
      cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), false)
    have heq : e = e'.1 := by
      simpa [e', finiteClusterGlue_leftEdge_sym2] using heLeft
    change ew ∈ spliceOn (finiteClusterOddGlueStar hd x)
      (finiteClusterOddGlueOpenTrace hd x) omega
    rw [show ew = e' by exact Subtype.ext heq]
    rw [mem_spliceOn_of_mem]
    · simp [finiteClusterOddGlueOpenTrace, e']
    · rw [finiteClusterOddGlueStar, Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · let e' : CubicEdge d :=
      cubicStepEdge (finiteClusterGlueCenter hd x)
        ((⟨0, hd⟩ : Fin d), true)
    have heq : e = e'.1 := by
      simpa [e', finiteClusterOddGlue_middleEdge_sym2] using heMiddle
    change ew ∈ spliceOn (finiteClusterOddGlueStar hd x)
      (finiteClusterOddGlueOpenTrace hd x) omega
    rw [show ew = e' by exact Subtype.ext heq]
    rw [mem_spliceOn_of_mem]
    · simp [finiteClusterOddGlueOpenTrace, e']
    · rw [finiteClusterOddGlueStar, Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · let e' : CubicEdge d :=
      cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
        ((⟨0, hd⟩ : Fin d), true)
    have heq : e = e'.1 := by
      simpa [e', finiteClusterOddGlue_rightEdge_sym2] using heRight
    change ew ∈ spliceOn (finiteClusterOddGlueStar hd x)
      (finiteClusterOddGlueOpenTrace hd x) omega
    rw [show ew = e' by exact Subtype.ext heq]
    rw [mem_spliceOn_of_mem]
    · simp [finiteClusterOddGlueOpenTrace, e']
    · rw [finiteClusterOddGlueStar, Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The odd splice joins the selected left and mirrored right finite clusters. -/
theorem splice_endpoint_inter_mem_oddConnectionEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      oddMirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega ∈
      connectionEvent d cubicOrigin (cubicAxisVertex d (2 * m + 3)) := by
  rcases homega with ⟨hleftEvent, hrightEvent⟩
  obtain ⟨X, hXcyl⟩ := Set.mem_iUnion.mp hleftEvent
  change cubicGraphIsoConfigurationPullback
      (finiteClusterAxisOddMirrorIso d hd m) omega ∈
    anchoredEndpointClusterEvent d hd m x at hrightEvent
  obtain ⟨Y, hYcyl⟩ := Set.mem_iUnion.mp hrightEvent
  let A := X.1.animal
  let B := Y.1.animal
  have hAx : A.topRight = x := X.2
  have hBx : B.topRight = x := Y.2
  obtain ⟨wA, hwA⟩ := A.connected A.topRight A.topRight_mem
  obtain ⟨wB, hwB⟩ := B.connected B.topRight B.topRight_mem
  have hwAOpen := walkIsOpen_splice_oddGlueStar_of_animal A
    X.1.animal_anchored X.1.animal_direction hAx hXcyl wA hwA
  have hwBMapOpen := walkIsOpen_splice_oddGlueStar_of_mappedAnimal B
    Y.1.animal_anchored Y.1.animal_direction hBx hYcyl wB hwB
  let centerOne := finiteClusterGlueCenter hd x
  let centerTwo := finiteClusterOddGlueCenterTwo hd x
  let right := cubicStepFrom centerTwo ((⟨0, hd⟩ : Fin d), true)
  have hxcoord : x ⟨0, hd⟩ = (m : ℤ) := by
    rw [← hAx]
    exact X.1.topRight_coordinate_zero
  have hFright : finiteClusterAxisOddMirrorIso d hd m x = right := by
    simpa [centerOne, centerTwo, right, finiteClusterOddGlueCenterTwo,
      finiteClusterGlueCenter] using
        finiteClusterAxisOddMirrorIso_rightEndpoint hd hxcoord
  let wBMap0 := wB.map (finiteClusterAxisOddMirrorIso d hd m).toHom
  let wBMap : (cubicGraph d).Walk (cubicAxisVertex d (2 * m + 3)) right :=
    wBMap0.copy (by simp) (by simp [hBx, hFright])
  have hwBOpen : walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega) wBMap := by
    exact (walkIsOpen_copy wBMap0 (by simp)
      (by simp [hBx, hFright])).mpr hwBMapOpen
  let hleft : (cubicGraph d).Adj x centerOne := cubicGraph_adj_stepFrom x _
  let hmiddle : (cubicGraph d).Adj centerOne centerTwo := cubicGraph_adj_stepFrom centerOne _
  let hright : (cubicGraph d).Adj centerTwo right := cubicGraph_adj_stepFrom centerTwo _
  let bridge : (cubicGraph d).Walk x right :=
    SimpleGraph.Walk.cons hleft
      (SimpleGraph.Walk.cons hmiddle
        (SimpleGraph.Walk.cons hright SimpleGraph.Walk.nil))
  have hbridgeOpen : walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega) bridge := by
    simpa [bridge, centerOne, centerTwo, right, hleft, hmiddle, hright] using
      walkIsOpen_oddGlueBridge_splice hd x omega
  let w : (cubicGraph d).Walk cubicOrigin (cubicAxisVertex d (2 * m + 3)) :=
    (wA.copy rfl hAx).append (bridge.append wBMap.reverse)
  refine ⟨w, ?_⟩
  apply walkIsOpen_append
  · exact (walkIsOpen_copy wA rfl hAx).mpr hwAOpen
  · exact walkIsOpen_append hbridgeOpen (walkIsOpen_reverse hwBOpen)

/-! ### Finiteness of the odd glued cluster -/

/-- The finite vertex set containing the cluster after the two-star odd overwrite. -/
noncomputable def finiteClusterOddGluedVertices
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t) : Finset (Cubic d) := by
  classical
  exact (A.vertices ∪
      {finiteClusterGlueCenter hd x, finiteClusterOddGlueCenterTwo hd x}) ∪
    B.vertices.map (finiteClusterAxisOddMirrorIso d hd m).toEquiv.toEmbedding

theorem finiteClusterOddGlueOpenTrace_edge_cases
    {d : ℕ} (hd : 0 < d) (x : Cubic d) {e : CubicEdge d}
    (he : e ∈ finiteClusterOddGlueOpenTrace hd x) :
    e = cubicStepEdge (finiteClusterGlueCenter hd x)
          ((⟨0, hd⟩ : Fin d), false) ∨
      e = cubicStepEdge (finiteClusterGlueCenter hd x)
          ((⟨0, hd⟩ : Fin d), true) ∨
      e = cubicStepEdge (finiteClusterOddGlueCenterTwo hd x)
          ((⟨0, hd⟩ : Fin d), true) := by
  simpa [finiteClusterOddGlueOpenTrace] using he

theorem mem_finiteClusterOddGluedVertices_of_mem_openTrace_endpoint
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    (hxcoord : x ⟨0, hd⟩ = (m : ℤ))
    {e : CubicEdge d} (heTrace : e ∈ finiteClusterOddGlueOpenTrace hd x)
    {v : Cubic d} (hve : v ∈ (e : Sym2 (Cubic d))) :
    v ∈ finiteClusterOddGluedVertices (m := m) hd x A B := by
  classical
  rcases finiteClusterOddGlueOpenTrace_edge_cases hd x heTrace with rfl | rfl | rfl
  · rw [finiteClusterGlue_leftEdge_sym2] at hve
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · simp [finiteClusterOddGluedVertices, ← hAx, A.topRight_mem]
    · simp [finiteClusterOddGluedVertices]
  · rw [finiteClusterOddGlue_middleEdge_sym2] at hve
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | rfl <;> simp [finiteClusterOddGluedVertices]
  · rw [finiteClusterOddGlue_rightEdge_sym2] at hve
    rw [Sym2.mem_iff] at hve
    rcases hve with rfl | hvRight
    · simp [finiteClusterOddGluedVertices]
    · have hFright := finiteClusterAxisOddMirrorIso_rightEndpoint hd hxcoord
      have hvF :
          cubicStepFrom (finiteClusterOddGlueCenterTwo hd x)
              ((⟨0, hd⟩ : Fin d), true) =
            finiteClusterAxisOddMirrorIso d hd m x := by
        simpa [finiteClusterOddGlueCenterTwo, finiteClusterGlueCenter] using hFright.symm
      rw [hvRight, hvF]
      rw [finiteClusterOddGluedVertices, Finset.mem_union]
      right
      apply Finset.mem_map.mpr
      refine ⟨B.topRight, B.topRight_mem, ?_⟩
      change finiteClusterAxisOddMirrorIso d hd m B.topRight =
        finiteClusterAxisOddMirrorIso d hd m x
      rw [hBx]

/-- One open step in the odd spliced configuration cannot leave the finite union of the two
animal vertex sets and the two separating vertices. -/
theorem finiteClusterOddGluedVertices_step_closed
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hA : A.IsBottomLeftAnchored)
    (hAdir : A.IsFirstDirectionMaximal hd m)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    {omega : EdgeConfiguration d}
    (hAcyl : omega ∈ A.clusterCylinder)
    (hBcyl : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisOddMirrorIso d hd m) omega ∈ B.clusterCylinder)
    {u v : Cubic d}
    (hu : u ∈ finiteClusterOddGluedVertices (m := m) hd x A B)
    (huv : (cubicGraph d).Adj u v)
    (hopen : (⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩ : CubicEdge d) ∈
      spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega) :
    v ∈ finiteClusterOddGluedVertices (m := m) hd x A B := by
  classical
  let e : CubicEdge d :=
    ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩
  have huve : u ∈ (e : Sym2 (Cubic d)) := by simp [e]
  have hvve : v ∈ (e : Sym2 (Cubic d)) := by simp [e]
  by_cases heStar : e ∈ finiteClusterOddGlueStar hd x
  · have heTrace : e ∈ finiteClusterOddGlueOpenTrace hd x := by
      exact (mem_spliceOn_of_mem heStar).mp hopen
    have hxcoord : x ⟨0, hd⟩ = (m : ℤ) := by
      rw [← hAx]
      have hnonneg := A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
      have hspan := hAdir.2
      rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
      simp only [cubicOrigin, sub_zero] at hspan
      calc
        A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
          (Int.toNat_of_nonneg hnonneg).symm
        _ = (m : ℤ) := by exact_mod_cast hspan
    exact mem_finiteClusterOddGluedVertices_of_mem_openTrace_endpoint
      hd x A B hAx hBx hxcoord heTrace hvve
  · have heOmega : e ∈ omega := by
      exact (mem_spliceOn_of_notMem
        (finiteClusterOddGlueOpenTrace_subset_star hd x) heStar).mp hopen
    simp only [finiteClusterOddGluedVertices, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_map] at hu ⊢
    rcases hu with ((huA | huCenterOne | huCenterTwo) | huB)
    · apply Or.inl
      apply Or.inl
      let q : (cubicGraph d).Walk u v :=
        SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
      have hqOpen : walkIsOpen omega q := by
        intro f hf
        simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.mem_singleton] at hf
        have hfe : f = e.1 := by simpa [e] using hf
        simpa [hfe] using heOmega
      exact A.endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder
        hAcyl huA q hqOpen
    · subst u
      exfalso
      exact heStar (mem_finiteClusterOddGlueStar_of_centerOne_incident huve)
    · subst u
      exfalso
      exact heStar (mem_finiteClusterOddGlueStar_of_centerTwo_incident huve)
    · right
      obtain ⟨b, hbB, hbu⟩ := huB
      let q : (cubicGraph d).Walk u v :=
        SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
      have hqOpen : walkIsOpen omega q := by
        intro f hf
        simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.mem_singleton] at hf
        have hfe : f = e.1 := by simpa [e] using hf
        simpa [hfe] using heOmega
      have hqBackOpen : walkIsOpen
          (cubicGraphIsoConfigurationPullback
            (finiteClusterAxisOddMirrorIso d hd m) omega)
          (q.map (finiteClusterAxisOddMirrorIso d hd m).symm.toHom) := by
        have h := walkIsOpen_map_cubicGraphIso
          (finiteClusterAxisOddMirrorIso d hd m).symm q
          (show walkIsOpen
            (cubicGraphIsoConfigurationPullback
              (finiteClusterAxisOddMirrorIso d hd m).symm
              (cubicGraphIsoConfigurationPullback
                (finiteClusterAxisOddMirrorIso d hd m) omega)) q by
              simpa using hqOpen)
        simpa using h
      let qBack0 := q.map (finiteClusterAxisOddMirrorIso d hd m).symm.toHom
      have hstart : (finiteClusterAxisOddMirrorIso d hd m).symm u = b := by
        rw [← hbu]
        simp
      let qBack : (cubicGraph d).Walk b
          ((finiteClusterAxisOddMirrorIso d hd m).symm v) :=
        qBack0.copy (by simpa [qBack0] using hstart) rfl
      have hqBackOpen' : walkIsOpen
          (cubicGraphIsoConfigurationPullback
            (finiteClusterAxisOddMirrorIso d hd m) omega) qBack := by
        exact (walkIsOpen_copy qBack0
          (by simpa [qBack0] using hstart) rfl).mpr hqBackOpen
      have hvB : (finiteClusterAxisOddMirrorIso d hd m).symm v ∈ B.vertices :=
        B.endpoint_mem_vertices_of_walkIsOpen_of_mem_clusterCylinder
          hBcyl hbB qBack hqBackOpen'
      exact ⟨(finiteClusterAxisOddMirrorIso d hd m).symm v, hvB, by simp⟩

theorem endpoint_mem_finiteClusterOddGluedVertices_of_walkIsOpen
    {d s t m : ℕ} (hd : 0 < d) (x : Cubic d)
    (A : CubicBondAnimal d s) (B : CubicBondAnimal d t)
    (hA : A.IsBottomLeftAnchored)
    (hAdir : A.IsFirstDirectionMaximal hd m)
    (hAx : A.topRight = x) (hBx : B.topRight = x)
    {omega : EdgeConfiguration d}
    (hAcyl : omega ∈ A.clusterCylinder)
    (hBcyl : cubicGraphIsoConfigurationPullback
      (finiteClusterAxisOddMirrorIso d hd m) omega ∈ B.clusterCylinder)
    {u v : Cubic d}
    (hu : u ∈ finiteClusterOddGluedVertices (m := m) hd x A B)
    (w : (cubicGraph d).Walk u v)
    (hopen : walkIsOpen
      (spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega) w) :
    v ∈ finiteClusterOddGluedVertices (m := m) hd x A B := by
  induction w with
  | nil => exact hu
  | @cons u z v huz w ih =>
      have heOpen :
          (⟨s(u, z), by simpa [SimpleGraph.mem_edgeSet] using huz⟩ : CubicEdge d) ∈
            spliceOn (finiteClusterOddGlueStar hd x)
              (finiteClusterOddGlueOpenTrace hd x) omega := by
        apply hopen
        simp
      have hz := finiteClusterOddGluedVertices_step_closed hd x A B hA
        hAdir hAx hBx hAcyl hBcyl hu huz heOpen
      apply ih hz
      intro e he
      exact hopen e (by simp [he])

theorem splice_endpoint_inter_mem_oddFiniteClusterEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      oddMirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega ∈ finiteClusterEvent d := by
  rcases homega with ⟨hleftEvent, hrightEvent⟩
  obtain ⟨X, hXcyl⟩ := Set.mem_iUnion.mp hleftEvent
  change cubicGraphIsoConfigurationPullback
      (finiteClusterAxisOddMirrorIso d hd m) omega ∈
    anchoredEndpointClusterEvent d hd m x at hrightEvent
  obtain ⟨Y, hYcyl⟩ := Set.mem_iUnion.mp hrightEvent
  let A := X.1.animal
  let B := Y.1.animal
  have hAx : A.topRight = x := X.2
  have hBx : B.topRight = x := Y.2
  change (cubicOpenCluster d
    (spliceOn (finiteClusterOddGlueStar hd x)
      (finiteClusterOddGlueOpenTrace hd x) omega)).Finite
  apply Set.Finite.subset
    (finiteClusterOddGluedVertices (m := m) hd x A B).finite_toSet
  intro z hz
  rcases hz with ⟨w, hwOpen⟩
  exact endpoint_mem_finiteClusterOddGluedVertices_of_walkIsOpen
    hd x A B X.1.animal_anchored X.1.animal_direction hAx hBx
    hXcyl hYcyl
    (by simp [finiteClusterOddGluedVertices, A, B, A.origin_mem]) w hwOpen

theorem splice_endpoint_inter_mem_oddTruncatedConnectionEvent
    {d m : ℕ} (hd : 0 < d) (x : Cubic d)
    {omega : EdgeConfiguration d}
    (homega : omega ∈ anchoredEndpointClusterEvent d hd m x ∩
      oddMirroredAnchoredEndpointClusterEvent d hd m x) :
    spliceOn (finiteClusterOddGlueStar hd x)
        (finiteClusterOddGlueOpenTrace hd x) omega ∈
      truncatedConnectionEvent d (cubicAxisVertex d (2 * m + 3)) :=
  ⟨splice_endpoint_inter_mem_oddConnectionEvent hd x homega,
    splice_endpoint_inter_mem_oddFiniteClusterEvent hd x homega⟩

/-! ### The odd lower gluing inequality -/

/-- Endpoint-conditioned form of (8.60), before the two pigeonhole estimates. -/
theorem oddGluePenalty_mul_anchoredEndpointMass_sq_le_truncatedAxisConnectivity
    {d m : ℕ} (hd : 0 < d) (p : I) (x : Cubic d) :
    (p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d - 4) *
        anchoredEndpointMass d p hd m x ^ 2 ≤
      truncatedAxisConnectivity d p (2 * m + 3) := by
  have hoverwrite := finiteBernoulliWeight_mul_measureReal_le_of_splice_subset
    (ι := CubicEdge d) p
    (finiteClusterOddGlueOpenTrace_subset_star hd x)
    (measurableSet_truncatedConnectionEvent d
      (cubicAxisVertex d (2 * m + 3)))
    (fun _omega homega =>
      splice_endpoint_inter_mem_oddTruncatedConnectionEvent hd x homega)
  rw [finiteBernoulliWeight_oddGlueOpenTrace,
    show setBer((Set.univ : Set (CubicEdge d)), p).real
        (anchoredEndpointClusterEvent d hd m x ∩
          oddMirroredAnchoredEndpointClusterEvent d hd m x) =
        anchoredEndpointMass d p hd m x ^ 2 by
      simpa [bernoulliBondMeasure] using
        bernoulliBondMeasure_real_endpoint_inter_oddMirrored d p hd m x] at hoverwrite
  simpa [bernoulliBondMeasure, truncatedAxisConnectivity,
    truncatedTwoPointConnectivity] using hoverwrite

/-- Denominator-free form of equation (8.60). -/
theorem oddGluePenalty_mul_diameterProbability_sq_le_prefactor_mul_truncatedAxis
    {d m : ℕ} (hd : 0 < d) (p : I) :
    (p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d - 4) *
        finiteClusterLInfDiameterProbability d p m ^ 2 ≤
      ((d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
          ((cubicBoxSurface d cubicOrigin m).card : ℝ)) ^ 2 *
        truncatedAxisConnectivity d p (2 * m + 3) := by
  obtain ⟨x, hxSurface, hxMass⟩ :=
    exists_boxSurface_mul_anchoredEndpointMass_ge_total d p hd m
  let Q := finiteClusterLInfDiameterProbability d p m
  let M := CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd m
  let R := anchoredEndpointMass d p hd m x
  let D := (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
    ((cubicBoxSurface d cubicOrigin m).card : ℝ)
  let c := (p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d - 4)
  let T := truncatedAxisConnectivity d p (2 * m + 3)
  have hQM : Q ≤
      (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := by
    simpa [Q, M] using
      finiteClusterLInfDiameterProbability_le_directionAnchorMass hd p
  have hMR : M ≤ ((cubicBoxSurface d cubicOrigin m).card : ℝ) * R := by
    simpa [M, R] using hxMass
  have hQD : Q ≤ D * R := by
    calc
      Q ≤ (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) * M := hQM
      _ ≤ (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
          (((cubicBoxSurface d cubicOrigin m).card : ℝ) * R) := by
        gcongr
      _ = D * R := by ring
  have hQ0 : 0 ≤ Q := finiteClusterLInfDiameterProbability_nonneg d p m
  have hD0 : 0 ≤ D := by positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    rw [anchoredEndpointMass_eq_probability]
    exact measureReal_nonneg
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (pow_nonneg p.2.1 3)
      (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hsq : Q ^ 2 ≤ D ^ 2 * R ^ 2 := by nlinarith
  have hlocal : c * R ^ 2 ≤ T := by
    simpa [c, R, T] using
      oddGluePenalty_mul_anchoredEndpointMass_sq_le_truncatedAxisConnectivity
        hd p x
  calc
    c * Q ^ 2 ≤ c * (D ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hc0
    _ = D ^ 2 * (c * R ^ 2) := by ring
    _ ≤ D ^ 2 * T := mul_le_mul_of_nonneg_left hlocal (sq_nonneg D)

/-- Equation (8.60), with the exact source polynomial prefactor. -/
theorem truncatedAxisConnectivity_odd_glue_lower_bound
    {d m : ℕ} (hd : 0 < d) (p : I) :
    ((p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d - 4) *
        finiteClusterLInfDiameterProbability d p m ^ 2) /
        ((d : ℝ) ^ 2 *
          ((cubicBoxSurface d cubicOrigin m).card : ℝ) ^ 2 *
          ((((2 * m + 1 : ℕ) : ℝ) ^ d) ^ 2)) ≤
      truncatedAxisConnectivity d p (2 * m + 3) := by
  have hden :=
    oddGluePenalty_mul_diameterProbability_sq_le_prefactor_mul_truncatedAxis
      (m := m) hd p
  let D := (d : ℝ) * (((2 * m + 1 : ℕ) : ℝ) ^ d) *
    ((cubicBoxSurface d cubicOrigin m).card : ℝ)
  have hsurface : 0 < ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hform :
      (d : ℝ) ^ 2 * ((cubicBoxSurface d cubicOrigin m).card : ℝ) ^ 2 *
          ((((2 * m + 1 : ℕ) : ℝ) ^ d) ^ 2) = D ^ 2 := by
    dsimp [D]
    ring
  rw [hform]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).2
  convert hden using 1 <;> (dsimp [D]; ring)

/-! ### Logarithmic squeeze -/

/-- The common polynomial denominator in (8.59) and (8.60). -/
noncomputable def truncatedGlueDenominator (d m : ℕ) : ℝ :=
  (d : ℝ) ^ 2 *
    ((cubicBoxSurface d cubicOrigin m).card : ℝ) ^ 2 *
    ((((2 * m + 1 : ℕ) : ℝ) ^ d) ^ 2)

theorem truncatedGlueDenominator_pos
    {d : ℕ} (hd : 0 < d) (m : ℕ) :
    0 < truncatedGlueDenominator d m := by
  unfold truncatedGlueDenominator
  have hs : 0 < ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
  positivity

private theorem cubicBoxSurface_log_div_nat_tendsto_zero
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ ↦
      Real.log ((cubicBoxSurface d cubicOrigin m).card : ℝ) / (m : ℝ))
      atTop (nhds 0) := by
  let C : ℝ := Real.log (2 * d : ℕ)
  have hC : Tendsto (fun m : ℕ ↦ C / (m : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hpoly := tendsto_log_two_mul_add_one_div_nat.const_mul ((d - 1 : ℕ) : ℝ)
  have hupperT : Tendsto (fun m : ℕ ↦
      C / (m : ℝ) + ((d - 1 : ℕ) : ℝ) *
        (Real.log ((2 * m + 1 : ℕ) : ℝ) / (m : ℝ)))
      atTop (nhds 0) := by
    simpa using hC.add hpoly
  have hlowerT : Tendsto (fun _m : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hlower : ∀ᶠ m : ℕ in atTop,
      0 ≤ Real.log ((cubicBoxSurface d cubicOrigin m).card : ℝ) / (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hs : 1 ≤ ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
      exact_mod_cast Finset.one_le_card.mpr
        ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
    exact div_nonneg (Real.log_nonneg hs) (by positivity)
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log ((cubicBoxSurface d cubicOrigin m).card : ℝ) / (m : ℝ) ≤
        C / (m : ℝ) + ((d - 1 : ℕ) : ℝ) *
          (Real.log ((2 * m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hsPos : 0 < ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
    have hboundNat := cubicBoxSurface_card_le hd cubicOrigin (n := m)
    have hbound : ((cubicBoxSurface d cubicOrigin m).card : ℝ) ≤
        (2 * d : ℕ) * (((2 * m + 1 : ℕ) : ℝ) ^ (d - 1)) := by
      exact_mod_cast hboundNat
    have hconstPos : 0 < ((2 * d : ℕ) : ℝ) := by positivity
    have hbasePos : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
    have hlog := Real.log_le_log hsPos hbound
    rw [Real.log_mul hconstPos.ne' (pow_pos hbasePos (d - 1)).ne',
      Real.log_pow] at hlog
    have hmR : (0 : ℝ) < m := by
      exact_mod_cast (zero_lt_one.trans_le hm)
    field_simp [hmR.ne']
    simpa [C] using hlog
  exact hlowerT.squeeze' hupperT hlower hupper

private theorem truncatedGlueDenominator_log_div_nat_tendsto_zero
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ ↦ Real.log (truncatedGlueDenominator d m) / (m : ℝ))
      atTop (nhds 0) := by
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log (d : ℝ))
  have hsurface := (cubicBoxSurface_log_div_nat_tendsto_zero hd).const_mul (2 : ℝ)
  have hbox := tendsto_log_two_mul_add_one_div_nat.const_mul (2 * d : ℝ)
  have hsum : Tendsto (fun m : ℕ ↦
      (2 * Real.log (d : ℝ)) / (m : ℝ) +
        2 * (Real.log ((cubicBoxSurface d cubicOrigin m).card : ℝ) / (m : ℝ)) +
        (2 * d : ℝ) *
          (Real.log ((2 * m + 1 : ℕ) : ℝ) / (m : ℝ)))
      atTop (nhds 0) := by
    simpa using (hconst.add hsurface).add hbox
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hdR : 0 < (d : ℝ) := by positivity
  have hs : 0 < ((cubicBoxSurface d cubicOrigin m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicAxisVertex d m, cubicAxisVertex_mem_boxSurface hd⟩
  have hb : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
  unfold truncatedGlueDenominator
  rw [Real.log_mul (mul_pos (pow_pos hdR 2) (pow_pos hs 2)).ne'
      (pow_pos (pow_pos hb d) 2).ne',
    Real.log_mul (pow_pos hdR 2).ne' (pow_pos hs 2).ne',
    Real.log_pow, Real.log_pow, Real.log_pow]
  rw [Real.log_pow]
  field_simp
  ring

private theorem tendsto_nat_two_mul_add_atTop (k : ℕ) :
    Tendsto (fun m : ℕ ↦ 2 * m + k) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  omega

private theorem tendsto_two_mul_div_two_mul_add (k : ℕ) :
    Tendsto (fun m : ℕ ↦ (2 * (m : ℝ)) / (2 * (m : ℝ) + k))
      atTop (nhds 1) := by
  have hk : Tendsto (fun m : ℕ ↦ (k : ℝ) / (m : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)
  have hnum : Tendsto (fun _m : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hden : Tendsto (fun m : ℕ ↦ (2 : ℝ) + (k : ℝ) / (m : ℝ))
      atTop (nhds (2 + 0)) := tendsto_const_nhds.add hk
  have h := hnum.div hden (by norm_num : (2 : ℝ) + 0 ≠ 0)
  have heq : (∀ᶠ m : ℕ in atTop,
      (2 : ℝ) / (2 + (k : ℝ) / (m : ℝ)) =
        2 * (m : ℝ) / (2 * (m : ℝ) + k)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [add_zero, div_self (by norm_num : (2 : ℝ) ≠ 0)] using h.congr' heq

private theorem tendsto_nat_div_two_mul_add (k : ℕ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) / (2 * (m : ℝ) + k))
      atTop (nhds (1 / 2 : ℝ)) := by
  have h := (tendsto_two_mul_div_two_mul_add k).const_mul (1 / 2 : ℝ)
  convert h using 1 <;> norm_num
  funext m
  ring

private theorem truncatedGlueDenominator_log_div_two_mul_add_tendsto_zero
    {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Tendsto (fun m : ℕ ↦
      Real.log (truncatedGlueDenominator d m) / (2 * (m : ℝ) + k))
      atTop (nhds 0) := by
  have h := (truncatedGlueDenominator_log_div_nat_tendsto_zero hd).mul
    (tendsto_nat_div_two_mul_add k)
  have heq : (∀ᶠ m : ℕ in atTop,
      Real.log (truncatedGlueDenominator d m) / (m : ℝ) *
          ((m : ℝ) / (2 * (m : ℝ) + k)) =
        Real.log (truncatedGlueDenominator d m) / (2 * (m : ℝ) + k)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    field_simp
  simpa using h.congr' heq

private theorem truncatedAxisConnectivity_glue_subsequence_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (k : ℕ) (hk : 0 < k) (c : ℝ) (hc : 0 < c)
    (hglue : ∀ m : ℕ,
      c * finiteClusterLInfDiameterProbability d p m ^ 2 /
          truncatedGlueDenominator d m ≤
        truncatedAxisConnectivity d p (2 * m + k)) :
    Tendsto (fun m : ℕ ↦
      -Real.log (truncatedAxisConnectivity d p (2 * m + k)) /
        (2 * m + k : ℕ)) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  let Q := finiteClusterLInfDiameterProbability d p
  let T := truncatedAxisConnectivity d p
  let R := finiteBoxRadiusProbability d p
  let D := truncatedGlueDenominator d
  let a := finiteClusterRadiusDecayRate d p
  have hNtop := tendsto_nat_two_mul_add_atTop k
  have hQrate := finiteClusterLInfDiameterProbability_logRate_tendsto hd p hp0 hp1
  have hQtermRaw := hQrate.mul (tendsto_two_mul_div_two_mul_add k)
  have hQterm : Tendsto (fun m : ℕ ↦
      -2 * Real.log (Q m) / (2 * (m : ℝ) + k)) atTop (nhds a) := by
    have heq : (∀ᶠ m : ℕ in atTop,
        (-Real.log (finiteClusterLInfDiameterProbability d p m) / (m : ℝ)) *
            (2 * (m : ℝ) / (2 * (m : ℝ) + k)) =
          -2 * Real.log (Q m) / (2 * (m : ℝ) + k)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      dsimp only [Q]
      field_simp
    simpa only [a, mul_one] using hQtermRaw.congr' heq
  have hconstBase : Tendsto (fun n : ℕ ↦ -Real.log c / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (-Real.log c)
  have hconst : Tendsto (fun m : ℕ ↦
      -Real.log c / (2 * m + k : ℕ)) atTop (nhds 0) := by
    change Tendsto
      ((fun n : ℕ ↦ -Real.log c / (n : ℝ)) ∘ (fun m : ℕ ↦ 2 * m + k))
      atTop (nhds 0)
    exact hconstBase.comp hNtop
  have hden : Tendsto (fun m : ℕ ↦
      Real.log (D m) / (2 * m + k : ℕ)) atTop (nhds 0) := by
    simpa only [D, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      truncatedGlueDenominator_log_div_two_mul_add_tendsto_zero
        (Nat.zero_lt_of_lt hd) k
  have hupperT : Tendsto (fun m : ℕ ↦
      (-Real.log c - 2 * Real.log (Q m) + Real.log (D m)) /
        (2 * m + k : ℕ)) atTop (nhds a) := by
    have hsum := (hconst.add hQterm).add hden
    have heq : (∀ᶠ m : ℕ in atTop,
        -Real.log c / (2 * m + k : ℕ) +
              (-2 * Real.log (Q m) / (2 * (m : ℝ) + k)) +
              Real.log (D m) / (2 * m + k : ℕ) =
          (-Real.log c - 2 * Real.log (Q m) + Real.log (D m)) /
            (2 * m + k : ℕ)) := by
      filter_upwards with m
      have hdenom : (0 : ℝ) < (2 * m + k : ℕ) := by positivity
      push_cast
      field_simp
      ring
    simpa only [zero_add, add_zero] using hsum.congr' heq
  have hlowerT : Tendsto (fun m : ℕ ↦
      -Real.log (R (2 * m + k)) / (2 * m + k : ℕ)) atTop (nhds a) := by
    simpa only [R, a] using
      (finiteBoxRadiusProbability_logRate_tendsto hd p hp0 hp1).comp hNtop
  have hlower : ∀ᶠ m : ℕ in atTop,
      -Real.log (R (2 * m + k)) / (2 * m + k : ℕ) ≤
        -Real.log (T (2 * m + k)) / (2 * m + k : ℕ) := by
    filter_upwards with m
    have hNpos : 0 < 2 * m + k := by omega
    have hTpos : 0 < T (2 * m + k) := by
      have hQpos : 0 < Q m :=
        finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 m
      have hDpos : 0 < D m := truncatedGlueDenominator_pos
        (Nat.zero_lt_of_lt hd) m
      exact (div_pos (mul_pos hc (sq_pos_of_pos hQpos)) hDpos).trans_le
        (hglue m)
    have hle : T (2 * m + k) ≤ R (2 * m + k) := by
      simpa only [T, R] using
        truncatedAxisConnectivity_le_finiteBoxRadiusProbability
          (Nat.zero_lt_of_lt hd) p (2 * m + k)
    exact div_le_div_of_nonneg_right
      (neg_le_neg (Real.log_le_log hTpos hle)) (by positivity)
  have hupper : ∀ᶠ m : ℕ in atTop,
      -Real.log (T (2 * m + k)) / (2 * m + k : ℕ) ≤
        (-Real.log c - 2 * Real.log (Q m) + Real.log (D m)) /
          (2 * m + k : ℕ) := by
    filter_upwards with m
    have hNpos : 0 < 2 * m + k := by omega
    have hQpos : 0 < Q m :=
      finiteClusterLInfDiameterProbability_pos hd p hp0 hp1 m
    have hDpos : 0 < D m := truncatedGlueDenominator_pos
      (Nat.zero_lt_of_lt hd) m
    have hleftpos : 0 < c * Q m ^ 2 / D m :=
      div_pos (mul_pos hc (sq_pos_of_pos hQpos)) hDpos
    have hTpos : 0 < T (2 * m + k) := hleftpos.trans_le (hglue m)
    have hlog := Real.log_le_log hleftpos (hglue m)
    rw [Real.log_div (mul_pos hc (sq_pos_of_pos hQpos)).ne' hDpos.ne',
      Real.log_mul hc.ne' (sq_pos_of_pos hQpos).ne', Real.log_pow] at hlog
    change Real.log c + (2 : ℝ) * Real.log (Q m) - Real.log (D m) ≤
      Real.log (T (2 * m + k)) at hlog
    apply (div_le_div_iff_of_pos_right (show (0 : ℝ) < (2 * m + k : ℕ) by
      positivity)).2
    linarith
  exact hlowerT.squeeze' hupperT hlower hupper

theorem truncatedAxisConnectivity_even_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun m : ℕ ↦
      -Real.log (truncatedAxisConnectivity d p (2 * m + 2)) /
        (2 * m + 2 : ℕ)) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  let c : ℝ := (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  apply truncatedAxisConnectivity_glue_subsequence_logRate_tendsto
    hd p hp0 hp1 2 (by omega) c hc
  intro m
  simpa only [c, truncatedGlueDenominator] using
    truncatedAxisConnectivity_even_glue_lower_bound
      (m := m) (Nat.zero_lt_of_lt hd) p

theorem truncatedAxisConnectivity_odd_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun m : ℕ ↦
      -Real.log (truncatedAxisConnectivity d p (2 * m + 3)) /
        (2 * m + 3 : ℕ)) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  let c : ℝ := (p : ℝ) ^ 3 * (1 - (p : ℝ)) ^ (4 * d - 4)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  apply truncatedAxisConnectivity_glue_subsequence_logRate_tendsto
    hd p hp0 hp1 3 (by omega) c hc
  intro m
  simpa only [c, truncatedGlueDenominator] using
    truncatedAxisConnectivity_odd_glue_lower_bound
      (m := m) (Nat.zero_lt_of_lt hd) p

private theorem tendsto_nat_of_even_odd_succ
    {f : ℕ → ℝ} {a : ℝ}
    (heven : Tendsto (fun m : ℕ ↦ f (2 * m + 2)) atTop (nhds a))
    (hodd : Tendsto (fun m : ℕ ↦ f (2 * m + 3)) atTop (nhds a)) :
    Tendsto f atTop (nhds a) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨Me, hMe⟩ := mem_atTop_sets.mp (heven hs)
  obtain ⟨Mo, hMo⟩ := mem_atTop_sets.mp (hodd hs)
  refine mem_atTop_sets.mpr ⟨2 * max Me Mo + 3, ?_⟩
  intro n hn
  let m := n / 2 - 1
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · have hm : Me ≤ m := by
      dsimp [m]
      omega
    have hnrep : n = 2 * m + 2 := by
      dsimp [m]
      omega
    rw [hnrep]
    exact hMe m hm
  · have hm : Mo ≤ m := by
      dsimp [m]
      omega
    have hnrep : n = 2 * m + 3 := by
      dsimp [m]
      omega
    rw [hnrep]
    exact hMo m hm

/-- **Grimmett, Theorem 8.53, equation (8.54).**  The truncated two-point function along a
coordinate axis has the same logarithmic decay rate as the finite-cluster radius. -/
theorem truncatedAxisConnectivity_logRate_tendsto
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦
      -Real.log (truncatedAxisConnectivity d p n) / n) atTop
      (nhds (finiteClusterRadiusDecayRate d p)) := by
  apply tendsto_nat_of_even_odd_succ
  · simpa using truncatedAxisConnectivity_even_logRate_tendsto hd p hp0 hp1
  · simpa using truncatedAxisConnectivity_odd_logRate_tendsto hd p hp0 hp1

end Percolation
