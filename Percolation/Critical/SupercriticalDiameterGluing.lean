import Percolation.Critical.SupercriticalFiniteRadius
import Percolation.Critical.ClusterSizeRate
import Percolation.Critical.CubicSymmetry

/-!
# Finite-cluster diameter gluing

This file formalizes the deterministic animal geometry in Grimmett, Lemma 8.27.  Two finite
animals whose first-coordinate widths realize their `L∞` diameters are separated by one new
vertex and joined by two new open edges.  The resulting animal has diameter exactly the sum of
the two input diameters plus two.
-/

namespace Percolation

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

namespace CubicBondAnimal

variable {d a b : ℕ}

/-- Coordinate-`L∞` diameter of the vertex set of a concrete animal. -/
noncomputable def lInfDiameter (A : CubicBondAnimal d a) : ℕ :=
  A.vertices.sup fun x ↦ A.vertices.sup fun y ↦ cubicLInfDist x y

theorem cubicLInfDist_le_lInfDiameter (A : CubicBondAnimal d a)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ A.vertices) :
    cubicLInfDist x y ≤ A.lInfDiameter := by
  exact (Finset.le_sup (s := A.vertices) (f := fun y ↦ cubicLInfDist x y) hy).trans
    (Finset.le_sup (s := A.vertices)
      (f := fun x ↦ A.vertices.sup fun y ↦ cubicLInfDist x y) hx)

theorem lInfDiameter_le_card_sub_one (A : CubicBondAnimal d a) :
    A.lInfDiameter ≤ a - 1 := by
  unfold lInfDiameter
  apply Finset.sup_le
  intro x hx
  apply Finset.sup_le
  intro y hy
  exact (cubicLInfDist_le_l1Dist x y).trans
    (A.cubicL1Dist_le_card_sub_one hx hy)

/-- The first-coordinate width, expressed using the lexicographic extrema.  Lexicographic
order compares coordinate zero first, so these are also first-coordinate extrema. -/
noncomputable def firstCoordinateSpan (A : CubicBondAnimal d a) (hd : 0 < d) : ℕ :=
  (A.topRight ⟨0, hd⟩ - A.bottomLeft ⟨0, hd⟩).natAbs

theorem bottomLeft_coordinate_zero_le (A : CubicBondAnimal d a) (hd : 0 < d)
    {x : Cubic d} (hx : x ∈ A.vertices) :
    A.bottomLeft ⟨0, hd⟩ ≤ x ⟨0, hd⟩ := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact Pi.apply_le_of_toLex (A.bottomLeft_lex_le hx)
    (i := (⟨0, hd⟩ : Fin d)) (by
      intro j hj
      exact (Fin.not_lt_zero j hj).elim)

theorem coordinate_zero_le_topRight' (A : CubicBondAnimal d a) (hd : 0 < d)
    {x : Cubic d} (hx : x ∈ A.vertices) :
    x ⟨0, hd⟩ ≤ A.topRight ⟨0, hd⟩ :=
  A.coordinate_zero_le_topRight hx hd

theorem bottomLeft_coordinate_zero_le_topRight (A : CubicBondAnimal d a) (hd : 0 < d) :
    A.bottomLeft ⟨0, hd⟩ ≤ A.topRight ⟨0, hd⟩ :=
  A.bottomLeft_coordinate_zero_le hd A.topRight_mem

theorem firstCoordinateSpan_eq_toNat_sub (A : CubicBondAnimal d a) (hd : 0 < d) :
    A.firstCoordinateSpan hd =
      Int.toNat (A.topRight ⟨0, hd⟩ - A.bottomLeft ⟨0, hd⟩) := by
  rw [firstCoordinateSpan]
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg
      (sub_nonneg.mpr (A.bottomLeft_coordinate_zero_le_topRight hd)),
    Int.toNat_of_nonneg
      (sub_nonneg.mpr (A.bottomLeft_coordinate_zero_le_topRight hd))]

theorem firstCoordinateSpan_le_lInfDiameter
    (A : CubicBondAnimal d a) (hd : 0 < d) :
    A.firstCoordinateSpan hd ≤ A.lInfDiameter := by
  rw [firstCoordinateSpan]
  exact (cubicLInfDist_coord_le A.bottomLeft A.topRight ⟨0, hd⟩).trans
    (A.cubicLInfDist_le_lInfDiameter A.bottomLeft_mem A.topRight_mem)

/-- The first direction realizes the animal diameter. -/
def IsFirstDirectionMaximal (A : CubicBondAnimal d a) (hd : 0 < d) (k : ℕ) : Prop :=
  A.lInfDiameter = k ∧ A.firstCoordinateSpan hd = k

noncomputable instance instDecidableIsFirstDirectionMaximal
    (A : CubicBondAnimal d a) (hd : 0 < d) (k : ℕ) :
    Decidable (A.IsFirstDirectionMaximal hd k) := by
  unfold IsFirstDirectionMaximal
  infer_instance

theorem lInfDiameter_eq_clusterLInfDiameter_of_mem_clusterCylinder
    (A : CubicBondAnimal d a) {omega : EdgeConfiguration d}
    (homega : omega ∈ A.clusterCylinder) :
    A.lInfDiameter = clusterLInfDiameter d omega := by
  have hcluster := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder homega
  have hfinite : (cubicOpenCluster d omega).Finite := by
    rw [hcluster]
    exact A.vertices.finite_toSet
  have hfinset : hfinite.toFinset = A.vertices := by
    ext x
    simpa [hcluster]
  rw [clusterLInfDiameter_eq_sup_of_finite hfinite, hfinset]
  rfl

/-- The lexicographic minimum of a root-preserving concatenation is inherited from the left
factor. -/
theorem rootedConcat_bottomLeft
    (A : CubicBondAnimal d a) (B : CubicBondAnimal d b)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).bottomLeft = A.bottomLeft := by
  let C := A.rootedConcat B hB hd
  apply toLex_inj.mp
  apply le_antisymm
  · apply C.bottomLeft_lex_le
    change A.bottomLeft ∈ A.concatenatedVertices B hd
    exact Finset.mem_union_left _ A.bottomLeft_mem
  · have hmem := C.bottomLeft_mem
    change C.bottomLeft ∈ A.concatenatedVertices B hd at hmem
    rw [concatenatedVertices, Finset.mem_union] at hmem
    rcases hmem with hleft | hright
    · exact A.bottomLeft_lex_le hleft
    · exact (A.toLex_lt_of_mem_vertices_of_mem_placedVertices B hB hd
        A.bottomLeft_mem hright).le

/-- The lexicographic maximum of a root-preserving concatenation is the translated maximum of
the right factor. -/
theorem rootedConcat_topRight
    (A : CubicBondAnimal d a) (B : CubicBondAnimal d b)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).topRight = A.placeRight B hd B.topRight := by
  let C := A.rootedConcat B hB hd
  have hcand : A.placeRight B hd B.topRight ∈ A.placedVertices B hd := by
    rw [mem_placedVertices_iff]
    exact ⟨B.topRight, B.topRight_mem, rfl⟩
  apply toLex_inj.mp
  apply le_antisymm
  · have hmem := C.topRight_mem
    change C.topRight ∈ A.concatenatedVertices B hd at hmem
    rw [concatenatedVertices, Finset.mem_union] at hmem
    rcases hmem with hleft | hright
    · exact (A.toLex_lt_of_mem_vertices_of_mem_placedVertices B hB hd
        hleft hcand).le
    · rw [mem_placedVertices_iff] at hright
      obtain ⟨y, hy, heq⟩ := hright
      rw [← heq]
      exact (toLex_cubicTranslate_le_iff B.bottomLeft
        (A.rightOfTopRight hd) y B.topRight).2 (B.lex_le_topRight hy)
  · apply C.lex_le_topRight
    change A.placeRight B hd B.topRight ∈ A.concatenatedVertices B hd
    exact Finset.mem_union_right _ hcand

/-- Insert one new vertex to the right of a rooted animal. -/
noncomputable def addRightSeparator (A : CubicBondAnimal d a) (hd : 0 < d) :
    CubicBondAnimal d (a + 1) :=
  A.rootedConcat (originAnimal d) (originAnimal_isBottomLeftAnchored d) hd

/-- Place an anchored second animal two lattice spacings to the right of the first. -/
noncomputable def diameterGlue
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) :
    CubicBondAnimal d ((a + 1) + b) :=
  (A.addRightSeparator hd).rootedConcat B.1 B.2 hd

@[simp] theorem originAnimal_bottomLeft (d : ℕ) :
    (originAnimal d).bottomLeft = cubicOrigin := by
  have h := (originAnimal d).bottomLeft_mem
  change (originAnimal d).bottomLeft ∈ ({cubicOrigin} : Finset (Cubic d)) at h
  simpa using h

@[simp] theorem originAnimal_topRight (d : ℕ) :
    (originAnimal d).topRight = cubicOrigin := by
  have h := (originAnimal d).topRight_mem
  change (originAnimal d).topRight ∈ ({cubicOrigin} : Finset (Cubic d)) at h
  simpa using h

private theorem cubicStepEdge_fixed_injective_for_diameter {d : ℕ} (x : Cubic d) :
    Function.Injective (cubicStepEdge x : CubicDirection d → CubicEdge d) := by
  intro u v huv
  have hs : s(x, cubicStepFrom x u) = s(x, cubicStepFrom x v) :=
    congrArg Subtype.val huv
  rcases Sym2.eq_iff.mp hs with h | h
  · exact cubicStepFrom_injective x h.2
  · exfalso
    exact (cubicGraph_adj_stepFrom x v).ne h.1

@[simp] theorem originAnimal_boundary_card (d : ℕ) :
    (originAnimal d).boundary.card = 2 * d := by
  classical
  have hstar : cubicIncidentEdges d ({cubicOrigin} : Finset (Cubic d)) =
      Finset.univ.image (fun u : CubicDirection d ↦ cubicStepEdge cubicOrigin u) := by
    ext e
    simp [cubicIncidentEdges]
  rw [boundary]
  change (cubicIncidentEdges d ({cubicOrigin} : Finset (Cubic d)) \ ∅).card = _
  rw [Finset.sdiff_empty, hstar,
    Finset.card_image_iff.mpr
      (cubicStepEdge_fixed_injective_for_diameter cubicOrigin).injOn]
  simp [CubicDirection, Fintype.card_prod, Nat.mul_comm]

@[simp] theorem weight_originAnimal (d : ℕ) (p : ℝ) :
    (originAnimal d).weight p = (1 - p) ^ (2 * d) := by
  rw [weight, originAnimal_boundary_card]
  simp [originAnimal]

@[simp] theorem addRightSeparator_topRight_coordinate_zero
    (A : CubicBondAnimal d a) (hd : 0 < d) :
    (A.addRightSeparator hd).topRight ⟨0, hd⟩ =
      A.topRight ⟨0, hd⟩ + 1 := by
  rw [addRightSeparator, A.rootedConcat_topRight
    (originAnimal d) (originAnimal_isBottomLeftAnchored d) hd]
  simp [placeRight, cubicTranslate, rightOfTopRight_coordinate_zero]

@[simp] theorem addRightSeparator_bottomLeft
    (A : CubicBondAnimal d a) (hd : 0 < d) :
    (A.addRightSeparator hd).bottomLeft = A.bottomLeft := by
  exact A.rootedConcat_bottomLeft (originAnimal d)
    (originAnimal_isBottomLeftAnchored d) hd

theorem diameterGlue_bottomLeft
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) :
    (A.diameterGlue B hd).bottomLeft = A.bottomLeft := by
  rw [diameterGlue, rootedConcat_bottomLeft, addRightSeparator_bottomLeft]

theorem diameterGlue_topRight_coordinate_zero
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) :
    (A.diameterGlue B hd).topRight ⟨0, hd⟩ =
      A.topRight ⟨0, hd⟩ + 2 + B.1.topRight ⟨0, hd⟩ := by
  rw [diameterGlue, rootedConcat_topRight]
  change cubicTranslate B.1.bottomLeft
      ((A.addRightSeparator hd).rightOfTopRight hd) B.1.topRight ⟨0, hd⟩ = _
  rw [B.2]
  simp only [cubicTranslate, cubicOrigin, Pi.zero_apply,
    rightOfTopRight_coordinate_zero, addRightSeparator_topRight_coordinate_zero]
  omega

theorem diameterGlue_firstCoordinateSpan
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) :
    (A.diameterGlue B hd).firstCoordinateSpan hd =
      A.firstCoordinateSpan hd + B.1.firstCoordinateSpan hd + 2 := by
  rw [firstCoordinateSpan_eq_toNat_sub, diameterGlue_bottomLeft,
    diameterGlue_topRight_coordinate_zero,
    firstCoordinateSpan_eq_toNat_sub, firstCoordinateSpan_eq_toNat_sub]
  have hA := A.bottomLeft_coordinate_zero_le_topRight hd
  have hB := B.1.bottomLeft_coordinate_zero_le_topRight hd
  have hB0 : B.1.bottomLeft ⟨0, hd⟩ = 0 := by
    rw [B.2]
    rfl
  rw [hB0]
  omega

theorem mem_addRightSeparator_vertices_iff
    (A : CubicBondAnimal d a) (hd : 0 < d) (x : Cubic d) :
    x ∈ (A.addRightSeparator hd).vertices ↔
      x ∈ A.vertices ∨ x = A.rightOfTopRight hd := by
  rw [addRightSeparator, rootedConcat_vertices, concatenatedVertices,
    Finset.mem_union, mem_placedVertices_iff]
  constructor
  · rintro (hx | ⟨y, hy, hxy⟩)
    · exact Or.inl hx
    · change y ∈ ({cubicOrigin} : Finset (Cubic d)) at hy
      simp only [Finset.mem_singleton] at hy
      subst y
      right
      simpa [placeRight, originAnimal_bottomLeft, cubicTranslate] using hxy.symm
  · rintro (hx | rfl)
    · exact Or.inl hx
    · right
      refine ⟨cubicOrigin, ?_, ?_⟩
      · change cubicOrigin ∈ ({cubicOrigin} : Finset (Cubic d))
        simp
      · simp [placeRight, originAnimal_bottomLeft, cubicTranslate]

theorem mem_diameterGlue_vertices_iff
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) (x : Cubic d) :
    x ∈ (A.diameterGlue B hd).vertices ↔
      x ∈ A.vertices ∨ x = A.rightOfTopRight hd ∨
        ∃ y ∈ B.1.vertices, (A.addRightSeparator hd).placeRight B.1 hd y = x := by
  rw [diameterGlue, rootedConcat_vertices, concatenatedVertices,
    Finset.mem_union, mem_placedVertices_iff]
  constructor
  · rintro (hx | hx)
    · rcases (A.mem_addRightSeparator_vertices_iff hd x).mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · rintro (hx | hx | hx)
    · exact Or.inl ((A.mem_addRightSeparator_vertices_iff hd x).mpr (Or.inl hx))
    · exact Or.inl ((A.mem_addRightSeparator_vertices_iff hd x).mpr (Or.inr hx))
    · exact Or.inr hx

theorem cubicLInfDist_topRight_rightOfTopRight_le_one
    (A : CubicBondAnimal d a) (hd : 0 < d) :
    cubicLInfDist A.topRight (A.rightOfTopRight hd) ≤ 1 := by
  exact cubicLInfDist_stepFrom_le_one A.topRight ((⟨0, hd⟩ : Fin d), true)

theorem cubicLInfDist_rightOfTopRight_outerAnchor_le_one
    (A : CubicBondAnimal d a) (hd : 0 < d) :
    cubicLInfDist (A.rightOfTopRight hd)
      ((A.addRightSeparator hd).rightOfTopRight hd) ≤ 1 := by
  have htop : (A.addRightSeparator hd).topRight = A.rightOfTopRight hd := by
    rw [addRightSeparator, rootedConcat_topRight]
    simp [placeRight, originAnimal_bottomLeft, originAnimal_topRight, cubicTranslate]
  rw [← htop]
  exact (A.addRightSeparator hd).cubicLInfDist_topRight_rightOfTopRight_le_one hd

theorem cubicLInfDist_outerAnchor_placeRight
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    (y : Cubic d) :
    cubicLInfDist ((A.addRightSeparator hd).rightOfTopRight hd)
      ((A.addRightSeparator hd).placeRight B.1 hd y) =
        cubicLInfDist B.1.bottomLeft y := by
  simpa [placeRight, cubicTranslate] using
    cubicLInfDist_translate B.1.bottomLeft
      ((A.addRightSeparator hd).rightOfTopRight hd) B.1.bottomLeft y

theorem cubicLInfDist_placeRight
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    (x y : Cubic d) :
    cubicLInfDist ((A.addRightSeparator hd).placeRight B.1 hd x)
      ((A.addRightSeparator hd).placeRight B.1 hd y) = cubicLInfDist x y := by
  exact cubicLInfDist_translate B.1.bottomLeft
    ((A.addRightSeparator hd).rightOfTopRight hd) x y

theorem cubicLInfDist_left_separator_le
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {x : Cubic d} (hx : x ∈ A.vertices) :
    cubicLInfDist x (A.rightOfTopRight hd) ≤
      A.lInfDiameter + B.1.lInfDiameter + 2 := by
  calc
    cubicLInfDist x (A.rightOfTopRight hd) ≤
        cubicLInfDist x A.topRight +
          cubicLInfDist A.topRight (A.rightOfTopRight hd) :=
      cubicLInfDist_triangle _ _ _
    _ ≤ A.lInfDiameter + 1 := by
      gcongr
      · exact A.cubicLInfDist_le_lInfDiameter hx A.topRight_mem
      · exact A.cubicLInfDist_topRight_rightOfTopRight_le_one hd
    _ ≤ A.lInfDiameter + B.1.lInfDiameter + 2 := by omega

theorem cubicLInfDist_left_placeRight_le
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ B.1.vertices) :
    cubicLInfDist x ((A.addRightSeparator hd).placeRight B.1 hd y) ≤
      A.lInfDiameter + B.1.lInfDiameter + 2 := by
  calc
    cubicLInfDist x ((A.addRightSeparator hd).placeRight B.1 hd y) ≤
        cubicLInfDist x A.topRight +
          cubicLInfDist A.topRight ((A.addRightSeparator hd).placeRight B.1 hd y) :=
      cubicLInfDist_triangle _ _ _
    _ ≤ A.lInfDiameter +
        (cubicLInfDist A.topRight (A.rightOfTopRight hd) +
          cubicLInfDist (A.rightOfTopRight hd)
            ((A.addRightSeparator hd).placeRight B.1 hd y)) := by
      gcongr
      · exact A.cubicLInfDist_le_lInfDiameter hx A.topRight_mem
      · exact cubicLInfDist_triangle _ _ _
    _ ≤ A.lInfDiameter +
        (1 + (cubicLInfDist (A.rightOfTopRight hd)
            ((A.addRightSeparator hd).rightOfTopRight hd) +
          cubicLInfDist ((A.addRightSeparator hd).rightOfTopRight hd)
            ((A.addRightSeparator hd).placeRight B.1 hd y))) := by
      gcongr
      · exact A.cubicLInfDist_topRight_rightOfTopRight_le_one hd
      · exact cubicLInfDist_triangle _ _ _
    _ ≤ A.lInfDiameter + (1 + (1 + B.1.lInfDiameter)) := by
      gcongr
      · exact A.cubicLInfDist_rightOfTopRight_outerAnchor_le_one hd
      · rw [A.cubicLInfDist_outerAnchor_placeRight B hd]
        exact B.1.cubicLInfDist_le_lInfDiameter B.1.bottomLeft_mem hy
    _ = A.lInfDiameter + B.1.lInfDiameter + 2 := by omega

theorem cubicLInfDist_separator_placeRight_le
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {y : Cubic d} (hy : y ∈ B.1.vertices) :
    cubicLInfDist (A.rightOfTopRight hd)
        ((A.addRightSeparator hd).placeRight B.1 hd y) ≤
      A.lInfDiameter + B.1.lInfDiameter + 2 := by
  calc
    cubicLInfDist (A.rightOfTopRight hd)
        ((A.addRightSeparator hd).placeRight B.1 hd y) ≤
        cubicLInfDist (A.rightOfTopRight hd)
            ((A.addRightSeparator hd).rightOfTopRight hd) +
          cubicLInfDist ((A.addRightSeparator hd).rightOfTopRight hd)
            ((A.addRightSeparator hd).placeRight B.1 hd y) :=
      cubicLInfDist_triangle _ _ _
    _ ≤ 1 + B.1.lInfDiameter := by
      gcongr
      · exact A.cubicLInfDist_rightOfTopRight_outerAnchor_le_one hd
      · rw [A.cubicLInfDist_outerAnchor_placeRight B hd]
        exact B.1.cubicLInfDist_le_lInfDiameter B.1.bottomLeft_mem hy
    _ ≤ A.lInfDiameter + B.1.lInfDiameter + 2 := by omega

/-- Every pair of vertices in the glued animal is at distance at most the sum of the two input
diameters plus two. -/
theorem cubicLInfDist_le_add_diameters_of_mem_diameterGlue
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {x y : Cubic d} (hx : x ∈ (A.diameterGlue B hd).vertices)
    (hy : y ∈ (A.diameterGlue B hd).vertices) :
    cubicLInfDist x y ≤ A.lInfDiameter + B.1.lInfDiameter + 2 := by
  rcases (A.mem_diameterGlue_vertices_iff B hd x).mp hx with
    hxA | rfl | ⟨xB, hxB, rfl⟩ <;>
    rcases (A.mem_diameterGlue_vertices_iff B hd y).mp hy with
      hyA | rfl | ⟨yB, hyB, rfl⟩
  · exact (A.cubicLInfDist_le_lInfDiameter hxA hyA).trans (by omega)
  · exact A.cubicLInfDist_left_separator_le B hd hxA
  · exact A.cubicLInfDist_left_placeRight_le B hd hxA hyB
  · rw [cubicLInfDist_comm]
    exact A.cubicLInfDist_left_separator_le B hd hyA
  · simp
  · exact A.cubicLInfDist_separator_placeRight_le B hd hyB
  · rw [cubicLInfDist_comm]
    exact A.cubicLInfDist_left_placeRight_le B hd hyA hxB
  · rw [cubicLInfDist_comm]
    exact A.cubicLInfDist_separator_placeRight_le B hd hxB
  · rw [A.cubicLInfDist_placeRight B hd]
    exact (B.1.cubicLInfDist_le_lInfDiameter hxB hyB).trans (by omega)

theorem diameterGlue_lInfDiameter_le
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d) :
    (A.diameterGlue B hd).lInfDiameter ≤
      A.lInfDiameter + B.1.lInfDiameter + 2 := by
  unfold lInfDiameter
  apply Finset.sup_le
  intro x hx
  apply Finset.sup_le
  intro y hy
  exact A.cubicLInfDist_le_add_diameters_of_mem_diameterGlue B hd hx hy

/-- Exact deterministic geometry behind Lemma 8.27. -/
theorem diameterGlue_isFirstDirectionMaximal
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {m n : ℕ} (hA : A.IsFirstDirectionMaximal hd m)
    (hB : B.1.IsFirstDirectionMaximal hd n) :
    (A.diameterGlue B hd).IsFirstDirectionMaximal hd (m + n + 2) := by
  have hspan := A.diameterGlue_firstCoordinateSpan B hd
  have hlower := (A.diameterGlue B hd).firstCoordinateSpan_le_lInfDiameter hd
  have hupper := A.diameterGlue_lInfDiameter_le B hd
  rw [hA.1, hB.1] at hupper
  rw [hA.2, hB.2] at hspan
  constructor
  · omega
  · omega

theorem originAnimal_isFirstDirectionMaximal
    (d : ℕ) (hd : 0 < d) :
    (originAnimal d).IsFirstDirectionMaximal hd 0 := by
  constructor
  · exact Nat.eq_zero_of_le_zero ((originAnimal d).lInfDiameter_le_card_sub_one)
  · rw [firstCoordinateSpan_eq_toNat_sub, originAnimal_bottomLeft,
      originAnimal_topRight]
    simp [cubicOrigin]

theorem addRightSeparator_origin_isFirstDirectionMaximal
    (d : ℕ) (hd : 0 < d) :
    ((originAnimal d).addRightSeparator hd).IsFirstDirectionMaximal hd 1 := by
  have hspan : ((originAnimal d).addRightSeparator hd).firstCoordinateSpan hd = 1 := by
    rw [firstCoordinateSpan_eq_toNat_sub, addRightSeparator_bottomLeft,
      addRightSeparator_topRight_coordinate_zero, originAnimal_bottomLeft,
      originAnimal_topRight]
    simp [cubicOrigin]
  have hlower := ((originAnimal d).addRightSeparator hd).firstCoordinateSpan_le_lInfDiameter hd
  have hupper := ((originAnimal d).addRightSeparator hd).lInfDiameter_le_card_sub_one
  constructor <;> omega

/-- The left input of the diameter gluing is intrinsically recoverable from the output: it is
exactly the part of the glued vertex set whose first coordinate is at most the bottom coordinate
plus the prescribed left diameter.  This is the separation fact needed to rule out collisions
between gluing inputs having different vertex counts. -/
theorem filter_diameterGlue_vertices_eq_left
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    {m : ℕ} (hA : A.IsFirstDirectionMaximal hd m) :
    (A.diameterGlue B hd).vertices.filter
        (fun x ↦ x ⟨0, hd⟩ ≤ A.bottomLeft ⟨0, hd⟩ + (m : ℤ)) =
      A.vertices := by
  classical
  have htop : A.topRight ⟨0, hd⟩ = A.bottomLeft ⟨0, hd⟩ + (m : ℤ) := by
    have hspan := hA.2
    rw [firstCoordinateSpan_eq_toNat_sub] at hspan
    have hle := A.bottomLeft_coordinate_zero_le_topRight hd
    omega
  ext x
  simp only [Finset.mem_filter]
  rw [A.mem_diameterGlue_vertices_iff B hd x]
  constructor
  · rintro ⟨hxA | rfl | ⟨y, hy, rfl⟩, hxle⟩
    · exact hxA
    · rw [rightOfTopRight_coordinate_zero, htop] at hxle
      omega
    · have hyLower := (A.addRightSeparator hd).placeRight_coordinate_zero_of_anchored
          B.1 B.2 hd hy
      rw [addRightSeparator_topRight_coordinate_zero, htop] at hyLower
      omega
  · intro hxA
    refine ⟨Or.inl hxA, ?_⟩
    exact (A.coordinate_zero_le_topRight hxA hd).trans_eq htop

/-- The deterministic gluing operation is injective for fixed input vertex counts. -/
theorem diameterGlue_injective (hd : 0 < d) :
    Function.Injective
      (fun AB : CubicBondAnimal d a × Anchored d b ↦ AB.1.diameterGlue AB.2 hd) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ h
  have houter :
      (A.addRightSeparator hd, B) = (A'.addRightSeparator hd, B') :=
    rootedConcat_injective (d := d) (m := a + 1) (n := b) hd h
  have hsep : A.addRightSeparator hd = A'.addRightSeparator hd :=
    congrArg Prod.fst houter
  have hinner :
      (A, originAnchored d) = (A', originAnchored d) :=
    rootedConcat_injective (d := d) (m := a) (n := 1) hd hsep
  have hA : A = A' := congrArg Prod.fst hinner
  have hB : B = B' := congrArg Prod.snd houter
  subst A'
  subst B'
  rfl

theorem weight_addRightSeparator
    (A : CubicBondAnimal d a) (hd : 0 < d)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (A.addRightSeparator hd).weight p =
      p * (1 - p)⁻¹ ^ 2 * A.weight p * (1 - p) ^ (2 * d) := by
  rw [addRightSeparator, weight_rootedConcat p hp0 hp1,
    weight_originAnimal]

theorem weight_diameterGlue
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 0 < d)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (A.diameterGlue B hd).weight p =
      p * (1 - p)⁻¹ ^ 2 *
        (p * (1 - p)⁻¹ ^ 2 * A.weight p * (1 - p) ^ (2 * d)) *
        B.1.weight p := by
  rw [diameterGlue, weight_rootedConcat p hp0 hp1,
    weight_addRightSeparator A hd p hp0 hp1]

/-- The source's conservative finite-energy factor.  The exact animal weight ratio is slightly
larger because the two joining bonds were boundary-closed in the two input cylinders. -/
theorem sourcePenalty_mul_weight_le_weight_diameterGlue
    (A : CubicBondAnimal d a) (B : Anchored d b) (hd : 2 ≤ d)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ 2 * (1 - p) ^ (2 * d - 2) * A.weight p * B.1.weight p ≤
      (A.diameterGlue B (by omega)).weight p := by
  let q := 1 - p
  have hq0 : 0 < q := sub_pos.mpr hp1
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hpowOrder : q ^ (2 * d - 2) ≤ q ^ (2 * d - 4) :=
    pow_le_pow_of_le_one hq0.le hq1 (by omega)
  have hweightA : 0 ≤ A.weight p := by
    exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0.le _)
  have hweightB : 0 ≤ B.1.weight p := by
    exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0.le _)
  have hfactor :
      p ^ 2 * q ^ (2 * d - 4) * A.weight p * B.1.weight p =
        (A.diameterGlue B (by omega)).weight p := by
    rw [A.weight_diameterGlue B (by omega) p hp0 hp1]
    have hq : q ≠ 0 := hq0.ne'
    have hpow : q ^ (2 * d) = q ^ (2 * d - 4) * q ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    change p ^ 2 * q ^ (2 * d - 4) * A.weight p * B.1.weight p =
      p * q⁻¹ ^ 2 * (p * q⁻¹ ^ 2 * A.weight p * q ^ (2 * d)) *
        B.1.weight p
    rw [hpow]
    field_simp
  rw [← hfactor]
  gcongr

end CubicBondAnimal

/-! ### Measurable coordinate-width events and symmetry -/

/-- All pairs of vertices in the origin cluster differ by at most `k` in coordinate `i`. -/
def clusterCoordinateSpanAtMostEvent
    (d : ℕ) (i : Fin d) (k : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ x : Cubic d, ⋂ y : Cubic d,
    if k < (y i - x i).natAbs then
      (connectionEvent d cubicOrigin x ∩ connectionEvent d cubicOrigin y)ᶜ
    else Set.univ

theorem measurableSet_clusterCoordinateSpanAtMostEvent
    (d : ℕ) (i : Fin d) (k : ℕ) :
    MeasurableSet (clusterCoordinateSpanAtMostEvent d i k) := by
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  split_ifs
  · exact ((measurableSet_connectionEvent d cubicOrigin x).inter
      (measurableSet_connectionEvent d cubicOrigin y)).compl
  · exact MeasurableSet.univ

theorem mem_clusterCoordinateSpanAtMostEvent_iff
    {d k : ℕ} {i : Fin d} {omega : EdgeConfiguration d} :
    omega ∈ clusterCoordinateSpanAtMostEvent d i k ↔
      ∀ x ∈ cubicOpenCluster d omega, ∀ y ∈ cubicOpenCluster d omega,
        (y i - x i).natAbs ≤ k := by
  simp only [clusterCoordinateSpanAtMostEvent, Set.mem_iInter]
  constructor
  · intro h x hx y hy
    by_contra hle
    have hlt : k < (y i - x i).natAbs := Nat.lt_of_not_ge hle
    have hxy := h x y
    rw [if_pos hlt, Set.mem_compl_iff, Set.mem_inter_iff] at hxy
    apply hxy
    simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq] using And.intro hx hy
  · intro h x y
    by_cases hlt : k < (y i - x i).natAbs
    · rw [if_pos hlt, Set.mem_compl_iff, Set.mem_inter_iff]
      intro hconn
      have hx : x ∈ cubicOpenCluster d omega := by
        simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
          Set.mem_setOf_eq] using hconn.1
      have hy : y ∈ cubicOpenCluster d omega := by
        simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
          Set.mem_setOf_eq] using hconn.2
      exact (Nat.not_lt_of_ge (h x hx y hy)) hlt
    · rw [if_neg hlt]
      exact Set.mem_univ omega

/-- Exact finite-cluster width in one coordinate. -/
def finiteClusterCoordinateSpanEvent
    (d : ℕ) (i : Fin d) (k : ℕ) : Set (EdgeConfiguration d) :=
  finiteClusterEvent d ∩ clusterCoordinateSpanAtMostEvent d i k ∩
    if k = 0 then Set.univ else (clusterCoordinateSpanAtMostEvent d i (k - 1))ᶜ

theorem measurableSet_finiteClusterCoordinateSpanEvent
    (d : ℕ) (i : Fin d) (k : ℕ) :
    MeasurableSet (finiteClusterCoordinateSpanEvent d i k) := by
  rw [finiteClusterCoordinateSpanEvent]
  apply ((measurableSet_finiteClusterEvent d).inter
    (measurableSet_clusterCoordinateSpanAtMostEvent d i k)).inter
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_clusterCoordinateSpanAtMostEvent d i (k - 1)).compl

theorem mem_finiteClusterCoordinateSpanEvent_iff_of_pos
    {d k : ℕ} {i : Fin d} (hk : 0 < k) {omega : EdgeConfiguration d} :
    omega ∈ finiteClusterCoordinateSpanEvent d i k ↔
      (cubicOpenCluster d omega).Finite ∧
      (∀ x ∈ cubicOpenCluster d omega, ∀ y ∈ cubicOpenCluster d omega,
        (y i - x i).natAbs ≤ k) ∧
      ∃ x ∈ cubicOpenCluster d omega, ∃ y ∈ cubicOpenCluster d omega,
        (y i - x i).natAbs = k := by
  simp only [finiteClusterCoordinateSpanEvent, if_neg hk.ne', Set.mem_inter_iff,
    Set.mem_compl_iff]
  rw [mem_clusterCoordinateSpanAtMostEvent_iff,
    mem_clusterCoordinateSpanAtMostEvent_iff]
  constructor
  · rintro ⟨⟨hfinite, hle⟩, hnot⟩
    change (cubicOpenCluster d omega).Finite at hfinite
    simp only [not_forall, not_le] at hnot
    obtain ⟨x, hx, y, hy, hdist⟩ := hnot
    exact ⟨hfinite, hle, x, hx, y, hy,
      Nat.le_antisymm (hle x hx y hy) (by omega)⟩
  · rintro ⟨hfinite, hle, x, hx, y, hy, hdist⟩
    refine ⟨⟨hfinite, hle⟩, ?_⟩
    intro hpred
    have := hpred x hx y hy
    omega

theorem mem_finiteClusterCoordinateSpanEvent_zero_iff
    {d : ℕ} {i : Fin d} {omega : EdgeConfiguration d} :
    omega ∈ finiteClusterCoordinateSpanEvent d i 0 ↔
      (cubicOpenCluster d omega).Finite ∧
      ∀ x ∈ cubicOpenCluster d omega, ∀ y ∈ cubicOpenCluster d omega,
        (y i - x i).natAbs = 0 := by
  change ((cubicOpenCluster d omega).Finite ∧
    omega ∈ clusterCoordinateSpanAtMostEvent d i 0) ∧ True ↔ _
  rw [mem_clusterCoordinateSpanAtMostEvent_iff]
  constructor
  · rintro ⟨⟨hfinite, h⟩, _⟩
    exact ⟨hfinite, fun x hx y hy ↦ Nat.eq_zero_of_le_zero (h x hx y hy)⟩
  · rintro ⟨hfinite, h⟩
    exact ⟨⟨hfinite, fun x hx y hy ↦ (h x hx y hy).le⟩, trivial⟩

/-- Exact diameter with the first coordinate as one maximizing direction. -/
def finiteClusterFirstDirectionDiameterEvent
    (d : ℕ) (hd : 0 < d) (k : ℕ) : Set (EdgeConfiguration d) :=
  finiteClusterLInfDiameterEvent d k ∩
    finiteClusterCoordinateSpanEvent d ⟨0, hd⟩ k

/-- Exact diameter with a specified coordinate as one maximizing direction. -/
def finiteClusterDirectionDiameterEvent
    (d : ℕ) (i : Fin d) (k : ℕ) : Set (EdgeConfiguration d) :=
  finiteClusterLInfDiameterEvent d k ∩ finiteClusterCoordinateSpanEvent d i k

theorem measurableSet_finiteClusterFirstDirectionDiameterEvent
    (d : ℕ) (hd : 0 < d) (k : ℕ) :
    MeasurableSet (finiteClusterFirstDirectionDiameterEvent d hd k) :=
  (measurableSet_finiteClusterLInfDiameterEvent d k).inter
    (measurableSet_finiteClusterCoordinateSpanEvent d ⟨0, hd⟩ k)

theorem cubicLInfDist_coordinatePermutation
    {d : ℕ} (e : Fin d ≃ Fin d) (x y : Cubic d) :
    cubicLInfDist (cubicCoordinatePermutationEquiv e x)
      (cubicCoordinatePermutationEquiv e y) = cubicLInfDist x y := by
  unfold cubicLInfDist
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    simpa [cubicCoordinatePermutationEquiv] using
      (Finset.le_sup (s := (Finset.univ : Finset (Fin d)))
        (f := fun i ↦ (y i - x i).natAbs) (Finset.mem_univ (e.symm j)))
  · apply Finset.sup_le
    intro i _hi
    have h := Finset.le_sup (s := (Finset.univ : Finset (Fin d)))
      (f := fun j ↦
        (cubicCoordinatePermutationEquiv e y j -
          cubicCoordinatePermutationEquiv e x j).natAbs)
      (Finset.mem_univ (e i))
    simpa [cubicCoordinatePermutationEquiv] using h

theorem mem_cubicOpenCluster_pullback_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin) (omega : EdgeConfiguration d) (x : Cubic d) :
    x ∈ cubicOpenCluster d (cubicGraphIsoConfigurationPullback F omega) ↔
      F x ∈ cubicOpenCluster d omega := by
  have h := cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
    F omega cubicOrigin x
  rw [hF0] at h
  simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
    Set.mem_setOf_eq] using h

theorem finite_cubicOpenCluster_pullback_iff
    {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin) (omega : EdgeConfiguration d) :
    (cubicOpenCluster d (cubicGraphIsoConfigurationPullback F omega)).Finite ↔
      (cubicOpenCluster d omega).Finite := by
  have hset : cubicOpenCluster d (cubicGraphIsoConfigurationPullback F omega) =
      F ⁻¹' cubicOpenCluster d omega := by
    ext x
    exact mem_cubicOpenCluster_pullback_iff F hF0 omega x
  rw [hset]
  constructor
  · intro hpre
    have himage := hpre.image F
    have heq : F '' (F ⁻¹' cubicOpenCluster d omega) = cubicOpenCluster d omega := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨F.symm y, by simpa, F.apply_symm_apply y⟩
    rwa [heq] at himage
  · intro hfinite
    exact hfinite.preimage F.injective.injOn

theorem mem_clusterCoordinateSpanAtMostEvent_pullback_coordinatePermutation_iff
    {d k : ℕ} (e : Fin d ≃ Fin d) (i : Fin d) (omega : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega ∈
        clusterCoordinateSpanAtMostEvent d i k ↔
      omega ∈ clusterCoordinateSpanAtMostEvent d (e i) k := by
  rw [mem_clusterCoordinateSpanAtMostEvent_iff,
    mem_clusterCoordinateSpanAtMostEvent_iff]
  constructor
  · intro h x hx y hy
    let x' := cubicCoordinatePermutationEquiv e.symm x
    let y' := cubicCoordinatePermutationEquiv e.symm y
    have hFx' : (cubicCoordinatePermutationIso e) x' = x := by
      ext j
      simp [x', cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]
    have hFy' : (cubicCoordinatePermutationIso e) y' = y := by
      ext j
      simp [y', cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]
    have hx' : x' ∈ cubicOpenCluster d
        (cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega) :=
      (mem_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e)
        (by ext j; simp [cubicCoordinatePermutationIso,
          cubicCoordinatePermutationEquiv, cubicOrigin]) omega x').2 (by simpa [hFx'])
    have hy' : y' ∈ cubicOpenCluster d
        (cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega) :=
      (mem_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e)
        (by ext j; simp [cubicCoordinatePermutationIso,
          cubicCoordinatePermutationEquiv, cubicOrigin]) omega y').2 (by simpa [hFy'])
    simpa [x', y', cubicCoordinatePermutationEquiv] using h x' hx' y' hy'
  · intro h x hx y hy
    have hx' := (mem_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e)
      (by ext j; simp [cubicCoordinatePermutationIso,
        cubicCoordinatePermutationEquiv, cubicOrigin]) omega x).1 hx
    have hy' := (mem_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e)
      (by ext j; simp [cubicCoordinatePermutationIso,
        cubicCoordinatePermutationEquiv, cubicOrigin]) omega y).1 hy
    simpa [cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv] using
      h _ hx' _ hy'

theorem clusterLInfDiameter_pullback_coordinatePermutation
    {d : ℕ} (e : Fin d ≃ Fin d) (omega : EdgeConfiguration d) :
    clusterLInfDiameter d
        (cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega) =
      clusterLInfDiameter d omega := by
  let F := cubicCoordinatePermutationIso e
  have hF0 : F cubicOrigin = cubicOrigin := by
    ext j
    simp [F, cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, cubicOrigin]
  have hfinite := finite_cubicOpenCluster_pullback_iff F hF0 omega
  by_cases homega : (cubicOpenCluster d omega).Finite
  · have hpull : (cubicOpenCluster d
        (cubicGraphIsoConfigurationPullback F omega)).Finite := hfinite.mpr homega
    apply Nat.le_antisymm
    · apply (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hpull).mp
      rw [mem_clusterLInfDiameterAtMostEvent_iff]
      intro x hx y hy
      have hx' := (mem_cubicOpenCluster_pullback_iff F hF0 omega x).1 hx
      have hy' := (mem_cubicOpenCluster_pullback_iff F hF0 omega y).1 hy
      rw [show cubicLInfDist x y = cubicLInfDist (F x) (F y) by
        symm
        exact cubicLInfDist_coordinatePermutation e x y]
      have hAtMost := (mem_clusterLInfDiameterAtMostEvent_iff_of_finite homega).mpr le_rfl
      exact mem_clusterLInfDiameterAtMostEvent_iff.mp hAtMost _ hx' _ hy'
    · have hAtMost :=
        (mem_clusterLInfDiameterAtMostEvent_iff_of_finite homega).mpr le_rfl
      have hall := mem_clusterLInfDiameterAtMostEvent_iff.mp hAtMost
      have hpullAtMost :
          cubicGraphIsoConfigurationPullback F omega ∈
            clusterLInfDiameterAtMostEvent d
              (clusterLInfDiameter d
                (cubicGraphIsoConfigurationPullback F omega)) :=
        (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hpull).mpr le_rfl
      have hpullAll := mem_clusterLInfDiameterAtMostEvent_iff.mp hpullAtMost
      apply (mem_clusterLInfDiameterAtMostEvent_iff_of_finite homega).mp
      rw [mem_clusterLInfDiameterAtMostEvent_iff]
      intro x hx y hy
      let x' := cubicCoordinatePermutationEquiv e.symm x
      let y' := cubicCoordinatePermutationEquiv e.symm y
      have hFx' : F x' = x := by
        ext j
        simp [F, x', cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]
      have hFy' : F y' = y := by
        ext j
        simp [F, y', cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv]
      have hx' : x' ∈ cubicOpenCluster d
          (cubicGraphIsoConfigurationPullback F omega) :=
        (mem_cubicOpenCluster_pullback_iff F hF0 omega x').2 (by simpa [hFx'])
      have hy' : y' ∈ cubicOpenCluster d
          (cubicGraphIsoConfigurationPullback F omega) :=
        (mem_cubicOpenCluster_pullback_iff F hF0 omega y').2 (by simpa [hFy'])
      rw [← hFx', ← hFy']
      have hdist : cubicLInfDist (F x') (F y') = cubicLInfDist x' y' := by
        simpa [F] using cubicLInfDist_coordinatePermutation e x' y'
      rw [hdist]
      exact hpullAll x' hx' y' hy'
  · have hpull : ¬(cubicOpenCluster d
        (cubicGraphIsoConfigurationPullback F omega)).Finite := by
      simpa [hfinite] using homega
    rw [clusterLInfDiameter, dif_neg hpull, clusterLInfDiameter, dif_neg homega]

theorem mem_finiteClusterLInfDiameterEvent_pullback_coordinatePermutation_iff
    {d k : ℕ} (e : Fin d ≃ Fin d) (omega : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega ∈
        finiteClusterLInfDiameterEvent d k ↔
      omega ∈ finiteClusterLInfDiameterEvent d k := by
  rw [mem_finiteClusterLInfDiameterEvent_iff,
    mem_finiteClusterLInfDiameterEvent_iff]
  have hF0 : cubicCoordinatePermutationIso e cubicOrigin = cubicOrigin := by
    ext j
    simp [cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, cubicOrigin]
  rw [finite_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e) hF0,
    clusterLInfDiameter_pullback_coordinatePermutation]

theorem mem_finiteClusterCoordinateSpanEvent_pullback_coordinatePermutation_iff
    {d k : ℕ} (e : Fin d ≃ Fin d) (i : Fin d) (omega : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega ∈
        finiteClusterCoordinateSpanEvent d i k ↔
      omega ∈ finiteClusterCoordinateSpanEvent d (e i) k := by
  unfold finiteClusterCoordinateSpanEvent
  have hF0 : cubicCoordinatePermutationIso e cubicOrigin = cubicOrigin := by
    ext j
    simp [cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, cubicOrigin]
  change (((cubicOpenCluster d
      (cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega)).Finite ∧
        cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega ∈
          clusterCoordinateSpanAtMostEvent d i k) ∧
        cubicGraphIsoConfigurationPullback (cubicCoordinatePermutationIso e) omega ∈
          (if k = 0 then Set.univ else
            (clusterCoordinateSpanAtMostEvent d i (k - 1))ᶜ)) ↔
      (((cubicOpenCluster d omega).Finite ∧
        omega ∈ clusterCoordinateSpanAtMostEvent d (e i) k) ∧
        omega ∈ (if k = 0 then Set.univ else
          (clusterCoordinateSpanAtMostEvent d (e i) (k - 1))ᶜ))
  rw [finite_cubicOpenCluster_pullback_iff (cubicCoordinatePermutationIso e) hF0,
    mem_clusterCoordinateSpanAtMostEvent_pullback_coordinatePermutation_iff]
  split_ifs
  · simp
  · simp only [Set.mem_compl_iff]
    rw [mem_clusterCoordinateSpanAtMostEvent_pullback_coordinatePermutation_iff]

theorem cubicGraphIsoEvent_directionDiameter_coordinatePermutation
    {d k : ℕ} (e : Fin d ≃ Fin d) (i : Fin d) :
    cubicGraphIsoEvent (cubicCoordinatePermutationIso e)
        (finiteClusterDirectionDiameterEvent d i k) =
      finiteClusterDirectionDiameterEvent d (e i) k := by
  ext omega
  simp only [cubicGraphIsoEvent, Set.mem_preimage,
    finiteClusterDirectionDiameterEvent, Set.mem_inter_iff]
  rw [mem_finiteClusterLInfDiameterEvent_pullback_coordinatePermutation_iff,
    mem_finiteClusterCoordinateSpanEvent_pullback_coordinatePermutation_iff]

theorem finiteClusterDirectionDiameter_probability_eq_first
    {d k : ℕ} (hd : 0 < d) (p : I) (i : Fin d) :
    (bernoulliBondMeasure d p).real (finiteClusterDirectionDiameterEvent d i k) =
      (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d hd k) := by
  let z : Fin d := ⟨0, hd⟩
  let e : Fin d ≃ Fin d := Equiv.swap i z
  have hei : e i = z := by simp [e]
  have htransport := cubicGraphIsoEvent_directionDiameter_coordinatePermutation
    (k := k) e i
  rw [hei] at htransport
  have hmeasure := bernoulliBondMeasure_real_cubicGraphIsoEvent p
    (cubicCoordinatePermutationIso e)
    (measurableSet_finiteClusterLInfDiameterEvent d k |>.inter
      (measurableSet_finiteClusterCoordinateSpanEvent d i k))
  change (bernoulliBondMeasure d p).real
      (cubicGraphIsoEvent (cubicCoordinatePermutationIso e)
        (finiteClusterDirectionDiameterEvent d i k)) =
    (bernoulliBondMeasure d p).real
      (finiteClusterDirectionDiameterEvent d i k) at hmeasure
  rw [htransport] at hmeasure
  simpa [finiteClusterDirectionDiameterEvent,
    finiteClusterFirstDirectionDiameterEvent, z] using hmeasure.symm

theorem finiteClusterLInfDiameterEvent_subset_iUnion_direction
    {d k : ℕ} (hd : 0 < d) :
    finiteClusterLInfDiameterEvent d k ⊆
      ⋃ i : Fin d, finiteClusterDirectionDiameterEvent d i k := by
  intro omega homega
  have hdiam := mem_finiteClusterLInfDiameterEvent_iff.mp homega
  by_cases hk : k = 0
  · subst k
    let i : Fin d := ⟨0, hd⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, homega, ?_⟩
    rw [mem_finiteClusterCoordinateSpanEvent_zero_iff]
    refine ⟨hdiam.1, ?_⟩
    have hAtMost := (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hdiam.1).mpr
      hdiam.2.le
    have hall := mem_clusterLInfDiameterAtMostEvent_iff.mp hAtMost
    intro x hx y hy
    exact Nat.eq_zero_of_le_zero
      ((cubicLInfDist_coord_le x y i).trans (hall x hx y hy))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    obtain ⟨hfinite, hle, x, hx, y, hy, hxy⟩ :=
      (mem_finiteClusterLInfDiameterEvent_iff_of_pos hkpos).mp homega
    have hnonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    obtain ⟨i, _hi, hisup⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin d)) hnonempty
      (fun j ↦ (y j - x j).natAbs)
    have hiEq : (y i - x i).natAbs = k := by
      rw [← hxy, cubicLInfDist, hisup]
    apply Set.mem_iUnion.mpr
    refine ⟨i, homega, ?_⟩
    exact (mem_finiteClusterCoordinateSpanEvent_iff_of_pos hkpos).mpr
      ⟨hfinite,
        fun u hu v hv ↦ (cubicLInfDist_coord_le u v i).trans (hle u hu v hv),
        x, hx, y, hy, hiEq⟩

/-- Equation (8.30): by coordinate symmetry, the first direction realizes the diameter with at
least a `1/d` fraction of the exact-diameter probability. -/
theorem finiteClusterLInfDiameterProbability_le_card_mul_firstDirection
    {d k : ℕ} (hd : 0 < d) (p : I) :
    finiteClusterLInfDiameterProbability d p k ≤
      d * (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d hd k) := by
  have hsub := finiteClusterLInfDiameterEvent_subset_iUnion_direction
    (k := k) hd
  calc
    finiteClusterLInfDiameterProbability d p k ≤
        (bernoulliBondMeasure d p).real
          (⋃ i : Fin d, finiteClusterDirectionDiameterEvent d i k) :=
      measureReal_mono hsub
    _ ≤ ∑ i : Fin d, (bernoulliBondMeasure d p).real
          (finiteClusterDirectionDiameterEvent d i k) :=
      measureReal_iUnion_fintype_le _
    _ = d * (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d hd k) := by
      simp_rw [finiteClusterDirectionDiameter_probability_eq_first hd p]
      simp

/-! ### Directional animal masses -/

namespace CubicBondAnimal

variable {d s : ℕ}

theorem reRoot_topRight (A : CubicBondAnimal d s)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).topRight = cubicTranslate v cubicOrigin A.topRight := by
  apply toLex_inj.mp
  apply le_antisymm
  · have hmem := (A.reRoot v hv).topRight_mem
    change (A.reRoot v hv).topRight ∈ A.translatedVertices v cubicOrigin at hmem
    rw [mem_translatedVertices_iff] at hmem
    obtain ⟨y, hyA, hyEq⟩ := hmem
    rw [← hyEq]
    exact (toLex_cubicTranslate_le_iff v cubicOrigin y A.topRight).mpr
      (A.lex_le_topRight hyA)
  · apply (A.reRoot v hv).lex_le_topRight
    change cubicTranslate v cubicOrigin A.topRight ∈ A.translatedVertices v cubicOrigin
    rw [mem_translatedVertices_iff]
    exact ⟨A.topRight, A.topRight_mem, rfl⟩

@[simp] theorem lInfDiameter_reRoot (A : CubicBondAnimal d s)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).lInfDiameter = A.lInfDiameter := by
  apply Nat.le_antisymm
  · unfold lInfDiameter
    apply Finset.sup_le
    intro x hx
    apply Finset.sup_le
    intro y hy
    change x ∈ A.translatedVertices v cubicOrigin at hx
    change y ∈ A.translatedVertices v cubicOrigin at hy
    rw [mem_translatedVertices_iff] at hx hy
    obtain ⟨x', hxA, rfl⟩ := hx
    obtain ⟨y', hyA, rfl⟩ := hy
    rw [cubicLInfDist_translate]
    exact A.cubicLInfDist_le_lInfDiameter hxA hyA
  · unfold lInfDiameter
    apply Finset.sup_le
    intro x hx
    apply Finset.sup_le
    intro y hy
    have hx' : cubicTranslate v cubicOrigin x ∈ (A.reRoot v hv).vertices := by
      change cubicTranslate v cubicOrigin x ∈ A.translatedVertices v cubicOrigin
      rw [mem_translatedVertices_iff]
      exact ⟨x, hx, rfl⟩
    have hy' : cubicTranslate v cubicOrigin y ∈ (A.reRoot v hv).vertices := by
      change cubicTranslate v cubicOrigin y ∈ A.translatedVertices v cubicOrigin
      rw [mem_translatedVertices_iff]
      exact ⟨y, hy, rfl⟩
    rw [← cubicLInfDist_translate v cubicOrigin x y]
    exact (A.reRoot v hv).cubicLInfDist_le_lInfDiameter hx' hy'

@[simp] theorem firstCoordinateSpan_reRoot (A : CubicBondAnimal d s)
    (hd : 0 < d) (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).firstCoordinateSpan hd = A.firstCoordinateSpan hd := by
  rw [firstCoordinateSpan, firstCoordinateSpan, A.reRoot_topRight v hv,
    A.reRoot_bottomLeft v hv]
  congr 1
  simp [cubicTranslate]

theorem isFirstDirectionMaximal_reRoot_iff
    (A : CubicBondAnimal d s) (hd : 0 < d) (k : ℕ)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).IsFirstDirectionMaximal hd k ↔ A.IsFirstDirectionMaximal hd k := by
  simp [IsFirstDirectionMaximal]

theorem coordinate_zero_natAbs_sub_le_firstCoordinateSpan
    (A : CubicBondAnimal d s) (hd : 0 < d)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ A.vertices) :
    (y ⟨0, hd⟩ - x ⟨0, hd⟩).natAbs ≤ A.firstCoordinateSpan hd := by
  have hloX := A.bottomLeft_coordinate_zero_le hd hx
  have hloY := A.bottomLeft_coordinate_zero_le hd hy
  have hxHi := A.coordinate_zero_le_topRight' hd hx
  have hyHi := A.coordinate_zero_le_topRight' hd hy
  have hbase : 0 ≤ A.topRight ⟨0, hd⟩ - A.bottomLeft ⟨0, hd⟩ := by omega
  rw [firstCoordinateSpan]
  by_cases hxy : x ⟨0, hd⟩ ≤ y ⟨0, hd⟩
  · apply (Nat.cast_le (α := ℤ)).mp
    rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg hbase]
    omega
  · rw [show y ⟨0, hd⟩ - x ⟨0, hd⟩ =
      -(x ⟨0, hd⟩ - y ⟨0, hd⟩) by omega, Int.natAbs_neg]
    apply (Nat.cast_le (α := ℤ)).mp
    rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg hbase]
    omega

theorem mem_finiteClusterLInfDiameterEvent_iff_of_mem_clusterCylinder
    (A : CubicBondAnimal d s) {omega : EdgeConfiguration d}
    (homega : omega ∈ A.clusterCylinder) (k : ℕ) :
    omega ∈ finiteClusterLInfDiameterEvent d k ↔ A.lInfDiameter = k := by
  rw [mem_finiteClusterLInfDiameterEvent_iff]
  have hcluster := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder homega
  have hfinite : (cubicOpenCluster d omega).Finite := by
    rw [hcluster]
    exact A.vertices.finite_toSet
  rw [← A.lInfDiameter_eq_clusterLInfDiameter_of_mem_clusterCylinder homega]
  simp [hfinite]

theorem mem_finiteClusterCoordinateSpanEvent_iff_of_mem_clusterCylinder
    (A : CubicBondAnimal d s) (hd : 0 < d) {omega : EdgeConfiguration d}
    (homega : omega ∈ A.clusterCylinder) (k : ℕ) :
    omega ∈ finiteClusterCoordinateSpanEvent d ⟨0, hd⟩ k ↔
      A.firstCoordinateSpan hd = k := by
  have hcluster := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder homega
  have hfinite : (cubicOpenCluster d omega).Finite := by
    rw [hcluster]
    exact A.vertices.finite_toSet
  cases k with
  | zero =>
      rw [mem_finiteClusterCoordinateSpanEvent_zero_iff]
      constructor
      · rintro ⟨_hfinite, hall⟩
        have h := hall A.bottomLeft (by simpa [hcluster] using A.bottomLeft_mem)
          A.topRight (by simpa [hcluster] using A.topRight_mem)
        simpa [firstCoordinateSpan] using h
      · intro hspan
        refine ⟨hfinite, ?_⟩
        intro x hx y hy
        have hxA : x ∈ A.vertices := by simpa [hcluster] using hx
        have hyA : y ∈ A.vertices := by simpa [hcluster] using hy
        exact Nat.eq_zero_of_le_zero
          ((A.coordinate_zero_natAbs_sub_le_firstCoordinateSpan hd hxA hyA).trans_eq hspan)
  | succ k =>
      rw [mem_finiteClusterCoordinateSpanEvent_iff_of_pos (Nat.succ_pos k)]
      constructor
      · rintro ⟨_hfinite, hle, x, hx, y, hy, hxy⟩
        have hxA : x ∈ A.vertices := by simpa [hcluster] using hx
        have hyA : y ∈ A.vertices := by simpa [hcluster] using hy
        exact Nat.le_antisymm
          (by
            have hupper := hle A.bottomLeft
              (by simpa [hcluster] using A.bottomLeft_mem) A.topRight
              (by simpa [hcluster] using A.topRight_mem)
            simpa [firstCoordinateSpan] using hupper)
          (by
            have hlower := A.coordinate_zero_natAbs_sub_le_firstCoordinateSpan hd hxA hyA
            simpa [hxy] using hlower)
      · intro hspan
        refine ⟨hfinite, ?_, A.bottomLeft, (by simpa [hcluster] using A.bottomLeft_mem),
          A.topRight, (by simpa [hcluster] using A.topRight_mem), ?_⟩
        · intro x hx y hy
          have hxA : x ∈ A.vertices := by simpa [hcluster] using hx
          have hyA : y ∈ A.vertices := by simpa [hcluster] using hy
          exact (A.coordinate_zero_natAbs_sub_le_firstCoordinateSpan hd hxA hyA).trans_eq hspan
        · simpa [firstCoordinateSpan] using hspan

theorem mem_finiteClusterFirstDirectionDiameterEvent_iff_of_mem_clusterCylinder
    (A : CubicBondAnimal d s) (hd : 0 < d) {omega : EdgeConfiguration d}
    (homega : omega ∈ A.clusterCylinder) (k : ℕ) :
    omega ∈ finiteClusterFirstDirectionDiameterEvent d hd k ↔
      A.IsFirstDirectionMaximal hd k := by
  unfold finiteClusterFirstDirectionDiameterEvent IsFirstDirectionMaximal
  rw [Set.mem_inter_iff,
    A.mem_finiteClusterLInfDiameterEvent_iff_of_mem_clusterCylinder homega,
    A.mem_finiteClusterCoordinateSpanEvent_iff_of_mem_clusterCylinder hd homega]

/-- Rooted animal mass at fixed vertex count whose first-coordinate width realizes diameter
`k`. -/
noncomputable def firstDirectionAnimalMass
    (d s : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) : ℝ :=
  by
    classical
    exact ∑ A : {A : CubicBondAnimal d s // A.IsFirstDirectionMaximal hd k},
      A.1.weight p

/-- Directional mass of bottom-left anchored translation classes. -/
noncomputable def firstDirectionAnchoredMass
    (d s : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) : ℝ := by
  classical
  exact ∑ A : {A : Anchored d s // A.1.IsFirstDirectionMaximal hd k},
    A.1.1.weight p

theorem firstDirectionAnimalMass_eq_sum_ite
    (d s : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnimalMass d s p hd k =
      ∑ A : CubicBondAnimal d s,
        if A.IsFirstDirectionMaximal hd k then A.weight p else 0 := by
  classical
  unfold firstDirectionAnimalMass
  have h :
      (∑ A ∈ (Finset.univ : Finset (CubicBondAnimal d s)).filter
          (fun A ↦ A.IsFirstDirectionMaximal hd k), A.weight p) =
        ∑ A : {A : CubicBondAnimal d s // A.IsFirstDirectionMaximal hd k},
          A.1.weight p :=
    Finset.sum_subtype
      ((Finset.univ : Finset (CubicBondAnimal d s)).filter
        fun A ↦ A.IsFirstDirectionMaximal hd k)
      (fun A ↦ by simp) (fun A ↦ A.weight p)
  rw [Finset.sum_filter] at h
  simpa using h.symm

theorem firstDirectionAnchoredMass_eq_sum_ite
    (d s : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnchoredMass d s p hd k =
      ∑ A : Anchored d s,
        if A.1.IsFirstDirectionMaximal hd k then A.1.weight p else 0 := by
  classical
  unfold firstDirectionAnchoredMass
  have h :
      (∑ A ∈ (Finset.univ : Finset (Anchored d s)).filter
          (fun A ↦ A.1.IsFirstDirectionMaximal hd k), A.1.weight p) =
        ∑ A : {A : Anchored d s // A.1.IsFirstDirectionMaximal hd k},
          A.1.1.weight p :=
    Finset.sum_subtype
      ((Finset.univ : Finset (Anchored d s)).filter
        fun A ↦ A.1.IsFirstDirectionMaximal hd k)
      (fun A ↦ by simp) (fun A ↦ A.1.weight p)
  rw [Finset.sum_filter] at h
  simpa using h.symm

/-- Filtered version of rooted/anchored orbit counting: every anchored animal has exactly `s`
possible roots, and the diameter/width predicate is translation invariant. -/
theorem firstDirectionAnimalMass_eq_nat_mul_anchoredMass
    (d s : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnimalMass d s p hd k =
      s * firstDirectionAnchoredMass d s p hd k := by
  classical
  rw [firstDirectionAnimalMass_eq_sum_ite,
    firstDirectionAnchoredMass_eq_sum_ite]
  let e := rootedEquivPointedAnchored (d := d) (n := s)
  calc
    (∑ A : CubicBondAnimal d s,
        if A.IsFirstDirectionMaximal hd k then A.weight p else 0) =
        ∑ A : CubicBondAnimal d s,
          if (fromPointedAnchored (e A)).IsFirstDirectionMaximal hd k then
            (fromPointedAnchored (e A)).weight p else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [show e A = toPointedAnchored A by rfl,
        fromPointedAnchored_toPointedAnchored]
    _ = ∑ X : PointedAnchored d s,
          if (fromPointedAnchored X).IsFirstDirectionMaximal hd k then
            (fromPointedAnchored X).weight p else 0 := by
      exact e.sum_comp fun X : PointedAnchored d s ↦
        if (fromPointedAnchored X).IsFirstDirectionMaximal hd k then
          (fromPointedAnchored X).weight p else 0
    _ = ∑ X : PointedAnchored d s,
          if X.1.1.IsFirstDirectionMaximal hd k then X.1.1.weight p else 0 := by
      apply Finset.sum_congr rfl
      intro X _
      have hP := X.1.1.isFirstDirectionMaximal_reRoot_iff hd k X.2.1 X.2.2
      change (if (X.1.1.reRoot X.2.1 X.2.2).IsFirstDirectionMaximal hd k then
          (X.1.1.reRoot X.2.1 X.2.2).weight p else 0) = _
      rw [if_congr hP (weight_reRoot p X.1.1 X.2.1 X.2.2) rfl]
    _ = ∑ A : Anchored d s, ∑ _v : A.1.vertices,
          if A.1.IsFirstDirectionMaximal hd k then A.1.weight p else 0 := by
      exact Fintype.sum_sigma fun X : PointedAnchored d s ↦
        if X.1.1.IsFirstDirectionMaximal hd k then X.1.1.weight p else 0
    _ = ∑ A : Anchored d s,
          s * (if A.1.IsFirstDirectionMaximal hd k then A.1.weight p else 0) := by
      apply Finset.sum_congr rfl
      intro A _
      simp [A.1.vertices_card, nsmul_eq_mul]
    _ = s * ∑ A : Anchored d s,
          if A.1.IsFirstDirectionMaximal hd k then A.1.weight p else 0 := by
      rw [Finset.mul_sum]

theorem firstDirectionAnchoredMass_nonneg
    (d s : ℕ) (p : I) (hd : 0 < d) (k : ℕ) :
    0 ≤ firstDirectionAnchoredMass d s p hd k := by
  classical
  unfold firstDirectionAnchoredMass
  apply Finset.sum_nonneg
  intro A _
  exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)

theorem vertices_subset_metricBox_lInfDiameter
    (A : CubicBondAnimal d s) :
    A.vertices ⊆ cubicMetricBox d cubicOrigin A.lInfDiameter := by
  intro x hx
  rw [mem_cubicMetricBox_iff_lInfDist_le]
  exact A.cubicLInfDist_le_lInfDiameter A.origin_mem hx

theorem vertexCount_le_boxCard_of_lInfDiameter_eq
    (A : CubicBondAnimal d s) {k : ℕ} (hk : A.lInfDiameter = k) :
    s ≤ (2 * k + 1) ^ d := by
  rw [← A.vertices_card, ← cubicMetricBox_card d cubicOrigin k]
  apply Finset.card_le_card
  simpa [hk] using A.vertices_subset_metricBox_lInfDiameter

theorem firstDirectionAnimalMass_le_boxCard_mul_anchoredMass
    (d s : ℕ) (p : I) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnimalMass d s p hd k ≤
      (2 * k + 1) ^ d * firstDirectionAnchoredMass d s p hd k := by
  rw [firstDirectionAnimalMass_eq_nat_mul_anchoredMass]
  by_cases hnonempty : Nonempty {A : Anchored d s //
      A.1.IsFirstDirectionMaximal hd k}
  · obtain ⟨A⟩ := hnonempty
    have hs : (s : ℝ) ≤ (2 * (k : ℝ) + 1) ^ d := by
      exact_mod_cast A.1.1.vertexCount_le_boxCard_of_lInfDiameter_eq A.2.1
    exact mul_le_mul_of_nonneg_right
      hs
      (firstDirectionAnchoredMass_nonneg d s p hd k)
  · haveI : IsEmpty {A : Anchored d s // A.1.IsFirstDirectionMaximal hd k} :=
      ⟨fun A ↦ hnonempty ⟨A⟩⟩
    simp [firstDirectionAnchoredMass]

/-- Total anchored directional mass over all possible cluster sizes at diameter `k`. -/
noncomputable def firstDirectionAnchoredTotalMass
    (d : ℕ) (p : ℝ) (hd : 0 < d) (k : ℕ) : ℝ :=
  ∑ s : Fin ((2 * k + 1) ^ d + 1),
    firstDirectionAnchoredMass d s.1 p hd k

theorem iUnion_firstDirectionAnimal_clusterCylinder
    (d s : ℕ) (hd : 0 < d) (k : ℕ) :
    (⋃ A : {A : CubicBondAnimal d s // A.IsFirstDirectionMaximal hd k},
        A.1.clusterCylinder) =
      finiteClusterSizeEvent d s ∩ finiteClusterFirstDirectionDiameterEvent d hd k := by
  ext omega
  constructor
  · intro homega
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp homega
    have hcluster := A.1.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hA
    have hfinite : (cubicOpenCluster d omega).Finite := by
      rw [hcluster]
      exact A.1.vertices.finite_toSet
    refine ⟨?_, (A.1.mem_finiteClusterFirstDirectionDiameterEvent_iff_of_mem_clusterCylinder
      hd hA k).mpr A.2⟩
    change clusterSizeENNReal d omega = (s : ENNReal)
    rw [clusterSizeENNReal_eq_ncard_of_finite hfinite, hcluster]
    simp [A.1.vertices_card]
  · rintro ⟨hsize, hdir⟩
    have hall : omega ∈ ⋃ A : CubicBondAnimal d s, A.clusterCylinder := by
      rw [iUnion_cubicBondAnimal_clusterCylinder]
      exact hsize
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hall
    have hprop :=
      (A.mem_finiteClusterFirstDirectionDiameterEvent_iff_of_mem_clusterCylinder
        hd hA k).mp hdir
    exact Set.mem_iUnion.mpr ⟨⟨A, hprop⟩, hA⟩

theorem firstDirectionAnimalMass_eq_measureReal_inter_size
    (d s : ℕ) (p : I) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnimalMass d s p hd k =
      (bernoulliBondMeasure d p).real
        (finiteClusterSizeEvent d s ∩ finiteClusterFirstDirectionDiameterEvent d hd k) := by
  let T := {A : CubicBondAnimal d s // A.IsFirstDirectionMaximal hd k}
  let F : T → Set (EdgeConfiguration d) := fun A ↦ A.1.clusterCylinder
  have hpair : Pairwise (Function.onFun Disjoint F) := by
    intro A B hAB
    apply CubicBondAnimal.clusterCylinder_pairwiseDisjoint
    intro hval
    exact hAB (Subtype.ext hval)
  have hsum := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p) hpair
    (fun A : T ↦ A.1.measurableSet_clusterCylinder)
  rw [show (⋃ A : T, F A) =
      finiteClusterSizeEvent d s ∩ finiteClusterFirstDirectionDiameterEvent d hd k by
    exact iUnion_firstDirectionAnimal_clusterCylinder d s hd k] at hsum
  change (∑ A : T, A.1.weight p) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro A _hA
  simpa [weight, F] using (A.1.bernoulliBondMeasure_real_clusterCylinder p).symm

/-- A bottom-left anchored animal whose first-coordinate width realizes its diameter gives a
configuration in Grimmett's anchored radius event. -/
theorem clusterCylinder_subset_firstCoordinateAnchoredDiameterEvent
    (A : CubicBondAnimal d s) (hA : A.IsBottomLeftAnchored)
    (hd : 0 < d) {k : ℕ} (hdir : A.IsFirstDirectionMaximal hd k) :
    A.clusterCylinder ⊆ firstCoordinateAnchoredDiameterEvent d hd k := by
  intro omega homega
  have hcluster := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder homega
  have hdiam : omega ∈ finiteClusterLInfDiameterEvent d k :=
    (A.mem_finiteClusterLInfDiameterEvent_iff_of_mem_clusterCylinder homega k).mpr hdir.1
  have htopNonneg : 0 ≤ A.topRight ⟨0, hd⟩ :=
    A.coordinate_zero_nonneg_of_anchored hA A.topRight_mem hd
  have htop : A.topRight ⟨0, hd⟩ = (k : ℤ) := by
    have hspan := hdir.2
    rw [A.firstCoordinateSpan_eq_toNat_sub hd, hA] at hspan
    simp only [cubicOrigin, sub_zero] at hspan
    calc
      A.topRight ⟨0, hd⟩ = (A.topRight ⟨0, hd⟩).toNat :=
        (Int.toNat_of_nonneg htopNonneg).symm
      _ = (k : ℤ) := by exact_mod_cast hspan
  refine ⟨⟨⟨hdiam.1.1, hdiam.1.2⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_iInter]
    intro x
    by_cases hx : x ⟨0, hd⟩ < 0 ∨ (k : ℤ) < x ⟨0, hd⟩
    · rw [if_pos hx, Set.mem_compl_iff]
      intro hxconn
      have hxCluster : x ∈ cubicOpenCluster d omega := by
        simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
          Set.mem_setOf_eq] using hxconn
      have hxA : x ∈ A.vertices := by simpa [hcluster] using hxCluster
      have hxlo := A.coordinate_zero_nonneg_of_anchored hA hxA hd
      have hxhi := A.coordinate_zero_le_topRight' hd hxA
      rcases hx with hx | hx <;> omega
    · rw [if_neg hx]
      exact Set.mem_univ omega
  · simp only [Set.mem_iUnion]
    refine ⟨A.topRight, ?_⟩
    rw [if_pos htop]
    have htopCluster : A.topRight ∈ cubicOpenCluster d omega := by
      simpa [hcluster] using A.topRight_mem
    simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq] using htopCluster

/-- At a fixed size, the directional anchored-animal mass is bounded by the probability of
Grimmett's anchored finite-radius event together with that size. -/
theorem firstDirectionAnchoredMass_le_measureReal_inter_size_anchoredEvent
    (d s : ℕ) (p : I) (hd : 0 < d) (k : ℕ) :
    firstDirectionAnchoredMass d s p hd k ≤
      (bernoulliBondMeasure d p).real
        (finiteClusterSizeEvent d s ∩ firstCoordinateAnchoredDiameterEvent d hd k) := by
  let T := {A : Anchored d s // A.1.IsFirstDirectionMaximal hd k}
  let F : T → Set (EdgeConfiguration d) := fun A ↦ A.1.1.clusterCylinder
  have hpair : Pairwise (Function.onFun Disjoint F) := by
    intro A B hAB
    apply CubicBondAnimal.clusterCylinder_pairwiseDisjoint
    intro hval
    apply hAB
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  have hsum := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p) hpair
    (fun A : T ↦ A.1.1.measurableSet_clusterCylinder)
  have hsub : (⋃ A : T, F A) ⊆
      finiteClusterSizeEvent d s ∩ firstCoordinateAnchoredDiameterEvent d hd k := by
    intro omega homega
    obtain ⟨A, homega⟩ := Set.mem_iUnion.mp homega
    refine ⟨?_, A.1.1.clusterCylinder_subset_firstCoordinateAnchoredDiameterEvent
      A.1.2 hd A.2 homega⟩
    rw [← iUnion_cubicBondAnimal_clusterCylinder d s]
    exact Set.mem_iUnion.mpr ⟨A.1.1, homega⟩
  unfold firstDirectionAnchoredMass
  calc
    (∑ A : T, A.1.1.weight p) =
        ∑ A : T, (bernoulliBondMeasure d p).real (F A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      simpa [F] using (A.1.1.bernoulliBondMeasure_real_clusterCylinder p).symm
    _ = (bernoulliBondMeasure d p).real (⋃ A : T, F A) := hsum.symm
    _ ≤ (bernoulliBondMeasure d p).real
        (finiteClusterSizeEvent d s ∩ firstCoordinateAnchoredDiameterEvent d hd k) :=
      measureReal_mono hsub

end CubicBondAnimal

theorem finiteCluster_ncard_le_boxCard_of_mem_lInfDiameterEvent
    {d k : ℕ} {omega : EdgeConfiguration d}
    (homega : omega ∈ finiteClusterLInfDiameterEvent d k) :
    (cubicOpenCluster d omega).ncard ≤ (2 * k + 1) ^ d := by
  have hdata := mem_finiteClusterLInfDiameterEvent_iff.mp homega
  have hAtMost :=
    (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hdata.1).mpr hdata.2.le
  have hall := mem_clusterLInfDiameterAtMostEvent_iff.mp hAtMost
  have hsub : hdata.1.toFinset ⊆ cubicMetricBox d cubicOrigin k := by
    intro x hx
    rw [mem_cubicMetricBox_iff_lInfDist_le]
    exact hall cubicOrigin (by
      exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen]⟩) x (by simpa using hx)
  calc
    (cubicOpenCluster d omega).ncard = hdata.1.toFinset.card :=
      Set.ncard_eq_toFinset_card _ hdata.1
    _ ≤ (cubicMetricBox d cubicOrigin k).card := Finset.card_le_card hsub
    _ = (2 * k + 1) ^ d := cubicMetricBox_card d cubicOrigin k

/-- For an exact diameter `k`, only the sizes `0,…,(2k+1)^d` occur. -/
theorem iUnion_size_inter_firstDirectionDiameter
    (d k : ℕ) (hd : 0 < d) :
    (⋃ s : Fin ((2 * k + 1) ^ d + 1),
        finiteClusterSizeEvent d s.1 ∩ finiteClusterFirstDirectionDiameterEvent d hd k) =
      finiteClusterFirstDirectionDiameterEvent d hd k := by
  ext omega
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    exact hs.2
  · intro hdir
    have hdiam : omega ∈ finiteClusterLInfDiameterEvent d k := hdir.1
    have hfinite := mem_finiteClusterLInfDiameterEvent_iff.mp hdiam |>.1
    let s := (cubicOpenCluster d omega).ncard
    have hs : s < (2 * k + 1) ^ d + 1 :=
      Nat.lt_succ_of_le (finiteCluster_ncard_le_boxCard_of_mem_lInfDiameterEvent hdiam)
    refine Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_, hdir⟩
    change clusterSizeENNReal d omega = (s : ENNReal)
    exact clusterSizeENNReal_eq_ncard_of_finite hfinite

theorem pairwiseDisjoint_size_inter_firstDirectionDiameter
    (d k : ℕ) (hd : 0 < d) :
    Pairwise (Function.onFun Disjoint fun s : Fin ((2 * k + 1) ^ d + 1) ↦
      finiteClusterSizeEvent d s.1 ∩ finiteClusterFirstDirectionDiameterEvent d hd k) := by
  intro s t hst
  change Disjoint
    (finiteClusterSizeEvent d s.1 ∩ finiteClusterFirstDirectionDiameterEvent d hd k)
    (finiteClusterSizeEvent d t.1 ∩ finiteClusterFirstDirectionDiameterEvent d hd k)
  rw [Set.disjoint_left]
  rintro omega ⟨hs, _⟩ ⟨ht, _⟩
  have hval : s.1 ≠ t.1 := by
    intro h
    exact hst (Fin.ext h)
  exact Set.disjoint_left.mp (pairwiseDisjoint_finiteClusterSizeEvent d hval) hs ht

theorem firstDirectionDiameter_probability_eq_sum_animalMass
    (d k : ℕ) (p : I) (hd : 0 < d) :
    (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d hd k) =
      ∑ s : Fin ((2 * k + 1) ^ d + 1),
        CubicBondAnimal.firstDirectionAnimalMass d s.1 p hd k := by
  have hsum := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p)
    (pairwiseDisjoint_size_inter_firstDirectionDiameter d k hd)
    (fun s : Fin ((2 * k + 1) ^ d + 1) ↦
      (measurableSet_finiteClusterSizeEvent d s.1).inter
        (measurableSet_finiteClusterFirstDirectionDiameterEvent d hd k))
  rw [iUnion_size_inter_firstDirectionDiameter d k hd] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro s _hs
  exact (CubicBondAnimal.firstDirectionAnimalMass_eq_measureReal_inter_size
    d s.1 p hd k).symm

theorem firstDirectionDiameter_probability_le_boxCard_mul_anchoredTotalMass
    (d k : ℕ) (p : I) (hd : 0 < d) :
    (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d hd k) ≤
      (2 * k + 1) ^ d *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd k := by
  rw [firstDirectionDiameter_probability_eq_sum_animalMass]
  unfold CubicBondAnimal.firstDirectionAnchoredTotalMass
  calc
    (∑ s : Fin ((2 * k + 1) ^ d + 1),
        CubicBondAnimal.firstDirectionAnimalMass d s.1 p hd k) ≤
        ∑ s : Fin ((2 * k + 1) ^ d + 1),
          (2 * k + 1) ^ d *
            CubicBondAnimal.firstDirectionAnchoredMass d s.1 p hd k := by
      exact Finset.sum_le_sum fun s _ ↦
        CubicBondAnimal.firstDirectionAnimalMass_le_boxCard_mul_anchoredMass
          d s.1 p hd k
    _ = (2 * k + 1) ^ d *
        ∑ s : Fin ((2 * k + 1) ^ d + 1),
          CubicBondAnimal.firstDirectionAnchoredMass d s.1 p hd k := by
      rw [Finset.mul_sum]

theorem pairwiseDisjoint_size_inter_firstCoordinateAnchoredDiameterEvent
    (d k : ℕ) (hd : 0 < d) :
    Pairwise (Function.onFun Disjoint fun s : Fin ((2 * k + 1) ^ d + 1) ↦
      finiteClusterSizeEvent d s.1 ∩ firstCoordinateAnchoredDiameterEvent d hd k) := by
  intro s t hst
  change Disjoint
    (finiteClusterSizeEvent d s.1 ∩ firstCoordinateAnchoredDiameterEvent d hd k)
    (finiteClusterSizeEvent d t.1 ∩ firstCoordinateAnchoredDiameterEvent d hd k)
  rw [Set.disjoint_left]
  rintro omega ⟨hs, _⟩ ⟨ht, _⟩
  have hval : s.1 ≠ t.1 := by
    intro h
    exact hst (Fin.ext h)
  exact Set.disjoint_left.mp (pairwiseDisjoint_finiteClusterSizeEvent d hval) hs ht

/-- The total directional anchored-animal mass is carried by configurations in the anchored
finite-radius event.  This is the measure-theoretic content behind (8.34)--(8.40). -/
theorem firstDirectionAnchoredTotalMass_le_finiteBoxRadiusProbability
    (d k : ℕ) (p : I) (hd : 0 < d) :
    CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd k ≤
      finiteBoxRadiusProbability d p k := by
  have hsum := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p)
    (pairwiseDisjoint_size_inter_firstCoordinateAnchoredDiameterEvent d k hd)
    (fun s : Fin ((2 * k + 1) ^ d + 1) ↦
      (measurableSet_finiteClusterSizeEvent d s.1).inter
        (measurableSet_firstCoordinateAnchoredDiameterEvent d hd k))
  have hsub : (⋃ s : Fin ((2 * k + 1) ^ d + 1),
      finiteClusterSizeEvent d s.1 ∩ firstCoordinateAnchoredDiameterEvent d hd k) ⊆
        firstCoordinateAnchoredDiameterEvent d hd k := by
    intro omega homega
    obtain ⟨s, homega⟩ := Set.mem_iUnion.mp homega
    exact homega.2
  unfold CubicBondAnimal.firstDirectionAnchoredTotalMass
  calc
    (∑ s : Fin ((2 * k + 1) ^ d + 1),
        CubicBondAnimal.firstDirectionAnchoredMass d s.1 p hd k) ≤
        ∑ s : Fin ((2 * k + 1) ^ d + 1),
          (bernoulliBondMeasure d p).real
            (finiteClusterSizeEvent d s.1 ∩
              firstCoordinateAnchoredDiameterEvent d hd k) := by
      apply Finset.sum_le_sum
      intro s _hs
      exact CubicBondAnimal.firstDirectionAnchoredMass_le_measureReal_inter_size_anchoredEvent
        d s.1 p hd k
    _ = (bernoulliBondMeasure d p).real
        (⋃ s : Fin ((2 * k + 1) ^ d + 1),
          finiteClusterSizeEvent d s.1 ∩ firstCoordinateAnchoredDiameterEvent d hd k) :=
      hsum.symm
    _ ≤ (bernoulliBondMeasure d p).real
        (firstCoordinateAnchoredDiameterEvent d hd k) := measureReal_mono hsub
    _ ≤ finiteBoxRadiusProbability d p k :=
      firstCoordinateAnchoredDiameter_probability_le_finiteBoxRadiusProbability hd p

/-- Equation (8.40): exact diameter probability is at most the directional and anchoring
loss times the finite-radius probability. -/
theorem finiteClusterLInfDiameterProbability_le_radius_prefactor
    {d : ℕ} (hd : 0 < d) (p : I) (k : ℕ) :
    finiteClusterLInfDiameterProbability d p k ≤
      (d : ℝ) * (((2 * k + 1 : ℕ) : ℝ) ^ d) *
        finiteBoxRadiusProbability d p k := by
  let Q := finiteClusterLInfDiameterProbability d p k
  let P := (bernoulliBondMeasure d p).real
    (finiteClusterFirstDirectionDiameterEvent d hd k)
  let M := CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd k
  let R := finiteBoxRadiusProbability d p k
  have hdir : Q ≤ (d : ℝ) * P := by
    simpa [Q, P] using finiteClusterLInfDiameterProbability_le_card_mul_firstDirection hd p
  have hanchor : P ≤ (((2 * k + 1 : ℕ) : ℝ) ^ d) * M := by
    simpa [P, M, Nat.cast_pow] using
      firstDirectionDiameter_probability_le_boxCard_mul_anchoredTotalMass d k p hd
  have hradius : M ≤ R := by
    simpa [M, R] using firstDirectionAnchoredTotalMass_le_finiteBoxRadiusProbability d k p hd
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbox0 : 0 ≤ (((2 * k + 1 : ℕ) : ℝ) ^ d) := by positivity
  calc
    Q ≤ (d : ℝ) * P := hdir
    _ ≤ (d : ℝ) * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * M) :=
      mul_le_mul_of_nonneg_left hanchor hd0
    _ ≤ (d : ℝ) * ((((2 * k + 1 : ℕ) : ℝ) ^ d) * R) := by
      gcongr
    _ = (d : ℝ) * (((2 * k + 1 : ℕ) : ℝ) ^ d) * R := by ring

/-! ### The variable-size gluing family -/

/-- All rooted animals of diameter `k` whose first-coordinate span realizes that diameter.  The
size index is bounded by the cardinality of the containing coordinate box. -/
abbrev FirstDirectionRootedAnimal
    (d : ℕ) (hd : 0 < d) (k : ℕ) :=
  Σ s : Fin ((2 * k + 1) ^ d + 1),
    {A : CubicBondAnimal d s.1 // A.IsFirstDirectionMaximal hd k}

/-- Anchored analogue of `FirstDirectionRootedAnimal`. -/
abbrev FirstDirectionAnchoredAnimal
    (d : ℕ) (hd : 0 < d) (k : ℕ) :=
  Σ s : Fin ((2 * k + 1) ^ d + 1),
    {A : CubicBondAnimal.Anchored d s.1 //
      A.1.IsFirstDirectionMaximal hd k}

/-- A pair in the finite source family used in Grimmett's diameter gluing. -/
abbrev DiameterGlueInput (d : ℕ) (hd : 0 < d) (m n : ℕ) :=
  FirstDirectionRootedAnimal d hd m × FirstDirectionAnchoredAnimal d hd n

/-- The animal obtained from a variable-size diameter-gluing input. -/
noncomputable def diameterGlueInputAnimal
    {d : ℕ} (hd : 0 < d) {m n : ℕ} (X : DiameterGlueInput d hd m n) :
    CubicBondAnimal d ((X.1.1.1 + 1) + X.2.1.1) :=
  X.1.2.1.diameterGlue X.2.2.1 hd

/-- Cylinder determined by the output of a variable-size diameter gluing. -/
def diameterGlueInputEvent
    {d : ℕ} (hd : 0 < d) {m n : ℕ} (X : DiameterGlueInput d hd m n) :
    Set (EdgeConfiguration d) :=
  (diameterGlueInputAnimal hd X).clusterCylinder

private theorem diameterGlue_left_bottomLeft_eq_of_vertices_eq
    {d a a' b b' : ℕ} (hd : 0 < d)
    (A : CubicBondAnimal d a) (A' : CubicBondAnimal d a')
    (B : CubicBondAnimal.Anchored d b) (B' : CubicBondAnimal.Anchored d b')
    (hvertices : (A.diameterGlue B hd).vertices =
      (A'.diameterGlue B' hd).vertices) :
    A.bottomLeft = A'.bottomLeft := by
  apply toLex_inj.mp
  apply le_antisymm
  · rw [← A.diameterGlue_bottomLeft B hd]
    apply (A.diameterGlue B hd).bottomLeft_lex_le
    rw [hvertices]
    exact (A'.mem_diameterGlue_vertices_iff B' hd A'.bottomLeft).mpr
      (Or.inl A'.bottomLeft_mem)
  · rw [← A'.diameterGlue_bottomLeft B' hd]
    apply (A'.diameterGlue B' hd).bottomLeft_lex_le
    rw [← hvertices]
    exact (A.mem_diameterGlue_vertices_iff B hd A.bottomLeft).mpr
      (Or.inl A.bottomLeft_mem)

/-- Equality of glued vertex sets already recovers the left input size, provided the prescribed
left diameter is the same. -/
private theorem diameterGlue_left_size_eq_of_vertices_eq
    {d a a' b b' m : ℕ} (hd : 0 < d)
    (A : CubicBondAnimal d a) (A' : CubicBondAnimal d a')
    (B : CubicBondAnimal.Anchored d b) (B' : CubicBondAnimal.Anchored d b')
    (hA : A.IsFirstDirectionMaximal hd m)
    (hA' : A'.IsFirstDirectionMaximal hd m)
    (hvertices : (A.diameterGlue B hd).vertices =
      (A'.diameterGlue B' hd).vertices) :
    a = a' := by
  have hbottom := diameterGlue_left_bottomLeft_eq_of_vertices_eq
    hd A A' B B' hvertices
  have hfilterA := A.filter_diameterGlue_vertices_eq_left B hd hA
  have hfilterA' := A'.filter_diameterGlue_vertices_eq_left B' hd hA'
  have hleftVertices : A.vertices = A'.vertices := by
    rw [← hfilterA, ← hfilterA', hvertices, hbottom]
  rw [← A.vertices_card, ← A'.vertices_card, hleftVertices]

/-- Different variable-size gluing inputs determine disjoint cluster cylinders.  The proof
uses the diameter cut to recover the left size, then the output cardinality to recover the
right size, before invoking fixed-size injectivity. -/
theorem diameterGlueInputEvent_pairwiseDisjoint
    {d m n : ℕ} (hd : 0 < d) :
    Pairwise (Function.onFun Disjoint
      (diameterGlueInputEvent (d := d) hd (m := m) (n := n))) := by
  classical
  intro X Y hXY
  change Disjoint (diameterGlueInputEvent hd X) (diameterGlueInputEvent hd Y)
  rw [Set.disjoint_left]
  intro omega hX hY
  apply hXY
  have hvertices : (diameterGlueInputAnimal hd X).vertices =
      (diameterGlueInputAnimal hd Y).vertices := by
    apply Finset.coe_injective
    exact ((diameterGlueInputAnimal hd X).cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hX).symm.trans
      ((diameterGlueInputAnimal hd Y).cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hY)
  have hleft : X.1.1.1 = Y.1.1.1 :=
    diameterGlue_left_size_eq_of_vertices_eq hd
      X.1.2.1 Y.1.2.1 X.2.2.1 Y.2.2.1 X.1.2.2 Y.1.2.2 hvertices
  have htotal : (X.1.1.1 + 1) + X.2.1.1 =
      (Y.1.1.1 + 1) + Y.2.1.1 := by
    rw [← (diameterGlueInputAnimal hd X).vertices_card,
      ← (diameterGlueInputAnimal hd Y).vertices_card, hvertices]
  have hright : X.2.1.1 = Y.2.1.1 := by omega
  rcases X with ⟨⟨sx, Ax⟩, ⟨tx, Bx⟩⟩
  rcases Y with ⟨⟨sy, Ay⟩, ⟨ty, By⟩⟩
  dsimp at hX hY hvertices hleft hright ⊢
  have hs : sx = sy := Fin.ext hleft
  have ht : tx = ty := Fin.ext hright
  subst sy
  subst ty
  have houtput : Ax.1.diameterGlue Bx.1 hd = Ay.1.diameterGlue By.1 hd :=
    CubicBondAnimal.eq_of_mem_clusterCylinder _ _ hX hY
  have hpairs : (Ax.1, Bx.1) = (Ay.1, By.1) :=
    CubicBondAnimal.diameterGlue_injective hd houtput
  have hAx : Ax = Ay := Subtype.ext (congrArg Prod.fst hpairs)
  have hBx : Bx = By := Subtype.ext (congrArg Prod.snd hpairs)
  subst Ay
  subst By
  rfl

theorem measurableSet_diameterGlueInputEvent
    {d m n : ℕ} (hd : 0 < d) (X : DiameterGlueInput d hd m n) :
    MeasurableSet (diameterGlueInputEvent hd X) :=
  (diameterGlueInputAnimal hd X).measurableSet_clusterCylinder

theorem diameterGlueInputEvent_subset_firstDirectionDiameter
    {d m n : ℕ} (hd : 0 < d) (X : DiameterGlueInput d hd m n) :
    diameterGlueInputEvent hd X ⊆
      finiteClusterFirstDirectionDiameterEvent d hd (m + n + 2) := by
  intro omega homega
  exact ((diameterGlueInputAnimal hd X).mem_finiteClusterFirstDirectionDiameterEvent_iff_of_mem_clusterCylinder
    hd homega (m + n + 2)).mpr
      (X.1.2.1.diameterGlue_isFirstDirectionMaximal X.2.2.1 hd X.1.2.2 X.2.2.2)

private theorem sum_firstDirectionRootedAnimal_weight
    (d k : ℕ) (p : ℝ) (hd : 0 < d) :
    (∑ X : FirstDirectionRootedAnimal d hd k, X.2.1.weight p) =
      ∑ s : Fin ((2 * k + 1) ^ d + 1),
        CubicBondAnimal.firstDirectionAnimalMass d s.1 p hd k := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold CubicBondAnimal.firstDirectionAnimalMass
  rfl

private theorem sum_firstDirectionAnchoredAnimal_weight
    (d k : ℕ) (p : ℝ) (hd : 0 < d) :
    (∑ X : FirstDirectionAnchoredAnimal d hd k, X.2.1.1.weight p) =
      CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd k := by
  classical
  unfold CubicBondAnimal.firstDirectionAnchoredTotalMass
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold CubicBondAnimal.firstDirectionAnchoredMass
  rfl

private theorem sum_diameterGlueInput_sourceWeight
    (d m n : ℕ) (p : I) (c : ℝ) (hd : 0 < d) :
    (∑ X : DiameterGlueInput d hd m n,
        c * X.1.2.1.weight p * X.2.2.1.1.weight p) =
      c * (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d hd m) *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd n := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ A : FirstDirectionRootedAnimal d hd m,
        ∑ B : FirstDirectionAnchoredAnimal d hd n,
          c * A.2.1.weight p * B.2.1.1.weight p) =
        ∑ A : FirstDirectionRootedAnimal d hd m,
          (c * A.2.1.weight p) *
            (∑ B : FirstDirectionAnchoredAnimal d hd n, B.2.1.1.weight p) := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
    _ = (∑ A : FirstDirectionRootedAnimal d hd m,
          c * A.2.1.weight p) *
            (∑ B : FirstDirectionAnchoredAnimal d hd n, B.2.1.1.weight p) := by
      rw [Finset.sum_mul]
    _ = (c * ∑ A : FirstDirectionRootedAnimal d hd m, A.2.1.weight p) *
            (∑ B : FirstDirectionAnchoredAnimal d hd n, B.2.1.1.weight p) := by
      congr 1
      rw [Finset.mul_sum]
    _ = c * (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d hd m) *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd n := by
      rw [sum_firstDirectionRootedAnimal_weight,
        sum_firstDirectionAnchoredAnimal_weight,
        ← firstDirectionDiameter_probability_eq_sum_animalMass]

/-- Summing the injective gluing family gives the directional, anchored form of Lemma 8.27. -/
theorem sourcePenalty_mul_firstDirectionProbability_mul_anchoredTotalMass_le
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) :
    (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d (by omega) m) *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p (by omega) n ≤
      (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d (by omega) (m + n + 2)) := by
  classical
  let hd0 : 0 < d := by omega
  let c : ℝ := (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)
  let F : DiameterGlueInput d hd0 m n → Set (EdgeConfiguration d) :=
    diameterGlueInputEvent hd0
  have hsum : (bernoulliBondMeasure d p).real
      (⋃ X : DiameterGlueInput d hd0 m n, F X) =
      ∑ X : DiameterGlueInput d hd0 m n,
        (bernoulliBondMeasure d p).real (F X) :=
    measureReal_iUnion_fintype
      (μ := bernoulliBondMeasure d p)
      (diameterGlueInputEvent_pairwiseDisjoint (m := m) (n := n) hd0)
      (measurableSet_diameterGlueInputEvent (m := m) (n := n) hd0)
  have hunion : (⋃ X : DiameterGlueInput d hd0 m n, F X) ⊆
      finiteClusterFirstDirectionDiameterEvent d hd0 (m + n + 2) :=
    Set.iUnion_subset fun X ↦ diameterGlueInputEvent_subset_firstDirectionDiameter hd0 X
  change c * (bernoulliBondMeasure d p).real
        (finiteClusterFirstDirectionDiameterEvent d hd0 m) *
      CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd0 n ≤ _
  calc
    c * (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d hd0 m) *
        CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd0 n =
        ∑ X : DiameterGlueInput d hd0 m n,
          c * X.1.2.1.weight p * X.2.2.1.1.weight p := by
      exact (sum_diameterGlueInput_sourceWeight d m n p c hd0).symm
    _ ≤ ∑ X : DiameterGlueInput d hd0 m n,
          (bernoulliBondMeasure d p).real (F X) := by
      apply Finset.sum_le_sum
      intro X _hX
      change c * X.1.2.1.weight p * X.2.2.1.1.weight p ≤
        (bernoulliBondMeasure d p).real
          (diameterGlueInputEvent hd0 X)
      rw [show (bernoulliBondMeasure d p).real
          (diameterGlueInputEvent hd0 X) =
          (diameterGlueInputAnimal hd0 X).weight p by
        exact (diameterGlueInputAnimal hd0 X).bernoulliBondMeasure_real_clusterCylinder p]
      exact X.1.2.1.sourcePenalty_mul_weight_le_weight_diameterGlue
        X.2.2.1 hd hp0 hp1
    _ = (bernoulliBondMeasure d p).real
          (⋃ X : DiameterGlueInput d hd0 m n, F X) := hsum.symm
    _ ≤ (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d hd0 (m + n + 2)) :=
      measureReal_mono hunion

/-- Directional probability form of Lemma 8.27.  The polynomial factor is precisely the
anchoring loss for the right input. -/
theorem sourcePenalty_mul_firstDirectionProbabilities_le
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) :
    (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d (by omega) m) *
        (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d (by omega) n) ≤
      ((2 * n + 1 : ℕ) ^ d : ℝ) *
        (bernoulliBondMeasure d p).real
          (finiteClusterFirstDirectionDiameterEvent d (by omega) (m + n + 2)) := by
  let hd0 : 0 < d := by omega
  let c : ℝ := (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)
  let P : ℕ → ℝ := fun k ↦ (bernoulliBondMeasure d p).real
    (finiteClusterFirstDirectionDiameterEvent d hd0 k)
  let M : ℝ := CubicBondAnimal.firstDirectionAnchoredTotalMass d p hd0 n
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hPm : 0 ≤ P m := measureReal_nonneg
  have hanchor : P n ≤ ((2 * n + 1 : ℕ) ^ d : ℝ) * M := by
    simpa [P, M] using firstDirectionDiameter_probability_le_boxCard_mul_anchoredTotalMass
      d n p hd0
  have hglue : c * P m * M ≤ P (m + n + 2) := by
    simpa [c, P, M] using
      sourcePenalty_mul_firstDirectionProbability_mul_anchoredTotalMass_le
        hd p hp0 hp1 m n
  have hmul := mul_le_mul_of_nonneg_left hanchor (mul_nonneg hc hPm)
  have hbox : 0 ≤ (((2 * n + 1 : ℕ) : ℝ) ^ d) := by positivity
  change c * P m * P n ≤ ((2 * n + 1 : ℕ) ^ d : ℝ) * P (m + n + 2)
  calc
    c * P m * P n ≤ c * P m * (((2 * n + 1 : ℕ) ^ d : ℝ) * M) := by
      simpa [mul_assoc] using hmul
    _ = ((2 * n + 1 : ℕ) ^ d : ℝ) * (c * P m * M) := by ring
    _ ≤ ((2 * n + 1 : ℕ) ^ d : ℝ) * P (m + n + 2) :=
      mul_le_mul_of_nonneg_left hglue hbox

/-- Denominator-free form of Grimmett's Lemma 8.27.  Two factors of `d` come from choosing a
coordinate direction realizing each input diameter, while `(2n+1)^d` is the anchoring loss. -/
theorem sourcePenalty_mul_finiteClusterLInfDiameterProbabilities_le
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) :
    (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
        finiteClusterLInfDiameterProbability d p m *
        finiteClusterLInfDiameterProbability d p n ≤
      (d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ) *
        finiteClusterLInfDiameterProbability d p (m + n + 2) := by
  let hd0 : 0 < d := by omega
  let c : ℝ := (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2)
  let Q : ℕ → ℝ := finiteClusterLInfDiameterProbability d p
  let P : ℕ → ℝ := fun k ↦ (bernoulliBondMeasure d p).real
    (finiteClusterFirstDirectionDiameterEvent d hd0 k)
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hQm : 0 ≤ Q m := finiteClusterLInfDiameterProbability_nonneg d p m
  have hQn : 0 ≤ Q n := finiteClusterLInfDiameterProbability_nonneg d p n
  have hPm : 0 ≤ P m := measureReal_nonneg
  have hPn : 0 ≤ P n := measureReal_nonneg
  have hm : Q m ≤ (d : ℝ) * P m := by
    simpa [Q, P] using finiteClusterLInfDiameterProbability_le_card_mul_firstDirection
      hd0 p (k := m)
  have hn : Q n ≤ (d : ℝ) * P n := by
    simpa [Q, P] using finiteClusterLInfDiameterProbability_le_card_mul_firstDirection
      hd0 p (k := n)
  have hinputs : Q m * Q n ≤ ((d : ℝ) * P m) * ((d : ℝ) * P n) :=
    mul_le_mul hm hn hQn (mul_nonneg (Nat.cast_nonneg d) hPm)
  have hdir : c * P m * P n ≤
      ((2 * n + 1 : ℕ) ^ d : ℝ) * P (m + n + 2) := by
    simpa [c, P] using sourcePenalty_mul_firstDirectionProbabilities_le
      hd p hp0 hp1 m n
  have hout : P (m + n + 2) ≤ Q (m + n + 2) := by
    exact measureReal_mono Set.inter_subset_left
  change c * Q m * Q n ≤
    (d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ) * Q (m + n + 2)
  calc
    c * Q m * Q n = c * (Q m * Q n) := by ring
    _ ≤ c * (((d : ℝ) * P m) * ((d : ℝ) * P n)) :=
      mul_le_mul_of_nonneg_left hinputs hc
    _ = (d : ℝ) ^ 2 * (c * P m * P n) := by ring
    _ ≤ (d : ℝ) ^ 2 *
        (((2 * n + 1 : ℕ) ^ d : ℝ) * P (m + n + 2)) :=
      mul_le_mul_of_nonneg_left hdir (sq_nonneg (d : ℝ))
    _ ≤ (d : ℝ) ^ 2 *
        (((2 * n + 1 : ℕ) ^ d : ℝ) * Q (m + n + 2)) := by
      gcongr
    _ = (d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ) * Q (m + n + 2) := by
      ring

/-- **Grimmett, Lemma 8.27.**  Exact source-facing lower bound for the probability of a finite
cluster with glued `L∞` diameter. -/
theorem finiteClusterLInfDiameterProbability_glue_lower_bound
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m n : ℕ) :
    ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) /
        ((d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ))) *
        finiteClusterLInfDiameterProbability d p m *
        finiteClusterLInfDiameterProbability d p n ≤
      finiteClusterLInfDiameterProbability d p (m + n + 2) := by
  have hden : 0 < (d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ) := by
    positivity
  have h := sourcePenalty_mul_finiteClusterLInfDiameterProbabilities_le
    hd p hp0 hp1 m n
  calc
    ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) /
          ((d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ))) *
          finiteClusterLInfDiameterProbability d p m *
          finiteClusterLInfDiameterProbability d p n =
        ((p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
          finiteClusterLInfDiameterProbability d p m *
          finiteClusterLInfDiameterProbability d p n) /
            ((d : ℝ) ^ 2 * ((2 * n + 1 : ℕ) ^ d : ℝ)) := by
      field_simp
    _ ≤ finiteClusterLInfDiameterProbability d p (m + n + 2) := by
      apply (div_le_iff₀ hden).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem finiteClusterLInfDiameterProbability_pos_of_animal
    {d s k : ℕ} (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (A : CubicBondAnimal d s) (hA : A.lInfDiameter = k) :
    0 < finiteClusterLInfDiameterProbability d p k := by
  have hsubset : A.clusterCylinder ⊆ finiteClusterLInfDiameterEvent d k := by
    intro omega homega
    exact (A.mem_finiteClusterLInfDiameterEvent_iff_of_mem_clusterCylinder homega k).mpr hA
  have hweight : 0 < A.weight p := by
    exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)
  have hcyl : 0 < (bernoulliBondMeasure d p).real A.clusterCylinder := by
    rw [A.bernoulliBondMeasure_real_clusterCylinder]
    exact hweight
  exact hcyl.trans_le (measureReal_mono hsubset)

/-- Exact finite-diameter probabilities are strictly positive at every index when `0 < p < 1`.
This makes all logarithms in the Fekete argument faithful rather than relying on the totalized
value `log 0 = 0`. -/
theorem finiteClusterLInfDiameterProbability_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ k : ℕ, 0 < finiteClusterLInfDiameterProbability d p k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | _ | k
      · exact finiteClusterLInfDiameterProbability_pos_of_animal p hp0 hp1
          (CubicBondAnimal.originAnimal d)
          (CubicBondAnimal.originAnimal_isFirstDirectionMaximal d (by omega)).1
      · exact finiteClusterLInfDiameterProbability_pos_of_animal p hp0 hp1
          ((CubicBondAnimal.originAnimal d).addRightSeparator (by omega))
          (CubicBondAnimal.addRightSeparator_origin_isFirstDirectionMaximal d (by omega)).1
      · have hk := ih k (by omega)
        have hzero := ih 0 (by omega)
        have hglue := sourcePenalty_mul_finiteClusterLInfDiameterProbabilities_le
          hd p hp0 hp1 k 0
        have hfactor : 0 <
            (p : ℝ) ^ 2 * (1 - (p : ℝ)) ^ (2 * d - 2) *
              finiteClusterLInfDiameterProbability d p k *
              finiteClusterLInfDiameterProbability d p 0 := by
          positivity
        have hout := hfactor.trans_le hglue
        have hdSq : 0 < (d : ℝ) ^ 2 := by positivity
        have htarget : 0 < finiteClusterLInfDiameterProbability d p (k + 2) := by
          norm_num at hout
          rcases (mul_pos_iff.mp hout) with hpos | hneg
          · exact hpos.2
          · exact (not_lt_of_ge hdSq.le hneg.1).elim
        convert htarget using 1 <;> omega

end Percolation
