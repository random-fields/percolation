import Percolation.Critical.ClusterExponential
import Percolation.Critical.ConcreteClusterSeries
import Mathlib.Order.PiLex

/-!
# Anchored lattice animals and concatenation

This module formalizes the geometric injection in Grimmett's Lemma 6.102.  Lexicographic
extrema replace the informal two-dimensional “top right” and “bottom left” convention and work
uniformly in every positive dimension.
-/

namespace Percolation

open Set MeasureTheory
open scoped BigOperators ENNReal unitInterval

namespace CubicBondAnimal

variable {d n : ℕ}

theorem toLex_cubicTranslate_lt_iff (a b x y : Cubic d) :
    toLex (cubicTranslate a b x) < toLex (cubicTranslate a b y) ↔
      toLex x < toLex y := by
  constructor
  · rintro ⟨i, hi, hxy⟩
    refine ⟨i, fun j hj ↦ ?_, ?_⟩
    · have := hi j hj
      change x j + (b j - a j) = y j + (b j - a j) at this
      exact add_right_cancel this
    · change x i + (b i - a i) < y i + (b i - a i) at hxy
      exact (add_lt_add_iff_right (b i - a i)).mp hxy
  · rintro ⟨i, hi, hxy⟩
    refine ⟨i, fun j hj ↦ ?_, ?_⟩
    · change x j + (b j - a j) = y j + (b j - a j)
      have hbase : x j = y j := hi j hj
      rw [hbase]
    · change x i + (b i - a i) < y i + (b i - a i)
      have hbase : x i < y i := hxy
      exact (add_lt_add_iff_right (b i - a i)).mpr hbase

theorem toLex_cubicTranslate_le_iff (a b x y : Cubic d) :
    toLex (cubicTranslate a b x) ≤ toLex (cubicTranslate a b y) ↔
      toLex x ≤ toLex y := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact (toLex_cubicTranslate_lt_iff a b x y).mp h |>.le
    · exact (cubicTranslate_injective a b (toLex_inj.mp h)) ▸ le_rfl
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact (toLex_cubicTranslate_lt_iff a b x y).mpr h |>.le
    · exact (congrArg (cubicTranslate a b) (toLex_inj.mp h)) ▸ le_rfl

/-- Vertices with the lexicographic order on their coordinates. -/
noncomputable def lexVertices (A : CubicBondAnimal d n) : Finset (Lex (Cubic d)) :=
  A.vertices.image toLex

theorem lexVertices_nonempty (A : CubicBondAnimal d n) : A.lexVertices.Nonempty := by
  exact Finset.Nonempty.image ⟨cubicOrigin, A.origin_mem⟩ toLex

/-- Lexicographically least vertex (“bottom left”). -/
noncomputable def bottomLeft (A : CubicBondAnimal d n) : Cubic d :=
  ofLex (A.lexVertices.min' A.lexVertices_nonempty)

/-- Lexicographically greatest vertex (“top right”). -/
noncomputable def topRight (A : CubicBondAnimal d n) : Cubic d :=
  ofLex (A.lexVertices.max' A.lexVertices_nonempty)

theorem bottomLeft_mem (A : CubicBondAnimal d n) : A.bottomLeft ∈ A.vertices := by
  have h := Finset.min'_mem A.lexVertices A.lexVertices_nonempty
  unfold lexVertices at h
  rw [Finset.mem_image] at h
  obtain ⟨x, hx, hxeq⟩ := h
  simpa [bottomLeft] using hxeq ▸ hx

theorem topRight_mem (A : CubicBondAnimal d n) : A.topRight ∈ A.vertices := by
  have h := Finset.max'_mem A.lexVertices A.lexVertices_nonempty
  unfold lexVertices at h
  rw [Finset.mem_image] at h
  obtain ⟨x, hx, hxeq⟩ := h
  simpa [topRight] using hxeq ▸ hx

theorem bottomLeft_lex_le (A : CubicBondAnimal d n) {x : Cubic d}
    (hx : x ∈ A.vertices) : toLex A.bottomLeft ≤ toLex x := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem lex_le_topRight (A : CubicBondAnimal d n) {x : Cubic d}
    (hx : x ∈ A.vertices) : toLex x ≤ toLex A.topRight := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Animals whose bottom-left anchor is the origin. -/
def IsBottomLeftAnchored (A : CubicBondAnimal d n) : Prop :=
  A.bottomLeft = cubicOrigin

/-- Finite type of bottom-left anchored animals. -/
abbrev Anchored (d n : ℕ) := {A : CubicBondAnimal d n // A.IsBottomLeftAnchored}

theorem coordinate_zero_nonneg_of_anchored {A : CubicBondAnimal d n}
    (hA : A.IsBottomLeftAnchored) {x : Cubic d} (hx : x ∈ A.vertices)
    (hd : 0 < d) : 0 ≤ x ⟨0, hd⟩ := by
  letI : NeZero d := ⟨hd.ne'⟩
  have hlex := A.bottomLeft_lex_le hx
  rw [hA] at hlex
  have hcoord := Pi.apply_le_of_toLex hlex (i := (⟨0, hd⟩ : Fin d)) (by
    intro j hj
    exact (Fin.not_lt_zero j hj).elim)
  simpa [cubicOrigin] using hcoord

theorem coordinate_zero_le_topRight {A : CubicBondAnimal d n}
    {x : Cubic d} (hx : x ∈ A.vertices) (hd : 0 < d) :
    x ⟨0, hd⟩ ≤ A.topRight ⟨0, hd⟩ := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact Pi.apply_le_of_toLex (A.lex_le_topRight hx) (i := (⟨0, hd⟩ : Fin d)) (by
    intro j hj
    exact (Fin.not_lt_zero j hj).elim)

variable {m : ℕ}

/-- Vertex immediately to the positive-first-coordinate side of the top-right anchor. -/
noncomputable def rightOfTopRight (A : CubicBondAnimal d m) (hd : 0 < d) : Cubic d :=
  cubicStepFrom A.topRight ((⟨0, hd⟩ : Fin d), true)

@[simp] theorem rightOfTopRight_coordinate_zero
    (A : CubicBondAnimal d m) (hd : 0 < d) :
    A.rightOfTopRight hd ⟨0, hd⟩ = A.topRight ⟨0, hd⟩ + 1 := by
  simp [rightOfTopRight, cubicStepFrom, cubicDirectionIncrement]

/-- Place a second anchored animal immediately to the right of the first. -/
noncomputable def placeRight (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) (x : Cubic d) : Cubic d :=
  cubicTranslate B.bottomLeft (A.rightOfTopRight hd) x

theorem placeRight_coordinate_zero_of_anchored
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) {x : Cubic d} (hx : x ∈ B.vertices) :
    A.topRight ⟨0, hd⟩ + 1 ≤ A.placeRight B hd x ⟨0, hd⟩ := by
  have hx0 := B.coordinate_zero_nonneg_of_anchored hB hx hd
  simp only [placeRight, cubicTranslate, rightOfTopRight_coordinate_zero]
  rw [hB]
  simp only [cubicOrigin, Pi.zero_apply]
  omega

theorem coordinate_zero_lt_placeRight_of_anchored
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ B.vertices) :
    x ⟨0, hd⟩ < A.placeRight B hd y ⟨0, hd⟩ := by
  exact (A.coordinate_zero_le_topRight hx hd).trans_lt
    (lt_of_lt_of_le (lt_add_one _) (A.placeRight_coordinate_zero_of_anchored B hB hd hy))

/-- Translated vertex set of the right-hand animal. -/
noncomputable def placedVertices (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) : Finset (Cubic d) :=
  B.vertices.map (cubicTranslationEquiv B.bottomLeft (A.rightOfTopRight hd)).toEmbedding

@[simp] theorem mem_placedVertices_iff (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) (x : Cubic d) :
    x ∈ A.placedVertices B hd ↔
      ∃ y ∈ B.vertices, A.placeRight B hd y = x := by
  rw [placedVertices, Finset.mem_map]
  rfl

theorem vertices_disjoint_placedVertices
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    Disjoint A.vertices (A.placedVertices B hd) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rw [mem_placedVertices_iff] at hxB
  obtain ⟨y, hy, rfl⟩ := hxB
  exact (A.coordinate_zero_lt_placeRight_of_anchored B hB hd hxA hy).ne rfl

@[simp] theorem placedVertices_card (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) :
    (A.placedVertices B hd).card = n := by
  rw [placedVertices, Finset.card_map, B.vertices_card]

/-- Translated occupied edges of the right-hand animal. -/
noncomputable def placedEdges (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) : Finset (CubicEdge d) :=
  B.edges.map
    (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet.toEmbedding

@[simp] theorem mem_placedEdges_iff (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) (e : CubicEdge d) :
    e ∈ A.placedEdges B hd ↔
      ∃ f ∈ B.edges,
        (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet f = e := by
  rw [placedEdges, Finset.mem_map]
  rfl

@[simp] theorem placedEdges_card (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) :
    (A.placedEdges B hd).card = B.edges.card := by
  rw [placedEdges, Finset.card_map]

/-- The unique new occupied edge joining the two placed animals. -/
noncomputable def connectorEdge (A : CubicBondAnimal d m) (hd : 0 < d) : CubicEdge d :=
  cubicStepEdge A.topRight ((⟨0, hd⟩ : Fin d), true)

theorem connectorEdge_sym2 (A : CubicBondAnimal d m) (hd : 0 < d) :
    (A.connectorEdge hd).1 = s(A.topRight, A.rightOfTopRight hd) := by
  simp [connectorEdge, rightOfTopRight, cubicStepEdge]

/-- Vertex and occupied-edge sets of the concatenated animal. -/
noncomputable def concatenatedVertices (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) : Finset (Cubic d) :=
  A.vertices ∪ A.placedVertices B hd

noncomputable def concatenatedEdges (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) : Finset (CubicEdge d) :=
  insert (A.connectorEdge hd) (A.edges ∪ A.placedEdges B hd)

theorem concatenatedVertices_card (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concatenatedVertices B hd).card = m + n := by
  rw [concatenatedVertices, Finset.card_union_of_disjoint
    (A.vertices_disjoint_placedVertices B hB hd), A.vertices_card, placedVertices_card]

theorem vertices_card_pos (A : CubicBondAnimal d n) : 0 < n := by
  rw [← A.vertices_card, Finset.card_pos]
  exact ⟨cubicOrigin, A.origin_mem⟩

theorem concatenatedVertices_subset_metricBall
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    A.concatenatedVertices B hd ⊆ cubicMetricBall d cubicOrigin (m + n - 1) := by
  intro x hx
  rw [concatenatedVertices, Finset.mem_union] at hx
  rw [mem_cubicMetricBall_iff_l1Dist_le]
  rcases hx with hxA | hxB
  · have hdist := mem_cubicMetricBall_iff_l1Dist_le.mp (A.vertices_subset hxA)
    omega
  · rw [mem_placedVertices_iff] at hxB
    obtain ⟨y, hy, rfl⟩ := hxB
    have hA := mem_cubicMetricBall_iff_l1Dist_le.mp
      (A.vertices_subset A.topRight_mem)
    have hBdist := mem_cubicMetricBall_iff_l1Dist_le.mp (B.vertices_subset hy)
    have hstep : cubicL1Dist A.topRight (A.rightOfTopRight hd) = 1 := by
      simp [rightOfTopRight, cubicL1Dist_stepFrom]
    have htrans : cubicL1Dist (A.rightOfTopRight hd) (A.placeRight B hd y) =
        cubicL1Dist B.bottomLeft y := by
      simpa [placeRight] using
        cubicL1Dist_translate B.bottomLeft (A.rightOfTopRight hd) B.bottomLeft y
    have hBanchor : cubicL1Dist B.bottomLeft y = cubicL1Dist cubicOrigin y := by rw [hB]
    calc
      cubicL1Dist cubicOrigin (A.placeRight B hd y) ≤
          cubicL1Dist cubicOrigin A.topRight +
            cubicL1Dist A.topRight (A.placeRight B hd y) :=
        cubicL1Dist_triangle _ _ _
      _ ≤ cubicL1Dist cubicOrigin A.topRight +
          (cubicL1Dist A.topRight (A.rightOfTopRight hd) +
            cubicL1Dist (A.rightOfTopRight hd) (A.placeRight B hd y)) := by
        gcongr
        exact cubicL1Dist_triangle _ _ _
      _ ≤ (m - 1) + (1 + (n - 1)) := by
        rw [hstep, htrans, hBanchor]
        omega
      _ ≤ m + n - 1 := by
        have hm := A.vertices_card_pos
        have hn := B.vertices_card_pos
        omega

theorem concatenatedEdges_endpoints
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) :
    ∀ e ∈ A.concatenatedEdges B hd, ∀ x ∈ (e : Sym2 (Cubic d)),
      x ∈ A.concatenatedVertices B hd := by
  intro e he x hx
  rw [concatenatedEdges, Finset.mem_insert, Finset.mem_union] at he
  rcases he with rfl | heA | heB
  · rw [concatenatedVertices, Finset.mem_union]
    rw [connectorEdge_sym2] at hx
    rcases (Sym2.mem_iff.mp hx) with rfl | rfl
    · exact Or.inl A.topRight_mem
    · apply Or.inr
      rw [mem_placedVertices_iff]
      exact ⟨B.bottomLeft, B.bottomLeft_mem, by
        simp [placeRight]⟩
  · exact Finset.mem_union_left _ (A.edge_endpoints e heA x hx)
  · rw [mem_placedEdges_iff] at heB
    obtain ⟨f, hf, rfl⟩ := heB
    apply Finset.mem_union_right
    rw [mem_placedVertices_iff]
    have hxmap : x ∈ Sym2.map
        (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)) f.1 := by
      simpa using hx
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hxmap
    exact ⟨y, B.edge_endpoints f hf y hy, hyx⟩

theorem concatenated_connected
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    ∀ x ∈ A.concatenatedVertices B hd,
      ∃ w : (cubicGraph d).Walk cubicOrigin x,
        walkEdgeFinset w ⊆ A.concatenatedEdges B hd := by
  intro x hx
  rw [concatenatedVertices, Finset.mem_union] at hx
  rcases hx with hxA | hxB
  · obtain ⟨w, hw⟩ := A.connected x hxA
    exact ⟨w, fun e he ↦ by
      rw [concatenatedEdges, Finset.mem_insert]
      exact Or.inr (Finset.mem_union_left _ (hw he))⟩
  · rw [mem_placedVertices_iff] at hxB
    obtain ⟨y, hy, rfl⟩ := hxB
    obtain ⟨wA, hwA⟩ := A.connected A.topRight A.topRight_mem
    obtain ⟨wB, hwB⟩ := B.connected y hy
    let T := cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)
    let wBT : (cubicGraph d).Walk (A.rightOfTopRight hd) (A.placeRight B hd y) :=
      (wB.map T.toHom).copy (by
        change cubicTranslate B.bottomLeft (A.rightOfTopRight hd) cubicOrigin = _
        rw [← hB]
        simp [cubicTranslate]) rfl
    have hadj : (cubicGraph d).Adj A.topRight (A.rightOfTopRight hd) := by
      rw [cubicGraph_adj_iff_exists_stepFrom]
      exact ⟨((⟨0, hd⟩ : Fin d), true), rfl⟩
    let w : (cubicGraph d).Walk cubicOrigin (A.placeRight B hd y) :=
      wA.append (SimpleGraph.Walk.cons hadj wBT)
    refine ⟨w, fun e he ↦ ?_⟩
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at he
    rw [concatenatedEdges, Finset.mem_insert]
    rcases he with heA | heTail
    · exact Or.inr (Finset.mem_union_left _
        (hwA ((mem_walkEdgeFinset_iff wA e).mpr heA)))
    · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at heTail
      rcases heTail with heConnector | heBmap
      · left
        apply Subtype.ext
        simpa [connectorEdge] using heConnector
      · right
        apply Finset.mem_union_right
        rw [mem_placedEdges_iff]
        have heBmap' : (e : Sym2 (Cubic d)) ∈ (wB.map T.toHom).edges := by
          simpa [wBT] using heBmap
        rw [SimpleGraph.Walk.edges_map] at heBmap'
        obtain ⟨f, hf, hfe⟩ := List.mem_map.mp heBmap'
        let f' : CubicEdge d := ⟨f, wB.edges_subset_edgeSet hf⟩
        refine ⟨f', hwB ((mem_walkEdgeFinset_iff wB f').mpr hf), ?_⟩
        apply Subtype.ext
        simpa [T] using hfe

/-- Concatenation of two bottom-left anchored animals. -/
noncomputable def concat
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    CubicBondAnimal d (m + n) where
  vertices := A.concatenatedVertices B hd
  vertices_subset := A.concatenatedVertices_subset_metricBall B hB hd
  edges := A.concatenatedEdges B hd
  edges_subset := by
    intro e he
    apply cubicEdge_mem_cubicMetricBallEdges_of_out_mem
    · exact A.concatenatedVertices_subset_metricBall B hB hd
        (A.concatenatedEdges_endpoints B hd e he e.1.out.1 (Sym2.out_fst_mem e.1))
    · exact A.concatenatedVertices_subset_metricBall B hB hd
        (A.concatenatedEdges_endpoints B hd e he e.1.out.2 (Sym2.out_snd_mem e.1))
  origin_mem := by
    rw [concatenatedVertices, Finset.mem_union]
    exact Or.inl A.origin_mem
  vertices_card := A.concatenatedVertices_card B hB hd
  edge_endpoints := A.concatenatedEdges_endpoints B hd
  connected := A.concatenated_connected B hB hd

/-- Concatenate an arbitrary rooted animal with a bottom-left anchored animal.  The left
animal need not itself be anchored: its original root remains the root of the output.  This is
the root-preserving version of `concat` used in Grimmett's diameter-gluing argument (Lemma
8.27). -/
noncomputable def rootedConcat
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    CubicBondAnimal d (m + n) where
  vertices := A.concatenatedVertices B hd
  vertices_subset := A.concatenatedVertices_subset_metricBall B hB hd
  edges := A.concatenatedEdges B hd
  edges_subset := by
    intro e he
    apply cubicEdge_mem_cubicMetricBallEdges_of_out_mem
    · exact A.concatenatedVertices_subset_metricBall B hB hd
        (A.concatenatedEdges_endpoints B hd e he e.1.out.1 (Sym2.out_fst_mem e.1))
    · exact A.concatenatedVertices_subset_metricBall B hB hd
        (A.concatenatedEdges_endpoints B hd e he e.1.out.2 (Sym2.out_snd_mem e.1))
  origin_mem := by
    rw [concatenatedVertices, Finset.mem_union]
    exact Or.inl A.origin_mem
  vertices_card := A.concatenatedVertices_card B hB hd
  edge_endpoints := A.concatenatedEdges_endpoints B hd
  connected := A.concatenated_connected B hB hd

@[simp] theorem rootedConcat_vertices
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).vertices = A.concatenatedVertices B hd := rfl

@[simp] theorem rootedConcat_edges
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).edges = A.concatenatedEdges B hd := rfl

theorem concat_isBottomLeftAnchored
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concat B hA hB hd).IsBottomLeftAnchored := by
  letI : NeZero d := ⟨hd.ne'⟩
  let C := A.concat B hA hB hd
  have hle : toLex C.bottomLeft ≤ toLex cubicOrigin :=
    C.bottomLeft_lex_le C.origin_mem
  have hge : toLex cubicOrigin ≤ toLex C.bottomLeft := by
    have hm := C.bottomLeft_mem
    change C.bottomLeft ∈ A.concatenatedVertices B hd at hm
    rw [concatenatedVertices, Finset.mem_union] at hm
    rcases hm with hmA | hmB
    · have := A.bottomLeft_lex_le hmA
      rw [hA] at this
      exact this
    · rw [mem_placedVertices_iff] at hmB
      obtain ⟨y, hy, heq⟩ := hmB
      rw [← heq]
      exact (show toLex cubicOrigin < toLex (A.placeRight B hd y) by
        refine ⟨(⟨0, hd⟩ : Fin d), ?_, ?_⟩
        · intro j hj
          exact (Fin.not_lt_zero j hj).elim
        · simpa [cubicOrigin] using
            A.coordinate_zero_lt_placeRight_of_anchored B hB hd A.origin_mem hy).le
  exact toLex_inj.mp (le_antisymm hle hge)

theorem endpoint_mem_placedVertices_of_mem_placedEdges
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n) (hd : 0 < d)
    {e : CubicEdge d} (he : e ∈ A.placedEdges B hd) {x : Cubic d}
    (hx : x ∈ (e : Sym2 (Cubic d))) : x ∈ A.placedVertices B hd := by
  rw [mem_placedEdges_iff] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [mem_placedVertices_iff]
  have hxmap : x ∈ Sym2.map
      (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)) f.1 := by simpa using hx
  obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hxmap
  exact ⟨y, B.edge_endpoints f hf y hy, hyx⟩

theorem edges_disjoint_placedEdges
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    Disjoint A.edges (A.placedEdges B hd) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  let x := e.1.out.1
  have hxA : x ∈ A.vertices :=
    A.edge_endpoints e heA x (Sym2.out_fst_mem e.1)
  have hxB : x ∈ A.placedVertices B hd :=
    A.endpoint_mem_placedVertices_of_mem_placedEdges B hd heB (Sym2.out_fst_mem e.1)
  exact Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B hB hd) hxA hxB

theorem connectorEdge_not_mem_edges
    (A : CubicBondAnimal d m) (hd : 0 < d) : A.connectorEdge hd ∉ A.edges := by
  intro he
  have hright : A.rightOfTopRight hd ∈ A.vertices :=
    A.edge_endpoints (A.connectorEdge hd) he _ (by
      rw [connectorEdge_sym2]
      simp)
  have hle := A.coordinate_zero_le_topRight hright hd
  rw [rightOfTopRight_coordinate_zero] at hle
  omega

theorem connectorEdge_not_mem_placedEdges
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    A.connectorEdge hd ∉ A.placedEdges B hd := by
  intro he
  have hleft : A.topRight ∈ A.placedVertices B hd :=
    A.endpoint_mem_placedVertices_of_mem_placedEdges B hd he (by
      rw [connectorEdge_sym2]
      simp)
  rw [mem_placedVertices_iff] at hleft
  obtain ⟨y, hy, heq⟩ := hleft
  have hlt := A.coordinate_zero_lt_placeRight_of_anchored B hB hd A.topRight_mem hy
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

theorem concatenatedEdges_card
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concatenatedEdges B hd).card = A.edges.card + B.edges.card + 1 := by
  have hconn : A.connectorEdge hd ∉ A.edges ∪ A.placedEdges B hd := by
    rw [Finset.mem_union]
    push Not
    exact ⟨A.connectorEdge_not_mem_edges hd,
      A.connectorEdge_not_mem_placedEdges B hB hd⟩
  rw [concatenatedEdges, Finset.card_insert_of_notMem hconn,
    Finset.card_union_of_disjoint (A.edges_disjoint_placedEdges B hB hd),
    placedEdges_card]

/-- The only lattice edge crossing between the two placed vertex sets is the connector. -/
theorem eq_anchors_of_adj_placed
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d)
    {a b : Cubic d} (ha : a ∈ A.vertices) (hb : b ∈ A.placedVertices B hd)
    (hab : (cubicGraph d).Adj a b) :
    a = A.topRight ∧ b = A.rightOfTopRight hd := by
  let i0 : Fin d := ⟨0, hd⟩
  let dir : CubicDirection d := (i0, true)
  have hab0 : a i0 < b i0 := by
    rw [mem_placedVertices_iff] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    exact A.coordinate_zero_lt_placeRight_of_anchored B hB hd ha hy
  obtain ⟨e, he⟩ := (cubicGraph_adj_iff_exists_stepFrom a b).mp hab
  have heq : e = dir := by
    rcases e with ⟨i, sgn⟩
    change (i, sgn) = (i0, true)
    by_cases hi : i = i0
    · subst i
      cases sgn
      · have hcoord := congrFun he i0
        simp [cubicStepFrom, cubicDirectionIncrement] at hcoord
        omega
      · rfl
    · have hcoord := congrFun he i0
      simp [cubicStepFrom, cubicDirectionIncrement,
        Function.update_of_ne (fun h ↦ hi h.symm)] at hcoord
      omega
  have hstep : b = cubicStepFrom a dir := he.trans (congrArg (cubicStepFrom a) heq)
  rw [mem_placedVertices_iff] at hb
  obtain ⟨y, hy, hby⟩ := hb
  have hright_le_b : toLex (A.rightOfTopRight hd) ≤ toLex b := by
    have hlex := (toLex_cubicTranslate_le_iff B.bottomLeft
      (A.rightOfTopRight hd) B.bottomLeft y).mpr (B.bottomLeft_lex_le hy)
    have hsource : cubicTranslate B.bottomLeft (A.rightOfTopRight hd) B.bottomLeft =
        A.rightOfTopRight hd := by
      ext j
      simp [cubicTranslate]
    rw [hsource] at hlex
    change toLex (A.rightOfTopRight hd) ≤ toLex (A.placeRight B hd y) at hlex
    rw [hby] at hlex
    exact hlex
  let u : Cubic d := cubicStepFrom cubicOrigin dir
  have htranslate_step (z : Cubic d) :
      cubicTranslate cubicOrigin u z = cubicStepFrom z dir := by
    ext j
    rcases dir with ⟨i, sgn⟩
    by_cases hji : j = i
    · subst j
      simp [u, cubicTranslate, cubicStepFrom, cubicDirectionIncrement]
    · simp [u, cubicTranslate, cubicStepFrom, cubicDirectionIncrement,
        Function.update_of_ne hji]
  have htop_le_a : toLex A.topRight ≤ toLex a := by
    rw [show A.rightOfTopRight hd = cubicTranslate cubicOrigin u A.topRight by
      rw [htranslate_step]
      rfl,
      show b = cubicTranslate cubicOrigin u a by rw [htranslate_step]; exact hstep]
      at hright_le_b
    exact (toLex_cubicTranslate_le_iff cubicOrigin u A.topRight a).mp hright_le_b
  have haeq : a = A.topRight :=
    toLex_inj.mp (le_antisymm (A.lex_le_topRight ha) htop_le_a)
  refine ⟨haeq, ?_⟩
  rw [hstep, haeq]
  rfl

/-- Translated closed boundary of the right-hand animal. -/
noncomputable def placedBoundary (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hd : 0 < d) : Finset (CubicEdge d) :=
  B.boundary.map
    (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet.toEmbedding

@[simp] theorem mem_placedBoundary_iff (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) (e : CubicEdge d) :
    e ∈ A.placedBoundary B hd ↔
      ∃ f ∈ B.boundary,
        (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet f = e := by
  rw [placedBoundary, Finset.mem_map]
  rfl

@[simp] theorem placedBoundary_card (A : CubicBondAnimal d m)
    (B : CubicBondAnimal d n) (hd : 0 < d) :
    (A.placedBoundary B hd).card = B.boundary.card := by
  rw [placedBoundary, Finset.card_map]

theorem map_cubicIncidentEdges_eq_placed
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n) (hd : 0 < d) :
    (cubicIncidentEdges d B.vertices).map
        (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet.toEmbedding =
      cubicIncidentEdges d (A.placedVertices B hd) := by
  let T := cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y, hyB, hyf⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp hf
    apply mem_cubicIncidentEdges_iff_exists_endpoint.mpr
    refine ⟨T y, Finset.mem_map.mpr ⟨y, hyB, rfl⟩, ?_⟩
    change cubicTranslate B.bottomLeft (A.rightOfTopRight hd) y ∈
      Sym2.map (cubicTranslate B.bottomLeft (A.rightOfTopRight hd)) f.1
    exact Sym2.mem_map.mpr ⟨y, hyf, rfl⟩
  · intro he
    obtain ⟨x, hxP, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp he
    obtain ⟨y, hyB, rfl⟩ := Finset.mem_map.mp hxP
    let f : CubicEdge d := T.mapEdgeSet.symm e
    have hmap : T.mapEdgeSet f = e := T.mapEdgeSet.apply_symm_apply e
    apply Finset.mem_map.mpr
    refine ⟨f, mem_cubicIncidentEdges_iff_exists_endpoint.mpr ⟨y, hyB, ?_⟩, hmap⟩
    have hyMap : T y ∈ (T.mapEdgeSet f : Sym2 (Cubic d)) := hmap.symm ▸ hxe
    rw [SimpleGraph.Iso.mapEdgeSet_apply] at hyMap
    obtain ⟨z, hzf, hzy⟩ := Sym2.mem_map.mp hyMap
    have hzy' : z = y := T.injective hzy
    simpa [hzy'] using hzf

theorem placedBoundary_eq_incident_sdiff
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n) (hd : 0 < d) :
    A.placedBoundary B hd =
      cubicIncidentEdges d (A.placedVertices B hd) \ A.placedEdges B hd := by
  rw [placedBoundary, boundary, Finset.map_sdiff,
    A.map_cubicIncidentEdges_eq_placed B hd]
  rfl

theorem connectorEdge_mem_boundary (A : CubicBondAnimal d m) (hd : 0 < d) :
    A.connectorEdge hd ∈ A.boundary := by
  rw [boundary, Finset.mem_sdiff]
  exact ⟨by
    apply mem_cubicIncidentEdges_of_endpoint A.topRight_mem
    rw [connectorEdge_sym2]
    simp, A.connectorEdge_not_mem_edges hd⟩

noncomputable def leftOfBottomLeft (B : CubicBondAnimal d n) (hd : 0 < d) : CubicEdge d :=
  cubicStepEdge B.bottomLeft ((⟨0, hd⟩ : Fin d), false)

theorem leftOfBottomLeft_mem_boundary
    (B : CubicBondAnimal d n) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    B.leftOfBottomLeft hd ∈ B.boundary := by
  rw [boundary, Finset.mem_sdiff]
  refine ⟨cubicStepEdge_mem_cubicIncidentEdges B.bottomLeft_mem _, ?_⟩
  intro he
  have hleft : cubicStepFrom B.bottomLeft ((⟨0, hd⟩ : Fin d), false) ∈ B.vertices :=
    B.edge_endpoints (B.leftOfBottomLeft hd) he _ (by
      simp [leftOfBottomLeft, cubicStepEdge])
  have hnonneg := B.coordinate_zero_nonneg_of_anchored hB hleft hd
  rw [hB] at hnonneg
  simp [cubicOrigin, cubicStepFrom, cubicDirectionIncrement] at hnonneg

theorem mapEdgeSet_leftOfBottomLeft_eq_connectorEdge
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (cubicTranslationIso B.bottomLeft (A.rightOfTopRight hd)).mapEdgeSet
      (B.leftOfBottomLeft hd) = A.connectorEdge hd := by
  apply Subtype.ext
  rw [SimpleGraph.Iso.mapEdgeSet_apply]
  change Sym2.map (cubicTranslate B.bottomLeft (A.rightOfTopRight hd))
      (B.leftOfBottomLeft hd).1 = (A.connectorEdge hd).1
  rw [show (B.leftOfBottomLeft hd).1 =
      s(B.bottomLeft, cubicStepFrom B.bottomLeft ((⟨0, hd⟩ : Fin d), false)) by
    rfl, connectorEdge_sym2]
  simp only [Sym2.map_pair_eq]
  rw [hB]
  apply Sym2.eq_iff.mpr
  right
  constructor <;> ext j
  · simp [cubicTranslate]
  · by_cases hj : j = (⟨0, hd⟩ : Fin d)
    · subst j
      simp [cubicTranslate, rightOfTopRight, cubicStepFrom, cubicDirectionIncrement]
      omega
    · simp [cubicTranslate, rightOfTopRight, cubicStepFrom, cubicDirectionIncrement,
        Function.update_of_ne hj]

theorem connectorEdge_mem_placedBoundary
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    A.connectorEdge hd ∈ A.placedBoundary B hd := by
  rw [mem_placedBoundary_iff]
  exact ⟨B.leftOfBottomLeft hd, B.leftOfBottomLeft_mem_boundary hB hd,
    A.mapEdgeSet_leftOfBottomLeft_eq_connectorEdge B hB hd⟩

theorem boundary_inter_placedBoundary_eq_singleton
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    A.boundary ∩ A.placedBoundary B hd = {A.connectorEdge hd} := by
  ext e
  rw [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨heA, heB⟩
    have heAI := (Finset.mem_sdiff.mp heA).1
    rw [A.placedBoundary_eq_incident_sdiff B hd] at heB
    have heBI := (Finset.mem_sdiff.mp heB).1
    obtain ⟨a, haA, hae⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heAI
    obtain ⟨b, hbB, hbe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heBI
    have hab_ne : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B hB hd) haA hbB
    have hedge : e.1 = s(a, b) :=
      (Sym2.mem_and_mem_iff hab_ne).mp ⟨hae, hbe⟩
    have hab : (cubicGraph d).Adj a b := by
      rw [← SimpleGraph.mem_edgeSet]
      exact hedge ▸ e.2
    obtain ⟨haeq, hbeq⟩ := A.eq_anchors_of_adj_placed B hB hd haA hbB hab
    apply Subtype.ext
    rw [hedge, haeq, hbeq, connectorEdge_sym2]
  · rintro rfl
    exact ⟨A.connectorEdge_mem_boundary hd,
      A.connectorEdge_mem_placedBoundary B hB hd⟩

theorem cubicIncidentEdges_union (V W : Finset (Cubic d)) :
    cubicIncidentEdges d (V ∪ W) =
      cubicIncidentEdges d V ∪ cubicIncidentEdges d W := by
  ext e
  simp only [mem_cubicIncidentEdges_iff_exists_endpoint, Finset.mem_union]
  aesop

theorem edges_disjoint_incident_placedVertices
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    Disjoint A.edges (cubicIncidentEdges d (A.placedVertices B hd)) := by
  rw [Finset.disjoint_left]
  intro e heA heI
  obtain ⟨x, hxB, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heI
  have hxA := A.edge_endpoints e heA x hxe
  exact Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B hB hd) hxA hxB

theorem placedEdges_disjoint_incident_vertices
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    Disjoint (A.placedEdges B hd) (cubicIncidentEdges d A.vertices) := by
  rw [Finset.disjoint_left]
  intro e heB heI
  obtain ⟨x, hxA, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp heI
  have hxB := A.endpoint_mem_placedVertices_of_mem_placedEdges B hd heB hxe
  exact Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B hB hd) hxA hxB

theorem concat_boundary_eq_union_erase_connector
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concat B hA hB hd).boundary =
      (A.boundary ∪ A.placedBoundary B hd).erase (A.connectorEdge hd) := by
  ext e
  change e ∈ cubicIncidentEdges d (A.concatenatedVertices B hd) \
      A.concatenatedEdges B hd ↔ _
  rw [concatenatedVertices, cubicIncidentEdges_union, concatenatedEdges,
    boundary, A.placedBoundary_eq_incident_sdiff B hd]
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  have hAIB := Finset.disjoint_left.mp (A.edges_disjoint_incident_placedVertices B hB hd)
  have hBIA := Finset.disjoint_left.mp (A.placedEdges_disjoint_incident_vertices B hB hd)
  constructor
  · rintro ⟨heI | heI, heOcc⟩
    · refine ⟨fun heC ↦ heOcc (Or.inl heC),
        Or.inl ⟨heI, fun heA ↦ heOcc (Or.inr (Or.inl heA))⟩⟩
    · refine ⟨fun heC ↦ heOcc (Or.inl heC),
        Or.inr ⟨heI, fun heB ↦ heOcc (Or.inr (Or.inr heB))⟩⟩
  · rintro ⟨heC, ⟨heI, heA⟩ | ⟨heI, heB⟩⟩
    · refine ⟨Or.inl heI, ?_⟩
      rintro (rfl | heA' | heB')
      · exact heC rfl
      · exact heA heA'
      · exact hBIA heB' heI
    · refine ⟨Or.inr heI, ?_⟩
      rintro (rfl | heA' | heB')
      · exact heC rfl
      · exact hAIB heA' heI
      · exact heB heB'

theorem concat_boundary_card
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concat B hA hB hd).boundary.card =
      A.boundary.card + B.boundary.card - 2 := by
  rw [A.concat_boundary_eq_union_erase_connector B hA hB hd,
    Finset.card_erase_of_mem (by
      rw [Finset.mem_union]
      exact Or.inl (A.connectorEdge_mem_boundary hd))]
  have hcard := Finset.card_union_add_card_inter
    A.boundary (A.placedBoundary B hd)
  rw [A.boundary_inter_placedBoundary_eq_singleton B hB hd,
    Finset.card_singleton, A.placedBoundary_card B hd] at hcard
  omega

/-- The root-preserving concatenation has the same boundary correction as the anchored
concatenation: the joining edge removes one boundary edge from each factor. -/
theorem rootedConcat_boundary_eq_union_erase_connector
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).boundary =
      (A.boundary ∪ A.placedBoundary B hd).erase (A.connectorEdge hd) := by
  ext e
  change e ∈ cubicIncidentEdges d (A.concatenatedVertices B hd) \
      A.concatenatedEdges B hd ↔ _
  rw [concatenatedVertices, cubicIncidentEdges_union, concatenatedEdges,
    boundary, A.placedBoundary_eq_incident_sdiff B hd]
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  have hAIB := Finset.disjoint_left.mp (A.edges_disjoint_incident_placedVertices B hB hd)
  have hBIA := Finset.disjoint_left.mp (A.placedEdges_disjoint_incident_vertices B hB hd)
  constructor
  · rintro ⟨heI | heI, heOcc⟩
    · refine ⟨fun heC ↦ heOcc (Or.inl heC),
        Or.inl ⟨heI, fun heA ↦ heOcc (Or.inr (Or.inl heA))⟩⟩
    · refine ⟨fun heC ↦ heOcc (Or.inl heC),
        Or.inr ⟨heI, fun heB ↦ heOcc (Or.inr (Or.inr heB))⟩⟩
  · rintro ⟨heC, ⟨heI, heA⟩ | ⟨heI, heB⟩⟩
    · refine ⟨Or.inl heI, ?_⟩
      rintro (rfl | heA' | heB')
      · exact heC rfl
      · exact heA heA'
      · exact hBIA heB' heI
    · refine ⟨Or.inr heI, ?_⟩
      rintro (rfl | heA' | heB')
      · exact heC rfl
      · exact hAIB heA' heI
      · exact heB heB'

theorem rootedConcat_boundary_card
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).boundary.card =
      A.boundary.card + B.boundary.card - 2 := by
  rw [A.rootedConcat_boundary_eq_union_erase_connector B hB hd,
    Finset.card_erase_of_mem (by
      rw [Finset.mem_union]
      exact Or.inl (A.connectorEdge_mem_boundary hd))]
  have hcard := Finset.card_union_add_card_inter
    A.boundary (A.placedBoundary B hd)
  rw [A.boundary_inter_placedBoundary_eq_singleton B hB hd,
    Finset.card_singleton, A.placedBoundary_card B hd] at hcard
  omega

theorem toLex_lt_of_mem_vertices_of_mem_placedVertices
    (A : CubicBondAnimal d m) (B : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ A.placedVertices B hd) :
    toLex x < toLex y := by
  letI : NeZero d := ⟨hd.ne'⟩
  rw [mem_placedVertices_iff] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨(⟨0, hd⟩ : Fin d), ?_,
    A.coordinate_zero_lt_placeRight_of_anchored B hB hd hx hz⟩
  intro j hj
  exact (Fin.not_lt_zero j hj).elim

/-- The left `m` vertices are intrinsically recoverable from a concatenated `(m+n)`-animal:
all of them precede every translated right vertex in lexicographic order. -/
theorem vertices_eq_of_concatenatedVertices_eq
    (A A' : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hconcat : A.concatenatedVertices B hd = A'.concatenatedVertices B' hd) :
    A.vertices = A'.vertices := by
  by_contra hne
  have hnsub : ¬A.vertices ⊆ A'.vertices := by
    intro hsub
    apply hne
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [A.vertices_card, A'.vertices_card])
  have hnsub' : ¬A'.vertices ⊆ A.vertices := by
    intro hsub
    apply hne
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [A.vertices_card, A'.vertices_card])
  obtain ⟨x, hxA, hxA'⟩ := Finset.not_subset.mp hnsub
  obtain ⟨y, hyA', hyA⟩ := Finset.not_subset.mp hnsub'
  have hxP' : x ∈ A'.placedVertices B' hd := by
    have hxU : x ∈ A'.concatenatedVertices B' hd := by
      rw [← hconcat, concatenatedVertices, Finset.mem_union]
      exact Or.inl hxA
    rw [concatenatedVertices, Finset.mem_union] at hxU
    exact hxU.resolve_left hxA'
  have hyP : y ∈ A.placedVertices B hd := by
    have hyU : y ∈ A.concatenatedVertices B hd := by
      rw [hconcat, concatenatedVertices, Finset.mem_union]
      exact Or.inl hyA'
    rw [concatenatedVertices, Finset.mem_union] at hyU
    exact hyU.resolve_left hyA
  have hxy := A.toLex_lt_of_mem_vertices_of_mem_placedVertices B hB hd hxA hyP
  have hyx := A'.toLex_lt_of_mem_vertices_of_mem_placedVertices B' hB' hd hyA' hxP'
  exact lt_asymm hxy hyx

theorem edges_subset_of_concatenatedEdges_eq_of_vertices_eq
    (A A' : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hV : A.vertices = A'.vertices)
    (hconcat : A.concatenatedEdges B hd = A'.concatenatedEdges B' hd) :
    A.edges ⊆ A'.edges := by
  intro e heA
  have heC : e ∈ A'.concatenatedEdges B' hd := by
    rw [← hconcat, concatenatedEdges, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl heA)
  rw [concatenatedEdges, Finset.mem_insert, Finset.mem_union] at heC
  rcases heC with heConnector | heA' | hePlaced
  · rw [heConnector] at heA
    have hrightA : A'.rightOfTopRight hd ∈ A.vertices :=
      A.edge_endpoints (A'.connectorEdge hd) heA _ (by
        rw [connectorEdge_sym2]
        simp)
    have hrightA' : A'.rightOfTopRight hd ∈ A'.vertices := by simpa [hV] using hrightA
    have hle := A'.coordinate_zero_le_topRight hrightA' hd
    rw [rightOfTopRight_coordinate_zero] at hle
    omega
  · exact heA'
  · let x := e.1.out.1
    have hxA : x ∈ A.vertices :=
      A.edge_endpoints e heA x (Sym2.out_fst_mem e.1)
    have hxA' : x ∈ A'.vertices := by simpa [hV] using hxA
    have hxP : x ∈ A'.placedVertices B' hd :=
      A'.endpoint_mem_placedVertices_of_mem_placedEdges B' hd hePlaced
        (Sym2.out_fst_mem e.1)
    exact (Finset.disjoint_left.mp
      (A'.vertices_disjoint_placedVertices B' hB' hd) hxA' hxP).elim

theorem edges_eq_of_concatenatedEdges_eq_of_vertices_eq
    (A A' : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hV : A.vertices = A'.vertices)
    (hconcat : A.concatenatedEdges B hd = A'.concatenatedEdges B' hd) :
    A.edges = A'.edges := by
  apply Finset.Subset.antisymm
  · exact A.edges_subset_of_concatenatedEdges_eq_of_vertices_eq A' B B' hB' hd hV hconcat
  · exact A'.edges_subset_of_concatenatedEdges_eq_of_vertices_eq A B' B hB hd hV.symm hconcat.symm

theorem ext_data (A A' : CubicBondAnimal d m)
    (hV : A.vertices = A'.vertices) (hE : A.edges = A'.edges) : A = A' := by
  cases A
  cases A'
  simp_all

theorem placedVertices_eq_of_concatenatedVertices_eq
    (A : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hconcat : A.concatenatedVertices B hd = A.concatenatedVertices B' hd) :
    A.placedVertices B hd = A.placedVertices B' hd := by
  ext x
  by_cases hxA : x ∈ A.vertices
  · have hxB : x ∉ A.placedVertices B hd := fun hx ↦
      Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B hB hd) hxA hx
    have hxB' : x ∉ A.placedVertices B' hd := fun hx ↦
      Finset.disjoint_left.mp (A.vertices_disjoint_placedVertices B' hB' hd) hxA hx
    simp [hxB, hxB']
  · have hx := Finset.ext_iff.mp hconcat x
    simpa [concatenatedVertices, hxA] using hx

theorem vertices_eq_of_placedVertices_eq
    (A : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hplaced : A.placedVertices B hd = A.placedVertices B' hd) :
    B.vertices = B'.vertices := by
  rw [placedVertices, placedVertices, hB, hB'] at hplaced
  exact Finset.map_injective
    (cubicTranslationEquiv cubicOrigin (A.rightOfTopRight hd)).toEmbedding hplaced

theorem placedEdges_eq_of_concatenatedEdges_eq
    (A : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hconcat : A.concatenatedEdges B hd = A.concatenatedEdges B' hd) :
    A.placedEdges B hd = A.placedEdges B' hd := by
  ext e
  by_cases heC : e = A.connectorEdge hd
  · subst e
    simp only [A.connectorEdge_not_mem_placedEdges B hB hd,
      A.connectorEdge_not_mem_placedEdges B' hB' hd]
  · by_cases heA : e ∈ A.edges
    · have heB : e ∉ A.placedEdges B hd := fun he ↦
        Finset.disjoint_left.mp (A.edges_disjoint_placedEdges B hB hd) heA he
      have heB' : e ∉ A.placedEdges B' hd := fun he ↦
        Finset.disjoint_left.mp (A.edges_disjoint_placedEdges B' hB' hd) heA he
      simp [heB, heB']
    · have he := Finset.ext_iff.mp hconcat e
      simpa [concatenatedEdges, heC, heA] using he

theorem edges_eq_of_placedEdges_eq
    (A : CubicBondAnimal d m) (B B' : CubicBondAnimal d n)
    (hB : B.IsBottomLeftAnchored) (hB' : B'.IsBottomLeftAnchored) (hd : 0 < d)
    (hplaced : A.placedEdges B hd = A.placedEdges B' hd) :
    B.edges = B'.edges := by
  rw [placedEdges, placedEdges, hB, hB'] at hplaced
  exact Finset.map_injective
    (cubicTranslationIso cubicOrigin (A.rightOfTopRight hd)).mapEdgeSet.toEmbedding hplaced

/-- The canonical injective concatenation on anchored animals of prescribed sizes. -/
noncomputable def anchoredConcat (hd : 0 < d) :
    Anchored d m × Anchored d n → Anchored d (m + n) := fun AB ↦
  ⟨AB.1.1.concat AB.2.1 AB.1.2 AB.2.2 hd,
    AB.1.1.concat_isBottomLeftAnchored AB.2.1 AB.1.2 AB.2.2 hd⟩

theorem anchoredConcat_injective (hd : 0 < d) :
    Function.Injective (anchoredConcat (m := m) (n := n) hd) := by
  rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ ⟨⟨A', hA'⟩, ⟨B', hB'⟩⟩ hconcat
  have hAnimal : A.concat B hA hB hd = A'.concat B' hA' hB' hd :=
    congrArg Subtype.val hconcat
  have hCV : A.concatenatedVertices B hd = A'.concatenatedVertices B' hd :=
    congrArg CubicBondAnimal.vertices hAnimal
  have hCE : A.concatenatedEdges B hd = A'.concatenatedEdges B' hd :=
    congrArg CubicBondAnimal.edges hAnimal
  have hAV := A.vertices_eq_of_concatenatedVertices_eq A' B B' hB hB' hd hCV
  have hAE := A.edges_eq_of_concatenatedEdges_eq_of_vertices_eq A' B B' hB hB' hd hAV hCE
  have hAA' := ext_data A A' hAV hAE
  subst A'
  have hPV := A.placedVertices_eq_of_concatenatedVertices_eq B B' hB hB' hd hCV
  have hBV := A.vertices_eq_of_placedVertices_eq B B' hB hB' hd hPV
  have hPE := A.placedEdges_eq_of_concatenatedEdges_eq B B' hB hB' hd hCE
  have hBE := A.edges_eq_of_placedEdges_eq B B' hB hB' hd hPE
  have hBB' := ext_data B B' hBV hBE
  subst B'
  rfl

/-- For fixed vertex counts, root-preserving concatenation is injective in both the rooted
left animal and the anchored right animal. -/
theorem rootedConcat_injective (hd : 0 < d) :
    Function.Injective
      (fun AB : CubicBondAnimal d m × Anchored d n ↦
        AB.1.rootedConcat AB.2.1 AB.2.2 hd) := by
  rintro ⟨A, ⟨B, hB⟩⟩ ⟨A', ⟨B', hB'⟩⟩ hconcat
  have hCV : A.concatenatedVertices B hd = A'.concatenatedVertices B' hd :=
    congrArg CubicBondAnimal.vertices hconcat
  have hCE : A.concatenatedEdges B hd = A'.concatenatedEdges B' hd :=
    congrArg CubicBondAnimal.edges hconcat
  have hAV := A.vertices_eq_of_concatenatedVertices_eq A' B B' hB hB' hd hCV
  have hAE := A.edges_eq_of_concatenatedEdges_eq_of_vertices_eq
    A' B B' hB hB' hd hAV hCE
  have hAA' := ext_data A A' hAV hAE
  subst A'
  have hPV := A.placedVertices_eq_of_concatenatedVertices_eq B B' hB hB' hd hCV
  have hBV := A.vertices_eq_of_placedVertices_eq B B' hB hB' hd hPV
  have hPE := A.placedEdges_eq_of_concatenatedEdges_eq B B' hB hB' hd hCE
  have hBE := A.edges_eq_of_placedEdges_eq B B' hB hB' hd hPE
  have hBB' := ext_data B B' hBV hBE
  subst B'
  rfl

end CubicBondAnimal

#print axioms CubicBondAnimal.bottomLeft_mem
#print axioms CubicBondAnimal.coordinate_zero_nonneg_of_anchored
#print axioms CubicBondAnimal.concat_boundary_card
#print axioms CubicBondAnimal.anchoredConcat_injective
#print axioms CubicBondAnimal.rootedConcat_injective

end Percolation
