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

end CubicBondAnimal

#print axioms CubicBondAnimal.bottomLeft_mem
#print axioms CubicBondAnimal.coordinate_zero_nonneg_of_anchored

end Percolation
