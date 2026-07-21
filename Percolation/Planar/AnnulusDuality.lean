import Percolation.Planar.BondCrossingDuality
import Percolation.Planar.RSWEvents
import Percolation.Critical.DynamicRootConnectivity
import Percolation.Critical.BoxSurfaceConnectivity

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Sym2 unitInterval

def squareDualFaceOfPrimalVertex (x : SquareVertex) : SquareVertex :=
  squareVertex (x 0 - 1) (x 1 - 1)

private theorem vertical_pos_edge_eq_shared_iff (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨1, by decide⟩, true)) =
        s(cubicStepFrom f (⟨0, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
            (⟨1, by decide⟩, true)) ↔
      u = cubicStepFrom f (⟨0, by decide⟩, true) := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · exact h.1
    · have h0 := congrFun h.1 1
      have h1 := congrFun h.2 1
      simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
      omega
  · intro h
    subst u
    exact Or.inl ⟨rfl, rfl⟩

private theorem vertical_neg_edge_eq_shared_iff (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨1, by decide⟩, false)) =
        s(cubicStepFrom f (⟨0, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
            (⟨1, by decide⟩, true)) ↔
      u = cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
        (⟨1, by decide⟩, true) := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · have h0 := congrFun h.1 1
      have h1 := congrFun h.2 1
      simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
      omega
    · exact h.1
  · intro h
    subst u
    exact Or.inr ⟨rfl, by
      ext j
      fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement]⟩

private theorem horizontal_pos_edge_ne_shared (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨0, by decide⟩, true)) ≠
      s(cubicStepFrom f (⟨0, by decide⟩, true),
        cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
          (⟨1, by decide⟩, true)) := by
  intro hEq
  rcases Sym2.eq_iff.mp hEq with h | h
  · have h0 := congrFun h.1 0
    have h1 := congrFun h.2 0
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega
  · have h0 := congrFun h.1 1
    have h1 := congrFun h.2 1
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega

private theorem horizontal_neg_edge_ne_shared (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨0, by decide⟩, false)) ≠
      s(cubicStepFrom f (⟨0, by decide⟩, true),
        cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
          (⟨1, by decide⟩, true)) := by
  intro hEq
  rcases Sym2.eq_iff.mp hEq with h | h
  · have h0 := congrFun h.1 1
    have h1 := congrFun h.2 1
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega
  · have h0 := congrFun h.1 0
    have h1 := congrFun h.2 0
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega

theorem walk_horizontalRayCount_stepRight_eq_add_shared
    {o t : SquareVertex} (w : squareGraph.Walk o t) (f : SquareVertex) :
    w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) =
      w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool
        (cubicStepFrom f (⟨0, by decide⟩, true))) +
      w.edges.countP (fun e ↦ decide
        (e = s(cubicStepFrom f (⟨0, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
            (⟨1, by decide⟩, true)))) := by
  have hlocal : ∀ {u v : SquareVertex}, squareGraph.Adj u v →
      (if squareEdgeCrossesFaceHorizontalRayBool f s(u, v) = true then 1 else 0) =
        (if squareEdgeCrossesFaceHorizontalRayBool
          (cubicStepFrom f (⟨0, by decide⟩, true)) s(u, v) = true then 1 else 0) +
        (if decide (s(u, v) =
          s(cubicStepFrom f (⟨0, by decide⟩, true),
            cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
              (⟨1, by decide⟩, true))) = true then 1 else 0) := by
    intro u v huv
    rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, b⟩, rfl⟩
    fin_cases i <;> cases b
    · have hne := horizontal_neg_edge_ne_shared u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨0, by decide⟩, false)) =
            s(cubicStepFrom f (⟨0, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
                (⟨1, by decide⟩, true))) = false :=
        decide_eq_false_iff_not.mpr hne
      rw [hdec]
      simp [
        squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
        cubicDirectionIncrement]
    · have hne := horizontal_pos_edge_ne_shared u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨0, by decide⟩, true)) =
            s(cubicStepFrom f (⟨0, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
                (⟨1, by decide⟩, true))) = false :=
        decide_eq_false_iff_not.mpr hne
      rw [hdec]
      simp [
        squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
        cubicDirectionIncrement]
    · have hiff := vertical_neg_edge_eq_shared_iff u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨1, by decide⟩, false)) =
            s(cubicStepFrom f (⟨0, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
                (⟨1, by decide⟩, true))) =
          decide (u = cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
            (⟨1, by decide⟩, true)) := by
        congr 1
        exact propext hiff
      rw [hdec]
      by_cases hu : u = cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
          (⟨1, by decide⟩, true)
      · subst u
        simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · have hcoords : ¬(u 0 = f 0 + 1 ∧ u 1 = f 1 + 1) := by
          rintro ⟨h0, h1⟩
          apply hu
          ext j
          fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement, h0, h1]
        have hdecHu : decide
            (u = cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
              (⟨1, by decide⟩, true)) = false :=
          decide_eq_false_iff_not.mpr hu
        rw [hdecHu]
        simp only [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
        by_cases h0 : u 0 = f 0 + 1
        · by_cases h1 : u 1 + -1 = f 1
          · exfalso
            apply hcoords
            exact ⟨h0, by omega⟩
          · simp [h0, h1]
        · by_cases h1 : u 1 + -1 = f 1 <;>
            by_cases hl : f 0 < u 0 <;> by_cases hr : f 0 + 1 < u 0 <;>
              simp [h0, h1, hl, hr] <;> omega
    · have hiff := vertical_pos_edge_eq_shared_iff u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨1, by decide⟩, true)) =
            s(cubicStepFrom f (⟨0, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨0, by decide⟩, true))
                (⟨1, by decide⟩, true))) =
          decide (u = cubicStepFrom f (⟨0, by decide⟩, true)) := by
        congr 1
        exact propext hiff
      rw [hdec]
      by_cases hu : u = cubicStepFrom f (⟨0, by decide⟩, true)
      · subst u
        simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
      · have hcoords : ¬(u 0 = f 0 + 1 ∧ u 1 = f 1) := by
          rintro ⟨h0, h1⟩
          apply hu
          ext j
          fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement, h0, h1]
        have hdecHu : decide (u = cubicStepFrom f (⟨0, by decide⟩, true)) = false :=
          decide_eq_false_iff_not.mpr hu
        rw [hdecHu]
        simp only [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement]
        by_cases h0 : u 0 = f 0 + 1
        · by_cases h1 : u 1 = f 1
          · exact (hcoords ⟨h0, h1⟩).elim
          · simp [h0, h1]
        · by_cases h1 : u 1 = f 1 <;>
            by_cases hl : f 0 < u 0 <;> by_cases hr : f 0 + 1 < u 0 <;>
              simp [h0, h1, hl, hr] <;> omega
  induction w with
  | nil => simp
  | @cons u v z huv w ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.countP_cons]
      rw [ih]
      have h := hlocal huv
      omega

private theorem horizontal_pos_edge_eq_upShared_iff (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨0, by decide⟩, true)) =
        s(cubicStepFrom f (⟨1, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
            (⟨0, by decide⟩, true)) ↔
      u = cubicStepFrom f (⟨1, by decide⟩, true) := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · exact h.1
    · have h0 := congrFun h.1 0
      have h1 := congrFun h.2 0
      simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
      omega
  · intro h
    subst u
    exact Or.inl ⟨rfl, rfl⟩

private theorem horizontal_neg_edge_eq_upShared_iff (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨0, by decide⟩, false)) =
        s(cubicStepFrom f (⟨1, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
            (⟨0, by decide⟩, true)) ↔
      u = cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
        (⟨0, by decide⟩, true) := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · have h0 := congrFun h.1 0
      have h1 := congrFun h.2 0
      simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
      omega
    · exact h.1
  · intro h
    subst u
    exact Or.inr ⟨rfl, by
      ext j
      fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement]⟩

private theorem vertical_pos_edge_ne_upShared (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨1, by decide⟩, true)) ≠
      s(cubicStepFrom f (⟨1, by decide⟩, true),
        cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
          (⟨0, by decide⟩, true)) := by
  intro hEq
  rcases Sym2.eq_iff.mp hEq with h | h
  · have h0 := congrFun h.1 0
    have h1 := congrFun h.2 0
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega
  · have h0 := congrFun h.1 1
    have h1 := congrFun h.2 1
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega

private theorem vertical_neg_edge_ne_upShared (u f : SquareVertex) :
    s(u, cubicStepFrom u (⟨1, by decide⟩, false)) ≠
      s(cubicStepFrom f (⟨1, by decide⟩, true),
        cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
          (⟨0, by decide⟩, true)) := by
  intro hEq
  rcases Sym2.eq_iff.mp hEq with h | h
  · have h0 := congrFun h.1 1
    have h1 := congrFun h.2 1
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega
  · have h0 := congrFun h.1 0
    have h1 := congrFun h.2 0
    simp [cubicStepFrom, cubicDirectionIncrement] at h0 h1
    omega

theorem walk_verticalRayCount_stepUp_eq_add_shared
    {o t : SquareVertex} (w : squareGraph.Walk o t) (f : SquareVertex) :
    w.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) =
      w.edges.countP (squareEdgeCrossesFaceVerticalRayBool
        (cubicStepFrom f (⟨1, by decide⟩, true))) +
      w.edges.countP (fun e ↦ decide
        (e = s(cubicStepFrom f (⟨1, by decide⟩, true),
          cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
            (⟨0, by decide⟩, true)))) := by
  have hlocal : ∀ {u v : SquareVertex}, squareGraph.Adj u v →
      (if squareEdgeCrossesFaceVerticalRayBool f s(u, v) = true then 1 else 0) =
        (if squareEdgeCrossesFaceVerticalRayBool
          (cubicStepFrom f (⟨1, by decide⟩, true)) s(u, v) = true then 1 else 0) +
        (if decide (s(u, v) =
          s(cubicStepFrom f (⟨1, by decide⟩, true),
            cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
              (⟨0, by decide⟩, true))) = true then 1 else 0) := by
    intro u v huv
    rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, b⟩, rfl⟩
    fin_cases i <;> cases b
    · have hiff := horizontal_neg_edge_eq_upShared_iff u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨0, by decide⟩, false)) =
            s(cubicStepFrom f (⟨1, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
                (⟨0, by decide⟩, true))) =
          decide (u = cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
            (⟨0, by decide⟩, true)) := by
        congr 1
        exact propext hiff
      rw [hdec]
      by_cases hu : u = cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
          (⟨0, by decide⟩, true)
      · subst u
        simp [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
      · have hcoords : ¬(u 0 = f 0 + 1 ∧ u 1 = f 1 + 1) := by
          rintro ⟨h0, h1⟩
          apply hu
          ext j
          fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement, h0, h1]
        have hdecHu : decide
            (u = cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
              (⟨0, by decide⟩, true)) = false :=
          decide_eq_false_iff_not.mpr hu
        rw [hdecHu]
        simp only [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
        by_cases h1 : u 1 = f 1 + 1
        · by_cases h0 : u 0 + -1 = f 0
          · exfalso
            apply hcoords
            exact ⟨by omega, h1⟩
          · simp [h0, h1]
        · by_cases h0 : u 0 + -1 = f 0 <;>
            by_cases hl : f 1 < u 1 <;> by_cases hr : f 1 + 1 < u 1 <;>
              simp [h0, h1, hl, hr] <;> omega
    · have hiff := horizontal_pos_edge_eq_upShared_iff u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨0, by decide⟩, true)) =
            s(cubicStepFrom f (⟨1, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
                (⟨0, by decide⟩, true))) =
          decide (u = cubicStepFrom f (⟨1, by decide⟩, true)) := by
        congr 1
        exact propext hiff
      rw [hdec]
      by_cases hu : u = cubicStepFrom f (⟨1, by decide⟩, true)
      · subst u
        simp [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
      · have hcoords : ¬(u 0 = f 0 ∧ u 1 = f 1 + 1) := by
          rintro ⟨h0, h1⟩
          apply hu
          ext j
          fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement, h0, h1]
        have hdecHu : decide (u = cubicStepFrom f (⟨1, by decide⟩, true)) = false :=
          decide_eq_false_iff_not.mpr hu
        rw [hdecHu]
        simp only [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
        by_cases h1 : u 1 = f 1 + 1
        · by_cases h0 : u 0 = f 0
          · exact (hcoords ⟨h0, h1⟩).elim
          · simp [h0, h1]
        · by_cases h0 : u 0 = f 0 <;>
            by_cases hl : f 1 < u 1 <;> by_cases hr : f 1 + 1 < u 1 <;>
              simp [h0, h1, hl, hr] <;> omega
    · have hne := vertical_neg_edge_ne_upShared u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨1, by decide⟩, false)) =
            s(cubicStepFrom f (⟨1, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
                (⟨0, by decide⟩, true))) = false :=
        decide_eq_false_iff_not.mpr hne
      rw [hdec]
      simp [squareEdgeCrossesFaceVerticalRayBool,
        squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
    · have hne := vertical_pos_edge_ne_upShared u f
      have hdec : decide
          (s(u, cubicStepFrom u (⟨1, by decide⟩, true)) =
            s(cubicStepFrom f (⟨1, by decide⟩, true),
              cubicStepFrom (cubicStepFrom f (⟨1, by decide⟩, true))
                (⟨0, by decide⟩, true))) = false :=
        decide_eq_false_iff_not.mpr hne
      rw [hdec]
      simp [squareEdgeCrossesFaceVerticalRayBool,
        squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement]
  induction w with
  | nil => simp
  | @cons u v z huv w ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.countP_cons]
      rw [ih]
      have h := hlocal huv
      omega

@[simp] theorem squareEdgeDualCrossingEquiv_toEdge (e : SquarePositiveEdge) :
    squareEdgeDualCrossingEquiv e.toEdge =
      (primalToDualCrossingPositiveEdge e).toEdge := by
  unfold squareEdgeDualCrossingEquiv
  simp only [Equiv.trans_apply, SquarePositiveEdge.edgeEquiv_apply,
    squarePositiveEdgeDualCrossingEquiv]
  have hsymm : SquarePositiveEdge.edgeEquiv.symm e.toEdge = e := by
    change SquarePositiveEdge.edgeEquiv.symm (squarePositiveEdgeEmbedding e) = e
    exact SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding e
  rw [hsymm]
  rfl

theorem squareEdgeDualCrossingEquiv_posHorizontal (u : SquareVertex) :
    squareEdgeDualCrossingEquiv
        (⟨s(u, cubicStepFrom u (⟨0, by decide⟩, true)), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom u (⟨0, by decide⟩, true)⟩ : SquareEdge) =
      (⟨s(cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨0, by decide⟩, true),
          cubicStepFrom
            (cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨0, by decide⟩, true))
            (⟨1, by decide⟩, true)), by
        rw [SimpleGraph.mem_edgeSet]
        exact cubicGraph_adj_stepFrom _ (⟨1, by decide⟩, true)⟩ : DualSquareEdge) := by
  change squareEdgeDualCrossingEquiv
      (SquarePositiveEdge.toEdge ⟨u, (0 : Fin 2)⟩) = _
  rw [squareEdgeDualCrossingEquiv_toEdge]
  apply Subtype.ext
  simp [SquarePositiveEdge.toEdge, primalToDualCrossingPositiveEdge,
    squareDualFaceOfPrimalVertex, cubicStepFrom, cubicDirectionIncrement, squarePerp]
  left
  constructor <;> ext j <;> fin_cases j <;> simp [squareVertex] <;> omega

theorem squareEdgeDualCrossingEquiv_posVertical (u : SquareVertex) :
    squareEdgeDualCrossingEquiv
        (⟨s(u, cubicStepFrom u (⟨1, by decide⟩, true)), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom u (⟨1, by decide⟩, true)⟩ : SquareEdge) =
      (⟨s(cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨1, by decide⟩, true),
          cubicStepFrom
            (cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨1, by decide⟩, true))
            (⟨0, by decide⟩, true)), by
        rw [SimpleGraph.mem_edgeSet]
        exact cubicGraph_adj_stepFrom _ (⟨0, by decide⟩, true)⟩ : DualSquareEdge) := by
  change squareEdgeDualCrossingEquiv
      (SquarePositiveEdge.toEdge ⟨u, (1 : Fin 2)⟩) = _
  rw [squareEdgeDualCrossingEquiv_toEdge]
  apply Subtype.ext
  simp [SquarePositiveEdge.toEdge, primalToDualCrossingPositiveEdge,
    squareDualFaceOfPrimalVertex, cubicStepFrom, cubicDirectionIncrement, squarePerp]
  left
  constructor <;> ext j <;> fin_cases j <;> simp [squareVertex] <;> omega

private theorem squareDualFace_stepFrom_right (u : SquareVertex) :
    squareDualFaceOfPrimalVertex (cubicStepFrom u (⟨0, by decide⟩, true)) =
      cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨0, by decide⟩, true) := by
  ext j
  fin_cases j <;>
    simp [squareDualFaceOfPrimalVertex, squareVertex, cubicStepFrom,
      cubicDirectionIncrement]

private theorem squareDualFace_stepFrom_left (u : SquareVertex) :
    squareDualFaceOfPrimalVertex u =
      cubicStepFrom
        (squareDualFaceOfPrimalVertex (cubicStepFrom u (⟨0, by decide⟩, false)))
        (⟨0, by decide⟩, true) := by
  ext j
  fin_cases j <;>
    simp [squareDualFaceOfPrimalVertex, squareVertex, cubicStepFrom,
      cubicDirectionIncrement] <;> omega

private theorem squareDualFace_stepFrom_up (u : SquareVertex) :
    squareDualFaceOfPrimalVertex (cubicStepFrom u (⟨1, by decide⟩, true)) =
      cubicStepFrom (squareDualFaceOfPrimalVertex u) (⟨1, by decide⟩, true) := by
  ext j
  fin_cases j <;>
    simp [squareDualFaceOfPrimalVertex, squareVertex, cubicStepFrom,
      cubicDirectionIncrement]

private theorem squareDualFace_stepFrom_down (u : SquareVertex) :
    squareDualFaceOfPrimalVertex u =
      cubicStepFrom
        (squareDualFaceOfPrimalVertex (cubicStepFrom u (⟨1, by decide⟩, false)))
        (⟨1, by decide⟩, true) := by
  ext j
  fin_cases j <;>
    simp [squareDualFaceOfPrimalVertex, squareVertex, cubicStepFrom,
      cubicDirectionIncrement] <;> omega

private theorem countP_decide_eq_zero_of_not_mem
    {α : Type*} [DecidableEq α] {a : α} {l : List α} (ha : a ∉ l) :
    l.countP (fun e ↦ decide (e = a)) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  simp only [decide_eq_true_eq, not_true_eq_false]
  intro hea
  exact ha (hea ▸ he)

theorem closedSquareWalkFaceParity_eq_of_dualCrossing_not_mem
    {o u v : SquareVertex} (c : squareGraph.Walk o o)
    (huv : squareGraph.Adj u v)
    (hnot : ((squareEdgeDualCrossingEquiv
      (⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩ : SquareEdge) :
        DualSquareEdge) : Sym2 DualSquareVertex) ∉ c.edges) :
    closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex u) =
      closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex v) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨⟨i, b⟩, rfl⟩
  fin_cases i <;> cases b
  · let v := cubicStepFrom u (⟨0, by decide⟩, false)
    have hedge :
        (⟨s(u, v), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom u (⟨0, by decide⟩, false)⟩ : SquareEdge) =
          (SquarePositiveEdge.toEdge ⟨v, (0 : Fin 2)⟩) := by
      apply Subtype.ext
      change s(u, v) = s(v, cubicStepFrom v (⟨0, by decide⟩, true))
      dsimp [v]
      rw [cubicStepFrom_neg_pos]
      exact Sym2.eq_swap
    rw [hedge, squareEdgeDualCrossingEquiv_toEdge] at hnot
    have hdual : (primalToDualCrossingPositiveEdge
        (⟨v, (0 : Fin 2)⟩ : SquarePositiveEdge)).toEdge =
        (⟨s(cubicStepFrom (squareDualFaceOfPrimalVertex v) (⟨0, by decide⟩, true),
            cubicStepFrom
              (cubicStepFrom (squareDualFaceOfPrimalVertex v) (⟨0, by decide⟩, true))
              (⟨1, by decide⟩, true)), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom _ (⟨1, by decide⟩, true)⟩ : DualSquareEdge) := by
      rw [← squareEdgeDualCrossingEquiv_toEdge]
      simpa only [SquarePositiveEdge.toEdge] using
        squareEdgeDualCrossingEquiv_posHorizontal v
    rw [hdual] at hnot
    have hcount := countP_decide_eq_zero_of_not_mem hnot
    have hstep := squareDualFace_stepFrom_left u
    have hformula := walk_horizontalRayCount_stepRight_eq_add_shared c
      (squareDualFaceOfPrimalVertex v)
    rw [hcount, add_zero] at hformula
    unfold closedSquareWalkFaceParity
    rw [hstep]
    exact congrArg (fun n : ℕ ↦ n % 2) hformula.symm
  · have hdual := squareEdgeDualCrossingEquiv_posHorizontal u
    rw [hdual] at hnot
    have hcount := countP_decide_eq_zero_of_not_mem hnot
    unfold closedSquareWalkFaceParity
    rw [squareDualFace_stepFrom_right]
    rw [walk_horizontalRayCount_stepRight_eq_add_shared]
    rw [hcount, add_zero]
  · let v := cubicStepFrom u (⟨1, by decide⟩, false)
    have hedge :
        (⟨s(u, v), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom u (⟨1, by decide⟩, false)⟩ : SquareEdge) =
          (SquarePositiveEdge.toEdge ⟨v, (1 : Fin 2)⟩) := by
      apply Subtype.ext
      change s(u, v) = s(v, cubicStepFrom v (⟨1, by decide⟩, true))
      dsimp [v]
      rw [cubicStepFrom_neg_pos]
      exact Sym2.eq_swap
    rw [hedge, squareEdgeDualCrossingEquiv_toEdge] at hnot
    have hdual : (primalToDualCrossingPositiveEdge
        (⟨v, (1 : Fin 2)⟩ : SquarePositiveEdge)).toEdge =
        (⟨s(cubicStepFrom (squareDualFaceOfPrimalVertex v) (⟨1, by decide⟩, true),
            cubicStepFrom
              (cubicStepFrom (squareDualFaceOfPrimalVertex v) (⟨1, by decide⟩, true))
              (⟨0, by decide⟩, true)), by
          rw [SimpleGraph.mem_edgeSet]
          exact cubicGraph_adj_stepFrom _ (⟨0, by decide⟩, true)⟩ : DualSquareEdge) := by
      rw [← squareEdgeDualCrossingEquiv_toEdge]
      simpa only [SquarePositiveEdge.toEdge] using
        squareEdgeDualCrossingEquiv_posVertical v
    rw [hdual] at hnot
    have hcount := countP_decide_eq_zero_of_not_mem hnot
    have hstep := squareDualFace_stepFrom_down u
    have hformula := walk_verticalRayCount_stepUp_eq_add_shared c
      (squareDualFaceOfPrimalVertex v)
    rw [hcount, add_zero] at hformula
    unfold closedSquareWalkFaceParity
    rw [closedWalk_faceRayCount_mod_two_eq c
      (squareDualFaceOfPrimalVertex u),
      closedWalk_faceRayCount_mod_two_eq c
        (squareDualFaceOfPrimalVertex v)]
    rw [hstep]
    exact congrArg (fun n : ℕ ↦ n % 2) hformula.symm
  · have hdual := squareEdgeDualCrossingEquiv_posVertical u
    rw [hdual] at hnot
    have hcount := countP_decide_eq_zero_of_not_mem hnot
    unfold closedSquareWalkFaceParity
    rw [closedWalk_faceRayCount_mod_two_eq c
      (squareDualFaceOfPrimalVertex u)]
    rw [squareDualFace_stepFrom_up]
    rw [walk_verticalRayCount_stepUp_eq_add_shared]
    rw [hcount, add_zero]
    exact (closedWalk_faceRayCount_mod_two_eq c
      (cubicStepFrom (squareDualFaceOfPrimalVertex u)
        (⟨1, by decide⟩, true))).symm

theorem closedSquareWalkFaceParity_eq_along_primal_walk_of_no_dual_crossings
    {o u v : SquareVertex} (c : squareGraph.Walk o o)
    (q : squareGraph.Walk u v)
    (hdisj : ∀ (e : SquareEdge), (e : Sym2 SquareVertex) ∈ q.edges →
      ((squareEdgeDualCrossingEquiv e : DualSquareEdge) : Sym2 DualSquareVertex) ∉
        c.edges) :
    closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex u) =
      closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex v) := by
  induction q with
  | nil => rfl
  | @cons u v z huv q ih =>
      have hhead :
          ((squareEdgeDualCrossingEquiv
            (⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩ : SquareEdge) :
              DualSquareEdge) : Sym2 DualSquareVertex) ∉ c.edges := by
        apply hdisj
        simp
      have htail : ∀ (e : SquareEdge), (e : Sym2 SquareVertex) ∈ q.edges →
          ((squareEdgeDualCrossingEquiv e : DualSquareEdge) : Sym2 DualSquareVertex) ∉
            c.edges := by
        intro e he
        apply hdisj e
        simp [he]
      exact (closedSquareWalkFaceParity_eq_of_dualCrossing_not_mem c huv hhead).trans
        (ih htail)

theorem cubicLInfDist_primalVertex_dualFace_le_one (x : SquareVertex) :
    cubicLInfDist x (squareDualFaceOfPrimalVertex x) ≤ 1 := by
  rw [cubicLInfDist]
  apply Finset.sup_le
  intro i hi
  fin_cases i <;>
    simp [squareDualFaceOfPrimalVertex, squareVertex] <;> omega

theorem cubicLInfDist_origin_dualFace_le_add_one (x : SquareVertex) :
    cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) ≤
      cubicLInfDist cubicOrigin x + 1 :=
  (cubicLInfDist_triangle cubicOrigin x (squareDualFaceOfPrimalVertex x)).trans
    (Nat.add_le_add_left (cubicLInfDist_primalVertex_dualFace_le_one x) _)

theorem cubicLInfDist_origin_le_dualFace_add_one (x : SquareVertex) :
    cubicLInfDist cubicOrigin x ≤
      cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) + 1 := by
  calc
    cubicLInfDist cubicOrigin x ≤
        cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) +
          cubicLInfDist (squareDualFaceOfPrimalVertex x) x :=
      cubicLInfDist_triangle _ _ _
    _ ≤ cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) + 1 :=
      Nat.add_le_add_left
        (cubicLInfDist_comm _ _ ▸ cubicLInfDist_primalVertex_dualFace_le_one x) _

theorem closedSquareWalkFaceParity_dualFace_eq_one_of_innerSurface
    {o : SquareVertex} (c : squareGraph.Walk o o) {l : ℕ} (hl : 2 ≤ l)
    (hsupport : ∀ z ∈ c.support,
      l < cubicLInfDist cubicOrigin z ∧
        cubicLInfDist cubicOrigin z ≤ 3 * l)
    (hparity : closedSquareWalkFaceParity c cubicOrigin = 1)
    {x : SquareVertex} (hx : x ∈ cubicBoxSurface 2 cubicOrigin (l - 2)) :
    closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex x) = 1 := by
  have hxDist : cubicLInfDist cubicOrigin x = l - 2 := mem_cubicBoxSurface.mp hx
  have hfaceDist : cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) ≤ l - 1 := by
    calc
      cubicLInfDist cubicOrigin (squareDualFaceOfPrimalVertex x) ≤
          cubicLInfDist cubicOrigin x + 1 :=
        cubicLInfDist_origin_dualFace_le_add_one x
      _ = (l - 2) + 1 := by rw [hxDist]
      _ = l - 1 := by omega
  have hfaceBox : squareDualFaceOfPrimalVertex x ∈
      cubicMetricBox 2 cubicOrigin (l - 1) :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr hfaceDist
  obtain ⟨q, hqEdges⟩ :=
    exists_cubicWalk_center_supported_in_box cubicOrigin
      (squareDualFaceOfPrimalVertex x) hfaceBox
  have hqSupport : ∀ z ∈ q.support,
      z ∈ cubicMetricBox 2 cubicOrigin (l - 1) :=
    walk_support_subset_cubicMetricBox_of_edges (by simp) q hqEdges
  have hdisj : ∀ z ∈ q.support, z ∉ c.support := by
    intro z hzq hzc
    have hzle : cubicLInfDist cubicOrigin z ≤ l - 1 :=
      mem_cubicMetricBox_iff_lInfDist_le.mp (hqSupport z hzq)
    have hzgt := (hsupport z hzc).1
    omega
  exact (closedSquareWalkFaceParity_eq_along_disjoint_walk c q hdisj).symm.trans hparity

theorem cubicLInfDist_origin_squareVertex_nat_zero (n : ℕ) :
    cubicLInfDist cubicOrigin (squareVertex (n : ℤ) 0) = n := by
  apply le_antisymm
  · rw [cubicLInfDist]
    apply Finset.sup_le
    intro i hi
    fin_cases i <;> simp [cubicOrigin, squareVertex]
  · have h := cubicLInfDist_coord_le cubicOrigin (squareVertex (n : ℤ) 0)
      (0 : Fin 2)
    simpa [cubicOrigin, squareVertex] using h

theorem closedSquareWalkFaceParity_dualFace_eq_zero_of_outerSurface
    {o : SquareVertex} (c : squareGraph.Walk o o) {l : ℕ}
    (hsupport : ∀ z ∈ c.support,
      l < cubicLInfDist cubicOrigin z ∧
        cubicLInfDist cubicOrigin z ≤ 3 * l)
    {y : SquareVertex} (hy : y ∈ cubicBoxSurface 2 cubicOrigin (3 * l + 2)) :
    closedSquareWalkFaceParity c (squareDualFaceOfPrimalVertex y) = 0 := by
  let f := squareDualFaceOfPrimalVertex y
  let N := cubicLInfDist cubicOrigin f
  have hyDist : cubicLInfDist cubicOrigin y = 3 * l + 2 := mem_cubicBoxSurface.mp hy
  have hN : 3 * l < N := by
    have htri := cubicLInfDist_origin_le_dualFace_add_one y
    dsimp [f, N]
    rw [hyDist] at htri
    omega
  have hfSurface : f ∈ cubicBoxSurface 2 cubicOrigin N := by
    rw [mem_cubicBoxSurface]
  have hrightSurface : squareVertex (N : ℤ) 0 ∈
      cubicBoxSurface 2 cubicOrigin N := by
    rw [mem_cubicBoxSurface, cubicLInfDist_origin_squareVertex_nat_zero]
  obtain ⟨q, hqSurface⟩ :=
    exists_cubicWalk_support_in_boxSurface (by decide : 2 ≤ 2)
      hfSurface hrightSurface
  have hdisj : ∀ z ∈ q.support, z ∉ c.support := by
    intro z hzq hzc
    have hzN : cubicLInfDist cubicOrigin z = N :=
      mem_cubicBoxSurface.mp (hqSurface z hzq)
    have hzle := (hsupport z hzc).2
    omega
  have hpathParity := closedSquareWalkFaceParity_eq_along_disjoint_walk c q hdisj
  have hrightZero :
      closedSquareWalkFaceParity c (squareVertex (N : ℤ) 0) = 0 := by
    unfold closedSquareWalkFaceParity
    rw [squareWalk_horizontalRayCount_right_eq_zero_of_support_le c N]
    intro z hzc
    have hzAbs := cubicLInfDist_coord_le cubicOrigin z (0 : Fin 2)
    have hzle := (hsupport z hzc).2
    have hzInt : (z 0 - (cubicOrigin : SquareVertex) 0).natAbs ≤ N :=
      hzAbs.trans (hzle.trans hN.le)
    have hzCast : ((z 0 - (cubicOrigin : SquareVertex) 0).natAbs : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hzInt
    have hzOrigin : (cubicOrigin : SquareVertex) 0 = 0 := rfl
    rw [hzOrigin, sub_zero] at hzCast
    exact Int.le_natAbs.trans hzCast
  exact hpathParity.trans hrightZero

/-- The event that the shifted-dual configuration contains an RSW circuit at scale `l`. -/
def dualRSWAnnulusOpenCircuitEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  dualSquareConfiguration ⁻¹' rswAnnulusOpenCircuitEvent l

theorem measurableSet_dualRSWAnnulusOpenCircuitEvent (l : ℕ) :
    MeasurableSet (dualRSWAnnulusOpenCircuitEvent l) :=
  (measurableSet_rswAnnulusOpenCircuitEvent l).preimage measurable_dualSquareConfiguration

theorem dualRSWAnnulusOpenCircuitEvent_subset_barrier
    {l : ℕ} (hl : 2 ≤ l) :
    dualRSWAnnulusOpenCircuitEvent l ⊆
      squareAnnulusBarrierEvent (l - 2) (3 * l + 2) := by
  intro ω hω
  change ω ∉ squareAnnulusRadialCrossingEvent (l - 2) (3 * l + 2)
  intro hradial
  rcases hω with ⟨o, c, hcycle, hcOpen, hsupport, hparity⟩
  simp only [squareAnnulusRadialCrossingEvent, Set.mem_iUnion] at hradial
  rcases hradial with ⟨x, hx, y, hy, q, hqOpen, hqEdges⟩
  have hinner := closedSquareWalkFaceParity_dualFace_eq_one_of_innerSurface
    c hl hsupport hparity hx
  have houter := closedSquareWalkFaceParity_dualFace_eq_zero_of_outerSurface
    c hsupport hy
  have hnoCrossing : ∀ (e : SquareEdge), (e : Sym2 SquareVertex) ∈ q.edges →
      ((squareEdgeDualCrossingEquiv e : DualSquareEdge) : Sym2 DualSquareVertex) ∉
        c.edges := by
    intro e heq hec
    have heOpen : e ∈ ω := hqOpen (e : Sym2 SquareVertex) heq
    let de : DualSquareEdge := squareEdgeDualCrossingEquiv e
    have hdeOpen : de ∈ dualSquareConfiguration ω := hcOpen (de : Sym2 DualSquareVertex) hec
    have heClosed : squareEdgeDualCrossingEquiv.symm de ∉ ω :=
      (dualSquareConfiguration_open_iff ω de).mp hdeOpen
    exact heClosed (by simpa [de] using heOpen)
  have heq := closedSquareWalkFaceParity_eq_along_primal_walk_of_no_dual_crossings
    c q hnoCrossing
  rw [hinner, houter] at heq
  omega

theorem bernoulliBondMeasure_real_dualRSWAnnulusOpenCircuitEvent_half (l : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (dualRSWAnnulusOpenCircuitEvent l) =
      rswAnnulusOpenCircuitProbability squareHalfDensity l := by
  let μ := bernoulliBondMeasure 2 squareHalfDensity
  let D := (dualSquareConfiguration : EdgeConfiguration 2 → EdgeConfiguration 2)
  let A := rswAnnulusOpenCircuitEvent l
  have hmap : μ.map D = μ := by
    have hsigma : σ squareHalfDensity = squareHalfDensity := by
      ext
      norm_num [squareHalfDensity]
    dsimp [μ, D]
    rw [bernoulliBondMeasure_map_dualSquareConfiguration, hsigma]
  calc
    μ.real (dualRSWAnnulusOpenCircuitEvent l) = (μ.map D).real A := by
      rw [map_measureReal_apply measurable_dualSquareConfiguration
        (measurableSet_rswAnnulusOpenCircuitEvent l)]
      rfl
    _ = μ.real A := by rw [hmap]
    _ = rswAnnulusOpenCircuitProbability squareHalfDensity l := rfl

theorem rswAnnulusOpenCircuitProbability_le_half_expandedBarrier
    {l : ℕ} (hl : 2 ≤ l) :
    rswAnnulusOpenCircuitProbability squareHalfDensity l ≤
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (squareAnnulusBarrierEvent (l - 2) (3 * l + 2)) := by
  rw [← bernoulliBondMeasure_real_dualRSWAnnulusOpenCircuitEvent_half]
  exact measureReal_mono (dualRSWAnnulusOpenCircuitEvent_subset_barrier hl)

/-! ### Shift-safe independent annuli -/

/-- The radius used by the `k`-th shifted-dual-safe annulus.  Starting at exponent two gives
enough room for the fixed two-site convention margin. -/
def expandedCriticalAnnulusScale (k : ℕ) : ℕ :=
  4 ^ (k + 2)

/-- Edge support of the widened critical annulus
`B(3·4^(k+2)+2) \ B(4^(k+2)-2)`. -/
noncomputable def expandedCriticalAnnulusEdges (k : ℕ) : Finset SquareEdge :=
  squareAnnulusEdges (expandedCriticalAnnulusScale k - 2)
    (3 * expandedCriticalAnnulusScale k + 2)

theorem expandedCriticalAnnulusScale_ge_sixteen (k : ℕ) :
    16 ≤ expandedCriticalAnnulusScale k := by
  rw [expandedCriticalAnnulusScale, pow_add]
  norm_num
  exact one_le_pow₀ (by omega)

theorem expandedCriticalAnnulus_outer_lt_next_inner {i j : ℕ} (hij : i < j) :
    3 * expandedCriticalAnnulusScale i + 2 <
      expandedCriticalAnnulusScale j - 2 := by
  have hexp : i + 3 ≤ j + 2 := by omega
  have hpow : 4 ^ (i + 3) ≤ 4 ^ (j + 2) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hscale : 4 * expandedCriticalAnnulusScale i ≤
      expandedCriticalAnnulusScale j := by
    simpa [expandedCriticalAnnulusScale, pow_succ, Nat.mul_comm] using hpow
  have hlarge := expandedCriticalAnnulusScale_ge_sixteen i
  omega

theorem pairwiseDisjoint_expandedCriticalAnnulusEdges :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) expandedCriticalAnnulusEdges := by
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · simpa [expandedCriticalAnnulusEdges] using
      (disjoint_squareAnnulusEdges_of_outer_lt_inner
        (inner₁ := expandedCriticalAnnulusScale i - 2)
        (outer₁ := 3 * expandedCriticalAnnulusScale i + 2)
        (inner₂ := expandedCriticalAnnulusScale j - 2)
        (outer₂ := 3 * expandedCriticalAnnulusScale j + 2)
        (expandedCriticalAnnulus_outer_lt_next_inner hij'))
  · simpa [expandedCriticalAnnulusEdges] using
      (disjoint_squareAnnulusEdges_of_outer_lt_inner
        (inner₁ := expandedCriticalAnnulusScale j - 2)
        (outer₁ := 3 * expandedCriticalAnnulusScale j + 2)
        (inner₂ := expandedCriticalAnnulusScale i - 2)
        (outer₂ := 3 * expandedCriticalAnnulusScale i + 2)
        (expandedCriticalAnnulus_outer_lt_next_inner hji')).symm

/-- The decreasing barrier event on the widened, shifted-dual-safe critical annulus. -/
def expandedCriticalAnnulusBarrierEvent (k : ℕ) : Set (EdgeConfiguration 2) :=
  squareAnnulusBarrierEvent (expandedCriticalAnnulusScale k - 2)
    (3 * expandedCriticalAnnulusScale k + 2)

theorem dependsOn_expandedCriticalAnnulusBarrierEvent (k : ℕ) :
    DependsOn (expandedCriticalAnnulusEdges k)
      (expandedCriticalAnnulusBarrierEvent k) :=
  dependsOn_squareAnnulusBarrierEvent _ _

theorem measurableSet_expandedCriticalAnnulusBarrierEvent (k : ℕ) :
    MeasurableSet (expandedCriticalAnnulusBarrierEvent k) :=
  (dependsOn_expandedCriticalAnnulusBarrierEvent k).measurableSet

theorem iIndepSet_expandedCriticalAnnulusBarrierEvent (p : I) :
    iIndepSet expandedCriticalAnnulusBarrierEvent (bernoulliBondMeasure 2 p) :=
  bernoulliBondMeasure_iIndepSet_of_pairwiseDisjoint_dependsOn p
    expandedCriticalAnnulusEdges expandedCriticalAnnulusBarrierEvent
    dependsOn_expandedCriticalAnnulusBarrierEvent
    pairwiseDisjoint_expandedCriticalAnnulusEdges

theorem hasInfiniteOpenCluster_subset_iInter_expandedCriticalAnnulusBarrierEvent_compl :
    {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} ⊆
      ⋂ k, (expandedCriticalAnnulusBarrierEvent k)ᶜ := by
  intro ω hinfinite
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro k hbarrier
  have hscale := expandedCriticalAnnulusScale_ge_sixteen k
  have hcross := hasInfiniteOpenCluster_mem_squareAnnulusRadialCrossingEvent
    (inner := expandedCriticalAnnulusScale k - 2)
    (outer := 3 * expandedCriticalAnnulusScale k + 2) (by omega) hinfinite
  exact hbarrier hcross

end Percolation
