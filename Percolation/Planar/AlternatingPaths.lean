import Mathlib.Algebra.BigOperators.Ring.Nat
import Percolation.Planar.Peierls
import Percolation.Planar.Projection

/-!
# Alternating square-grid paths intersect

This file supplies the discrete planar lemma hidden behind Grimmett's phrase "it is clear from
Figure 7.14".  The proof uses a mod-two ray index on faces of the square lattice.  Keeping this
geometry independent of percolation prevents the probabilistic argument from assuming an
unformalized Jordan-curve principle.
-/

namespace Percolation

open scoped Sym2

/-- A square edge crosses the horizontal ray which starts at the centre of the face whose
lower-left corner is `f`. -/
def squareEdgeCrossesFaceHorizontalRay (f : SquareVertex) : Sym2 SquareVertex → Prop :=
  Sym2.lift ⟨(fun u v ↦
    u 0 = v 0 ∧ min (u 1) (v 1) = f 1 ∧ f 0 < u 0), (by
      intro u v
      simp only [eq_comm (a := u 0) (b := v 0), min_comm]
      apply propext
      constructor <;> rintro ⟨h, hmin, hlt⟩
      · exact ⟨h, hmin, h ▸ hlt⟩
      · exact ⟨h, hmin, h ▸ hlt⟩)⟩

/-- A square edge crosses the vertical ray which starts at the centre of the face whose
lower-left corner is `f`. -/
def squareEdgeCrossesFaceVerticalRay (f : SquareVertex) : Sym2 SquareVertex → Prop :=
  Sym2.lift ⟨(fun u v ↦
    u 1 = v 1 ∧ min (u 0) (v 0) = f 0 ∧ f 1 < u 1), (by
      intro u v
      simp only [eq_comm (a := u 1) (b := v 1), min_comm]
      apply propext
      constructor <;> rintro ⟨h, hmin, hlt⟩
      · exact ⟨h, hmin, h ▸ hlt⟩
      · exact ⟨h, hmin, h ▸ hlt⟩)⟩

/-- The open north-east quadrant based at the centre of a square face. -/
def squareFaceNorthEast (f x : SquareVertex) : Prop :=
  f 0 < x 0 ∧ f 1 < x 1

instance squareFaceNorthEast_decidable (f : SquareVertex) :
    DecidablePred (squareFaceNorthEast f) := fun x ↦ by
  unfold squareFaceNorthEast
  infer_instance

/-- Crossing the boundary of a north-east quadrant is exactly crossing one of its two rays.
The alternatives are disjoint for a nearest-neighbour square edge. -/
theorem square_edge_crosses_northEast_iff
    (f u v : SquareVertex) (huv : squareGraph.Adj u v) :
    ((squareFaceNorthEast f u ∧ ¬ squareFaceNorthEast f v) ∨
      (squareFaceNorthEast f v ∧ ¬ squareFaceNorthEast f u)) ↔
      (squareEdgeCrossesFaceHorizontalRay f s(u, v) ∨
        squareEdgeCrossesFaceVerticalRay f s(u, v)) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
  fin_cases i <;>
    simp [squareFaceNorthEast, squareEdgeCrossesFaceHorizontalRay,
      squareEdgeCrossesFaceVerticalRay, cubicStepFrom, cubicDirectionIncrement] <;>
    omega

theorem square_edge_not_crosses_both_face_rays
    (f u v : SquareVertex) (huv : squareGraph.Adj u v) :
    ¬ (squareEdgeCrossesFaceHorizontalRay f s(u, v) ∧
      squareEdgeCrossesFaceVerticalRay f s(u, v)) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
  fin_cases i <;>
    simp [squareEdgeCrossesFaceHorizontalRay, squareEdgeCrossesFaceVerticalRay,
      cubicStepFrom, cubicDirectionIncrement]

/-- Boolean horizontal-ray crossing predicate used by `List.countP`. -/
noncomputable def squareEdgeCrossesFaceHorizontalRayBool
    (f : SquareVertex) (e : Sym2 SquareVertex) : Bool := by
  classical
  exact decide (squareEdgeCrossesFaceHorizontalRay f e)

/-- Boolean vertical-ray crossing predicate used by `List.countP`. -/
noncomputable def squareEdgeCrossesFaceVerticalRayBool
    (f : SquareVertex) (e : Sym2 SquareVertex) : Bool := by
  classical
  exact decide (squareEdgeCrossesFaceVerticalRay f e)

/-- For one square edge, the north-east cut indicator is the sum of its two disjoint ray
indicators. -/
theorem square_edge_northEast_indicator
    (f u v : SquareVertex) (huv : squareGraph.Adj u v) :
    (SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f) s(u, v)).toNat =
      (squareEdgeCrossesFaceHorizontalRayBool f s(u, v)).toNat +
        (squareEdgeCrossesFaceVerticalRayBool f s(u, v)).toNat := by
  have hiff := square_edge_crosses_northEast_iff f u v huv
  have hdisj := square_edge_not_crosses_both_face_rays f u v huv
  by_cases hh : squareEdgeCrossesFaceHorizontalRay f s(u, v)
  · by_cases hv : squareEdgeCrossesFaceVerticalRay f s(u, v)
    · exact (hdisj ⟨hh, hv⟩).elim
    · have hcut := hiff.mpr (Or.inl hh)
      have hcutBool :
          SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f) s(u, v) = true :=
        (SimpleGraph.Walk.edgeCrossesSetBool_eq_true _ _).mpr hcut
      simp [hcutBool, squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceVerticalRayBool, hh, hv]
  · by_cases hv : squareEdgeCrossesFaceVerticalRay f s(u, v)
    · have hcut := hiff.mpr (Or.inr hv)
      have hcutBool :
          SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f) s(u, v) = true :=
        (SimpleGraph.Walk.edgeCrossesSetBool_eq_true _ _).mpr hcut
      simp [hcutBool, squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceVerticalRayBool, hh, hv]
    · have hnotcut : ¬ ((squareFaceNorthEast f u ∧ ¬ squareFaceNorthEast f v) ∨
          (squareFaceNorthEast f v ∧ ¬ squareFaceNorthEast f u)) := by
        intro hcut
        exact (hiff.mp hcut).elim hh hv
      have hcutBool :
          SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f) s(u, v) = false := by
        rw [Bool.eq_false_iff]
        simpa using hnotcut
      simp [hcutBool, squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceVerticalRayBool, hh, hv]

/-- The north-east cut count of any square walk splits into the two ray counts. -/
theorem walk_northEastCut_count_eq_add_faceRays
    {u v : SquareVertex} (w : squareGraph.Walk u v) (f : SquareVertex) :
    w.edges.countP
        (SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f)) =
      w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) +
        w.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) := by
  induction w with
  | nil => simp
  | @cons u v z huv w ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.countP_cons]
      rw [ih]
      have hind := square_edge_northEast_indicator f u v huv
      cases hc : SimpleGraph.Walk.edgeCrossesSetBool
          (squareFaceNorthEast f) s(u, v) <;>
        cases hh : squareEdgeCrossesFaceHorizontalRayBool f s(u, v) <;>
          cases hv : squareEdgeCrossesFaceVerticalRayBool f s(u, v) <;>
            simp [hc, hh, hv] at hind ⊢ <;> omega

/-- On a closed square walk, horizontal- and vertical-ray crossing counts based at the same face
have the same parity. -/
theorem closedWalk_faceRayCount_mod_two_eq
    {u : SquareVertex} (w : squareGraph.Walk u u) (f : SquareVertex) :
    w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) % 2 =
      w.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) % 2 := by
  classical
  have hsum := walk_northEastCut_count_eq_add_faceRays w f
  have heven :=
    SimpleGraph.Walk.even_countP_edges_edgeCrossesSet_of_closed
      (squareFaceNorthEast f) w
  rw [hsum] at heven
  rw [Nat.even_iff] at heven
  omega

/-- Moving a face one step right does not change the horizontal-ray crossing count of a closed
walk unless the shared lower-right primal vertex lies on that walk. -/
theorem closedWalk_horizontalRayCount_stepRight_eq_of_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : SquareVertex)
    (hnot : cubicStepFrom f (⟨0, by decide⟩, true) ∉ c.support) :
    c.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) =
      c.edges.countP (squareEdgeCrossesFaceHorizontalRayBool
        (cubicStepFrom f (⟨0, by decide⟩, true))) := by
  classical
  apply List.countP_congr
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := c.adj_of_mem_edges he
      have hu : u ∈ c.support := c.fst_mem_support_of_mem_edges he
      have hv : v ∈ c.support := c.snd_mem_support_of_mem_edges he
      have hune : u ≠ cubicStepFrom f (⟨0, by decide⟩, true) := fun h ↦ hnot (h ▸ hu)
      have hvne : v ≠ cubicStepFrom f (⟨0, by decide⟩, true) := fun h ↦ hnot (h ▸ hv)
      have hucoords : ¬ (u 0 = f 0 + 1 ∧ u 1 = f 1) := by
        rintro ⟨hu0, hu1⟩
        apply hune
        ext j
        fin_cases j <;>
          simp [cubicStepFrom, cubicDirectionIncrement, hu0, hu1]
      have hvcoords : ¬ (v 0 = f 0 + 1 ∧ v 1 = f 1) := by
        rintro ⟨hv0, hv1⟩
        apply hvne
        ext j
        fin_cases j <;>
          simp [cubicStepFrom, cubicDirectionIncrement, hv0, hv1]
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
      fin_cases i <;>
        simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
          cubicDirectionIncrement] at hucoords hvcoords ⊢ <;>
        omega

/-- Moving a face one step up does not change the vertical-ray crossing count unless the shared
upper-left primal vertex lies on the closed walk. -/
theorem closedWalk_verticalRayCount_stepUp_eq_of_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : SquareVertex)
    (hnot : cubicStepFrom f (⟨1, by decide⟩, true) ∉ c.support) :
    c.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) =
      c.edges.countP (squareEdgeCrossesFaceVerticalRayBool
        (cubicStepFrom f (⟨1, by decide⟩, true))) := by
  classical
  apply List.countP_congr
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := c.adj_of_mem_edges he
      have hu : u ∈ c.support := c.fst_mem_support_of_mem_edges he
      have hv : v ∈ c.support := c.snd_mem_support_of_mem_edges he
      have hune : u ≠ cubicStepFrom f (⟨1, by decide⟩, true) := fun h ↦ hnot (h ▸ hu)
      have hvne : v ≠ cubicStepFrom f (⟨1, by decide⟩, true) := fun h ↦ hnot (h ▸ hv)
      have hucoords : ¬ (u 0 = f 0 ∧ u 1 = f 1 + 1) := by
        rintro ⟨hu0, hu1⟩
        apply hune
        ext j
        fin_cases j <;>
          simp [cubicStepFrom, cubicDirectionIncrement, hu0, hu1]
      have hvcoords : ¬ (v 0 = f 0 ∧ v 1 = f 1 + 1) := by
        rintro ⟨hv0, hv1⟩
        apply hvne
        ext j
        fin_cases j <;>
          simp [cubicStepFrom, cubicDirectionIncrement, hv0, hv1]
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
      fin_cases i <;>
        simp [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay, cubicStepFrom,
          cubicDirectionIncrement] at hucoords hvcoords ⊢ <;>
        omega

/-- Mod-two face index of a closed square walk, computed with the horizontal ray. -/
noncomputable def closedSquareWalkFaceParity
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : SquareVertex) : ℕ :=
  c.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) % 2

theorem closedSquareWalkFaceParity_stepRight_eq_of_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : SquareVertex)
    (hnot : cubicStepFrom f (⟨0, by decide⟩, true) ∉ c.support) :
    closedSquareWalkFaceParity c f =
      closedSquareWalkFaceParity c (cubicStepFrom f (⟨0, by decide⟩, true)) := by
  unfold closedSquareWalkFaceParity
  rw [closedWalk_horizontalRayCount_stepRight_eq_of_not_mem c f hnot]

theorem closedSquareWalkFaceParity_stepUp_eq_of_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : SquareVertex)
    (hnot : cubicStepFrom f (⟨1, by decide⟩, true) ∉ c.support) :
    closedSquareWalkFaceParity c f =
      closedSquareWalkFaceParity c (cubicStepFrom f (⟨1, by decide⟩, true)) := by
  unfold closedSquareWalkFaceParity
  rw [closedWalk_faceRayCount_mod_two_eq c f,
    closedWalk_verticalRayCount_stepUp_eq_of_not_mem c f hnot,
    closedWalk_faceRayCount_mod_two_eq c
      (cubicStepFrom f (⟨1, by decide⟩, true))]

set_option maxHeartbeats 800000 in
/-- Adjacent faces have the same parity whenever both corresponding primal vertices avoid the
closed walk. -/
theorem closedSquareWalkFaceParity_eq_of_adj_of_not_mem
    {o u v : SquareVertex} (c : squareGraph.Walk o o) (huv : squareGraph.Adj u v)
    (hu : u ∉ c.support) (hv : v ∉ c.support) :
    closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c v := by
  rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
  rcases i with ⟨i, b⟩
  fin_cases i <;> cases b
  · have hstep : cubicStepFrom (cubicStepFrom u (⟨0, by decide⟩, false))
        (⟨0, by decide⟩, true) = u := by
      ext j
      fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement]
    have h := (closedSquareWalkFaceParity_stepRight_eq_of_not_mem c
      (cubicStepFrom u (⟨0, by decide⟩, false)) (hstep ▸ hu)).symm
    simpa only [hstep] using h
  · exact closedSquareWalkFaceParity_stepRight_eq_of_not_mem c u hv
  · have hstep : cubicStepFrom (cubicStepFrom u (⟨1, by decide⟩, false))
        (⟨1, by decide⟩, true) = u := by
      ext j
      fin_cases j <;> simp [cubicStepFrom, cubicDirectionIncrement]
    have h := (closedSquareWalkFaceParity_stepUp_eq_of_not_mem c
      (cubicStepFrom u (⟨1, by decide⟩, false)) (hstep ▸ hu)).symm
    simpa only [hstep] using h
  · exact closedSquareWalkFaceParity_stepUp_eq_of_not_mem c u hv

/-- The mod-two face index is constant along every square walk whose support avoids the closed
walk. -/
theorem closedSquareWalkFaceParity_eq_along_disjoint_walk
    {o u v : SquareVertex} (c : squareGraph.Walk o o) (q : squareGraph.Walk u v)
    (hdisj : ∀ z ∈ q.support, z ∉ c.support) :
    closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c v := by
  induction q with
  | nil => rfl
  | @cons u v z huv q ih =>
      rw [SimpleGraph.Walk.support_cons] at hdisj
      have hu : u ∉ c.support := hdisj u (by simp)
      have htail : ∀ x ∈ q.support, x ∉ c.support := by
        intro x hx
        exact hdisj x (by simp [hx])
      exact (closedSquareWalkFaceParity_eq_of_adj_of_not_mem c huv hu
        (htail v q.start_mem_support)).trans (ih htail)

/-! ### An exterior closure for a corner-to-right-face path -/

theorem mem_cubicVerticesFrom_append_iff {d : ℕ} (x z : Cubic d)
    (s t : List (CubicDirection d)) :
    z ∈ cubicVerticesFrom x (s ++ t) ↔
      z ∈ cubicVerticesFrom x s ∨
        z ∈ cubicVerticesFrom (cubicEndpointFrom x s) t := by
  induction s generalizing x with
  | nil =>
      constructor
      · exact Or.inr
      · rintro (hz | hz)
        · have hzx : z = x := by simpa [cubicVerticesFrom] using hz
          subst z
          cases t <;> simp
        · exact hz
  | cons a s ih =>
      simp only [List.cons_append, cubicVerticesFrom, cubicEndpointFrom, List.mem_cons]
      rw [ih]
      tauto

/-- Direction word which closes a path ending at `(m,a)` by travelling strictly above and to
the sides of `[0,m]²`. -/
def squareUpperExteriorClosureSteps (m a : ℕ) : List (CubicDirection 2) :=
  List.replicate 1 (⟨0, by decide⟩, true) ++
    (List.replicate (m + 1 - a) (⟨1, by decide⟩, true) ++
      (List.replicate (m + 2) (⟨0, by decide⟩, false) ++
        (List.replicate (m + 1) (⟨1, by decide⟩, false) ++
          List.replicate 1 (⟨0, by decide⟩, true))))

theorem cubicEndpointFrom_squareUpperExteriorClosureSteps
    {m a : ℕ} (ha : a ≤ m) :
    cubicEndpointFrom (squareVertex (m : ℤ) (a : ℤ))
      (squareUpperExteriorClosureSteps m a) = squareVertex 0 0 := by
  simp only [squareUpperExteriorClosureSteps, cubicEndpointFrom_append,
    cubicEndpointFrom_replicate_pos, cubicEndpointFrom_replicate_neg]
  ext i
  fin_cases i <;> (simp [squareVertex, Function.update, Fin.isValue] <;> omega)

/-- The concrete exterior walk from `(m,a)` back to `(0,0)`. -/
def squareUpperExteriorClosureWalk (m a : ℕ) (ha : a ≤ m) :
    squareGraph.Walk (squareVertex (m : ℤ) (a : ℤ)) (squareVertex 0 0) :=
  (cubicWalkFrom (squareVertex (m : ℤ) (a : ℤ))
    (squareUpperExteriorClosureSteps m a)).copy rfl
      (cubicEndpointFrom_squareUpperExteriorClosureSteps ha)

/-- Apart from its two endpoints, the exterior closure stays strictly outside `[0,m]²`. -/
theorem mem_cubicVerticesFrom_squareUpperExteriorClosureSteps
    {m a : ℕ} (ha : a ≤ m) {z : SquareVertex}
    (hz : z ∈ cubicVerticesFrom (squareVertex (m : ℤ) (a : ℤ))
      (squareUpperExteriorClosureSteps m a)) :
    z = squareVertex (m : ℤ) (a : ℤ) ∨ z = squareVertex 0 0 ∨
      z 0 < 0 ∨ (m : ℤ) < z 0 ∨ (m : ℤ) < z 1 := by
  let x0 := squareVertex (m : ℤ) (a : ℤ)
  let x1 := squareVertex ((m : ℤ) + 1) (a : ℤ)
  let x2 := squareVertex ((m : ℤ) + 1) ((m : ℤ) + 1)
  let x3 := squareVertex (-1) ((m : ℤ) + 1)
  let x4 := squareVertex (-1) 0
  let s0 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  let s1 : List (CubicDirection 2) :=
    List.replicate (m + 1 - a) (⟨1, by decide⟩, true)
  let s2 : List (CubicDirection 2) := List.replicate (m + 2) (⟨0, by decide⟩, false)
  let s3 : List (CubicDirection 2) := List.replicate (m + 1) (⟨1, by decide⟩, false)
  let s4 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  have he0 : cubicEndpointFrom x0 s0 = x1 := by
    ext i
    fin_cases i <;> simp [x0, x1, s0, squareVertex,
      cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement,
      Function.update]
  have he1 : cubicEndpointFrom x1 s1 = x2 := by
    ext i
    fin_cases i
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
      omega
  have he2 : cubicEndpointFrom x2 s2 = x3 := by
    ext i
    fin_cases i <;> simp [x2, x3, s2, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  have he3 : cubicEndpointFrom x3 s3 = x4 := by
    ext i
    fin_cases i <;> simp [x3, x4, s3, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  have hz' : z ∈ cubicVerticesFrom x0 (s0 ++ (s1 ++ (s2 ++ (s3 ++ s4)))) := by
    simpa [x0, s0, s1, s2, s3, s4, squareUpperExteriorClosureSteps] using hz
  rw [mem_cubicVerticesFrom_append_iff] at hz'
  rcases hz' with h0 | hz'
  · have hz0 := cubicVerticesFrom_replicate_pos_coord_between
      x0 (⟨0, by decide⟩) 1 h0
    have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      x0 (⟨0, by decide⟩) (⟨1, by decide⟩) 1 (by decide) h0
    simp [x0] at hz0 hz1
    by_cases hzm : z 0 = m
    · left
      ext i
      fin_cases i <;> simp [squareVertex, hzm, hz1]
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · rw [he0, mem_cubicVerticesFrom_append_iff] at hz'
    rcases hz' with h1 | hz'
    · have hz0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
        x1 (⟨1, by decide⟩) (⟨0, by decide⟩) (m + 1 - a) (by decide) h1
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [x1] at hz0; omega))))
    · rw [he1, mem_cubicVerticesFrom_append_iff] at hz'
      rcases hz' with h2 | hz'
      · have hz1 := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
          x2 (⟨0, by decide⟩) (⟨1, by decide⟩) (m + 2) (by decide) h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [x2] at hz1; omega))))
      · rw [he2, mem_cubicVerticesFrom_append_iff] at hz'
        rcases hz' with h3 | h4
        · have hz0 := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
            x3 (⟨1, by decide⟩) (⟨0, by decide⟩) (m + 1) (by decide) h3
          exact Or.inr (Or.inr (Or.inl (by simp [x3] at hz0; omega)))
        · rw [he3] at h4
          have hz0 := cubicVerticesFrom_replicate_pos_coord_between
            x4 (⟨0, by decide⟩) 1 h4
          have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
            x4 (⟨0, by decide⟩) (⟨1, by decide⟩) 1 (by decide) h4
          simp [x4] at hz0 hz1
          by_cases hzorigin : z 0 = 0
          · right; left
            ext i
            fin_cases i <;> simp [squareVertex, hzorigin, hz1]
          · exact Or.inr (Or.inr (Or.inl (by omega)))

theorem mem_squareUpperExteriorClosureWalk_support
    {m a : ℕ} (ha : a ≤ m) {z : SquareVertex}
    (hz : z ∈ (squareUpperExteriorClosureWalk m a ha).support) :
    z = squareVertex (m : ℤ) (a : ℤ) ∨ z = squareVertex 0 0 ∨
      z 0 < 0 ∨ (m : ℤ) < z 0 ∨ (m : ℤ) < z 1 := by
  apply mem_cubicVerticesFrom_squareUpperExteriorClosureSteps ha
  simpa [squareUpperExteriorClosureWalk] using hz

theorem cubicWalkFrom_edges_append {d : ℕ} (x : Cubic d)
    (s t : List (CubicDirection d)) :
    (cubicWalkFrom x (s ++ t)).edges =
      (cubicWalkFrom x s).edges ++
        (cubicWalkFrom (cubicEndpointFrom x s) t).edges := by
  induction s generalizing x with
  | nil => rfl
  | cons a s ih =>
      simp [cubicWalkFrom, cubicEndpointFrom, ih]

theorem horizontalRayCount_cubicWalkFrom_replicate_horizontal
    (x f : SquareVertex) (n : ℕ) (b : Bool) :
    (cubicWalkFrom x (List.replicate n (⟨0, by decide⟩, b))).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  cases b
  · induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [List.replicate_succ]
        simp only [cubicWalkFrom, SimpleGraph.Walk.edges_cons, List.countP_cons]
        have htail := ih (cubicStepFrom x (⟨0, by decide⟩, false))
        calc
          (cubicWalkFrom (cubicStepFrom x (⟨0, by decide⟩, false))
                (List.replicate n (⟨0, by decide⟩, false))).edges.countP
                (squareEdgeCrossesFaceHorizontalRayBool f) +
              (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨0, by decide⟩, false)) = true then 1 else 0) =
              0 + (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨0, by decide⟩, false)) = true then 1 else 0) :=
            congrArg (fun k ↦ k + (if squareEdgeCrossesFaceHorizontalRayBool f
              s(x, cubicStepFrom x (⟨0, by decide⟩, false)) = true then 1 else 0)) htail
          _ = 0 := by
            simp [squareEdgeCrossesFaceHorizontalRayBool,
              squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
              cubicDirectionIncrement]
  · induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [List.replicate_succ]
        simp only [cubicWalkFrom, SimpleGraph.Walk.edges_cons, List.countP_cons]
        have htail := ih (cubicStepFrom x (⟨0, by decide⟩, true))
        calc
          (cubicWalkFrom (cubicStepFrom x (⟨0, by decide⟩, true))
                (List.replicate n (⟨0, by decide⟩, true))).edges.countP
                (squareEdgeCrossesFaceHorizontalRayBool f) +
              (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨0, by decide⟩, true)) = true then 1 else 0) =
              0 + (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨0, by decide⟩, true)) = true then 1 else 0) :=
            congrArg (fun k ↦ k + (if squareEdgeCrossesFaceHorizontalRayBool f
              s(x, cubicStepFrom x (⟨0, by decide⟩, true)) = true then 1 else 0)) htail
          _ = 0 := by
            simp [squareEdgeCrossesFaceHorizontalRayBool,
              squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
              cubicDirectionIncrement]

set_option maxHeartbeats 800000 in
theorem horizontalRayCount_cubicWalkFrom_replicate_vertical_pos
    (x f : SquareVertex) (n : ℕ) :
    (cubicWalkFrom x (List.replicate n (⟨1, by decide⟩, true))).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) =
        if f 0 < x 0 ∧ x 1 ≤ f 1 ∧ f 1 < x 1 + n then 1 else 0 := by
  induction n generalizing x with
  | zero =>
      calc
        (cubicWalkFrom x (List.replicate 0 (⟨1, by decide⟩, true))).edges.countP
            (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := rfl
        _ = if f 0 < x 0 ∧ x 1 ≤ f 1 ∧ f 1 < x 1 + (0 : ℕ) then 1 else 0 := by
          split_ifs <;> omega
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [cubicWalkFrom, SimpleGraph.Walk.edges_cons, List.countP_cons]
      have htail := ih (cubicStepFrom x (⟨1, by decide⟩, true))
      calc
        (cubicWalkFrom (cubicStepFrom x (⟨1, by decide⟩, true))
              (List.replicate n (⟨1, by decide⟩, true))).edges.countP
              (squareEdgeCrossesFaceHorizontalRayBool f) +
            (if squareEdgeCrossesFaceHorizontalRayBool f
              s(x, cubicStepFrom x (⟨1, by decide⟩, true)) = true then 1 else 0) =
            (if f 0 < cubicStepFrom x (⟨1, by decide⟩, true) 0 ∧
                cubicStepFrom x (⟨1, by decide⟩, true) 1 ≤ f 1 ∧
                f 1 < cubicStepFrom x (⟨1, by decide⟩, true) 1 + n then 1 else 0) +
              (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨1, by decide⟩, true)) = true then 1 else 0) :=
          congrArg (fun k ↦ k + (if squareEdgeCrossesFaceHorizontalRayBool f
            s(x, cubicStepFrom x (⟨1, by decide⟩, true)) = true then 1 else 0)) htail
        _ = if f 0 < x 0 ∧ x 1 ≤ f 1 ∧ f 1 < x 1 + (n + 1) then 1 else 0 := by
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement]
          split_ifs <;> omega

set_option maxHeartbeats 800000 in
theorem horizontalRayCount_cubicWalkFrom_replicate_vertical_neg
    (x f : SquareVertex) (n : ℕ) :
    (cubicWalkFrom x (List.replicate n (⟨1, by decide⟩, false))).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) =
        if f 0 < x 0 ∧ x 1 - n ≤ f 1 ∧ f 1 < x 1 then 1 else 0 := by
  induction n generalizing x with
  | zero =>
      calc
        (cubicWalkFrom x (List.replicate 0 (⟨1, by decide⟩, false))).edges.countP
            (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := rfl
        _ = if f 0 < x 0 ∧ x 1 - (0 : ℕ) ≤ f 1 ∧ f 1 < x 1 then 1 else 0 := by
          split_ifs <;> omega
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [cubicWalkFrom, SimpleGraph.Walk.edges_cons, List.countP_cons]
      have htail := ih (cubicStepFrom x (⟨1, by decide⟩, false))
      calc
        (cubicWalkFrom (cubicStepFrom x (⟨1, by decide⟩, false))
              (List.replicate n (⟨1, by decide⟩, false))).edges.countP
              (squareEdgeCrossesFaceHorizontalRayBool f) +
            (if squareEdgeCrossesFaceHorizontalRayBool f
              s(x, cubicStepFrom x (⟨1, by decide⟩, false)) = true then 1 else 0) =
            (if f 0 < cubicStepFrom x (⟨1, by decide⟩, false) 0 ∧
                cubicStepFrom x (⟨1, by decide⟩, false) 1 - n ≤ f 1 ∧
                f 1 < cubicStepFrom x (⟨1, by decide⟩, false) 1 then 1 else 0) +
              (if squareEdgeCrossesFaceHorizontalRayBool f
                s(x, cubicStepFrom x (⟨1, by decide⟩, false)) = true then 1 else 0) :=
          congrArg (fun k ↦ k + (if squareEdgeCrossesFaceHorizontalRayBool f
            s(x, cubicStepFrom x (⟨1, by decide⟩, false)) = true then 1 else 0)) htail
        _ = if f 0 < x 0 ∧ x 1 - (n + 1) ≤ f 1 ∧ f 1 < x 1 then 1 else 0 := by
          simp [squareEdgeCrossesFaceHorizontalRayBool,
            squareEdgeCrossesFaceHorizontalRay, cubicStepFrom,
            cubicDirectionIncrement]
          split_ifs <;> omega

set_option maxHeartbeats 1200000 in
theorem squareUpperExteriorClosureWalk_bottomRight_rayCount_eq_zero
    {m a : ℕ} (ha : a ≤ m) (ha0 : 0 < a) :
    (squareUpperExteriorClosureWalk m a ha).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool
        (squareVertex (m : ℤ) 0)) = 0 := by
  simp only [squareUpperExteriorClosureWalk, SimpleGraph.Walk.edges_copy]
  let x0 := squareVertex (m : ℤ) (a : ℤ)
  let x1 := squareVertex ((m : ℤ) + 1) (a : ℤ)
  let x2 := squareVertex ((m : ℤ) + 1) ((m : ℤ) + 1)
  let x3 := squareVertex (-1) ((m : ℤ) + 1)
  let x4 := squareVertex (-1) 0
  let s0 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  let s1 : List (CubicDirection 2) :=
    List.replicate (m + 1 - a) (⟨1, by decide⟩, true)
  let s2 : List (CubicDirection 2) := List.replicate (m + 2) (⟨0, by decide⟩, false)
  let s3 : List (CubicDirection 2) := List.replicate (m + 1) (⟨1, by decide⟩, false)
  let s4 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  have he0 : cubicEndpointFrom x0 s0 = x1 := by
    ext i
    fin_cases i <;> simp [x0, x1, s0, squareVertex, cubicEndpointFrom,
      cubicStepFrom, cubicDirectionIncrement, Function.update]
  have he1 : cubicEndpointFrom x1 s1 = x2 := by
    ext i
    fin_cases i
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
      omega
  have he2 : cubicEndpointFrom x2 s2 = x3 := by
    ext i
    fin_cases i <;> simp [x2, x3, s2, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  have he3 : cubicEndpointFrom x3 s3 = x4 := by
    ext i
    fin_cases i <;> simp [x3, x4, s3, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  change (cubicWalkFrom x0 (s0 ++ (s1 ++ (s2 ++ (s3 ++ s4))))).edges.countP
    (squareEdgeCrossesFaceHorizontalRayBool (squareVertex (m : ℤ) 0)) = 0
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [horizontalRayCount_cubicWalkFrom_replicate_horizontal,
    horizontalRayCount_cubicWalkFrom_replicate_vertical_pos,
    horizontalRayCount_cubicWalkFrom_replicate_horizontal,
    horizontalRayCount_cubicWalkFrom_replicate_vertical_neg,
    horizontalRayCount_cubicWalkFrom_replicate_horizontal]
  have hfillNat : a + (m + 1 - a) = m + 1 := by omega
  have hfillInt : (a : ℤ) + (m + 1 - a : ℕ) = (m + 1 : ℕ) := by
    exact_mod_cast hfillNat
  simp [x0, s0, s1, s2, squareVertex,
    cubicEndpointFrom_replicate_pos, cubicEndpointFrom_replicate_neg,
    cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, Function.update,
    hfillInt]
  exact Nat.ne_of_gt ha0

set_option maxHeartbeats 1200000 in
theorem squareUpperExteriorClosureWalk_top_rayCount_eq_one
    {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    (squareUpperExteriorClosureWalk m a ha).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool
        (squareVertex (b : ℤ) (m : ℤ))) = 1 := by
  simp only [squareUpperExteriorClosureWalk, SimpleGraph.Walk.edges_copy]
  let x0 := squareVertex (m : ℤ) (a : ℤ)
  let x1 := squareVertex ((m : ℤ) + 1) (a : ℤ)
  let x2 := squareVertex ((m : ℤ) + 1) ((m : ℤ) + 1)
  let x3 := squareVertex (-1) ((m : ℤ) + 1)
  let x4 := squareVertex (-1) 0
  let s0 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  let s1 : List (CubicDirection 2) :=
    List.replicate (m + 1 - a) (⟨1, by decide⟩, true)
  let s2 : List (CubicDirection 2) := List.replicate (m + 2) (⟨0, by decide⟩, false)
  let s3 : List (CubicDirection 2) := List.replicate (m + 1) (⟨1, by decide⟩, false)
  let s4 : List (CubicDirection 2) := List.replicate 1 (⟨0, by decide⟩, true)
  have he0 : cubicEndpointFrom x0 s0 = x1 := by
    ext i
    fin_cases i <;> simp [x0, x1, s0, squareVertex, cubicEndpointFrom,
      cubicStepFrom, cubicDirectionIncrement, Function.update]
  have he1 : cubicEndpointFrom x1 s1 = x2 := by
    ext i
    fin_cases i
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
    · simp [x1, x2, s1, squareVertex, cubicEndpointFrom_replicate_pos, Function.update]
      omega
  have he2 : cubicEndpointFrom x2 s2 = x3 := by
    ext i
    fin_cases i <;> simp [x2, x3, s2, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  have he3 : cubicEndpointFrom x3 s3 = x4 := by
    ext i
    fin_cases i <;> simp [x3, x4, s3, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  change (cubicWalkFrom x0 (s0 ++ (s1 ++ (s2 ++ (s3 ++ s4))))).edges.countP
    (squareEdgeCrossesFaceHorizontalRayBool
      (squareVertex (b : ℤ) (m : ℤ))) = 1
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [horizontalRayCount_cubicWalkFrom_replicate_horizontal,
    horizontalRayCount_cubicWalkFrom_replicate_vertical_pos,
    horizontalRayCount_cubicWalkFrom_replicate_horizontal,
    horizontalRayCount_cubicWalkFrom_replicate_vertical_neg,
    horizontalRayCount_cubicWalkFrom_replicate_horizontal]
  have hfillNat : a + (m + 1 - a) = m + 1 := by omega
  have hfillInt : (a : ℤ) + (m + 1 - a : ℕ) = (m + 1 : ℕ) := by
    exact_mod_cast hfillNat
  have haInt : (a : ℤ) ≤ m := by exact_mod_cast ha
  have hbInt : (b : ℤ) ≤ m := by exact_mod_cast hb
  simp [x0, s0, s1, s2, squareVertex,
    cubicEndpointFrom_replicate_pos, cubicEndpointFrom_replicate_neg,
    cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, Function.update,
    hfillInt, haInt, hbInt]

theorem squareWalk_horizontalRayCount_right_eq_zero_of_support_le
    {u v : SquareVertex} (w : squareGraph.Walk u v) (m : ℕ)
    (hbox : ∀ z ∈ w.support, z 0 ≤ m) :
    w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool
      (squareVertex (m : ℤ) 0)) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hbox x (w.fst_mem_support_of_mem_edges he)
      have hy := hbox y (w.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay, squareVertex]
      omega

theorem squareWalk_horizontalRayCount_top_eq_zero_of_support_le
    {u v : SquareVertex} (w : squareGraph.Walk u v) (m b : ℕ)
    (hbox : ∀ z ∈ w.support, z 1 ≤ m) :
    w.edges.countP (squareEdgeCrossesFaceHorizontalRayBool
      (squareVertex (b : ℤ) (m : ℤ))) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : squareGraph.Adj x y := w.adj_of_mem_edges he
      have hx := hbox x (w.fst_mem_support_of_mem_edges he)
      have hy := hbox y (w.snd_mem_support_of_mem_edges he)
      rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨i, rfl⟩
      fin_cases i <;>
        simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay, squareVertex,
          cubicStepFrom, cubicDirectionIncrement] at hx hy ⊢ <;>
        omega

/-- Alternating corner-to-boundary walks in a finite square have intersecting supports.  This is
the discrete Jordan-arc statement needed by Figure 7.14. -/
theorem squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top
    {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (p : squareGraph.Walk (squareVertex 0 0)
      (squareVertex (m : ℤ) (a : ℤ)))
    (q : squareGraph.Walk (squareVertex (m : ℤ) 0)
      (squareVertex (b : ℤ) (m : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  by_cases ha0 : a = 0
  · subst a
    exact ⟨squareVertex (m : ℤ) 0, p.end_mem_support, q.start_mem_support⟩
  have haPos : 0 < a := Nat.pos_of_ne_zero ha0
  by_contra hinter
  push Not at hinter
  let r := squareUpperExteriorClosureWalk m a ha
  let c : squareGraph.Walk (squareVertex 0 0) (squareVertex 0 0) := p.append r
  have hqdisj : ∀ z ∈ q.support, z ∉ c.support := by
    intro z hzq hzc
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzc
    rcases hzc with hzp | hzr
    · exact hinter z hzp hzq
    · rcases mem_squareUpperExteriorClosureWalk_support ha hzr with
        hzend | hzorigin | hzneg | hzright | hztop
      · exact hinter z (hzend ▸ p.end_mem_support) hzq
      · exact hinter z (hzorigin ▸ p.start_mem_support) hzq
      · exact (not_lt_of_ge (hqbox z hzq).1) hzneg
      · exact (not_lt_of_ge (hqbox z hzq).2.1) hzright
      · exact (not_lt_of_ge (hqbox z hzq).2.2.2) hztop
  have hparity := closedSquareWalkFaceParity_eq_along_disjoint_walk c q hqdisj
  have hleft : closedSquareWalkFaceParity c (squareVertex (m : ℤ) 0) = 0 := by
    unfold closedSquareWalkFaceParity c
    simp only [r, SimpleGraph.Walk.edges_append, List.countP_append]
    rw [squareWalk_horizontalRayCount_right_eq_zero_of_support_le p m
      (fun z hz ↦ (hpbox z hz).2.1),
      squareUpperExteriorClosureWalk_bottomRight_rayCount_eq_zero ha haPos]
  have hright :
      closedSquareWalkFaceParity c (squareVertex (b : ℤ) (m : ℤ)) = 1 := by
    unfold closedSquareWalkFaceParity c
    simp only [r, SimpleGraph.Walk.edges_append, List.countP_append]
    rw [squareWalk_horizontalRayCount_top_eq_zero_of_support_le p m b
      (fun z hz ↦ (hpbox z hz).2.2.2),
      squareUpperExteriorClosureWalk_top_rayCount_eq_one ha hb]
  rw [hleft, hright] at hparity
  norm_num at hparity

/-! ### Cyclic square symmetries -/

/-- Clockwise quarter-turn of `[0,m]²`: `(x,y) ↦ (y,m-x)`. -/
def squareQuarterTurn (m : ℕ) (x : SquareVertex) : SquareVertex :=
  squareVertex (x 1) ((m : ℤ) - x 0)

@[simp] theorem squareQuarterTurn_zero (m : ℕ) (x : SquareVertex) :
    squareQuarterTurn m x 0 = x 1 := by simp [squareQuarterTurn]

@[simp] theorem squareQuarterTurn_one (m : ℕ) (x : SquareVertex) :
    squareQuarterTurn m x 1 = (m : ℤ) - x 0 := by simp [squareQuarterTurn]

theorem squareQuarterTurn_injective (m : ℕ) : Function.Injective (squareQuarterTurn m) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  ext i
  fin_cases i <;> simp at h0 h1 ⊢ <;> omega

/-- The quarter-turn as a square-graph homomorphism. -/
def squareQuarterTurnHom (m : ℕ) : squareGraph →g squareGraph where
  toFun := squareQuarterTurn m
  map_rel' := by
    intro x y hxy
    rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨i, rfl⟩
    rcases i with ⟨i, b⟩
    fin_cases i <;> cases b
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨1, by decide⟩, true), ?_⟩
      ext j
      fin_cases j <;> simp [squareQuarterTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨1, by decide⟩, false), ?_⟩
      ext j
      fin_cases j <;> simp [squareQuarterTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨0, by decide⟩, false), ?_⟩
      ext j
      fin_cases j <;> simp [squareQuarterTurn, cubicStepFrom, cubicDirectionIncrement]
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨0, by decide⟩, true), ?_⟩
      ext j
      fin_cases j <;> simp [squareQuarterTurn, cubicStepFrom, cubicDirectionIncrement]

/-- Half-turn of `[0,m]²`: `(x,y) ↦ (m-x,m-y)`. -/
def squareHalfTurn (m : ℕ) (x : SquareVertex) : SquareVertex :=
  squareVertex ((m : ℤ) - x 0) ((m : ℤ) - x 1)

@[simp] theorem squareHalfTurn_zero (m : ℕ) (x : SquareVertex) :
    squareHalfTurn m x 0 = (m : ℤ) - x 0 := by simp [squareHalfTurn]

@[simp] theorem squareHalfTurn_one (m : ℕ) (x : SquareVertex) :
    squareHalfTurn m x 1 = (m : ℤ) - x 1 := by simp [squareHalfTurn]

theorem squareHalfTurn_injective (m : ℕ) : Function.Injective (squareHalfTurn m) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  ext i
  fin_cases i <;> simp at h0 h1 ⊢ <;> omega

/-- The half-turn as a square-graph homomorphism. -/
def squareHalfTurnHom (m : ℕ) : squareGraph →g squareGraph where
  toFun := squareHalfTurn m
  map_rel' := by
    intro x y hxy
    rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨i, rfl⟩
    rcases i with ⟨i, b⟩
    fin_cases i <;> cases b
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨0, by decide⟩, true), ?_⟩
      ext j
      fin_cases j <;> simp [squareHalfTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨0, by decide⟩, false), ?_⟩
      ext j
      fin_cases j <;> simp [squareHalfTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨1, by decide⟩, true), ?_⟩
      ext j
      fin_cases j <;> simp [squareHalfTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega
    · rw [cubicGraph_adj_iff_exists_stepFrom]
      refine ⟨(⟨1, by decide⟩, false), ?_⟩
      ext j
      fin_cases j <;> simp [squareHalfTurn, cubicStepFrom, cubicDirectionIncrement] <;> omega

theorem walk_support_inter_of_map_support_inter
    {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G')
    (hf : Function.Injective f) {u₁ v₁ u₂ v₂ : V}
    (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂)
    (h : ∃ z, z ∈ (p.map f).support ∧ z ∈ (q.map f).support) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  rcases h with ⟨z, hzp, hzq⟩
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzp hzq
  rcases hzp with ⟨x, hxp, rfl⟩
  rcases hzq with ⟨y, hyq, hxy⟩
  have : y = x := hf hxy
  subst y
  exact ⟨x, hxp, hyq⟩

/-- The quarter-turned cyclic instance: a bottom-right-to-top walk meets a
top-right-to-left walk. -/
theorem squareWalk_support_inter_of_bottomRight_top_and_topRight_left
    {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (p : squareGraph.Walk (squareVertex (m : ℤ) 0)
      (squareVertex (a : ℤ) (m : ℤ)))
    (q : squareGraph.Walk (squareVertex (m : ℤ) (m : ℤ))
      (squareVertex 0 (b : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let f := squareQuarterTurnHom m
  have hps : f (squareVertex (m : ℤ) 0) = squareVertex 0 0 := by
    ext i
    fin_cases i <;> simp [f, squareQuarterTurnHom, squareQuarterTurn]
  have hpe : f (squareVertex (a : ℤ) (m : ℤ)) =
      squareVertex (m : ℤ) ((m - a : ℕ) : ℤ) := by
    ext i
    fin_cases i <;> simp [f, squareQuarterTurnHom, squareQuarterTurn, Nat.cast_sub ha]
  have hqs : f (squareVertex (m : ℤ) (m : ℤ)) = squareVertex (m : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [f, squareQuarterTurnHom, squareQuarterTurn]
  have hqe : f (squareVertex 0 (b : ℤ)) =
      squareVertex (b : ℤ) (m : ℤ) := by
    ext i
    fin_cases i <;> simp [f, squareQuarterTurnHom, squareQuarterTurn]
  let p' := (p.map f).copy hps hpe
  let q' := (q.map f).copy hqs hqe
  have hp' : ∀ z ∈ p'.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    simp only [p', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
    rw [List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hpbox x hx
    simp [f, squareQuarterTurnHom, squareQuarterTurn]
    omega
  have hq' : ∀ z ∈ q'.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    simp only [q', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
    rw [List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hqbox x hx
    simp [f, squareQuarterTurnHom, squareQuarterTurn]
    omega
  have hinter' := squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top
    (Nat.sub_le m a) hb p' q' hp' hq'
  have hinter : ∃ z, z ∈ (p.map f).support ∧ z ∈ (q.map f).support := by
    simpa [p', q'] using hinter'
  exact walk_support_inter_of_map_support_inter f (squareQuarterTurn_injective m) p q hinter

/-- The half-turned cyclic instance: a top-right-to-left walk meets a top-left-to-bottom walk. -/
theorem squareWalk_support_inter_of_topRight_left_and_topLeft_bottom
    {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (p : squareGraph.Walk (squareVertex (m : ℤ) (m : ℤ))
      (squareVertex 0 (a : ℤ)))
    (q : squareGraph.Walk (squareVertex 0 (m : ℤ))
      (squareVertex (b : ℤ) 0))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let f := squareHalfTurnHom m
  have hps : f (squareVertex (m : ℤ) (m : ℤ)) = squareVertex 0 0 := by
    ext i
    fin_cases i <;> simp [f, squareHalfTurnHom, squareHalfTurn]
  have hpe : f (squareVertex 0 (a : ℤ)) =
      squareVertex (m : ℤ) ((m - a : ℕ) : ℤ) := by
    ext i
    fin_cases i <;> simp [f, squareHalfTurnHom, squareHalfTurn, Nat.cast_sub ha]
  have hqs : f (squareVertex 0 (m : ℤ)) = squareVertex (m : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [f, squareHalfTurnHom, squareHalfTurn]
  have hqe : f (squareVertex (b : ℤ) 0) =
      squareVertex ((m - b : ℕ) : ℤ) (m : ℤ) := by
    ext i
    fin_cases i <;> simp [f, squareHalfTurnHom, squareHalfTurn, Nat.cast_sub hb]
  let p' := (p.map f).copy hps hpe
  let q' := (q.map f).copy hqs hqe
  have hp' : ∀ z ∈ p'.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    simp only [p', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
    rw [List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hpbox x hx
    simp [f, squareHalfTurnHom, squareHalfTurn]
    omega
  have hq' : ∀ z ∈ q'.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    simp only [q', SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
    rw [List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have h := hqbox x hx
    simp [f, squareHalfTurnHom, squareHalfTurn]
    omega
  have hinter' := squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top
    (Nat.sub_le m a) (Nat.sub_le m b) p' q' hp' hq'
  have hinter : ∃ z, z ∈ (p.map f).support ∧ z ∈ (q.map f).support := by
    simpa [p', q'] using hinter'
  exact walk_support_inter_of_map_support_inter f (squareHalfTurn_injective m) p q hinter

end Percolation
