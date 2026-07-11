import Percolation.Planar.Basic

/-!
# Projection of cubic-lattice walks to the first two coordinates

The slab arguments in Grimmett's equation (7.83) project paths in
`[0,m]² × [0,L]^(d-2)` onto the planar square.  A transverse cubic edge projects to a stutter,
so the ordinary graph-homomorphism map on walks is not applicable.  This file gives the exact
contraction map and records that its support is precisely the coordinatewise image of the
original support.
-/

namespace Percolation

/-- Restrict a cubic-lattice vertex to its first `m` coordinates. -/
def cubicRestrict {m d : ℕ} (hmd : m ≤ d) (x : Cubic d) : Cubic m :=
  fun i ↦ x (Fin.castLE hmd i)

@[simp]
theorem cubicRestrict_apply {m d : ℕ} (hmd : m ≤ d) (x : Cubic d) (i : Fin m) :
    cubicRestrict hmd x i = x (Fin.castLE hmd i) :=
  rfl

@[simp]
theorem cubicRestrict_cubicEmbed {m d : ℕ} (hmd : m ≤ d) (x : Cubic m) :
    cubicRestrict hmd (cubicEmbed m d x) = x := by
  ext i
  simp [cubicRestrict]

/-- Projection to the first two coordinates. -/
abbrev cubicFirstTwoProjection {d : ℕ} (hd : 2 ≤ d) (x : Cubic d) : SquareVertex :=
  cubicRestrict hd x

/-- A cubic edge either projects to a square edge or contracts to one planar vertex. -/
theorem cubicFirstTwoProjection_adj_or_eq {d : ℕ} (hd : 2 ≤ d) {x y : Cubic d}
    (hxy : (cubicGraph d).Adj x y) :
    squareGraph.Adj (cubicFirstTwoProjection hd x) (cubicFirstTwoProjection hd y) ∨
      cubicFirstTwoProjection hd x = cubicFirstTwoProjection hd y := by
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨⟨i, b⟩, rfl⟩
  by_cases hi : i.val < 2
  · let j : Fin 2 := ⟨i.val, hi⟩
    left
    rw [show cubicFirstTwoProjection hd (cubicStepFrom x (i, b)) =
        cubicStepFrom (cubicFirstTwoProjection hd x) (j, b) by
      ext k
      by_cases hki : Fin.castLE hd k = i
      · have hkj : k = j := by
          ext
          simpa [j] using congrArg Fin.val hki
        subst k
        change Function.update x i (x i + cubicDirectionIncrement (i, b))
            (Fin.castLE hd j) =
          Function.update (fun k : Fin 2 ↦ x (Fin.castLE hd k)) j
            (x (Fin.castLE hd j) + cubicDirectionIncrement (j, b)) j
        rw [hki]
        simp [cubicDirectionIncrement]
      · have hkj : k ≠ j := by
          intro h
          subst k
          apply hki
          ext
          simp [j]
        simp [cubicFirstTwoProjection, cubicRestrict, cubicStepFrom,
          cubicDirectionIncrement, hki, hkj]]
    exact cubicGraph_adj_stepFrom _ _
  · right
    ext j
    have hji : Fin.castLE hd j ≠ i := by
      intro h
      apply hi
      rw [← h]
      exact j.isLt
    simp [cubicFirstTwoProjection, cubicRestrict, cubicStepFrom, hji]

/-- If a projected cubic edge does not contract, it is a square-lattice edge. -/
theorem cubicFirstTwoProjection_adj_of_ne {d : ℕ} (hd : 2 ≤ d) {x y : Cubic d}
    (hxy : (cubicGraph d).Adj x y)
    (hne : cubicFirstTwoProjection hd x ≠ cubicFirstTwoProjection hd y) :
    squareGraph.Adj (cubicFirstTwoProjection hd x) (cubicFirstTwoProjection hd y) :=
  (cubicFirstTwoProjection_adj_or_eq hd hxy).resolve_right hne

/-- Project a cubic walk to the square lattice, deleting precisely the transverse stutters. -/
def projectCubicWalkFirstTwo {d : ℕ} (hd : 2 ≤ d) {x y : Cubic d} :
    (cubicGraph d).Walk x y →
      squareGraph.Walk (cubicFirstTwoProjection hd x) (cubicFirstTwoProjection hd y)
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ u v z huv w =>
      if h : cubicFirstTwoProjection hd u = cubicFirstTwoProjection hd v then
        (projectCubicWalkFirstTwo hd w).copy h.symm rfl
      else
        .cons (cubicFirstTwoProjection_adj_of_ne hd huv h)
          (projectCubicWalkFirstTwo hd w)

@[simp]
theorem projectCubicWalkFirstTwo_nil {d : ℕ} (hd : 2 ≤ d) (x : Cubic d) :
    projectCubicWalkFirstTwo hd
      (SimpleGraph.Walk.nil : (cubicGraph d).Walk x x) = SimpleGraph.Walk.nil :=
  rfl

/-- The contracted planar walk visits exactly the projections of the vertices visited by the
original cubic walk. -/
theorem mem_projectCubicWalkFirstTwo_support_iff {d : ℕ} (hd : 2 ≤ d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) (z : SquareVertex) :
    z ∈ (projectCubicWalkFirstTwo hd w).support ↔
      ∃ u ∈ w.support, cubicFirstTwoProjection hd u = z := by
  induction w with
  | nil => simp [eq_comm]
  | @cons u v z huv w ih =>
      by_cases h : cubicFirstTwoProjection hd u = cubicFirstTwoProjection hd v
      · simp only [projectCubicWalkFirstTwo, h, ↓reduceDIte,
          SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons, List.mem_cons]
        rw [ih]
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ⟨a, Or.inr ha, rfl⟩
        · rintro ⟨a, rfl | ha, rfl⟩
          · exact ⟨v, w.start_mem_support, h.symm⟩
          · exact ⟨a, ha, rfl⟩
      · simp only [projectCubicWalkFirstTwo, h, ↓reduceDIte,
          SimpleGraph.Walk.support_cons, List.mem_cons]
        rw [ih]
        constructor
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨u, Or.inl rfl, rfl⟩
          · exact ⟨a, Or.inr ha, rfl⟩
        · rintro ⟨a, rfl | ha, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨a, ha, rfl⟩

/-- Two projected supports meet exactly when the original walks contain vertices agreeing in
their first two coordinates. -/
theorem projectCubicWalkFirstTwo_support_inter_iff {d : ℕ} (hd : 2 ≤ d)
    {x₁ y₁ x₂ y₂ : Cubic d} (w₁ : (cubicGraph d).Walk x₁ y₁)
    (w₂ : (cubicGraph d).Walk x₂ y₂) :
    (∃ z, z ∈ (projectCubicWalkFirstTwo hd w₁).support ∧
        z ∈ (projectCubicWalkFirstTwo hd w₂).support) ↔
      ∃ u ∈ w₁.support, ∃ v ∈ w₂.support,
        ∀ i : Fin d, i.val < 2 → u i = v i := by
  constructor
  · rintro ⟨z, hz₁, hz₂⟩
    rw [mem_projectCubicWalkFirstTwo_support_iff] at hz₁ hz₂
    obtain ⟨u, hu, huzu⟩ := hz₁
    obtain ⟨v, hv, hvz⟩ := hz₂
    refine ⟨u, hu, v, hv, ?_⟩
    intro i hi
    let j : Fin 2 := ⟨i.val, hi⟩
    have hcoord := congrFun (huzu.trans hvz.symm) j
    simpa [cubicFirstTwoProjection, cubicRestrict, j] using hcoord
  · rintro ⟨u, hu, v, hv, huv⟩
    let z := cubicFirstTwoProjection hd u
    refine ⟨z, (mem_projectCubicWalkFirstTwo_support_iff hd w₁ z).2
      ⟨u, hu, rfl⟩, (mem_projectCubicWalkFirstTwo_support_iff hd w₂ z).2 ⟨v, hv, ?_⟩⟩
    change cubicFirstTwoProjection hd v = cubicFirstTwoProjection hd u
    apply funext
    intro j
    exact (huv (Fin.castLE hd j) j.isLt).symm

end Percolation
