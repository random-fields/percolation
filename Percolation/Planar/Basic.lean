import Percolation.Bernoulli.Basic

/-!
# Planar percolation scaffold

The planar layer will host dual graphs, crossing events, RSW-style inputs, and the square-lattice
bond-percolation threshold theorem.

The first production slice below encodes the square lattice and its shifted dual lattice
combinatorially. A dual vertex is represented by the integer coordinates of the lower-left primal
face corner, i.e. the actual geometric point `(i + 1/2, j + 1/2)` is encoded as `(i, j)`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval

/-- A scaffold for planar dual graph data. Production work should use Mathlib graph embeddings
or a project-specific planar-lattice API after design review. -/
structure PlanarDualPair (V Vd : Type u) where
  primal : BaseGraph V
  dual : BaseGraph Vd
  Crosses : V → V → Vd → Vd → Prop

/-- Vertices of the square lattice. -/
abbrev SquareVertex := Cubic 2

/-- The nearest-neighbour square lattice graph. -/
abbrev squareGraph : SimpleGraph SquareVertex := cubicGraph 2

/-- Bonds of the square lattice. -/
abbrev SquareEdge := CubicEdge 2

/-- A square-lattice vertex from its two integer coordinates. -/
def squareVertex (x y : ℤ) : SquareVertex :=
  fun i ↦ if i = 0 then x else y

@[simp]
theorem squareVertex_zero (x y : ℤ) : squareVertex x y 0 = x := by
  simp [squareVertex]

@[simp]
theorem squareVertex_one (x y : ℤ) : squareVertex x y 1 = y := by
  simp [squareVertex]

@[simp]
theorem squareVertex_eta (x : SquareVertex) : squareVertex (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp [squareVertex]

theorem squareVertex_injective : Function.Injective (fun p : ℤ × ℤ ↦ squareVertex p.1 p.2) := by
  intro a b h
  ext <;> first | exact congrFun h 0 | exact congrFun h 1

/-- The embedding of integer coordinate pairs as square-lattice vertices. -/
def squareVertexEmbedding : ℤ × ℤ ↪ SquareVertex where
  toFun := fun p ↦ squareVertex p.1 p.2
  inj' := squareVertex_injective

@[simp]
theorem squareVertex_zero_zero : squareVertex 0 0 = (cubicOrigin : SquareVertex) := by
  ext i
  by_cases hi : i = 0 <;> simp [squareVertex, cubicOrigin, hi]

/-- Vertices in Grimmett's box `B(m) = [-m,m]^2 ∩ ℤ²`. -/
noncomputable def squareBoxVertices (m : ℕ) : Finset SquareVertex :=
  ((Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)).product
    (Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ))).map squareVertexEmbedding

/-- Coordinate membership in the finite square box `B(m)`. -/
theorem mem_squareBoxVertices_iff (m : ℕ) (x y : ℤ) :
    squareVertex x y ∈ squareBoxVertices m ↔
      x ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) ∧
        y ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨p, hp, hp_eq⟩
    have hp1 : p.1 = x := by
      have := congrFun hp_eq 0
      simpa [squareVertex] using this
    have hp2 : p.2 = y := by
      have := congrFun hp_eq 1
      simpa [squareVertex] using this
    have hp' : p.1 ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) ∧
        p.2 ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := by
      simpa [squareBoxVertices] using hp
    simpa [hp1, hp2] using hp'
  · intro h
    exact Finset.mem_map.mpr ⟨(x, y), by simpa [squareBoxVertices] using h, rfl⟩

/-- Coordinate membership for an arbitrary square-lattice vertex in Grimmett's box. -/
theorem mem_squareBoxVertices_iff_coords (m : ℕ) (x : SquareVertex) :
    x ∈ squareBoxVertices m ↔
      x 0 ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) ∧
        x 1 ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := by
  nth_rewrite 1 [← squareVertex_eta x]
  exact mem_squareBoxVertices_iff m (x 0) (x 1)

/-- Square boxes are monotone in their radius. -/
theorem squareBoxVertices_mono {m n : ℕ} (hmn : m ≤ n) :
    (squareBoxVertices m : Set SquareVertex) ⊆ squareBoxVertices n := by
  intro x hx
  change x ∈ squareBoxVertices n
  change x ∈ squareBoxVertices m at hx
  rw [mem_squareBoxVertices_iff_coords] at hx ⊢
  have hx0 := hx.1
  have hx1 := hx.2
  rw [Finset.mem_Icc] at hx0 hx1
  constructor <;> rw [Finset.mem_Icc] <;> omega

/-- A nearest-neighbour step from `B(m)` lands in the one-step enlarged box `B(m+1)`. -/
theorem squareBox_adj_mem_succ {m : ℕ} {x y : SquareVertex}
    (hx : x ∈ squareBoxVertices m) (hxy : squareGraph.Adj x y) :
    y ∈ squareBoxVertices (m + 1) := by
  rw [mem_squareBoxVertices_iff_coords] at hx ⊢
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  have hx0 := hx.1
  have hx1 := hx.2
  rw [Finset.mem_Icc] at hx0 hx1
  constructor <;> rw [Finset.mem_Icc]
  · have hup := cubicStepFrom_coord_le_add_one x a (0 : Fin 2)
    have hdown := cubicStepFrom_coord_sub_one_le x a (0 : Fin 2)
    constructor <;> omega
  · have hup := cubicStepFrom_coord_le_add_one x a (1 : Fin 2)
    have hdown := cubicStepFrom_coord_sub_one_le x a (1 : Fin 2)
    constructor <;> omega

/-- If an integer lies in `[-m,m]`, its absolute value is at most `m`. -/
theorem natAbs_le_of_mem_Icc_neg_nat {m : ℕ} {a : ℤ}
    (ha : a ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)) :
    a.natAbs ≤ m := by
  rw [Finset.mem_Icc] at ha
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact abs_le.mpr ha

/-- The origin belongs to every square box. -/
theorem cubicOrigin_mem_squareBoxVertices (m : ℕ) :
    (cubicOrigin : SquareVertex) ∈ squareBoxVertices m := by
  rw [← squareVertex_zero_zero, mem_squareBoxVertices_iff]
  simp

/-- The positive horizontal Manhattan segment from the origin to `(n,0)` stays inside `B(m)` when
`n ≤ m`. This is the first concrete connector used by Grimmett's box-open event `G_m`. -/
theorem exists_squareBoxHorizontalPosConnector (m n : ℕ) (hn : n ≤ m) :
    ∃ c : squareGraph.Walk cubicOrigin (squareVertex (n : ℤ) 0),
      ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
  let steps : List (CubicDirection 2) := List.replicate n ((0 : Fin 2), true)
  let w : squareGraph.Walk cubicOrigin (cubicEndpointFrom cubicOrigin steps) :=
    cubicWalkFrom cubicOrigin steps
  have hend : cubicEndpointFrom cubicOrigin steps = squareVertex (n : ℤ) 0 := by
    dsimp [steps]
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i <;> simp [squareVertex, cubicOrigin]
  let c : squareGraph.Walk cubicOrigin (squareVertex (n : ℤ) 0) := w.copy rfl hend
  refine ⟨c, ?_⟩
  intro z hz
  have hzsupport : z ∈ w.support := by
    simpa [c, w] using hz
  have hzvertices :
      z ∈ cubicVerticesFrom (cubicOrigin : SquareVertex) steps := by
    simpa [w, steps] using hzsupport
  rw [mem_squareBoxVertices_iff_coords]
  constructor
  · rw [Finset.mem_Icc]
    have hbetween :=
      cubicVerticesFrom_replicate_pos_coord_between (cubicOrigin : SquareVertex)
        (0 : Fin 2) n hzvertices
    constructor
    · have : (0 : ℤ) ≤ z 0 := by
        simpa [cubicOrigin] using hbetween.1
      omega
    · have : z 0 ≤ (n : ℤ) := by
        simpa [cubicOrigin] using hbetween.2
      omega
  · have hcoord :
        z 1 = (cubicOrigin : SquareVertex) 1 :=
      cubicVerticesFrom_replicate_pos_coord_eq_of_ne (cubicOrigin : SquareVertex)
        (0 : Fin 2) (1 : Fin 2) n (by decide) hzvertices
    rw [Finset.mem_Icc]
    constructor <;> simp [hcoord, cubicOrigin]

/-- The negative horizontal Manhattan segment from the origin to `(-n,0)` stays inside `B(m)` when
`n ≤ m`. -/
theorem exists_squareBoxHorizontalNegConnector (m n : ℕ) (hn : n ≤ m) :
    ∃ c : squareGraph.Walk cubicOrigin (squareVertex (-(n : ℤ)) 0),
      ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
  let steps : List (CubicDirection 2) := List.replicate n ((0 : Fin 2), false)
  let w : squareGraph.Walk cubicOrigin (cubicEndpointFrom cubicOrigin steps) :=
    cubicWalkFrom cubicOrigin steps
  have hend : cubicEndpointFrom cubicOrigin steps = squareVertex (-(n : ℤ)) 0 := by
    dsimp [steps]
    rw [cubicEndpointFrom_replicate_neg]
    ext i
    fin_cases i <;> simp [squareVertex, cubicOrigin]
  let c : squareGraph.Walk cubicOrigin (squareVertex (-(n : ℤ)) 0) := w.copy rfl hend
  refine ⟨c, ?_⟩
  intro z hz
  have hzsupport : z ∈ w.support := by
    simpa [c, w] using hz
  have hzvertices :
      z ∈ cubicVerticesFrom (cubicOrigin : SquareVertex) steps := by
    simpa [w, steps] using hzsupport
  rw [mem_squareBoxVertices_iff_coords]
  constructor
  · rw [Finset.mem_Icc]
    have hbetween :=
      cubicVerticesFrom_replicate_neg_coord_between (cubicOrigin : SquareVertex)
        (0 : Fin 2) n hzvertices
    constructor
    · have : -(n : ℤ) ≤ z 0 := by
        simpa [cubicOrigin] using hbetween.1
      omega
    · have : z 0 ≤ (0 : ℤ) := by
        simpa [cubicOrigin] using hbetween.2
      omega
  · have hcoord :
        z 1 = (cubicOrigin : SquareVertex) 1 :=
      cubicVerticesFrom_replicate_neg_coord_eq_of_ne (cubicOrigin : SquareVertex)
        (0 : Fin 2) (1 : Fin 2) n (by decide) hzvertices
    rw [Finset.mem_Icc]
    constructor <;> simp [hcoord, cubicOrigin]

/-- The positive vertical Manhattan segment from `(a,0)` to `(a,n)` stays inside `B(m)` when
`a ∈ [-m,m]` and `n ≤ m`. -/
theorem exists_squareBoxVerticalPosConnectorFrom (m n : ℕ) {a : ℤ}
    (ha : a ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)) (hn : n ≤ m) :
    ∃ c : squareGraph.Walk (squareVertex a 0) (squareVertex a (n : ℤ)),
      ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
  let start : SquareVertex := squareVertex a 0
  let steps : List (CubicDirection 2) := List.replicate n ((1 : Fin 2), true)
  let w : squareGraph.Walk start (cubicEndpointFrom start steps) :=
    cubicWalkFrom start steps
  have hend : cubicEndpointFrom start steps = squareVertex a (n : ℤ) := by
    dsimp [steps, start]
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i <;> simp [squareVertex]
  let c : squareGraph.Walk (squareVertex a 0) (squareVertex a (n : ℤ)) :=
    w.copy rfl hend
  refine ⟨c, ?_⟩
  intro z hz
  have hzsupport : z ∈ w.support := by
    simpa [c, w, start] using hz
  have hzvertices : z ∈ cubicVerticesFrom start steps := by
    simpa [w, steps] using hzsupport
  rw [mem_squareBoxVertices_iff_coords]
  constructor
  · have hcoord : z 0 = start 0 :=
      cubicVerticesFrom_replicate_pos_coord_eq_of_ne start
        (1 : Fin 2) (0 : Fin 2) n (by decide) hzvertices
    simpa [start, squareVertex, hcoord] using ha
  · rw [Finset.mem_Icc]
    have hbetween :=
      cubicVerticesFrom_replicate_pos_coord_between start (1 : Fin 2) n hzvertices
    constructor
    · have : (0 : ℤ) ≤ z 1 := by
        simpa [start, squareVertex] using hbetween.1
      omega
    · have : z 1 ≤ (n : ℤ) := by
        simpa [start, squareVertex] using hbetween.2
      omega

/-- The negative vertical Manhattan segment from `(a,0)` to `(a,-n)` stays inside `B(m)` when
`a ∈ [-m,m]` and `n ≤ m`. -/
theorem exists_squareBoxVerticalNegConnectorFrom (m n : ℕ) {a : ℤ}
    (ha : a ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)) (hn : n ≤ m) :
    ∃ c : squareGraph.Walk (squareVertex a 0) (squareVertex a (-(n : ℤ))),
      ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
  let start : SquareVertex := squareVertex a 0
  let steps : List (CubicDirection 2) := List.replicate n ((1 : Fin 2), false)
  let w : squareGraph.Walk start (cubicEndpointFrom start steps) :=
    cubicWalkFrom start steps
  have hend : cubicEndpointFrom start steps = squareVertex a (-(n : ℤ)) := by
    dsimp [steps, start]
    rw [cubicEndpointFrom_replicate_neg]
    ext i
    fin_cases i <;> simp [squareVertex]
  let c : squareGraph.Walk (squareVertex a 0) (squareVertex a (-(n : ℤ))) :=
    w.copy rfl hend
  refine ⟨c, ?_⟩
  intro z hz
  have hzsupport : z ∈ w.support := by
    simpa [c, w, start] using hz
  have hzvertices : z ∈ cubicVerticesFrom start steps := by
    simpa [w, steps] using hzsupport
  rw [mem_squareBoxVertices_iff_coords]
  constructor
  · have hcoord : z 0 = start 0 :=
      cubicVerticesFrom_replicate_neg_coord_eq_of_ne start
        (1 : Fin 2) (0 : Fin 2) n (by decide) hzvertices
    simpa [start, squareVertex, hcoord] using ha
  · rw [Finset.mem_Icc]
    have hbetween :=
      cubicVerticesFrom_replicate_neg_coord_between start (1 : Fin 2) n hzvertices
    constructor
    · have : -(n : ℤ) ≤ z 1 := by
        simpa [start, squareVertex] using hbetween.1
      omega
    · have : z 1 ≤ (0 : ℤ) := by
        simpa [start, squareVertex] using hbetween.2
      omega

/-- Every vertex in Grimmett's square box is connected to the origin by a square-lattice walk
whose vertices all remain in the box. This is the concrete Manhattan connector used by the
box-open event `G_m`. -/
theorem exists_squareBoxConnector (m : ℕ) {x : SquareVertex}
    (hx : x ∈ squareBoxVertices m) :
    ∃ c : squareGraph.Walk cubicOrigin x,
      ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
  let a : ℤ := x 0
  let b : ℤ := x 1
  have hxcoords := (mem_squareBoxVertices_iff_coords m x).mp hx
  have ha : a ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := by
    simpa [a] using hxcoords.1
  have hb : b ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := by
    simpa [b] using hxcoords.2
  have hHorizontal :
      ∃ c : squareGraph.Walk cubicOrigin (squareVertex a 0),
        ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
    by_cases ha_nonneg : 0 ≤ a
    · have hn : a.natAbs ≤ m := natAbs_le_of_mem_Icc_neg_nat ha
      rcases exists_squareBoxHorizontalPosConnector m a.natAbs hn with ⟨c₀, hc₀⟩
      have hendpoint : squareVertex (a.natAbs : ℤ) 0 = squareVertex a 0 := by
        ext i
        fin_cases i <;> simp [Int.natAbs_of_nonneg ha_nonneg]
      let c : squareGraph.Walk cubicOrigin (squareVertex a 0) := c₀.copy rfl hendpoint
      refine ⟨c, ?_⟩
      intro z hz
      exact hc₀ z (by simpa [c] using hz)
    · have ha_nonpos : a ≤ 0 := by omega
      have hn : a.natAbs ≤ m := natAbs_le_of_mem_Icc_neg_nat ha
      rcases exists_squareBoxHorizontalNegConnector m a.natAbs hn with ⟨c₀, hc₀⟩
      have hneg : -(a.natAbs : ℤ) = a := by
        have hnat : (a.natAbs : ℤ) = -a := by
          simpa [Int.natAbs_neg] using
            (Int.natAbs_of_nonneg (a := -a) (by omega : 0 ≤ -a))
        omega
      have hendpoint : squareVertex (-(a.natAbs : ℤ)) 0 = squareVertex a 0 := by
        ext i
        fin_cases i
        · exact hneg
        · simp
      let c : squareGraph.Walk cubicOrigin (squareVertex a 0) := c₀.copy rfl hendpoint
      refine ⟨c, ?_⟩
      intro z hz
      exact hc₀ z (by simpa [c] using hz)
  have hVertical :
      ∃ c : squareGraph.Walk (squareVertex a 0) (squareVertex a b),
        ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m := by
    by_cases hb_nonneg : 0 ≤ b
    · have hn : b.natAbs ≤ m := natAbs_le_of_mem_Icc_neg_nat hb
      rcases exists_squareBoxVerticalPosConnectorFrom m b.natAbs ha hn with ⟨c₀, hc₀⟩
      have hendpoint : squareVertex a (b.natAbs : ℤ) = squareVertex a b := by
        ext i
        fin_cases i <;> simp [Int.natAbs_of_nonneg hb_nonneg]
      let c : squareGraph.Walk (squareVertex a 0) (squareVertex a b) :=
        c₀.copy rfl hendpoint
      refine ⟨c, ?_⟩
      intro z hz
      exact hc₀ z (by simpa [c] using hz)
    · have hb_nonpos : b ≤ 0 := by omega
      have hn : b.natAbs ≤ m := natAbs_le_of_mem_Icc_neg_nat hb
      rcases exists_squareBoxVerticalNegConnectorFrom m b.natAbs ha hn with ⟨c₀, hc₀⟩
      have hneg : -(b.natAbs : ℤ) = b := by
        have hnat : (b.natAbs : ℤ) = -b := by
          simpa [Int.natAbs_neg] using
            (Int.natAbs_of_nonneg (a := -b) (by omega : 0 ≤ -b))
        omega
      have hendpoint : squareVertex a (-(b.natAbs : ℤ)) = squareVertex a b := by
        ext i
        fin_cases i
        · simp
        · exact hneg
      let c : squareGraph.Walk (squareVertex a 0) (squareVertex a b) :=
        c₀.copy rfl hendpoint
      refine ⟨c, ?_⟩
      intro z hz
      exact hc₀ z (by simpa [c] using hz)
  rcases hHorizontal with ⟨c₁, hc₁⟩
  rcases hVertical with ⟨c₂, hc₂⟩
  have htarget : squareVertex a b = x := by
    simp [a, b]
  let c : squareGraph.Walk cubicOrigin x := (c₁.append c₂).copy rfl htarget
  refine ⟨c, ?_⟩
  intro z hz
  have hzappend : z ∈ (c₁.append c₂).support := by
    simpa [c] using hz
  exact walk_append_support_subset hc₁ hc₂ z hzappend

/-- A square-lattice walk from `B(m)` to outside `B(m+n)` has length at least `n`. -/
theorem squareBox_exit_walk_length_ge {m n : ℕ} {x y : SquareVertex}
    (hx : x ∈ squareBoxVertices m) (hy : y ∉ squareBoxVertices (m + n))
    (q : squareGraph.Walk x y) :
    n ≤ q.length := by
  rw [mem_squareBoxVertices_iff_coords] at hx
  have hnot :
      ¬ (y 0 ∈ Finset.Icc (-(((m + n : ℕ) : ℤ))) ((m + n : ℕ) : ℤ) ∧
        y 1 ∈ Finset.Icc (-(((m + n : ℕ) : ℤ))) ((m + n : ℕ) : ℤ)) := by
    simpa [mem_squareBoxVertices_iff_coords] using hy
  have hx0 := hx.1
  have hx1 := hx.2
  rw [Finset.mem_Icc] at hx0 hx1
  by_cases hy0 :
      y 0 ∈ Finset.Icc (-(((m + n : ℕ) : ℤ))) ((m + n : ℕ) : ℤ)
  · have hy1 :
        y 1 ∉ Finset.Icc (-(((m + n : ℕ) : ℤ))) ((m + n : ℕ) : ℤ) := by
      intro hy1
      exact hnot ⟨hy0, hy1⟩
    rw [Finset.mem_Icc] at hy1
    have hcoord_up := cubicWalk_coord_le_start_add_length q (1 : Fin 2)
    have hcoord_down := cubicWalk_start_coord_le_end_add_length q (1 : Fin 2)
    omega
  · rw [Finset.mem_Icc] at hy0
    have hcoord_up := cubicWalk_coord_le_start_add_length q (0 : Fin 2)
    have hcoord_down := cubicWalk_start_coord_le_end_add_length q (0 : Fin 2)
    omega

/-- Vertices of the shifted dual square lattice, encoded by lower-left face coordinates. -/
abbrev DualSquareVertex := Cubic 2

/-- The shifted dual square lattice has the same nearest-neighbour adjacency in encoded
coordinates. -/
abbrev dualSquareGraph : SimpleGraph DualSquareVertex := cubicGraph 2

/-- Bonds of the shifted dual square lattice. -/
abbrev DualSquareEdge := CubicEdge 2

/-- The lower endpoint of the shifted-dual vertical edge crossing the positive horizontal ray at
integer coordinate `k`. -/
def dualPositiveXAxisLowerVertex (k : ℕ) : DualSquareVertex :=
  fun i ↦ if i = 0 then (k : ℤ) else -1

/-- The upper endpoint of the shifted-dual vertical edge crossing the positive horizontal ray at
integer coordinate `k`. -/
def dualPositiveXAxisUpperVertex (k : ℕ) : DualSquareVertex :=
  cubicStepFrom (dualPositiveXAxisLowerVertex k) (1, true)

@[simp]
theorem dualPositiveXAxisLowerVertex_zero (k : ℕ) :
    dualPositiveXAxisLowerVertex k 0 = (k : ℤ) := by
  simp [dualPositiveXAxisLowerVertex]

@[simp]
theorem dualPositiveXAxisLowerVertex_one (k : ℕ) :
    dualPositiveXAxisLowerVertex k 1 = -1 := by
  simp [dualPositiveXAxisLowerVertex]

@[simp]
theorem dualPositiveXAxisUpperVertex_zero (k : ℕ) :
    dualPositiveXAxisUpperVertex k 0 = (k : ℤ) := by
  simp [dualPositiveXAxisUpperVertex, dualPositiveXAxisLowerVertex, cubicStepFrom,
    cubicDirectionIncrement]

@[simp]
theorem dualPositiveXAxisUpperVertex_one (k : ℕ) :
    dualPositiveXAxisUpperVertex k 1 = 0 := by
  simp [dualPositiveXAxisUpperVertex, dualPositiveXAxisLowerVertex, cubicStepFrom,
    cubicDirectionIncrement]

/-- The shifted-dual vertical edge crossing the positive horizontal ray at integer coordinate
`k`. -/
def dualPositiveXAxisCrossingEdge (k : ℕ) : DualSquareEdge :=
  ⟨s(dualPositiveXAxisLowerVertex k, dualPositiveXAxisUpperVertex k), by
    rw [SimpleGraph.mem_edgeSet]
    exact cubicGraph_adj_stepFrom (dualPositiveXAxisLowerVertex k) (1, true)⟩

@[simp]
theorem dualPositiveXAxisCrossingEdge_coe (k : ℕ) :
    (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) =
      s(dualPositiveXAxisLowerVertex k, dualPositiveXAxisUpperVertex k) :=
  rfl

/-- The positive-axis crossing coordinate is determined by the lower dual endpoint. -/
theorem dualPositiveXAxisLowerVertex_injective :
    Function.Injective dualPositiveXAxisLowerVertex := by
  intro k l h
  have h0 : (k : ℤ) = (l : ℤ) := by
    simpa using congrFun h 0
  exact_mod_cast h0

/-- The positive-axis crossing coordinate is determined by the upper dual endpoint. -/
theorem dualPositiveXAxisUpperVertex_injective :
    Function.Injective dualPositiveXAxisUpperVertex := by
  intro k l h
  have h0 : (k : ℤ) = (l : ℤ) := by
    simpa using congrFun h 0
  exact_mod_cast h0

/-- The shifted-dual positive-axis crossing edge determines its coordinate. -/
theorem dualPositiveXAxisCrossingEdge_injective :
    Function.Injective dualPositiveXAxisCrossingEdge := by
  intro k l h
  have hsym : (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) =
      (dualPositiveXAxisCrossingEdge l : Sym2 DualSquareVertex) := by
    exact congrArg Subtype.val h
  simp [dualPositiveXAxisCrossingEdge_coe] at hsym
  rcases hsym with hsame | hswap
  · rcases hsame with ⟨hlower, _⟩
    exact dualPositiveXAxisLowerVertex_injective hlower
  · rcases hswap with ⟨hlower_upper, _⟩
    have h1 : (-1 : ℤ) = 0 := by
      simpa using congrFun hlower_upper 1
    omega

/-- The perpendicular coordinate axis in the square lattice. -/
def squarePerp (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

@[simp]
theorem squarePerp_zero : squarePerp 0 = 1 := by
  simp [squarePerp]

@[simp]
theorem squarePerp_one : squarePerp 1 = 0 := by
  simp [squarePerp]

/-- Rotating coordinate axes by a right angle twice returns to the original axis. -/
theorem squarePerp_involutive (i : Fin 2) : squarePerp (squarePerp i) = i := by
  by_cases hi : i = 0
  · subst hi
    simp
  · have hi1 : i = 1 := by
      ext
      omega
    subst hi1
    simp

/-- The perpendicular axis is different from the starting axis. -/
theorem squarePerp_ne (i : Fin 2) : squarePerp i ≠ i := by
  by_cases hi : i = 0
  · subst hi
    simp
  · have hi1 : i = 1 := by
      ext
      omega
    subst hi1
    simp

/-- A positively oriented square-lattice bond, represented by its lower endpoint in the chosen
axis. This is the convenient combinatorial model for the primal/dual crossing bijection; its
underlying undirected bond is `SquarePositiveEdge.toEdge`. -/
structure SquarePositiveEdge where
  base : SquareVertex
  axis : Fin 2

namespace SquarePositiveEdge

/-- The undirected square-lattice bond represented by a positive oriented bond. -/
def toEdge (e : SquarePositiveEdge) : SquareEdge :=
  ⟨s(e.base, cubicStepFrom e.base (e.axis, true)), by
    rw [SimpleGraph.mem_edgeSet]
    exact cubicGraph_adj_stepFrom e.base (e.axis, true)⟩

@[simp]
theorem toEdge_coe (e : SquarePositiveEdge) :
    (e.toEdge : Sym2 SquareVertex) = s(e.base, cubicStepFrom e.base (e.axis, true)) :=
  rfl

/-- Positive oriented square bonds have distinct underlying undirected square-lattice bonds. -/
theorem toEdge_injective : Function.Injective toEdge := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have hsym : s(x, cubicStepFrom x (i, true)) = s(y, cubicStepFrom y (j, true)) :=
    congrArg (fun e : SquareEdge ↦ (e : Sym2 SquareVertex)) h
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hsame | hswap
  · rcases hsame with ⟨rfl, hstep⟩
    have haxis : i = j := by
      by_contra hij
      have hcoord := congrFun hstep i
      simp [cubicStepFrom, cubicDirectionIncrement, hij] at hcoord
    subst haxis
    rfl
  · rcases hswap with ⟨rfl, hyx⟩
    by_cases hij : i = j
    · subst hij
      have hcoord := congrFun hyx i
      simp [cubicStepFrom, cubicDirectionIncrement] at hcoord
      omega
    · have hcoord := congrFun hyx i
      simp [cubicStepFrom, cubicDirectionIncrement, hij] at hcoord

/-- Every undirected square-lattice bond has a unique positive orientation. -/
theorem toEdge_surjective : Function.Surjective toEdge := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp he with ⟨a, rfl⟩
      rcases a with ⟨i, b⟩
      cases b
      · refine ⟨⟨cubicStepFrom x (i, false), i⟩, ?_⟩
        apply Subtype.ext
        dsimp [toEdge]
        rw [cubicStepFrom_neg_pos]
        exact Sym2.eq_swap
      · refine ⟨⟨x, i⟩, ?_⟩
        apply Subtype.ext
        rfl

/-- Positive oriented square bonds are equivalent to the undirected square-lattice edge subtype. -/
noncomputable def edgeEquiv : SquarePositiveEdge ≃ SquareEdge :=
  Equiv.ofBijective toEdge ⟨toEdge_injective, toEdge_surjective⟩

@[simp]
theorem edgeEquiv_apply (e : SquarePositiveEdge) : edgeEquiv e = e.toEdge :=
  rfl

end SquarePositiveEdge

/-- Positive oriented square-lattice bonds as embedded undirected bonds. -/
noncomputable def squarePositiveEdgeEmbedding : SquarePositiveEdge ↪ SquareEdge where
  toFun := SquarePositiveEdge.toEdge
  inj' := SquarePositiveEdge.toEdge_injective

@[simp]
theorem SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding
    (e : SquarePositiveEdge) :
    SquarePositiveEdge.edgeEquiv.symm (squarePositiveEdgeEmbedding e) = e := by
  apply SquarePositiveEdge.edgeEquiv.injective
  simp [SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeEmbedding]

/-- Positively oriented bonds whose two endpoints both lie in Grimmett's box `B(m)`. -/
noncomputable def squareBoxPositiveEdges (m : ℕ) : Finset SquarePositiveEdge :=
  (((squareBoxVertices m).product (Finset.univ : Finset (Fin 2))).filter
    (fun p : SquareVertex × Fin 2 ↦ cubicStepFrom p.1 (p.2, true) ∈ squareBoxVertices m)).map
      ⟨(fun p : SquareVertex × Fin 2 ↦ ⟨p.1, p.2⟩), by
        intro a b h
        apply Prod.ext
        · exact congrArg SquarePositiveEdge.base h
        · exact congrArg SquarePositiveEdge.axis h⟩

/-- The finite edge set of Grimmett's square box `B(m)`: all nearest-neighbour bonds with both
endpoints in the box. This is the finite support of the event `G_m` in the proof of Theorem
(1.10) and Equation (1.12). -/
noncomputable def squareBoxEdges (m : ℕ) : Finset SquareEdge :=
  (squareBoxPositiveEdges m).map squarePositiveEdgeEmbedding

/-- Membership in the positive oriented edge set of Grimmett's box is exactly membership of both
endpoints in the box. -/
theorem mem_squareBoxPositiveEdges_iff (m : ℕ) (e : SquarePositiveEdge) :
    e ∈ squareBoxPositiveEdges m ↔
      e.base ∈ squareBoxVertices m ∧
        cubicStepFrom e.base (e.axis, true) ∈ squareBoxVertices m := by
  rcases e with ⟨base, axis⟩
  constructor
  · intro h
    rw [squareBoxPositiveEdges, Finset.mem_map] at h
    rcases h with ⟨p, hp, hp_eq⟩
    rcases p with ⟨pbase, paxis⟩
    cases hp_eq
    simpa [Finset.mem_product] using hp
  · intro h
    rw [squareBoxPositiveEdges, Finset.mem_map]
    exact ⟨(base, axis), by simpa [Finset.mem_product] using h, rfl⟩

namespace SquarePositiveEdge

/-- A positive oriented bond belongs to the unoriented edge set of Grimmett's box exactly when
both of its endpoints lie in the box. -/
theorem toEdge_mem_squareBoxEdges_iff (m : ℕ) (e : SquarePositiveEdge) :
    e.toEdge ∈ squareBoxEdges m ↔
      e.base ∈ squareBoxVertices m ∧
        cubicStepFrom e.base (e.axis, true) ∈ squareBoxVertices m := by
  constructor
  · intro h
    rw [squareBoxEdges, Finset.mem_map] at h
    rcases h with ⟨e', he', heq⟩
    have heq' : e' = e := SquarePositiveEdge.toEdge_injective heq
    simpa [heq'] using (mem_squareBoxPositiveEdges_iff m e').mp he'
  · intro h
    rw [squareBoxEdges, Finset.mem_map]
    exact ⟨e, (mem_squareBoxPositiveEdges_iff m e).mpr h, rfl⟩

end SquarePositiveEdge

/-- Any signed unit step whose two endpoints lie in Grimmett's box has its unoriented bond in the
box edge set. -/
theorem signedStepEdge_mem_squareBoxEdges {m : ℕ} {x : SquareVertex} (i : Fin 2) (b : Bool)
    (hx : x ∈ squareBoxVertices m)
    (hx' : cubicStepFrom x (i, b) ∈ squareBoxVertices m) :
    (⟨s(x, cubicStepFrom x (i, b)), by
      rw [SimpleGraph.mem_edgeSet]
      exact cubicGraph_adj_stepFrom x (i, b)⟩ : SquareEdge) ∈ squareBoxEdges m := by
  cases b
  · let e : SquarePositiveEdge := ⟨cubicStepFrom x (i, false), i⟩
    have hemem : e.toEdge ∈ squareBoxEdges m := by
      rw [SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff]
      exact ⟨hx', by simpa [e, cubicStepFrom_neg_pos] using hx⟩
    have hedge :
        e.toEdge =
          (⟨s(x, cubicStepFrom x (i, false)), by
            rw [SimpleGraph.mem_edgeSet]
            exact cubicGraph_adj_stepFrom x (i, false)⟩ : SquareEdge) := by
      apply Subtype.ext
      dsimp [e, SquarePositiveEdge.toEdge]
      rw [cubicStepFrom_neg_pos]
      exact Sym2.eq_swap
    simpa [hedge] using hemem
  · let e : SquarePositiveEdge := ⟨x, i⟩
    have hemem : e.toEdge ∈ squareBoxEdges m := by
      rw [SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff]
      exact ⟨hx, hx'⟩
    have hedge :
        e.toEdge =
          (⟨s(x, cubicStepFrom x (i, true)), by
            rw [SimpleGraph.mem_edgeSet]
            exact cubicGraph_adj_stepFrom x (i, true)⟩ : SquareEdge) := by
      apply Subtype.ext
      rfl
    simpa [hedge] using hemem

/-- Any square-lattice edge whose endpoints lie in Grimmett's box belongs to the finite box-edge
set. -/
theorem squareEdge_mem_squareBoxEdges_of_adj {m : ℕ} {x y : SquareVertex}
    (hxy : squareGraph.Adj x y) (hx : x ∈ squareBoxVertices m)
    (hy : y ∈ squareBoxVertices m) :
    (⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩ : SquareEdge) ∈ squareBoxEdges m := by
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  exact signedStepEdge_mem_squareBoxEdges a.1 a.2 hx hy

/-- A square-lattice walk that stays inside Grimmett's box uses only the box-edge set. This is the
local deterministic bridge from the box-open event `G_m` to openness of concrete connector walks
inside `B(m)`. -/
theorem walkEdgeFinset_subset_squareBoxEdges_of_support_subset {m : ℕ} {u v : SquareVertex}
    (w : squareGraph.Walk u v)
    (hbox : ∀ x : SquareVertex, x ∈ w.support → x ∈ squareBoxVertices m) :
    walkEdgeFinset w ⊆ squareBoxEdges m := by
  intro e he
  have hew : (e : Sym2 SquareVertex) ∈ w.edges := (mem_walkEdgeFinset_iff w e).mp he
  rcases e with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | hf x y =>
      have hx : x ∈ squareBoxVertices m := hbox x (w.fst_mem_support_of_mem_edges hew)
      have hy : y ∈ squareBoxVertices m := hbox y (w.snd_mem_support_of_mem_edges hew)
      have hxy : squareGraph.Adj x y := w.adj_of_mem_edges hew
      have hmem :
          (⟨s(x, y), by
            rw [SimpleGraph.mem_edgeSet]
            exact hxy⟩ : SquareEdge) ∈ squareBoxEdges m :=
        squareEdge_mem_squareBoxEdges_of_adj hxy hx hy
      have heq :
          (⟨s(x, y), hedge⟩ : SquareEdge) =
            (⟨s(x, y), by
              rw [SimpleGraph.mem_edgeSet]
              exact hxy⟩ : SquareEdge) :=
        Subtype.ext rfl
      simpa [heq] using hmem

/-- Under Grimmett's box-open event, every square-lattice walk whose vertices remain in the box is
open. -/
theorem walkIsOpen_of_mem_openEdgeSetEvent_squareBoxEdges_of_support_subset
    {m : ℕ} {u v : SquareVertex} {ω : EdgeConfiguration 2}
    (hω : ω ∈ openEdgeSetEvent 2 (squareBoxEdges m)) (w : squareGraph.Walk u v)
    (hbox : ∀ x : SquareVertex, x ∈ w.support → x ∈ squareBoxVertices m) :
    walkIsOpen ω w :=
  walkIsOpen_of_mem_openEdgeSetEvent_of_walkEdgeFinset_subset hω w
    (walkEdgeFinset_subset_squareBoxEdges_of_support_subset w hbox)

/-- A positively oriented shifted-dual square-lattice bond. The type is definitionally the same
coordinate model as `SquarePositiveEdge`; the separate name keeps primal and dual roles explicit. -/
abbrev DualSquarePositiveEdge := SquarePositiveEdge

/-- The shifted-dual bond crossing a positive primal square-lattice bond. If the primal bond starts
at `x` in axis `i`, the crossing dual bond starts one encoded face-coordinate step in the negative
perpendicular direction and runs in the perpendicular axis. -/
def primalToDualCrossingPositiveEdge (e : SquarePositiveEdge) : DualSquarePositiveEdge where
  base := cubicStepFrom e.base (squarePerp e.axis, false)
  axis := squarePerp e.axis

/-- A positive horizontal primal bond on the positive x-axis crosses the corresponding shifted-dual
vertical positive-axis bond. This is the positive-oriented normal form behind Grimmett's
positive-axis marking. -/
theorem primalToDualCrossingPositiveEdge_positiveXAxis (k : ℕ) :
    primalToDualCrossingPositiveEdge
        (⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩ : SquarePositiveEdge) =
      (⟨dualPositiveXAxisLowerVertex k, (1 : Fin 2)⟩ : DualSquarePositiveEdge) := by
  simp [primalToDualCrossingPositiveEdge, squarePerp, cubicStepFrom,
    cubicDirectionIncrement]
  ext i
  fin_cases i <;> simp [squareVertex, dualPositiveXAxisLowerVertex]

/-- The positive-oriented shifted-dual edge at positive-axis coordinate `k` has the same
underlying undirected edge as `dualPositiveXAxisCrossingEdge k`. -/
theorem dualPositiveXAxisPositiveEdge_toEdge (k : ℕ) :
    SquarePositiveEdge.toEdge
        (⟨dualPositiveXAxisLowerVertex k, (1 : Fin 2)⟩ : DualSquarePositiveEdge) =
      dualPositiveXAxisCrossingEdge k := by
  apply Subtype.ext
  rfl

/-- The primal bond crossing a positive shifted-dual square-lattice bond. This is the inverse
construction to `primalToDualCrossingPositiveEdge`. -/
def dualToPrimalCrossingPositiveEdge (e : DualSquarePositiveEdge) : SquarePositiveEdge where
  base := cubicStepFrom e.base (e.axis, true)
  axis := squarePerp e.axis

@[simp]
theorem dualToPrimal_primalToDualCrossingPositiveEdge (e : SquarePositiveEdge) :
    dualToPrimalCrossingPositiveEdge (primalToDualCrossingPositiveEdge e) = e := by
  cases e with
  | mk base axis =>
      simp [primalToDualCrossingPositiveEdge, dualToPrimalCrossingPositiveEdge,
        cubicStepFrom_neg_pos, squarePerp_involutive]

@[simp]
theorem primalToDual_dualToPrimalCrossingPositiveEdge (e : DualSquarePositiveEdge) :
    primalToDualCrossingPositiveEdge (dualToPrimalCrossingPositiveEdge e) = e := by
  cases e with
  | mk base axis =>
      simp [primalToDualCrossingPositiveEdge, dualToPrimalCrossingPositiveEdge,
        cubicStepFrom_pos_neg, squarePerp_involutive]

/-- The primal/shifted-dual crossing correspondence for positive square-lattice bonds. This is the
combinatorial bijection used by the Peierls circuit argument before quotienting to unoriented
`CubicEdge` bonds. -/
def squarePositiveEdgeDualCrossingEquiv :
    SquarePositiveEdge ≃ DualSquarePositiveEdge where
  toFun := primalToDualCrossingPositiveEdge
  invFun := dualToPrimalCrossingPositiveEdge
  left_inv := dualToPrimal_primalToDualCrossingPositiveEdge
  right_inv := primalToDual_dualToPrimalCrossingPositiveEdge

/-- The primal/shifted-dual crossing correspondence transported to undirected square-lattice
bonds. This is the edge-level bijection used to convert primal open/closed status into dual
closed/open status in the Peierls part of Grimmett's proof. -/
noncomputable def squareEdgeDualCrossingEquiv : SquareEdge ≃ DualSquareEdge :=
  SquarePositiveEdge.edgeEquiv.symm.trans <|
    squarePositiveEdgeDualCrossingEquiv.trans SquarePositiveEdge.edgeEquiv

/-- The shifted-dual configuration induced by a primal square-lattice bond configuration: a dual
bond is open exactly when the primal bond it crosses is closed. -/
noncomputable def dualSquareConfiguration (ω : EdgeConfiguration 2) : EdgeConfiguration 2 :=
  {e | squareEdgeDualCrossingEquiv.symm e ∉ ω}

/-- Dual openness is primal closedness for the crossed square-lattice bond. -/
theorem dualSquareConfiguration_open_iff (ω : EdgeConfiguration 2) (e : DualSquareEdge) :
    edgeOpen (dualSquareConfiguration ω) e ↔ squareEdgeDualCrossingEquiv.symm e ∉ ω :=
  Iff.rfl

/-- The event that a finite set of dual bonds is open is the event that the corresponding crossed
primal bonds are all closed. -/
theorem dualSquareConfiguration_openOn_finset_event_eq (s : Finset DualSquareEdge) :
    {ω : EdgeConfiguration 2 | (s : Set DualSquareEdge) ⊆ dualSquareConfiguration ω} =
      {ω : EdgeConfiguration 2 |
        Disjoint ((s.map squareEdgeDualCrossingEquiv.symm.toEmbedding : Finset SquareEdge) :
          Set SquareEdge) ω} := by
  ext ω
  change ((∀ ed : DualSquareEdge, ed ∈ s → squareEdgeDualCrossingEquiv.symm ed ∉ ω) ↔
    Disjoint ((s.map squareEdgeDualCrossingEquiv.symm.toEmbedding : Finset SquareEdge) :
      Set SquareEdge) ω)
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro e hemap heω
    rcases Finset.mem_map.mp hemap with ⟨ed, hed, rfl⟩
    exact h ed hed heω
  · intro h ed hed hedω
    rw [Set.disjoint_left] at h
    exact h (Finset.mem_map.mpr ⟨ed, hed, rfl⟩) hedω

/-- The event that a fixed finite set of shifted-dual bonds is open is measurable. -/
theorem measurableSet_dualSquareConfiguration_openOn_finset (s : Finset DualSquareEdge) :
    MeasurableSet {ω : EdgeConfiguration 2 |
      (s : Set DualSquareEdge) ⊆ dualSquareConfiguration ω} := by
  rw [dualSquareConfiguration_openOn_finset_event_eq]
  exact measurableSet_disjoint_finset _

/-- A fixed finite set of shifted-dual bonds is open with probability `(1 - p)^n`, where `n` is
the number of listed dual bonds. This is the finite dual-circuit cylinder calculation in
Grimmett's Peierls argument. -/
theorem bernoulliBondMeasure_real_dualSquareConfiguration_openOn_finset
    (s : Finset DualSquareEdge) (p : I) :
    (bernoulliBondMeasure 2 p).real
        {ω : EdgeConfiguration 2 | (s : Set DualSquareEdge) ⊆ dualSquareConfiguration ω} =
      (1 - (p : ℝ)) ^ s.card := by
  rw [dualSquareConfiguration_openOn_finset_event_eq]
  rw [bernoulliBondMeasure_real_closedOn_finset]
  simp

/-- A finite primal-open cylinder is independent of a finite shifted-dual-open cylinder when the
primal edges in the first event are disjoint from the primal edges crossed by the dual cylinder.
This is the finite support form of the independence used in Grimmett's `G_m`/closed-dual-circuit
step. -/
theorem bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualSquareConfiguration_openOn_finset
    (p : I) (s : Finset SquareEdge) (t : Finset DualSquareEdge)
    (hdisj : Disjoint (s : Set SquareEdge)
      ((t.map squareEdgeDualCrossingEquiv.symm.toEmbedding : Finset SquareEdge) :
        Set SquareEdge)) :
    IndepSet (openEdgeSetEvent 2 s)
      {ω : EdgeConfiguration 2 | (t : Set DualSquareEdge) ⊆ dualSquareConfiguration ω}
      (bernoulliBondMeasure 2 p) := by
  rw [dualSquareConfiguration_openOn_finset_event_eq]
  exact bernoulliBondMeasure_indepSet_openEdgeSetEvent_closedEdgeSetEvent 2 p s
    (t.map squareEdgeDualCrossingEquiv.symm.toEmbedding) hdisj

/-- A shifted-dual walk is open in a primal configuration when all of its dual bonds are open in
the induced dual configuration, equivalently when all crossed primal bonds are closed. -/
def dualWalkIsOpen (ω : EdgeConfiguration 2) {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) : Prop :=
  walkIsOpen (dualSquareConfiguration ω) w

/-- The event that a shifted-dual walk is open is the finite cylinder event that all of its dual
edges are open in the induced dual configuration. -/
theorem dualWalkIsOpen_event_eq_openOn_walkEdgeFinset {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) :
    {ω : EdgeConfiguration 2 | dualWalkIsOpen ω w} =
      {ω : EdgeConfiguration 2 | (walkEdgeFinset w : Set DualSquareEdge) ⊆
        dualSquareConfiguration ω} := by
  ext ω
  exact Set.ext_iff.mp (walkIsOpen_event_eq_openOn_walkEdgeFinset w)
    (dualSquareConfiguration ω)

/-- The event that a fixed shifted-dual walk is open is measurable. -/
theorem measurableSet_dualWalkIsOpen {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) :
    MeasurableSet {ω : EdgeConfiguration 2 | dualWalkIsOpen ω w} := by
  rw [dualWalkIsOpen_event_eq_openOn_walkEdgeFinset]
  exact measurableSet_dualSquareConfiguration_openOn_finset (walkEdgeFinset w)

/-- A finite primal-open cylinder is independent of a fixed shifted-dual walk-open event when the
primal support is disjoint from the primal edges crossed by the dual walk. -/
theorem bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualWalkIsOpen
    {u v : DualSquareVertex} (p : I) (s : Finset SquareEdge)
    (w : dualSquareGraph.Walk u v)
    (hdisj : Disjoint (s : Set SquareEdge)
      (((walkEdgeFinset w).map squareEdgeDualCrossingEquiv.symm.toEmbedding :
          Finset SquareEdge) : Set SquareEdge)) :
    IndepSet (openEdgeSetEvent 2 s) {ω : EdgeConfiguration 2 | dualWalkIsOpen ω w}
      (bernoulliBondMeasure 2 p) := by
  rw [dualWalkIsOpen_event_eq_openOn_walkEdgeFinset]
  exact bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualSquareConfiguration_openOn_finset
    p s (walkEdgeFinset w) hdisj

/-- A fixed shifted-dual trail of length `n` is open with probability `(1 - p)^n`. This is the
closed-dual-circuit probability input in Grimmett's Peierls estimate, stated for trails so that
circuits are an immediate specialization. -/
theorem bernoulliBondMeasure_real_dualWalkIsOpen {u v : DualSquareVertex}
    (p : I) (w : dualSquareGraph.Walk u v) (h : w.IsTrail) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 | dualWalkIsOpen ω w} =
      (1 - (p : ℝ)) ^ w.length := by
  rw [dualWalkIsOpen_event_eq_openOn_walkEdgeFinset]
  rw [bernoulliBondMeasure_real_dualSquareConfiguration_openOn_finset]
  rw [walkEdgeFinset_card_of_isTrail h]

/-- A fixed shifted-dual circuit is open with probability `(1 - p)^n`. -/
theorem bernoulliBondMeasure_real_dualCircuitIsOpen {u : DualSquareVertex}
    (p : I) (c : dualSquareGraph.Walk u u) (h : c.IsCircuit) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 | dualWalkIsOpen ω c} =
      (1 - (p : ℝ)) ^ c.length :=
  bernoulliBondMeasure_real_dualWalkIsOpen p c h.isTrail

/-- A shifted-dual circuit bundled with its base point. -/
structure DualCircuit where
  vertex : DualSquareVertex
  walk : dualSquareGraph.Walk vertex vertex
  isCircuit : walk.IsCircuit

namespace DualCircuit

/-- The length of a shifted-dual circuit. -/
def length (c : DualCircuit) : ℕ :=
  c.walk.length

/-- A shifted-dual circuit is open when every crossed primal bond is closed. -/
def IsOpen (c : DualCircuit) (ω : EdgeConfiguration 2) : Prop :=
  dualWalkIsOpen ω c.walk

/-- The event that a fixed shifted-dual circuit is open is measurable. -/
theorem measurableSet_isOpen (c : DualCircuit) :
    MeasurableSet {ω : EdgeConfiguration 2 | c.IsOpen ω} :=
  measurableSet_dualWalkIsOpen c.walk

/-- The primal square-lattice bonds crossed by a shifted-dual circuit. -/
noncomputable def crossedPrimalEdgeFinset (c : DualCircuit) : Finset SquareEdge :=
  (walkEdgeFinset c.walk).map squareEdgeDualCrossingEquiv.symm.toEmbedding

/-- A shifted-dual circuit is open exactly when every crossed primal bond is closed. -/
theorem isOpen_event_eq_closedEdgeSetEvent (c : DualCircuit) :
    {ω : EdgeConfiguration 2 | c.IsOpen ω} =
      closedEdgeSetEvent 2 c.crossedPrimalEdgeFinset := by
  change {ω : EdgeConfiguration 2 | dualWalkIsOpen ω c.walk} =
    closedEdgeSetEvent 2 ((walkEdgeFinset c.walk).map
      squareEdgeDualCrossingEquiv.symm.toEmbedding)
  rw [dualWalkIsOpen_event_eq_openOn_walkEdgeFinset]
  rw [dualSquareConfiguration_openOn_finset_event_eq]
  rfl

/-- A shifted-dual circuit-open event is measurable with respect to the finite coordinate
sigma-algebra generated by its crossed primal bonds. -/
theorem measurableSet_isOpen_edgeCoordinateMeasurableSpace (c : DualCircuit) :
    MeasurableSet[edgeCoordinateMeasurableSpace 2 c.crossedPrimalEdgeFinset]
      {ω : EdgeConfiguration 2 | c.IsOpen ω} := by
  rw [isOpen_event_eq_closedEdgeSetEvent]
  exact measurableSet_closedEdgeSetEvent_edgeCoordinateMeasurableSpace 2
    c.crossedPrimalEdgeFinset

end DualCircuit

/-- A finite primal-open cylinder is independent of a fixed shifted-dual circuit-open event when
the primal support is disjoint from the primal edges crossed by the dual circuit. -/
theorem bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualCircuitIsOpen
    (p : I) (s : Finset SquareEdge) (c : DualCircuit)
    (hdisj : Disjoint (s : Set SquareEdge)
      (((walkEdgeFinset c.walk).map squareEdgeDualCrossingEquiv.symm.toEmbedding :
          Finset SquareEdge) : Set SquareEdge)) :
    IndepSet (openEdgeSetEvent 2 s) {ω : EdgeConfiguration 2 | c.IsOpen ω}
      (bernoulliBondMeasure 2 p) := by
  change IndepSet (openEdgeSetEvent 2 s)
    {ω : EdgeConfiguration 2 | dualWalkIsOpen ω c.walk} (bernoulliBondMeasure 2 p)
  exact bernoulliBondMeasure_indepSet_openEdgeSetEvent_dualWalkIsOpen p s c.walk hdisj

/-- Finite union bound for an indexed family of shifted-dual circuits. This is the probabilistic
half of Grimmett's finite closed-circuit estimate before the geometric circuit count is applied. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_le {β : Type*} [Fintype β]
    (p : I) (circuits : β → DualCircuit) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
      ∑ b : β, (1 - (p : ℝ)) ^ (circuits b).length := by
  classical
  calc
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω}
        = (bernoulliBondMeasure 2 p).real
            (⋃ b : β, {ω : EdgeConfiguration 2 | (circuits b).IsOpen ω}) := by
          congr 1
          ext ω
          simp [DualCircuit.IsOpen]
    _ ≤ ∑ b : β,
          (bernoulliBondMeasure 2 p).real
            {ω : EdgeConfiguration 2 | (circuits b).IsOpen ω} :=
        measureReal_iUnion_fintype_le _
    _ = ∑ b : β, (1 - (p : ℝ)) ^ (circuits b).length := by
        apply Finset.sum_congr rfl
        intro b _hb
        change (bernoulliBondMeasure 2 p).real
            {ω : EdgeConfiguration 2 | dualWalkIsOpen ω (circuits b).walk} =
          (1 - (p : ℝ)) ^ (circuits b).walk.length
        rw [bernoulliBondMeasure_real_dualCircuitIsOpen p (circuits b).walk
          (circuits b).isCircuit]

/-- Finite union bound for a family of shifted-dual circuits all having a fixed length. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le {β : Type*}
    [Fintype β] (p : I) (circuits : β → DualCircuit) {n : ℕ}
    (hlen : ∀ b : β, (circuits b).length = n) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
      (Fintype.card β : ℝ) * (1 - (p : ℝ)) ^ n := by
  calc
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
        ∑ b : β, (1 - (p : ℝ)) ^ (circuits b).length :=
      bernoulliBondMeasure_real_existsOpenDualCircuit_le p circuits
    _ = (Fintype.card β : ℝ) * (1 - (p : ℝ)) ^ n := by
      simp [hlen, Finset.sum_const, nsmul_eq_mul]

/-- If a length-`n` finite family of shifted-dual circuits has at most `N` members, then the
probability that one of them is open is at most `N * (1-p)^n`. This is the exact slot where the
Peierls circuit-count estimate `ρ(n) ≤ n * σ(n - 1)` will be used. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le_of_card_le
    {β : Type*} [Fintype β] (p : I) (circuits : β → DualCircuit) {n N : ℕ}
    (hlen : ∀ b : β, (circuits b).length = n) (hcard : Fintype.card β ≤ N) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
      (N : ℝ) * (1 - (p : ℝ)) ^ n := by
  calc
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
        (Fintype.card β : ℝ) * (1 - (p : ℝ)) ^ n :=
      bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le p circuits hlen
    _ ≤ (N : ℝ) * (1 - (p : ℝ)) ^ n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (pow_nonneg (sub_nonneg.mpr p.2.2) n)

/-- Peierls finite-family bound in the form produced by Grimmett's circuit encoding: if a
length-`n` family of dual circuits injects into `n` choices of a marked circuit edge times a
self-avoiding walk of length `n - 1`, then the probability that one of the circuits is open is at
most `n * σ(n - 1) * (1-p)^n`. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_of_encoding_le
    {β : Type*} [Fintype β] (p : I) (circuits : β → DualCircuit) {n : ℕ}
    (hlen : ∀ b : β, (circuits b).length = n)
    (encode : β ↪ Fin n × SelfAvoidingWalk 2 (n - 1)) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ b : β, (circuits b).IsOpen ω} ≤
      ((n * selfAvoidingWalkCount 2 (n - 1) : ℕ) : ℝ) * (1 - (p : ℝ)) ^ n := by
  refine bernoulliBondMeasure_real_existsOpenDualCircuit_of_length_le_of_card_le
    p circuits hlen ?_
  calc
    Fintype.card β ≤ Fintype.card (Fin n × SelfAvoidingWalk 2 (n - 1)) :=
      Fintype.card_le_of_embedding encode
    _ = n * selfAvoidingWalkCount 2 (n - 1) := by
      simp [Fintype.card_prod, Fintype.card_fin, selfAvoidingWalkCount]

/-- Finite-window version of Grimmett's Peierls circuit estimate. If, for each length in the
window `N, ..., N + M - 1`, the relevant dual circuits come with Grimmett's encoding into a marked
edge and a self-avoiding walk of length one less, then the probability that some circuit in the
window is open is bounded by the corresponding finite Peierls sum. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_window_of_encoding_le
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : Fin M, ∃ b : β (N + (k : ℕ)),
          (circuits (N + (k : ℕ)) b).IsOpen ω} ≤
      ∑ k : Fin M,
        (((N + (k : ℕ)) * selfAvoidingWalkCount 2 (N + (k : ℕ) - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + (k : ℕ)) := by
  classical
  calc
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : Fin M, ∃ b : β (N + (k : ℕ)),
          (circuits (N + (k : ℕ)) b).IsOpen ω}
        = (bernoulliBondMeasure 2 p).real
            (⋃ k : Fin M,
              {ω : EdgeConfiguration 2 | ∃ b : β (N + (k : ℕ)),
                (circuits (N + (k : ℕ)) b).IsOpen ω}) := by
          congr 1
          ext ω
          simp
    _ ≤ ∑ k : Fin M,
          (bernoulliBondMeasure 2 p).real
            {ω : EdgeConfiguration 2 | ∃ b : β (N + (k : ℕ)),
              (circuits (N + (k : ℕ)) b).IsOpen ω} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ k : Fin M,
        (((N + (k : ℕ)) * selfAvoidingWalkCount 2 (N + (k : ℕ) - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + (k : ℕ)) := by
      refine Finset.sum_le_sum ?_
      intro k _hk
      simpa using
        (bernoulliBondMeasure_real_existsOpenDualCircuit_of_encoding_le
          (p := p) (circuits := circuits (N + (k : ℕ)))
          (hlen := hlen (N + (k : ℕ))) (encode := encode (N + (k : ℕ))))

/-- Countable-tail version of Grimmett's Peierls circuit estimate. Once the lengthwise
families of dual circuits have Grimmett's marked-edge/self-avoiding-walk encoding and the
resulting Peierls majorant is summable, the probability that some encoded circuit of length at
least `N` is open is bounded by the corresponding infinite tail sum. -/
theorem bernoulliBondMeasure_real_existsOpenDualCircuit_tail_of_encoding_le
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hsumm : Summable fun k : ℕ ↦
      (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
        (1 - (p : ℝ)) ^ (N + k)) :
    (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω} ≤
      ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + k) := by
  classical
  let μ := bernoulliBondMeasure 2 p
  let F : ℕ → Set (EdgeConfiguration 2) := fun M ↦
    {ω | ∃ k : Fin M, ∃ b : β (N + (k : ℕ)),
      (circuits (N + (k : ℕ)) b).IsOpen ω}
  let tail : Set (EdgeConfiguration 2) :=
    {ω | ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω}
  let g : ℕ → ℝ := fun k ↦
    (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
      (1 - (p : ℝ)) ^ (N + k)
  have hmono : Monotone F := by
    intro M L hML ω hω
    rcases hω with ⟨k, b, hb⟩
    refine ⟨⟨k, lt_of_lt_of_le k.isLt hML⟩, ?_⟩
    exact ⟨b, by simpa using hb⟩
  have hUnion : (⋃ M : ℕ, F M) = tail := by
    ext ω
    simp only [Set.mem_iUnion, F, tail, Set.mem_setOf_eq]
    constructor
    · rintro ⟨M, k, b, hb⟩
      exact ⟨k, b, hb⟩
    · rintro ⟨k, b, hb⟩
      exact ⟨k + 1, ⟨⟨k, Nat.lt_succ_self k⟩, b, by simpa using hb⟩⟩
  have hF_enn : Filter.Tendsto (fun M : ℕ ↦ μ (F M)) Filter.atTop (nhds (μ tail)) := by
    have hcont := tendsto_measure_iUnion_atTop (μ := μ) hmono
    simpa [hUnion, Function.comp_def] using hcont
  have hF_real : Filter.Tendsto (fun M : ℕ ↦ μ.real (F M)) Filter.atTop
      (nhds (μ.real tail)) := by
    have htail_ne_top : μ tail ≠ ∞ := by
      change setBer((Set.univ : Set (CubicEdge 2)), p) tail ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ tail)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    simpa [Measure.real] using (ENNReal.tendsto_toReal htail_ne_top).comp hF_enn
  have hsum : Filter.Tendsto (fun M : ℕ ↦ ∑ k : Fin M, g (k : ℕ)) Filter.atTop
      (nhds (∑' k : ℕ, g k)) := by
    have hpartial : Filter.Tendsto (fun M : ℕ ↦ ∑ k ∈ Finset.range M, g k)
        Filter.atTop (nhds (∑' k : ℕ, g k)) :=
      hsumm.hasSum.tendsto_sum_nat
    rw [show (fun M : ℕ ↦ ∑ k : Fin M, g (k : ℕ)) =
        fun M : ℕ ↦ ∑ k ∈ Finset.range M, g k by
      funext M
      exact Fin.sum_univ_eq_sum_range g M]
    exact hpartial
  have hle : ∀ M : ℕ, μ.real (F M) ≤ ∑ k : Fin M, g (k : ℕ) := by
    intro M
    simpa [μ, F, g, add_comm, add_left_comm, add_assoc] using
      (bernoulliBondMeasure_real_existsOpenDualCircuit_window_of_encoding_le
        (p := p) (circuits := circuits) (N := N) (M := M) hlen encode)
  simpa [μ, tail, g] using le_of_tendsto_of_tendsto hF_real hsum
    (Filter.Eventually.of_forall hle)

end Percolation
