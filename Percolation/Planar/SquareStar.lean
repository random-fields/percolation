import Percolation.Critical.BoxRadius

/-!
# The square star lattice

The star lattice joins distinct square-lattice vertices whose coordinate `L∞` distance is at
most one. It is the eight-neighbor graph used to encode closed separators in planar site
percolation. This file supplies an exact finite neighbor set and degree, so later Peierls counting
can use the literal branching factor eight.
-/

namespace Percolation

/-- The eight-neighbor (king-move) graph on `ℤ²`. -/
def squareStarGraph : SimpleGraph SquareVertex where
  Adj x y := x ≠ y ∧ cubicLInfDist x y ≤ 1
  symm x y h := ⟨h.1.symm, by simpa [cubicLInfDist_comm] using h.2⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

@[simp]
theorem squareStarGraph_adj_iff {x y : SquareVertex} :
    squareStarGraph.Adj x y ↔ x ≠ y ∧ cubicLInfDist x y ≤ 1 :=
  Iff.rfl

/-- Every nearest-neighbor square edge is a star edge. -/
theorem squareGraph_adj_imp_squareStarGraph_adj {x y : SquareVertex}
    (hxy : squareGraph.Adj x y) :
    squareStarGraph.Adj x y := by
  refine ⟨hxy.ne, ?_⟩
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  exact cubicLInfDist_stepFrom_le_one x a

/-- Concrete finite set of the eight star neighbors of `x`. -/
noncomputable def squareStarNeighborFinset (x : SquareVertex) : Finset SquareVertex :=
  (cubicMetricBox 2 x 1).erase x

@[simp]
theorem mem_squareStarNeighborFinset_iff {x y : SquareVertex} :
    y ∈ squareStarNeighborFinset x ↔ squareStarGraph.Adj x y := by
  classical
  rw [squareStarNeighborFinset, Finset.mem_erase, squareStarGraph_adj_iff,
    mem_cubicMetricBox_iff_lInfDist_le]
  constructor
  · exact fun h ↦ ⟨h.1.symm, h.2⟩
  · exact fun h ↦ ⟨h.1.symm, h.2⟩

noncomputable instance squareStarGraph_neighborSet_fintype (x : SquareVertex) :
    Fintype (squareStarGraph.neighborSet x) := by
  classical
  let emb : squareStarGraph.neighborSet x ↪ {y // y ∈ squareStarNeighborFinset x} :=
    { toFun := fun y ↦ ⟨y.1, mem_squareStarNeighborFinset_iff.mpr y.2⟩
      inj' := by
        intro y z hyz
        apply Subtype.ext
        exact congrArg (fun q : {y // y ∈ squareStarNeighborFinset x} ↦ (q.1 : SquareVertex)) hyz }
  exact Fintype.ofInjective emb emb.injective

noncomputable instance squareStarGraph_locallyFinite : squareStarGraph.LocallyFinite :=
  fun x ↦ squareStarGraph_neighborSet_fintype x

/-- The star lattice has the source's exact degree eight. -/
@[simp]
theorem squareStarGraph_degree (x : SquareVertex) : squareStarGraph.degree x = 8 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hneighbors : squareStarGraph.neighborFinset x = squareStarNeighborFinset x := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, mem_squareStarNeighborFinset_iff]
  rw [hneighbors, squareStarNeighborFinset, Finset.card_erase_of_mem]
  · rw [cubicMetricBox_card]
    norm_num
  · exact mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)

/-! ### Exact direction-word coding -/

/-- A noncanonical but fixed numbering of the eight star neighbors of each vertex. -/
noncomputable def squareStarNeighborEquiv (x : SquareVertex) :
    Fin 8 ≃ squareStarGraph.neighborSet x :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree,
      squareStarGraph_degree])

/-- Follow a finite word of numbered star-neighbor choices from a starting vertex. -/
noncomputable def squareStarWalkFromList (x : SquareVertex) :
    (steps : List (Fin 8)) → Σ y, squareStarGraph.Walk x y
  | [] => ⟨x, SimpleGraph.Walk.nil⟩
  | a :: steps =>
      let y := (squareStarNeighborEquiv x a).1
      let q := squareStarWalkFromList y steps
      ⟨q.1, SimpleGraph.Walk.cons (squareStarNeighborEquiv x a).2 q.2⟩

@[simp]
theorem squareStarWalkFromList_nil (x : SquareVertex) :
    squareStarWalkFromList x [] = ⟨x, SimpleGraph.Walk.nil⟩ :=
  rfl

theorem squareStarWalkFromList_cons
    (x : SquareVertex) (a : Fin 8) (steps : List (Fin 8)) :
    squareStarWalkFromList x (a :: steps) =
      let y := (squareStarNeighborEquiv x a).1
      let q := squareStarWalkFromList y steps
      ⟨q.1, SimpleGraph.Walk.cons (squareStarNeighborEquiv x a).2 q.2⟩ :=
  rfl

@[simp]
theorem squareStarWalkFromList_length (x : SquareVertex) (steps : List (Fin 8)) :
    (squareStarWalkFromList x steps).2.length = steps.length := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
      rw [squareStarWalkFromList_cons]
      simp only [SimpleGraph.Walk.length_cons, List.length_cons, add_left_inj]
      exact ih _

/-- Encode a star walk by the numbered neighbor chosen at each step. -/
noncomputable def squareStarWalkCodeList {x y : SquareVertex} :
    squareStarGraph.Walk x y → List (Fin 8)
  | .nil => []
  | .cons h p =>
      (squareStarNeighborEquiv _).symm ⟨_, h⟩ :: squareStarWalkCodeList p

@[simp]
theorem squareStarWalkCodeList_length {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) :
    (squareStarWalkCodeList w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h p ih => simp [squareStarWalkCodeList, ih]

/-- Decoding the code of a walk recovers the walk itself, not merely its endpoint. -/
theorem squareStarWalkFromList_code {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) :
    squareStarWalkFromList x (squareStarWalkCodeList w) = ⟨y, w⟩ := by
  induction w with
  | nil => rfl
  | @cons x y z h p ih =>
      rw [squareStarWalkCodeList, squareStarWalkFromList_cons]
      have hneighbor :
          (squareStarNeighborEquiv x) ((squareStarNeighborEquiv x).symm ⟨y, h⟩) =
            ⟨y, h⟩ :=
        (squareStarNeighborEquiv x).apply_symm_apply ⟨y, h⟩
      rw [hneighbor]
      change
        (let q := squareStarWalkFromList y (squareStarWalkCodeList p);
          (⟨q.1, SimpleGraph.Walk.cons h q.2⟩ :
            Σ z, squareStarGraph.Walk x z)) =
          (⟨z, SimpleGraph.Walk.cons h p⟩ : Σ z, squareStarGraph.Walk x z)
      rw [ih]

/-- Length-indexed direction word of a star walk. -/
noncomputable def squareStarWalkCode {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) : List.Vector (Fin 8) w.length :=
  ⟨squareStarWalkCodeList w, squareStarWalkCodeList_length w⟩

/-- Decode a length-indexed star direction word. -/
noncomputable def squareStarWalkFromVector {n : ℕ} (x : SquareVertex)
    (steps : List.Vector (Fin 8) n) : Σ y, squareStarGraph.Walk x y :=
  squareStarWalkFromList x steps.toList

@[simp]
theorem squareStarWalkFromVector_length {n : ℕ} (x : SquareVertex)
    (steps : List.Vector (Fin 8) n) :
    (squareStarWalkFromVector x steps).2.length = n := by
  simp [squareStarWalkFromVector]

theorem squareStarWalkFromVector_code {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) :
    squareStarWalkFromVector x (squareStarWalkCode w) = ⟨y, w⟩ :=
  squareStarWalkFromList_code w

/-- Direction words whose decoded star walk is self-avoiding. -/
def SquareStarSelfAvoidingCode (x : SquareVertex) (n : ℕ) :=
  {steps : List.Vector (Fin 8) n // (squareStarWalkFromVector x steps).2.IsPath}

noncomputable instance (x : SquareVertex) (n : ℕ) :
    Fintype (SquareStarSelfAvoidingCode x n) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- There are at most `8^n` self-avoiding star walks of length `n` from a fixed start. -/
theorem card_squareStarSelfAvoidingCode_le (x : SquareVertex) (n : ℕ) :
    Fintype.card (SquareStarSelfAvoidingCode x n) ≤ 8 ^ n := by
  calc
    Fintype.card (SquareStarSelfAvoidingCode x n) ≤
        Fintype.card (List.Vector (Fin 8) n) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 8 ^ n := by simp

/-- Every self-avoiding star walk is represented by the counted code family. -/
noncomputable def squareStarSelfAvoidingCodeOfWalk {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) (hw : w.IsPath) :
    SquareStarSelfAvoidingCode x w.length :=
  ⟨squareStarWalkCode w, by
    rw [squareStarWalkFromVector_code]
    exact hw⟩

end Percolation
