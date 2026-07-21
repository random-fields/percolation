import Percolation.Extensions.RigidityPercolation
import Percolation.Core.CubicWalkLevel
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Boundary deficiency of finite cubic graphs

The rigidity matrix has one row per graph edge.  This file relates that elementary rank bound
to the directed edge boundary of a finite induced cubic graph.  The resulting deficiency grows
with the number of occupied coordinate hyperplanes and is the combinatorial obstruction behind
the fact that the cubic lattice is not rigid.
-/

namespace Percolation

open Set SimpleGraph

/-- Directed cubic steps based at `U` which leave `U`. -/
def CubicMissingDart {d : ℕ} (U : Finset (Cubic d)) :=
  {q : {x : Cubic d // x ∈ U} × CubicDirection d //
    cubicStepFrom q.1.1 q.2 ∉ U}

/-- Directed cubic steps based at `U` which remain in `U`. -/
def CubicInternalDart {d : ℕ} (U : Finset (Cubic d)) :=
  {q : {x : Cubic d // x ∈ U} × CubicDirection d //
    cubicStepFrom q.1.1 q.2 ∈ U}

noncomputable instance {d : ℕ} (U : Finset (Cubic d)) :
    Fintype (CubicMissingDart U) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun q : {x : Cubic d // x ∈ U} × CubicDirection d ↦
      cubicStepFrom q.1.1 q.2 ∉ U) (by simp)

noncomputable instance {d : ℕ} (U : Finset (Cubic d)) :
    Fintype (CubicInternalDart U) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun q : {x : Cubic d // x ∈ U} × CubicDirection d ↦
      cubicStepFrom q.1.1 q.2 ∈ U) (by simp)

/-- An internal signed step is a dart of the induced cubic graph. -/
noncomputable def cubicInternalDartToDart {d : ℕ} (U : Finset (Cubic d)) :
    CubicInternalDart U → ((cubicGraph d).induce (U : Set (Cubic d))).Dart := by
  intro q
  let y : (U : Set (Cubic d)) := ⟨cubicStepFrom q.1.1 q.1.2, q.2⟩
  exact ⟨(q.1.1, y), by
    rw [SimpleGraph.induce_adj]
    exact cubicGraph_adj_stepFrom q.1.1 q.1.2⟩

theorem cubicInternalDartToDart_injective {d : ℕ} (U : Finset (Cubic d)) :
    Function.Injective (cubicInternalDartToDart U) := by
  intro q r h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z ↦ z.toProd.1.1) h
  · apply cubicStepFrom_injective q.1.1
    have hbase : q.1.1.1 = r.1.1.1 := congrArg (fun z ↦ z.toProd.1.1) h
    have hend : cubicStepFrom q.1.1 q.1.2 = cubicStepFrom r.1.1 r.1.2 :=
      congrArg (fun z ↦ z.toProd.2.1) h
    simpa [hbase] using hend

theorem cubicInternalDartToDart_surjective {d : ℕ} (U : Finset (Cubic d)) :
    Function.Surjective (cubicInternalDartToDart U) := by
  intro a
  have hadj : (cubicGraph d).Adj a.toProd.1.1 a.toProd.2.1 :=
    SimpleGraph.induce_adj.mp a.adj
  obtain ⟨dir, hdir⟩ :=
    (cubicGraph_adj_iff_exists_stepFrom a.toProd.1.1 a.toProd.2.1).mp hadj
  let q : CubicInternalDart U :=
    ⟨(a.toProd.1, dir), by simpa [← hdir] using a.toProd.2.2⟩
  refine ⟨q, ?_⟩
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact hdir.symm

/-- Internal signed steps are exactly the darts of the induced cubic graph. -/
noncomputable def cubicInternalDartEquiv {d : ℕ} (U : Finset (Cubic d)) :
    CubicInternalDart U ≃ ((cubicGraph d).induce (U : Set (Cubic d))).Dart :=
  Equiv.ofBijective (cubicInternalDartToDart U)
    ⟨cubicInternalDartToDart_injective U, cubicInternalDartToDart_surjective U⟩

/-- Every based signed step is uniquely either internal or missing. -/
noncomputable def cubicDartPartitionEquiv {d : ℕ} (U : Finset (Cubic d)) :
    ((cubicGraph d).induce (U : Set (Cubic d))).Dart ⊕ CubicMissingDart U ≃
      {x : Cubic d // x ∈ U} × CubicDirection d :=
  (Equiv.sumCongr (cubicInternalDartEquiv U).symm (Equiv.refl _)).trans
    (Equiv.sumCompl fun q : {x : Cubic d // x ∈ U} × CubicDirection d ↦
      cubicStepFrom q.1.1 q.2 ∈ U)

/-- Exact finite handshake identity, including the directed boundary deficiency. -/
theorem twice_edge_card_add_missingDart_card {d : ℕ} (U : Finset (Cubic d)) :
    2 * Nat.card ((cubicGraph d).induce (U : Set (Cubic d))).edgeSet +
        Fintype.card (CubicMissingDart U) =
      U.card * (2 * d) := by
  classical
  calc
    2 * Nat.card ((cubicGraph d).induce (U : Set (Cubic d))).edgeSet +
        Fintype.card (CubicMissingDart U) =
        Fintype.card ((cubicGraph d).induce (U : Set (Cubic d))).Dart +
          Fintype.card (CubicMissingDart U) := by
            apply congrArg (fun n ↦ n + Fintype.card (CubicMissingDart U))
            rw [Nat.card_eq_fintype_card,
              ← ((cubicGraph d).induce (U : Set (Cubic d))).edgeFinset_card]
            exact
              ((cubicGraph d).induce (U : Set (Cubic d))).dart_card_eq_twice_card_edges.symm
    _ = Fintype.card
        (((cubicGraph d).induce (U : Set (Cubic d))).Dart ⊕ CubicMissingDart U) := by
          rw [Fintype.card_sum]
    _ = Fintype.card ({x : Cubic d // x ∈ U} × CubicDirection d) :=
      Fintype.card_congr (cubicDartPartitionEquiv U)
    _ = U.card * (2 * d) := by
      rw [Fintype.card_prod]
      simp [Fintype.card_prod, Nat.mul_comm]

/-- The rank of a finite rigidity matrix is at most its number of rows. -/
theorem rigidityLinearMap_finrank_le_edge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (F : Framework G d) :
    Module.finrank ℝ (LinearMap.range (Framework.rigidityLinearMap F)) ≤
      Nat.card G.edgeSet := by
  classical
  exact (LinearMap.range (Framework.rigidityLinearMap F)).finrank_le.trans_eq
    ((Module.finrank_pi ℝ).trans Nat.card_eq_fintype_card.symm)

/-- A generically rigid finite graph needs at least the Maxwell rank number of edges. -/
theorem GenericallyRigid.expectedRank_le_edge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (hG : GenericallyRigid G d) :
    expectedRigidityRank d (Fintype.card V) ≤ Nat.card G.edgeSet := by
  obtain ⟨F, hF⟩ := hG.2.2
  exact hF.trans (rigidityLinearMap_finrank_le_edge_card F)

/-! ### Missing darts from occupied coordinate slices -/

/-- Coordinates transverse to `i`. -/
abbrev CubicTransverseCoordinate {d : ℕ} (i : Fin d) := {j : Fin d // j ≠ i}

theorem card_cubicTransverseCoordinate {d : ℕ} (i : Fin d) :
    Fintype.card (CubicTransverseCoordinate i) = d - 1 := by
  simpa [CubicTransverseCoordinate] using
    (Fintype.card_subtype_compl (fun j : Fin d ↦ j = i))

/-- Vertices of `U` on one coordinate hyperplane. -/
def cubicCoordinateSlice {d : ℕ} (U : Finset (Cubic d)) (i : Fin d) (a : ℤ) :
    Finset (Cubic d) :=
  U.filter fun x ↦ x i = a

@[simp]
theorem mem_cubicCoordinateSlice {d : ℕ} {U : Finset (Cubic d)}
    {i : Fin d} {a : ℤ} {x : Cubic d} :
    x ∈ cubicCoordinateSlice U i a ↔ x ∈ U ∧ x i = a := by
  simp [cubicCoordinateSlice]

/-- A vertex maximizing coordinate `j` in a nonempty finite slice. -/
noncomputable def cubicCoordinateSliceMax {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : Fin d)
    (h : (cubicCoordinateSlice U i a).Nonempty) : Cubic d :=
  Classical.choose (Finset.exists_max_image (cubicCoordinateSlice U i a) (fun x ↦ x j) h)

theorem cubicCoordinateSliceMax_mem {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : Fin d)
    (h : (cubicCoordinateSlice U i a).Nonempty) :
    cubicCoordinateSliceMax U i a j h ∈ cubicCoordinateSlice U i a :=
  (Classical.choose_spec
    (Finset.exists_max_image (cubicCoordinateSlice U i a) (fun x ↦ x j) h)).1

theorem cubicCoordinateSliceMax_isMax {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : Fin d)
    (h : (cubicCoordinateSlice U i a).Nonempty)
    {x : Cubic d} (hx : x ∈ cubicCoordinateSlice U i a) :
    x j ≤ cubicCoordinateSliceMax U i a j h j :=
  (Classical.choose_spec
    (Finset.exists_max_image (cubicCoordinateSlice U i a) (fun x ↦ x j) h)).2 x hx

theorem cubicCoordinateSliceMax_mem_U {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : Fin d)
    (h : (cubicCoordinateSlice U i a).Nonempty) :
    cubicCoordinateSliceMax U i a j h ∈ U :=
  (mem_cubicCoordinateSlice.mp (cubicCoordinateSliceMax_mem U i a j h)).1

theorem cubicCoordinateSliceMax_coord {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : Fin d)
    (h : (cubicCoordinateSlice U i a).Nonempty) :
    cubicCoordinateSliceMax U i a j h i = a :=
  (mem_cubicCoordinateSlice.mp (cubicCoordinateSliceMax_mem U i a j h)).2

/-- The positive transverse step from a slice maximum leaves `U`. -/
theorem cubicStepFrom_sliceMax_not_mem {d : ℕ} (U : Finset (Cubic d))
    (i : Fin d) (a : ℤ) (j : CubicTransverseCoordinate i)
    (h : (cubicCoordinateSlice U i a).Nonempty) :
    cubicStepFrom (cubicCoordinateSliceMax U i a j h) (j, true) ∉ U := by
  intro hmem
  have hcoord :
      cubicStepFrom (cubicCoordinateSliceMax U i a j h) (j, true) i = a := by
    rw [show cubicStepFrom (cubicCoordinateSliceMax U i a j h) (j, true) i =
        cubicCoordinateSliceMax U i a j h i by
      simp [cubicStepFrom, cubicDirectionIncrement, Ne.symm j.2]]
    exact cubicCoordinateSliceMax_coord U i a j h
  have hinSlice :
      cubicStepFrom (cubicCoordinateSliceMax U i a j h) (j, true) ∈
        cubicCoordinateSlice U i a :=
    mem_cubicCoordinateSlice.mpr ⟨hmem, hcoord⟩
  have hle := cubicCoordinateSliceMax_isMax U i a j h hinSlice
  simp [cubicStepFrom, cubicDirectionIncrement] at hle

/-- Distinct occupied `i`-levels and transverse coordinates give distinct missing darts. -/
noncomputable def cubicSliceMissingDartEmbedding
    {d : ℕ} {kappa : Type*} (U : Finset (Cubic d)) (i : Fin d)
    (level : kappa → ℤ) (hlevel : Function.Injective level)
    (hslice : ∀ k, (cubicCoordinateSlice U i (level k)).Nonempty) :
    kappa × CubicTransverseCoordinate i ↪ CubicMissingDart U where
  toFun q :=
    ⟨(⟨cubicCoordinateSliceMax U i (level q.1) q.2 (hslice q.1),
        cubicCoordinateSliceMax_mem_U U i (level q.1) q.2 (hslice q.1)⟩,
      (q.2, true)),
      cubicStepFrom_sliceMax_not_mem U i (level q.1) q.2 (hslice q.1)⟩
  inj' := by
    intro q r hqr
    have hdir : (q.2.1, true) = (r.2.1, true) :=
      congrArg (fun z : CubicMissingDart U ↦ z.1.2) hqr
    have hj : q.2 = r.2 := by
      apply Subtype.ext
      exact congrArg Prod.fst hdir
    have hx : cubicCoordinateSliceMax U i (level q.1) q.2 (hslice q.1) =
        cubicCoordinateSliceMax U i (level r.1) r.2 (hslice r.1) := by
      exact congrArg (fun z : CubicMissingDart U ↦ z.1.1.1) hqr
    have hlevels : level q.1 = level r.1 := by
      calc
        level q.1 = cubicCoordinateSliceMax U i (level q.1) q.2 (hslice q.1) i :=
          (cubicCoordinateSliceMax_coord U i (level q.1) q.2 (hslice q.1)).symm
        _ = cubicCoordinateSliceMax U i (level r.1) r.2 (hslice r.1) i :=
          congrArg (fun x ↦ x i) hx
        _ = level r.1 := cubicCoordinateSliceMax_coord U i (level r.1) r.2 (hslice r.1)
    exact Prod.ext (hlevel hlevels) hj

/-- The number of missing darts is bounded below by any injectively indexed family of occupied
coordinate slices, once for every transverse coordinate. -/
theorem card_mul_pred_le_missingDart_card
    {d : ℕ} {kappa : Type*} [Fintype kappa]
    (U : Finset (Cubic d)) (i : Fin d)
    (level : kappa → ℤ) (hlevel : Function.Injective level)
    (hslice : ∀ k, (cubicCoordinateSlice U i (level k)).Nonempty) :
    Fintype.card kappa * (d - 1) ≤ Fintype.card (CubicMissingDart U) := by
  rw [← card_cubicTransverseCoordinate i, ← Fintype.card_prod]
  exact Fintype.card_le_of_injective (cubicSliceMissingDartEmbedding U i level hlevel hslice)
    (cubicSliceMissingDartEmbedding U i level hlevel hslice).injective

end Percolation
