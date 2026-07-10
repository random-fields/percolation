import Percolation.Critical.BoxRadius

/-!
# Coordinate symmetries of the cubic lattice

Coordinate permutations and sign changes are graph automorphisms preserving the i.i.d. bond law.
Chapter 6 uses them to identify the probabilities of the `2d` faces of a coordinate box.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ### Coordinate permutations -/

/-- Relabel the coordinates of a cubic-lattice vertex. -/
def cubicCoordinatePermutationEquiv {d : ℕ} (e : Fin d ≃ Fin d) : Cubic d ≃ Cubic d where
  toFun x j := x (e.symm j)
  invFun x i := x (e i)
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext i; simp

@[simp]
theorem cubicCoordinatePermutationEquiv_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (x : Cubic d) (j : Fin d) :
    cubicCoordinatePermutationEquiv e x j = x (e.symm j) := rfl

theorem cubicCoordinatePermutation_stepFrom {d : ℕ} (e : Fin d ≃ Fin d)
    (x : Cubic d) (a : CubicDirection d) :
    cubicCoordinatePermutationEquiv e (cubicStepFrom x a) =
      cubicStepFrom (cubicCoordinatePermutationEquiv e x) (e a.1, a.2) := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = e i
  · subst j
    simp only [cubicCoordinatePermutationEquiv_apply]
    rw [e.symm_apply_apply]
    simp [cubicStepFrom, cubicDirectionIncrement]
  · have hsymm : e.symm j ≠ i := by
      intro h
      apply hji
      simpa using congrArg e h
    simp [cubicCoordinatePermutationEquiv, cubicStepFrom, cubicDirectionIncrement, hji, hsymm]

/-- Coordinate permutations as cubic-graph automorphisms. -/
def cubicCoordinatePermutationIso {d : ℕ} (e : Fin d ≃ Fin d) :
    cubicGraph d ≃g cubicGraph d where
  toEquiv := cubicCoordinatePermutationEquiv e
  map_rel_iff' := by
    intro x y
    rw [cubicGraph_adj_iff_exists_stepFrom, cubicGraph_adj_iff_exists_stepFrom]
    constructor
    · rintro ⟨a, ha⟩
      let a' : CubicDirection d := (e.symm a.1, a.2)
      refine ⟨a', (cubicCoordinatePermutationEquiv e).injective ?_⟩
      rw [cubicCoordinatePermutation_stepFrom]
      simpa [a'] using ha
    · rintro ⟨a, rfl⟩
      exact ⟨(e a.1, a.2), cubicCoordinatePermutation_stepFrom e x a⟩

/-! ### Coordinate reflections -/

/-- Reflect one coordinate through zero. -/
def cubicCoordinateReflectionEquiv {d : ℕ} (i : Fin d) : Cubic d ≃ Cubic d where
  toFun x j := if j = i then -x j else x j
  invFun x j := if j = i then -x j else x j
  left_inv := by
    intro x
    ext j
    by_cases hji : j = i <;> simp [hji]
  right_inv := by
    intro x
    ext j
    by_cases hji : j = i <;> simp [hji]

@[simp]
theorem cubicCoordinateReflectionEquiv_apply_self {d : ℕ} (i : Fin d) (x : Cubic d) :
    cubicCoordinateReflectionEquiv i (cubicCoordinateReflectionEquiv i x) = x := by
  exact (cubicCoordinateReflectionEquiv i).left_inv x

/-- Reflection reverses the sign of a step in the reflected coordinate. -/
theorem cubicCoordinateReflection_stepFrom {d : ℕ} (i : Fin d)
    (x : Cubic d) (a : CubicDirection d) :
    cubicCoordinateReflectionEquiv i (cubicStepFrom x a) =
      cubicStepFrom (cubicCoordinateReflectionEquiv i x)
        (a.1, if a.1 = i then !a.2 else a.2) := by
  rcases a with ⟨j, b⟩
  ext k
  by_cases hkj : k = j
  · subst k
    by_cases hji : j = i
    · subst j
      cases b <;> simp [cubicCoordinateReflectionEquiv, cubicStepFrom,
        cubicDirectionIncrement] <;> ring
    · cases b <;> simp [cubicCoordinateReflectionEquiv, cubicStepFrom,
        cubicDirectionIncrement, hji]
  · by_cases hki : k = i
    · subst k
      have hji : j ≠ i := by exact fun h ↦ hkj h.symm
      simp [cubicCoordinateReflectionEquiv, cubicStepFrom, cubicDirectionIncrement, hkj, hji]
    · simp [cubicCoordinateReflectionEquiv, cubicStepFrom, cubicDirectionIncrement, hkj, hki]

private theorem cubicCoordinateReflection_adj {d : ℕ} (i : Fin d) {x y : Cubic d}
    (hxy : (cubicGraph d).Adj x y) :
    (cubicGraph d).Adj (cubicCoordinateReflectionEquiv i x)
      (cubicCoordinateReflectionEquiv i y) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  rw [cubicCoordinateReflection_stepFrom]
  exact cubicGraph_adj_stepFrom _ _

/-- Reflection of one coordinate as a cubic-graph automorphism. -/
def cubicCoordinateReflectionIso {d : ℕ} (i : Fin d) :
    cubicGraph d ≃g cubicGraph d where
  toEquiv := cubicCoordinateReflectionEquiv i
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have h' := cubicCoordinateReflection_adj i h
      simpa using h'
    · exact cubicCoordinateReflection_adj i

/-! ### Generic pullback along a cubic graph automorphism -/

/-- Pull a configuration back along the edge bijection induced by a cubic graph automorphism. -/
def cubicGraphIsoConfigurationPullback {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (ω : EdgeConfiguration d) : EdgeConfiguration d :=
  F.mapEdgeSet ⁻¹' ω

@[simp]
theorem cubicGraphIsoConfigurationPullback_symm {d : ℕ}
    (F : cubicGraph d ≃g cubicGraph d) (ω : EdgeConfiguration d) :
    cubicGraphIsoConfigurationPullback F.symm (cubicGraphIsoConfigurationPullback F ω) = ω := by
  ext e
  simp only [cubicGraphIsoConfigurationPullback, Set.mem_preimage]
  have hsymm : F.symm.mapEdgeSet = F.mapEdgeSet.symm := by
    ext e'
    rfl
  rw [hsymm]
  change F.mapEdgeSet (F.mapEdgeSet.symm e) ∈ ω ↔ e ∈ ω
  rw [Equiv.apply_symm_apply]

theorem measurable_cubicGraphIsoConfigurationPullback {d : ℕ}
    (F : cubicGraph d ≃g cubicGraph d) :
    Measurable (cubicGraphIsoConfigurationPullback F) :=
  measurable_preimage_embedding F.mapEdgeSet.toEmbedding

/-- The i.i.d. Bernoulli bond measure is invariant under any cubic graph automorphism. -/
theorem bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback
    {d : ℕ} (p : I) (F : cubicGraph d ≃g cubicGraph d) :
    (bernoulliBondMeasure d p).map (cubicGraphIsoConfigurationPullback F) =
      bernoulliBondMeasure d p := by
  simpa [bernoulliBondMeasure, cubicGraphIsoConfigurationPullback] using
    setBernoulli_map_preimage_univ F.mapEdgeSet.toEmbedding p

theorem walkIsOpen_map_cubicGraphIso {d : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    {u v : Cubic d} {ω : EdgeConfiguration d} (w : (cubicGraph d).Walk u v)
    (hw : walkIsOpen (cubicGraphIsoConfigurationPullback F ω) w) :
    walkIsOpen ω (w.map F.toHom) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  let ef : CubicEdge d := ⟨f, w.edges_subset_edgeSet hf⟩
  exact hw ef.1 hf

end Percolation
