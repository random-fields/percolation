import Percolation.Core.Cubic

/-!
# First level hits of cubic walks

A nearest-neighbor cubic walk cannot jump over an integer coordinate hyperplane.  The lemmas
below strengthen this discrete intermediate-value fact by returning an initial subwalk that
stays on the starting side of the hyperplane.  This is the deterministic first-hit operation
needed when neighboring renormalization boxes overlap.
-/

namespace Percolation

/-- Starting above a coordinate level and ending below it, a walk has an initial subwalk to
that level whose vertices all remain above the level. -/
theorem exists_cubicWalk_prefix_to_level_of_end_le
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : a ≤ u i) (hv : v i ≤ a) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧
        (∀ x ∈ q.support, a ≤ x i) ∧
        ∀ x ∈ q.support, x ∈ w.support := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_⟩
      · omega
      · simpa using hu
      · simp
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_⟩ <;> simp [hlevel]
      · have halt : a < u₀ i := lt_of_le_of_ne hu (Ne.symm hlevel)
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepLower : u₀ i ≤ u₁ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_sub_one_le u₀ dir i
        have hu₁ : a ≤ u₁ i := by omega
        obtain ⟨z, q, hz, hqSide, hqSub⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSub x hx)

/-- Starting below a coordinate level and ending above it, a walk has an initial subwalk to
that level whose vertices all remain below the level. -/
theorem exists_cubicWalk_prefix_to_level_of_le_end
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : u i ≤ a) (hv : a ≤ v i) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧
        (∀ x ∈ q.support, x i ≤ a) ∧
        ∀ x ∈ q.support, x ∈ w.support := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_⟩
      · omega
      · simpa using hu
      · simp
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_⟩ <;> simp [hlevel]
      · have halt : u₀ i < a := lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepUpper : u₁ i ≤ u₀ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_le_add_one u₀ dir i
        have hu₁ : u₁ i ≤ a := by omega
        obtain ⟨z, q, hz, hqSide, hqSub⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSub x hx)

end Percolation
