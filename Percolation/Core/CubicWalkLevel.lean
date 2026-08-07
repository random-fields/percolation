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

/-- Edge-prefix strengthening of `exists_cubicWalk_prefix_to_level_of_end_le`.  It is the
downward counterpart of `exists_cubicWalk_edgePrefix_to_level_of_le_end` and is needed when a
last visit to a lower hyperplane is obtained by reversing a first-hit prefix. -/
theorem exists_cubicWalk_edgePrefix_to_level_of_end_le
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : a ≤ u i) (hv : v i ≤ a) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧ (∀ x ∈ q.support, a ≤ x i) ∧
        (∀ x ∈ q.support, x ∈ w.support) ∧ q.edges <+: w.edges := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_, ?_⟩
      · omega
      · simpa using hu
      · simp
      · exact List.nil_prefix
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_, ?_⟩
        · simp [hlevel]
        · simp
        · exact List.nil_prefix
      · have halt : a < u₀ i := lt_of_le_of_ne hu (Ne.symm hlevel)
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepLower : u₀ i ≤ u₁ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_sub_one_le u₀ dir i
        have hu₁ : a ≤ u₁ i := by omega
        obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSupport x hx)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            (List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩)

/-- First-hit strengthening of the downward edge-prefix lemma: the endpoint is the only vertex
of the retained prefix on the target level. -/
theorem exists_cubicWalk_edgePrefix_to_level_of_end_le_unique
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : a ≤ u i) (hv : v i ≤ a) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧ (∀ x ∈ q.support, a ≤ x i) ∧
        (∀ x ∈ q.support, x ∈ w.support) ∧ q.edges <+: w.edges ∧
        ∀ x ∈ q.support, x i = a → x = z := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_, List.nil_prefix, ?_⟩
      · omega
      · simpa using hu
      · simp
      · intro x hx _hxa
        simpa using hx
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_, List.nil_prefix, ?_⟩
        · simp [hlevel]
        · simp
        · intro x hx _hxa
          simpa using hx
      · have halt : a < u₀ i := lt_of_le_of_ne hu (Ne.symm hlevel)
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepLower : u₀ i ≤ u₁ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_sub_one_le u₀ dir i
        have hu₁ : a ≤ u₁ i := by omega
        obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix, hqUnique⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSupport x hx)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            (List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩)
        · intro x hx hxa
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact (hlevel hxa).elim
          · exact hqUnique x hx hxa

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

/-- Edge-prefix strengthening of `exists_cubicWalk_prefix_to_level_of_le_end`.  This version is
used when openness of the first-hit walk must be inherited from the original walk. -/
theorem exists_cubicWalk_edgePrefix_to_level_of_le_end
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : u i ≤ a) (hv : a ≤ v i) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧ (∀ x ∈ q.support, x i ≤ a) ∧
        (∀ x ∈ q.support, x ∈ w.support) ∧ q.edges <+: w.edges := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_, ?_⟩
      · omega
      · simpa using hu
      · simp
      · exact List.prefix_rfl
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_, ?_⟩
        · simp [hlevel]
        · simp
        · exact List.nil_prefix
      · have halt : u₀ i < a := lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepUpper : u₁ i ≤ u₀ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_le_add_one u₀ dir i
        have hu₁ : u₁ i ≤ a := by omega
        obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSupport x hx)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            (List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩)

/-- First-hit strengthening of the upward edge-prefix lemma: the endpoint is the only vertex of
the retained prefix on the target level. -/
theorem exists_cubicWalk_edgePrefix_to_level_of_le_end_unique
    {d : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {u v : Cubic d} (w : G.Walk u v) (i : Fin d) (a : ℤ)
    (hu : u i ≤ a) (hv : a ≤ v i) :
    ∃ z : Cubic d, ∃ q : G.Walk u z,
      z i = a ∧ (∀ x ∈ q.support, x i ≤ a) ∧
        (∀ x ∈ q.support, x ∈ w.support) ∧ q.edges <+: w.edges ∧
        ∀ x ∈ q.support, x i = a → x = z := by
  induction w with
  | nil =>
      refine ⟨_, .nil, ?_, ?_, ?_, List.prefix_rfl, ?_⟩
      · omega
      · simpa using hu
      · simp
      · intro x hx _hxa
        simpa using hx
  | @cons u₀ u₁ v₀ hu₀u₁ p ih =>
      by_cases hlevel : u₀ i = a
      · refine ⟨u₀, .nil, hlevel, ?_, ?_, List.nil_prefix, ?_⟩
        · simp [hlevel]
        · simp
        · intro x hx _hxa
          simpa using hx
      · have halt : u₀ i < a := lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨dir, hstep⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hstepUpper : u₁ i ≤ u₀ i + 1 := by
          simpa [hstep] using cubicStepFrom_coord_le_add_one u₀ dir i
        have hu₁ : u₁ i ≤ a := by omega
        obtain ⟨z, q, hz, hqSide, hqSupport, hqPrefix, hqUnique⟩ := ih hu₁ hv
        refine ⟨z, q.cons hu₀u₁, hz, ?_, ?_, ?_, ?_⟩
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hqSide x hx
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hqSupport x hx)
        · simpa only [SimpleGraph.Walk.edges_cons] using
            (List.cons_prefix_cons.mpr ⟨rfl, hqPrefix⟩)
        · intro x hx hxa
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact (hlevel hxa).elim
          · exact hqUnique x hx hxa

/-- An open cubic walk crossing a coordinate band contains an open simple subpath normalized at
its last visit to the lower level and first subsequent visit to the upper level.  The two level
hyperplanes meet the returned path only at its endpoints. -/
theorem exists_open_cubicPath_between_levels_normalized
    {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hwOpen : walkIsOpen ω w)
    (i : Fin d) (a b : ℤ) (hab : a ≤ b)
    (hu : u i ≤ a) (hv : b ≤ v i) :
    ∃ x y : Cubic d, ∃ q : (cubicGraph d).Walk x y,
      x i = a ∧ y i = b ∧ walkIsOpen ω q ∧ q.IsPath ∧
        q.edges ⊆ w.edges ∧
        (∀ z ∈ q.support, a ≤ z i ∧ z i ≤ b ∧ z ∈ w.support) ∧
        (∀ z ∈ q.support, z i = a → z = x) ∧
        ∀ z ∈ q.support, z i = b → z = y := by
  obtain ⟨y, p, hy, hpUpper, hpSupport, hpPrefix, hpUnique⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end_unique
      (G := cubicGraph d) le_rfl w i b (hu.trans hab) hv
  have hpOpen : walkIsOpen ω p :=
    walkIsOpen_of_edges_subset hwOpen hpPrefix.subset
  obtain ⟨x, r, hx, hrLower, hrSupport, hrPrefix, hrUnique⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_end_le_unique
      (G := cubicGraph d) le_rfl p.reverse i a
        (by simpa [hy] using hab) (by simpa using hu)
  have hrOpen : walkIsOpen ω r :=
    walkIsOpen_of_edges_subset (walkIsOpen_reverse hpOpen) hrPrefix.subset
  let q : (cubicGraph d).Walk x y := (r.reverse).toPath
  refine ⟨x, y, q, hx, hy, walkIsOpen_toPath r.reverse
    (walkIsOpen_reverse hrOpen), (r.reverse).toPath.2, ?_, ?_, ?_, ?_⟩
  · intro e he
    have heReverse : e ∈ r.reverse.edges := r.reverse.edges_toPath_subset he
    have heR : e ∈ r.edges := by simpa using heReverse
    have hePReverse : e ∈ p.reverse.edges := hrPrefix.subset heR
    have heP : e ∈ p.edges := by simpa using hePReverse
    exact hpPrefix.subset heP
  · intro z hz
    have hzReverse : z ∈ r.reverse.support :=
      SimpleGraph.Walk.support_toPath_subset r.reverse hz
    have hzR : z ∈ r.support := by simpa using hzReverse
    have hzPReverse : z ∈ p.reverse.support := hrSupport z hzR
    have hzP : z ∈ p.support := by simpa using hzPReverse
    exact ⟨hrLower z hzR, hpUpper z hzP, hpSupport z hzP⟩
  · intro z hz hza
    have hzReverse : z ∈ r.reverse.support :=
      SimpleGraph.Walk.support_toPath_subset r.reverse hz
    have hzR : z ∈ r.support := by simpa using hzReverse
    exact hrUnique z hzR hza
  · intro z hz hzb
    have hzReverse : z ∈ r.reverse.support :=
      SimpleGraph.Walk.support_toPath_subset r.reverse hz
    have hzR : z ∈ r.support := by simpa using hzReverse
    have hzPReverse : z ∈ p.reverse.support := hrSupport z hzR
    have hzP : z ∈ p.support := by simpa using hzPReverse
    exact hpUnique z hzP hzb

end Percolation
