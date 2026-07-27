import Percolation.Critical.DynamicEdgeExploration

/-!
# Recursive heterogeneous edge updates

After the first radial phase, Grimmett's lower boundary threshold is edge-dependent.  This file
generalizes the finite line-graph exploration from a constant increment to the literal family
`e ↦ beta_k(e) + delta` and proves that one such recursive step realizes the complete updated
interval profile.  No independence or probability assertion is used here: this is the
deterministic uniform-label semantics of equations (7.31)--(7.34).
-/

namespace Percolation

open scoped unitInterval

/-- The literal source increment `beta(e) + delta`, packaged in the unit interval only after
the caller proves the global reveal budget. -/
def revealThresholdIncrement {d : ℕ}
    (beta : CubicEdge d → I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hbudget : ∀ e, (beta e : ℝ) + delta ≤ 1) : CubicEdge d → I :=
  fun e ↦ ⟨(beta e : ℝ) + delta,
    add_nonneg (beta e).2.1 hdelta, hbudget e⟩

@[simp]
theorem coe_revealThresholdIncrement {d : ℕ}
    (beta : CubicEdge d → I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hbudget : ∀ e, (beta e : ℝ) + delta ≤ 1) (e : CubicEdge d) :
    (revealThresholdIncrement beta delta hdelta hbudget e : ℝ) =
      (beta e : ℝ) + delta :=
  rfl

theorem le_revealThresholdIncrement {d : ℕ}
    (beta : CubicEdge d → I) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hbudget : ∀ e, (beta e : ℝ) + delta ≤ 1) (e : CubicEdge d) :
    beta e ≤ revealThresholdIncrement beta delta hdelta hbudget e := by
  change (beta e : ℝ) ≤ (beta e : ℝ) + delta
  linarith

/-- Edges in a finite support whose common-uniform labels lie below an edgewise threshold. -/
noncomputable def finiteEdgesBelowFamily {d : ℕ}
    (E : Finset (CubicEdge d)) (q : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) := by
  classical
  exact E.filter fun e ↦ X e < (q e : ℝ)

@[simp]
theorem mem_finiteEdgesBelowFamily_iff {d : ℕ}
    {E : Finset (CubicEdge d)} {q : CubicEdge d → I} {X : CubicEdge d → ℝ}
    {e : CubicEdge d} :
    e ∈ finiteEdgesBelowFamily E q X ↔ e ∈ E ∧ X e < (q e : ℝ) := by
  classical
  simp [finiteEdgesBelowFamily]

theorem finiteEdgesBelowFamily_subset {d : ℕ}
    (E : Finset (CubicEdge d)) (q : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    finiteEdgesBelowFamily E q X ⊆ E := by
  intro e he
  exact (mem_finiteEdgesBelowFamily_iff.mp he).1

/-- Literal heterogeneous successor `E_{k+1}`: enter across an old boundary edge open at its
incremented threshold, then continue through exterior edges open at the background density. -/
noncomputable def exploredEdgeStepFamily {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  let openBoundary := finiteEdgesBelowFamily oldBoundary incremented X
  let openExterior := finiteEdgesBelow exterior p X
  nextExploredEdgeSet oldExplored (openBoundary ∪ openExterior) openBoundary

/-- The heterogeneous exploration specializes exactly to the constant-threshold first radial
exploration. -/
theorem exploredEdgeStepFamily_const {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p incremented : I) (X : CubicEdge d → ℝ) :
    exploredEdgeStepFamily oldExplored oldBoundary exterior p
        (fun _ ↦ incremented) X =
      exploredEdgeStep oldExplored oldBoundary exterior p incremented X := by
  classical
  simp [exploredEdgeStepFamily, exploredEdgeStep,
    finiteEdgesBelowFamily, finiteEdgesBelow]

theorem oldExplored_subset_exploredEdgeStepFamily {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    oldExplored ⊆ exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X :=
  oldExplored_subset_nextExploredEdgeSet _ _ _

theorem openBoundary_subset_exploredEdgeStepFamily {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    finiteEdgesBelowFamily oldBoundary incremented X ⊆
      exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X := by
  let B := finiteEdgesBelowFamily oldBoundary incremented X
  let A := B ∪ finiteEdgesBelow exterior p X
  change B ⊆ nextExploredEdgeSet oldExplored A B
  exact (sources_subset_finiteEdgeReachableClosure
      (allowed := A) (sources := B) Finset.subset_union_left).trans
    (finiteEdgeReachableClosure_subset_nextExploredEdgeSet oldExplored A B)

theorem exploredEdgeStepFamily_subset {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X ⊆
      oldExplored ∪ oldBoundary ∪ exterior := by
  intro e he
  rw [exploredEdgeStepFamily, nextExploredEdgeSet, Finset.mem_union] at he
  rcases he with heOld | heClosure
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ heOld)
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heBoundary | heExterior
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (finiteEdgesBelowFamily_subset _ _ _ heBoundary))
    · exact Finset.mem_union_right _ (finiteEdgesBelow_subset _ _ _ heExterior)

theorem label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStepFamily
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hold : Disjoint oldBoundary oldExplored)
    (hexterior : Disjoint oldBoundary exterior)
    {e : CubicEdge d} (heBoundary : e ∈ oldBoundary)
    (heNext : e ∈
      exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X) :
    X e < (incremented e : ℝ) := by
  have heNotOld : e ∉ oldExplored := fun heOld ↦
    Finset.disjoint_left.mp hold heBoundary heOld
  rw [exploredEdgeStepFamily, nextExploredEdgeSet, Finset.mem_union] at heNext
  rcases heNext with heOld | heClosure
  · exact (heNotOld heOld).elim
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heOpenBoundary | heOpenExterior
    · exact (mem_finiteEdgesBelowFamily_iff.mp heOpenBoundary).2
    · exact (Finset.disjoint_left.mp hexterior heBoundary
        (mem_finiteEdgesBelow_iff.mp heOpenExterior).1).elim

theorem incremented_le_label_of_mem_oldBoundary_not_mem_exploredEdgeStepFamily
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    {e : CubicEdge d} (heBoundary : e ∈ oldBoundary)
    (heNotNext : e ∉
      exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X) :
    (incremented e : ℝ) ≤ X e := by
  apply le_of_not_gt
  intro heOpen
  apply heNotNext
  exact openBoundary_subset_exploredEdgeStepFamily
    oldExplored oldBoundary exterior p incremented X
    (mem_finiteEdgesBelowFamily_iff.mpr ⟨heBoundary, heOpen⟩)

theorem label_lt_density_of_mem_exploredEdgeStepFamily_not_old_not_boundary
    {d : ℕ}
    (oldExplored oldBoundary exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    {e : CubicEdge d}
    (heNext : e ∈
      exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X)
    (heNotOld : e ∉ oldExplored) (heNotBoundary : e ∉ oldBoundary) :
    X e < (p : ℝ) := by
  rw [exploredEdgeStepFamily, nextExploredEdgeSet, Finset.mem_union] at heNext
  rcases heNext with heOld | heClosure
  · exact (heNotOld heOld).elim
  · have heAllowed := finiteEdgeReachableClosure_subset_allowed _ _ heClosure
    rw [Finset.mem_union] at heAllowed
    rcases heAllowed with heOpenBoundary | heOpenExterior
    · exact (heNotBoundary (mem_finiteEdgesBelowFamily_iff.mp heOpenBoundary).1).elim
    · exact (mem_finiteEdgesBelow_iff.mp heOpenExterior).2

theorem density_le_label_of_mem_newBoundaryFamily_not_oldBoundary
    {d : ℕ}
    (oldExplored oldBoundary ambient exterior : Finset (CubicEdge d))
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hlineBoundary : cubicEdgeBoundaryWithin oldExplored ambient ⊆ oldBoundary)
    (hexterior : exterior = ambient \ (oldExplored ∪ oldBoundary))
    {e : CubicEdge d}
    (heNew : e ∈ cubicEdgeBoundaryWithin
      (exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X) ambient)
    (heNotOldBoundary : e ∉ oldBoundary) :
    (p : ℝ) ≤ X e := by
  apply le_of_not_gt
  intro heOpen
  obtain ⟨heAmbient, heNotNext, f, hfNext, hfe⟩ :=
    mem_cubicEdgeBoundaryWithin_iff.mp heNew
  have heNotOld : e ∉ oldExplored := fun heOld ↦
    heNotNext (oldExplored_subset_exploredEdgeStepFamily
      oldExplored oldBoundary exterior p incremented X heOld)
  have heExterior : e ∈ exterior := by
    rw [hexterior, Finset.mem_sdiff, Finset.mem_union]
    exact ⟨heAmbient, fun h ↦ h.elim heNotOld heNotOldBoundary⟩
  have heAllowed : e ∈
      finiteEdgesBelowFamily oldBoundary incremented X ∪ finiteEdgesBelow exterior p X :=
    Finset.mem_union_right _ (mem_finiteEdgesBelow_iff.mpr ⟨heExterior, heOpen⟩)
  rw [exploredEdgeStepFamily, nextExploredEdgeSet, Finset.mem_union] at hfNext
  rcases hfNext with hfOld | hfClosure
  · apply heNotOldBoundary
    apply hlineBoundary
    rw [mem_cubicEdgeBoundaryWithin_iff]
    exact ⟨heAmbient, heNotOld, f, hfOld, hfe⟩
  · apply heNotNext
    rw [exploredEdgeStepFamily, nextExploredEdgeSet, Finset.mem_union]
    exact Or.inr (mem_finiteEdgeReachableClosure_of_adj hfClosure heAllowed hfe)

/-- When both boundaries are the literal line-graph boundaries and the explored set grows, the
two cases in (7.31) cover exactly the new boundary—neither dropping nor inventing a closed
coordinate. -/
theorem edgeBoundary_sdiff_update_eq
    {d : ℕ} (oldExplored nextExplored ambient : Finset (CubicEdge d))
    (hmono : oldExplored ⊆ nextExplored) :
    cubicEdgeBoundaryWithin oldExplored ambient \ nextExplored ∪
        ((cubicEdgeBoundaryWithin nextExplored ambient \
          cubicEdgeBoundaryWithin oldExplored ambient) ∩ ambient) =
      cubicEdgeBoundaryWithin nextExplored ambient := by
  classical
  ext e
  constructor
  · intro he
    rw [Finset.mem_union] at he
    rcases he with heOld | heNew
    · obtain ⟨heOldBoundary, heNotNext⟩ := Finset.mem_sdiff.mp heOld
      obtain ⟨heAmbient, _heNotOld, f, hfOld, hfe⟩ :=
        mem_cubicEdgeBoundaryWithin_iff.mp heOldBoundary
      rw [mem_cubicEdgeBoundaryWithin_iff]
      exact ⟨heAmbient, heNotNext, f, hmono hfOld, hfe⟩
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp heNew).1).1
  · intro heNextBoundary
    have heNotNext := (mem_cubicEdgeBoundaryWithin_iff.mp heNextBoundary).2.1
    by_cases heOldBoundary : e ∈ cubicEdgeBoundaryWithin oldExplored ambient
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨heOldBoundary, heNotNext⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨heNextBoundary, heOldBoundary⟩,
          (mem_cubicEdgeBoundaryWithin_iff.mp heNextBoundary).1⟩)

/-- One heterogeneous source step realizes its exact new interval profile.  The old-open
hypothesis is precisely the open half of the preceding profile; the old closed half is consumed
when deciding which boundary exits are available. -/
theorem exploredEdgeStepFamily_mem_updatedProfile
    {d : ℕ}
    (oldExplored oldBoundary ambient : Finset (CubicEdge d))
    (lower upper incremented : CubicEdge d → I) (p : I)
    (X : CubicEdge d → ℝ)
    (holdBoundary : Disjoint oldBoundary oldExplored)
    (holdBoundaryAmbient : oldBoundary ⊆ ambient)
    (hlineBoundary : cubicEdgeBoundaryWithin oldExplored ambient ⊆ oldBoundary)
    (holdOpen : ∀ e ∈ oldExplored, X e < (upper e : ℝ)) :
    let exterior := ambient \ (oldExplored ∪ oldBoundary)
    let nextExplored :=
      exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X
    let nextBoundary := cubicEdgeBoundaryWithin nextExplored ambient
    let D : RevealThresholdUpdateData (CubicEdge d) :=
      { oldExplored := oldExplored
        nextExplored := nextExplored
        oldBoundary := oldBoundary
        nextBoundary := nextBoundary
        ambient := ambient
        lower := lower
        upper := upper
        incremented := incremented
        density := p }
    X ∈ D.updatedProfile.event := by
  dsimp only
  let exterior := ambient \ (oldExplored ∪ oldBoundary)
  let nextExplored :=
    exploredEdgeStepFamily oldExplored oldBoundary exterior p incremented X
  let nextBoundary := cubicEdgeBoundaryWithin nextExplored ambient
  let D : RevealThresholdUpdateData (CubicEdge d) :=
    { oldExplored := oldExplored
      nextExplored := nextExplored
      oldBoundary := oldBoundary
      nextBoundary := nextBoundary
      ambient := ambient
      lower := lower
      upper := upper
      incremented := incremented
      density := p }
  rw [RevealThresholdUpdateData.mem_updatedProfile_event_iff]
  constructor
  · intro e heClosed
    rw [RevealThresholdUpdateData.updatedClosedSupport, Finset.mem_union] at heClosed
    rcases heClosed with heOld | heNew
    · have heBoundary := (Finset.mem_sdiff.mp heOld).1
      have heNotNext := (Finset.mem_sdiff.mp heOld).2
      rw [RevealThresholdUpdateData.updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
        D (holdBoundaryAmbient heBoundary) heBoundary heNotNext]
      exact incremented_le_label_of_mem_oldBoundary_not_mem_exploredEdgeStepFamily
        oldExplored oldBoundary exterior p incremented X heBoundary heNotNext
    · obtain ⟨heNewBoundary, heNotOldBoundary⟩ :=
        Finset.mem_sdiff.mp (Finset.mem_inter.mp heNew).1
      have heAmbient := (Finset.mem_inter.mp heNew).2
      rw [RevealThresholdUpdateData.updatedLower_eq_density_of_mem_newBoundary
        D heAmbient heNewBoundary heNotOldBoundary]
      exact density_le_label_of_mem_newBoundaryFamily_not_oldBoundary
        oldExplored oldBoundary ambient exterior p incremented X hlineBoundary rfl
        heNewBoundary heNotOldBoundary
  · intro e heNext
    by_cases heOld : e ∈ oldExplored
    · rw [RevealThresholdUpdateData.updatedUpper_eq_old_of_mem_oldExplored D heOld]
      exact holdOpen e heOld
    · by_cases heBoundary : e ∈ oldBoundary
      · rw [RevealThresholdUpdateData.updatedUpper_eq_incremented_of_mem_absorbedBoundary
          D heOld heBoundary heNext]
        have hboundaryExterior : Disjoint oldBoundary exterior := by
          rw [Finset.disjoint_left]
          intro f hfBoundary hfExterior
          exact (Finset.mem_sdiff.mp hfExterior).2
            (Finset.mem_union_right _ hfBoundary)
        exact label_lt_incremented_of_mem_oldBoundary_mem_exploredEdgeStepFamily
          oldExplored oldBoundary exterior p incremented X holdBoundary
          hboundaryExterior heBoundary heNext
      · rw [RevealThresholdUpdateData.updatedUpper_eq_density_of_mem_newInterior
          D heOld heBoundary heNext]
        exact label_lt_density_of_mem_exploredEdgeStepFamily_not_old_not_boundary
          oldExplored oldBoundary exterior p incremented X heNext heOld heBoundary

/-! ### A recursively composable source state -/

/-- Finite deterministic state carried between source restart stages.  Its closed support is
derived from the literal line boundary, so the recursive invariant cannot accidentally use an
unrelated advertised boundary. -/
structure FiniteEdgeRevealState (d : ℕ) where
  ambient : Finset (CubicEdge d)
  explored : Finset (CubicEdge d)
  lower : CubicEdge d → I
  upper : CubicEdge d → I

namespace FiniteEdgeRevealState

noncomputable def boundary {d : ℕ} (S : FiniteEdgeRevealState d) :
    Finset (CubicEdge d) :=
  cubicEdgeBoundaryWithin S.explored S.ambient

noncomputable def exterior {d : ℕ} (S : FiniteEdgeRevealState d) :
    Finset (CubicEdge d) :=
  S.ambient \ (S.explored ∪ S.boundary)

noncomputable def profile {d : ℕ} (S : FiniteEdgeRevealState d) :
    FiniteRevealIntervalProfile (CubicEdge d) where
  closedSupport := S.boundary
  openSupport := S.explored
  lower := S.lower
  upper := S.upper

/-- The next explored edge set at an edgewise increment. -/
noncomputable def nextExplored {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    Finset (CubicEdge d) :=
  exploredEdgeStepFamily S.explored S.boundary S.exterior p incremented X

/-- Exact threshold-update record associated to a recursive edge step. -/
noncomputable def updateData {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    RevealThresholdUpdateData (CubicEdge d) where
  oldExplored := S.explored
  nextExplored := S.nextExplored p incremented X
  oldBoundary := S.boundary
  nextBoundary := cubicEdgeBoundaryWithin (S.nextExplored p incremented X) S.ambient
  ambient := S.ambient
  lower := S.lower
  upper := S.upper
  incremented := incremented
  density := p

/-- Source successor state after one heterogeneous exploration. -/
noncomputable def next {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    FiniteEdgeRevealState d where
  ambient := S.ambient
  explored := S.nextExplored p incremented X
  lower := (S.updateData p incremented X).updatedLower
  upper := (S.updateData p incremented X).updatedUpper

theorem explored_subset_nextExplored {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    S.explored ⊆ S.nextExplored p incremented X :=
  oldExplored_subset_exploredEdgeStepFamily _ _ _ _ _ _

theorem updateData_updatedClosedSupport_eq_nextBoundary
    {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    (S.updateData p incremented X).updatedClosedSupport =
      (S.next p incremented X).boundary := by
  simpa [updateData, next, boundary, RevealThresholdUpdateData.updatedClosedSupport]
    using edgeBoundary_sdiff_update_eq S.explored
      (S.nextExplored p incremented X) S.ambient
      (S.explored_subset_nextExplored p incremented X)

/-- The abstract update profile is exactly the canonical boundary/explored profile of the
successor state. -/
theorem next_profile_eq_updatedProfile
    {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    (S.next p incremented X).profile =
      (S.updateData p incremented X).updatedProfile := by
  unfold profile RevealThresholdUpdateData.updatedProfile
  rw [← S.updateData_updatedClosedSupport_eq_nextBoundary p incremented X]
  rfl

/-- Recursive interval invariant: a realization of the current canonical state profile is a
realization of the successor profile produced by the literal heterogeneous edge exploration. -/
theorem mem_next_profile
    {d : ℕ} (S : FiniteEdgeRevealState d)
    (p : I) (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (S.next p incremented X).profile.event := by
  rw [S.next_profile_eq_updatedProfile p incremented X]
  apply exploredEdgeStepFamily_mem_updatedProfile
    S.explored S.boundary S.ambient S.lower S.upper incremented p X
    (disjoint_cubicEdgeBoundaryWithin_left _ _)
    (cubicEdgeBoundaryWithin_subset_ambient _ _)
    (fun _ he ↦ he)
  exact hcurrent.2

/-- Iterate the literal edge-state update through a finite source schedule of edgewise
increments.  The ambient support and background density stay fixed while `E_k, beta_k,
gamma_k` evolve. -/
noncomputable def run {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) : List (CubicEdge d → I) → FiniteEdgeRevealState d
  | [] => S
  | incremented :: rest => (S.next p incremented X).run p X rest

@[simp]
theorem run_nil {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) :
    S.run p X [] = S :=
  rfl

@[simp]
theorem run_cons {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) (incremented : CubicEdge d → I)
    (rest : List (CubicEdge d → I)) :
    S.run p X (incremented :: rest) = (S.next p incremented X).run p X rest :=
  rfl

/-- Exact interval invariance through any finite sequence of the heterogeneous source update. -/
theorem mem_run_profile {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) (increments : List (CubicEdge d → I))
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (S.run p X increments).profile.event := by
  induction increments generalizing S with
  | nil => exact hcurrent
  | cons incremented rest ih =>
      exact ih (S := S.next p incremented X)
        (S.mem_next_profile p incremented X hcurrent)

/-! ### Stage-dependent finite regions -/

/-- Replace the finite region `E_Z` while retaining the explored set and accumulated
thresholds.  This operation is safe only after proving that the literal edge boundary has not
changed; see `withAmbient_profile_eq_of_boundary_eq`. -/
noncomputable def withAmbient {d : ℕ} (S : FiniteEdgeRevealState d)
    (ambient : Finset (CubicEdge d)) : FiniteEdgeRevealState d where
  ambient := ambient
  explored := S.explored
  lower := S.lower
  upper := S.upper

@[simp]
theorem withAmbient_explored {d : ℕ} (S : FiniteEdgeRevealState d)
    (ambient : Finset (CubicEdge d)) :
    (S.withAmbient ambient).explored = S.explored :=
  rfl

/-- Changing the stage region preserves the canonical interval profile exactly when it
preserves the actual line boundary of the explored set.  This makes the required geometric
freshness condition visible instead of silently treating all stages as having one ambient
box. -/
theorem withAmbient_profile_eq_of_boundary_eq {d : ℕ}
    (S : FiniteEdgeRevealState d) (ambient : Finset (CubicEdge d))
    (hboundary : cubicEdgeBoundaryWithin S.explored ambient = S.boundary) :
    (S.withAmbient ambient).profile = S.profile := by
  unfold boundary at hboundary
  unfold profile withAmbient boundary
  rw [hboundary]

/-- A checkable sufficient condition for safely changing the finite stage region: it contains
the old region and adds no edge line-adjacent to the currently explored set. -/
theorem withAmbient_profile_eq_of_subset_of_no_new_adj {d : ℕ}
    (S : FiniteEdgeRevealState d) (ambient : Finset (CubicEdge d))
    (hsubset : S.ambient ⊆ ambient)
    (hnew : ∀ e ∈ ambient, e ∉ S.ambient →
      ∀ f ∈ S.explored, ¬ (cubicEdgeLineGraph d).Adj f e) :
    (S.withAmbient ambient).profile = S.profile := by
  apply S.withAmbient_profile_eq_of_boundary_eq
  exact cubicEdgeBoundaryWithin_eq_of_subset_of_no_new_adj
    S.explored S.ambient ambient hsubset hnew

/-- One source update in a possibly different finite region `E_Z`. -/
noncomputable def nextWithin {d : ℕ} (S : FiniteEdgeRevealState d)
    (ambient : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ) :
    FiniteEdgeRevealState d :=
  (S.withAmbient ambient).next p incremented X

/-- Exact interval invariance for a stage-dependent finite region.  The explicit boundary
equality is the source-faithful handoff obligation between consecutive steering boxes. -/
theorem mem_nextWithin_profile {d : ℕ} (S : FiniteEdgeRevealState d)
    (ambient : Finset (CubicEdge d)) (p : I)
    (incremented : CubicEdge d → I) (X : CubicEdge d → ℝ)
    (hboundary : cubicEdgeBoundaryWithin S.explored ambient = S.boundary)
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (S.nextWithin ambient p incremented X).profile.event := by
  apply (S.withAmbient ambient).mem_next_profile p incremented X
  rw [S.withAmbient_profile_eq_of_boundary_eq ambient hboundary]
  exact hcurrent

/-- Run the recursive construction through the literal sequence of changing finite regions
and edgewise threshold increments. -/
noncomputable def runWithin {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) :
    List (Finset (CubicEdge d) × (CubicEdge d → I)) → FiniteEdgeRevealState d
  | [] => S
  | (ambient, incremented) :: rest =>
      (S.nextWithin ambient p incremented X).runWithin p X rest

@[simp]
theorem runWithin_nil {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) : S.runWithin p X [] = S :=
  rfl

@[simp]
theorem runWithin_cons {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ) (ambient : Finset (CubicEdge d))
    (incremented : CubicEdge d → I)
    (rest : List (Finset (CubicEdge d) × (CubicEdge d → I))) :
    S.runWithin p X ((ambient, incremented) :: rest) =
      (S.nextWithin ambient p incremented X).runWithin p X rest :=
  rfl

/-- Interval invariance through a changing-region schedule, provided each region exposes
exactly the already-recorded boundary before its update. -/
theorem mem_runWithin_profile {d : ℕ} (S : FiniteEdgeRevealState d) (p : I)
    (X : CubicEdge d → ℝ)
    (stages : List (Finset (CubicEdge d) × (CubicEdge d → I)))
    (hboundary : ∀ j (hj : j < stages.length),
      let state := S.runWithin p X (stages.take j)
      cubicEdgeBoundaryWithin state.explored (stages[j].1) = state.boundary)
    (hcurrent : X ∈ S.profile.event) :
    X ∈ (S.runWithin p X stages).profile.event := by
  induction stages generalizing S with
  | nil => exact hcurrent
  | cons stage rest ih =>
      rcases stage with ⟨ambient, incremented⟩
      have hfirst : cubicEdgeBoundaryWithin S.explored ambient = S.boundary := by
        simpa using hboundary 0 (by simp)
      apply ih (S := S.nextWithin ambient p incremented X)
      · intro j hj
        have hs := hboundary (j + 1) (by simp; omega)
        simpa [List.take_succ_cons] using hs
      · exact S.mem_nextWithin_profile ambient p incremented X hfirst hcurrent

end FiniteEdgeRevealState

end Percolation
