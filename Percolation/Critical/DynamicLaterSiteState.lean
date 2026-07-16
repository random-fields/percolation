import Percolation.Critical.DynamicRootOutgoingSeeds

/-!
# Literal non-root source schedule

A non-root Grimmett--Marstrand block performs two inlet restarts and then one restart in every
direction except back toward its parent.  The target seed at each slot is a dependent finite
object because its witness type remembers the exit coordinate.  This file defines that finite
profile and runs the same global-boundary source recursion used by the completed root.
-/

namespace Percolation

open scoped unitInterval

/-- Number of restart slots at a non-root site. -/
def laterSiteSlotCount (d : ℕ) : ℕ := 2 * d + 1

/-- Slot type of the source schedule. -/
abbrev LaterSiteSlot (d : ℕ) := Fin (laterSiteSlotCount d)

/-- The literal direction attached to a non-root slot. -/
noncomputable def laterSiteSlotDirection
    {d : ℕ} (hd : 0 < d) (incoming : CubicDirection d)
    (k : LaterSiteSlot d) : CubicDirection d :=
  (laterSiteDirectionOrder incoming)[k.1]'(by
    simpa [laterSiteSlotCount, laterSiteDirectionOrder_length hd] using k.2)

@[simp]
theorem laterSiteSlotDirection_zero
    {d : ℕ} (hd : 0 < d) (incoming : CubicDirection d) :
    laterSiteSlotDirection hd incoming ⟨0, by simp [laterSiteSlotCount]⟩ = incoming := by
  simp [laterSiteSlotDirection, laterSiteDirectionOrder]

@[simp]
theorem laterSiteSlotDirection_one
    {d : ℕ} (hd : 0 < d) (incoming : CubicDirection d) :
    laterSiteSlotDirection hd incoming ⟨1, by
      simp [laterSiteSlotCount]; omega⟩ = incoming := by
  simp [laterSiteSlotDirection, laterSiteDirectionOrder]

/-- A finite profile naming the actual mixed target seed at every non-root slot. -/
structure LaterSiteMixedSeedProfile
    (d m n : ℕ) (hd : 0 < d) (incoming : CubicDirection d) where
  witness : ∀ k : LaterSiteSlot d,
    RestartSeedWitnessIndex d (laterSiteSlotDirection hd incoming k).1 m n

noncomputable instance laterSiteMixedSeedProfileFintype
    (d m n : ℕ) (hd : 0 < d) (incoming : CubicDirection d) :
    Fintype (LaterSiteMixedSeedProfile d m n hd incoming) := by
  let witnessType := ∀ k : LaterSiteSlot d,
    RestartSeedWitnessIndex d (laterSiteSlotDirection hd incoming k).1 m n
  let e : LaterSiteMixedSeedProfile d m n hd incoming ≃ witnessType :=
    { toFun := LaterSiteMixedSeedProfile.witness
      invFun := fun W ↦ ⟨W⟩
      left_inv := fun W ↦ by cases W; rfl
      right_inv := fun W ↦ rfl }
  exact Fintype.ofEquiv witnessType e.symm

noncomputable instance laterSiteMixedSeedProfileDecidableEq
    (d m n : ℕ) (hd : 0 < d) (incoming : CubicDirection d) :
    DecidableEq (LaterSiteMixedSeedProfile d m n hd incoming) :=
  Classical.decEq _

namespace LaterSiteMixedSeedProfile

/-- First inlet slot. -/
def firstSlot {d : ℕ} : LaterSiteSlot d := ⟨0, by simp [laterSiteSlotCount]⟩

/-- Second inlet slot; it exists because a valid cubic direction already forces `d>0`. -/
def secondSlot {d : ℕ} (hd : 0 < d) : LaterSiteSlot d := ⟨1, by
  simp [laterSiteSlotCount]
  omega⟩

/-- Center reached by the first inlet restart. -/
noncomputable def firstTargetCenter
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip : Fin d → Bool) : Cubic d :=
  cubicRestartFrameIso inletCenter
    (laterSiteSlotDirection hd incoming firstSlot) firstFlip
    (W.witness firstSlot).seedCenter.1

/-- Center reached by the second inlet restart.  This is the common center from which all
non-backtracking branch restarts start. -/
noncomputable def centralTargetCenter
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool) : Cubic d :=
  cubicRestartFrameIso (W.firstTargetCenter inletCenter firstFlip)
    (laterSiteSlotDirection hd incoming (secondSlot hd)) secondFlip
    (W.witness (secondSlot hd)).seedCenter.1

/-- Physical center from which slot `k` starts. -/
noncomputable def slotCenter
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (k : LaterSiteSlot d) : Cubic d :=
  if k.1 = 0 then inletCenter
  else if k.1 = 1 then W.firstTargetCenter inletCenter firstFlip
  else W.centralTargetCenter inletCenter firstFlip secondFlip

/-- Full transverse steering frame of slot `k`.  The two inlet frames are supplied by the
geometric caller; later branches use the source's away-from-inlet mask. -/
noncomputable def slotTransverseFlip
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (_W : LaterSiteMixedSeedProfile d m n hd incoming)
    (firstFlip secondFlip : Fin d → Bool) (k : LaterSiteSlot d) : Fin d → Bool :=
  if k.1 = 0 then firstFlip
  else if k.1 = 1 then secondFlip
  else awayFromInletTransverseFlip incoming (laterSiteSlotDirection hd incoming k)

@[simp]
theorem slotCenter_first
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool) :
    W.slotCenter inletCenter firstFlip secondFlip firstSlot = inletCenter := by
  simp [slotCenter, firstSlot]

@[simp]
theorem slotCenter_second
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool) :
    W.slotCenter inletCenter firstFlip secondFlip (secondSlot hd) =
      W.firstTargetCenter inletCenter firstFlip := by
  simp [slotCenter, secondSlot]

@[simp]
theorem slotTransverseFlip_first
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (firstFlip secondFlip : Fin d → Bool) :
    W.slotTransverseFlip firstFlip secondFlip firstSlot = firstFlip := by
  simp [slotTransverseFlip, firstSlot]

@[simp]
theorem slotTransverseFlip_second
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (firstFlip secondFlip : Fin d → Bool) :
    W.slotTransverseFlip firstFlip secondFlip (secondSlot hd) = secondFlip := by
  simp [slotTransverseFlip, secondSlot]

/-- Run the literal global-boundary recursion through a supplied list of non-root slots. -/
noncomputable def runExtensions
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    SourceFiniteEdgeRevealState d → List (LaterSiteSlot d) →
      SourceFiniteEdgeRevealState d
  | S, [] => S
  | S, k :: rest =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      W.runExtensions inletCenter firstFlip secondFlip p incremented X
        (S.next (Q.restartSupport m n) p (incremented S a) X) rest

@[simp]
theorem runExtensions_nil
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d) :
    W.runExtensions inletCenter firstFlip secondFlip p incremented X S [] = S :=
  rfl

@[simp]
theorem runExtensions_cons
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (k : LaterSiteSlot d) (rest : List (LaterSiteSlot d)) :
    W.runExtensions inletCenter firstFlip secondFlip p incremented X S (k :: rest) =
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      W.runExtensions inletCenter firstFlip secondFlip p incremented X
        (S.next (Q.restartSupport m n) p (incremented S a) X) rest :=
  rfl

/-- Running two pieces of the literal non-root schedule is sequential composition. -/
theorem runExtensions_append
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (first second : List (LaterSiteSlot d)) :
    W.runExtensions inletCenter firstFlip secondFlip p incremented X S
        (first ++ second) =
      W.runExtensions inletCenter firstFlip secondFlip p incremented X
        (W.runExtensions inletCenter firstFlip secondFlip p incremented X S first) second := by
  induction first generalizing S with
  | nil => rfl
  | cons k rest ih =>
      simp only [List.cons_append, runExtensions_cons]
      exact ih _

/-- A source exploration only enlarges its explored edge set along the non-root schedule. -/
theorem explored_subset_runExtensions
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d)) :
    S.explored ⊆
      (W.runExtensions inletCenter firstFlip secondFlip p incremented X S slots).explored := by
  induction slots generalizing S with
  | nil => exact Finset.Subset.rfl
  | cons k rest ih =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      exact (S.explored_subset_nextExplored
        (Q.restartSupport m n) p (incremented S a) X).trans
          (ih (S := S.next (Q.restartSupport m n) p (incremented S a) X))

/-- Literal conjunction of the named mixed witnesses along the supplied slot list. -/
def runMixedWitnesses
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    SourceFiniteEdgeRevealState d → List (LaterSiteSlot d) → Prop
  | _S, [] => True
  | S, k :: rest =>
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      (W.witness k).IsMixedRestartWitness Q.region p Q.beta delta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a flip) X) ∧
        W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X
          (S.next (Q.restartSupport m n) p (incremented S a) X) rest

@[simp]
theorem runMixedWitnesses_nil
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d) :
    W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X S [] :=
  trivial

@[simp]
theorem runMixedWitnesses_cons
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (k : LaterSiteSlot d) (rest : List (LaterSiteSlot d)) :
    W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X S (k :: rest) ↔
      let a := laterSiteSlotDirection hd incoming k
      let center := W.slotCenter inletCenter firstFlip secondFlip k
      let flip := W.slotTransverseFlip firstFlip secondFlip k
      let Q := S.framedQuery center a flip
      (W.witness k).IsMixedRestartWitness Q.region p Q.beta delta
          (cubicGraphIsoCouplingReindex
            (cubicRestartFrameIso center a flip) X) ∧
        W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X
          (S.next (Q.restartSupport m n) p (incremented S a) X) rest :=
  Iff.rfl

/-- The fixed named witnesses on an appended schedule split at the literal intermediate
source state. -/
theorem runMixedWitnesses_append
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (first second : List (LaterSiteSlot d)) :
    W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X S
        (first ++ second) ↔
      W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X S first ∧
        W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X
          (W.runExtensions inletCenter firstFlip secondFlip p incremented X S first) second := by
  induction first generalizing S with
  | nil => simp
  | cons k rest ih =>
      simp only [List.cons_append, runMixedWitnesses_cons, runExtensions_cons]
      rw [ih]
      tauto

/-- Success of the complete named schedule exposes the literal witness at each slot, evaluated
in the source state produced by the preceding slots. -/
theorem runMixedWitnesses_getElem
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : SourceFiniteEdgeRevealState d)
    (slots : List (LaterSiteSlot d))
    (hsuccess : W.runMixedWitnesses inletCenter firstFlip secondFlip
      p delta incremented X S slots)
    (j : ℕ) (hj : j < slots.length) :
    let k := slots[j]
    let Sj := W.runExtensions inletCenter firstFlip secondFlip p incremented X S
      (slots.take j)
    let a := laterSiteSlotDirection hd incoming k
    let center := W.slotCenter inletCenter firstFlip secondFlip k
    let flip := W.slotTransverseFlip firstFlip secondFlip k
    let Q := Sj.framedQuery center a flip
    (W.witness k).IsMixedRestartWitness Q.region p Q.beta delta
      (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a flip) X) := by
  have hsplit : slots = slots.take j ++ slots.drop j :=
    (List.take_append_drop j slots).symm
  rw [hsplit, W.runMixedWitnesses_append] at hsuccess
  have htail := hsuccess.2
  rw [List.drop_eq_getElem_cons hj] at htail
  exact htail.1

/-- Numeric slot order used by the source. -/
def slotOrder (d : ℕ) : List (LaterSiteSlot d) := List.finRange (laterSiteSlotCount d)

@[simp]
theorem slotOrder_length (d : ℕ) : (slotOrder d).length = laterSiteSlotCount d := by
  simp [slotOrder]

@[simp]
theorem slotOrder_getElem (d : ℕ) (j : ℕ)
    (hj : j < (slotOrder d).length) :
    (slotOrder d)[j] = ⟨j, by simpa [slotOrder] using hj⟩ := by
  simp [slotOrder]

/-- State before slot `k`. -/
noncomputable def prefixState
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (initial : SourceFiniteEdgeRevealState d) (k : ℕ) :
    SourceFiniteEdgeRevealState d :=
  W.runExtensions inletCenter firstFlip secondFlip p incremented X initial
    ((slotOrder d).take k)

/-- Semantic event that the fixed named profile succeeds through every non-root slot. -/
def event
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (initial : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d) :
    Set (CubicEdge d → ℝ) :=
  {X | W.runMixedWitnesses inletCenter firstFlip secondFlip p delta incremented X
    (initial X) (slotOrder d)}

/-- A realization of the fixed-profile non-root event carries its named mixed witness at every
slot of the source schedule. -/
theorem mixedWitness_of_mem_event
    {d m n : ℕ} {hd : 0 < d} {incoming : CubicDirection d}
    (W : LaterSiteMixedSeedProfile d m n hd incoming)
    (inletCenter : Cubic d) (firstFlip secondFlip : Fin d → Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (initial : (CubicEdge d → ℝ) → SourceFiniteEdgeRevealState d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.event inletCenter firstFlip secondFlip p delta incremented initial)
    (k : LaterSiteSlot d) :
    let S := W.prefixState inletCenter firstFlip secondFlip p incremented X (initial X) k.1
    let a := laterSiteSlotDirection hd incoming k
    let center := W.slotCenter inletCenter firstFlip secondFlip k
    let flip := W.slotTransverseFlip firstFlip secondFlip k
    let Q := S.framedQuery center a flip
    (W.witness k).IsMixedRestartWitness Q.region p Q.beta delta
      (cubicGraphIsoCouplingReindex (cubicRestartFrameIso center a flip) X) := by
  rcases k with ⟨k, hk⟩
  have hk' : k < (slotOrder d).length := by
    simpa [slotOrder] using hk
  have hslot := W.runMixedWitnesses_getElem inletCenter firstFlip secondFlip
    p delta incremented X (initial X) (slotOrder d) hX k hk'
  have hget : (slotOrder d)[k]'hk' = (⟨k, hk⟩ : LaterSiteSlot d) := by
    apply Fin.ext
    simp [slotOrder]
  rw [hget] at hslot
  simpa [prefixState] using hslot

end LaterSiteMixedSeedProfile

end Percolation
