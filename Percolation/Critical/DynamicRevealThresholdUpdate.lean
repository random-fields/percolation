import Percolation.Critical.DynamicRevealIntervals

/-!
# Threshold updates for Grimmett's dynamic exploration

Equations (7.31)--(7.32) update three pieces of finite state after a successful restart:
the explored edge set, the lower thresholds at which edges are known closed, and the upper
thresholds at which edges are known open.  This file records the equations independently of the
later geometric proof that the newly explored set is the union of all admissible paths.

The `incremented` field is supplied as a unit-interval value.  In the source it is
`lower(e) + delta`; separating its construction avoids silently clamping a threshold above one.
The eventual block program must prove the advertised equality and the global reveal budget.
-/

namespace Percolation

open scoped unitInterval

/-- Finite data entering one application of the update rules (7.31)--(7.32). -/
structure RevealThresholdUpdateData (ι : Type*) where
  oldExplored : Finset ι
  nextExplored : Finset ι
  oldBoundary : Finset ι
  nextBoundary : Finset ι
  ambient : Finset ι
  lower : ι → I
  upper : ι → I
  incremented : ι → I
  density : I

namespace RevealThresholdUpdateData

variable {ι : Type*} [DecidableEq ι]

/-- Equation (7.31), with the source's first-step zero replaced by the previous lower threshold.
For the initial state the two formulations are definitionally equal. -/
def updatedLower (D : RevealThresholdUpdateData ι) (e : ι) : I :=
  if e ∉ D.ambient then D.lower e
  else if e ∈ D.oldBoundary \ D.nextExplored then D.incremented e
  else if e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient then D.density
  else D.lower e

/-- Equation (7.32), retaining the previous upper threshold outside the newly inspected cases. -/
def updatedUpper (D : RevealThresholdUpdateData ι) (e : ι) : I :=
  if e ∈ D.oldExplored then D.upper e
  else if e ∈ D.oldBoundary ∩ D.nextExplored then D.incremented e
  else if e ∈ D.nextExplored \ (D.oldExplored ∪ D.oldBoundary) then D.density
  else D.upper e

/-- All nontrivial closed constraints retained or learned by this update. -/
def updatedClosedSupport (D : RevealThresholdUpdateData ι) : Finset ι :=
  D.oldBoundary \ D.nextExplored ∪
    ((D.nextBoundary \ D.oldBoundary) ∩ D.ambient)

/-- The source knows every edge of the new explored set open at its updated upper threshold. -/
def updatedOpenSupport (D : RevealThresholdUpdateData ι) : Finset ι :=
  D.nextExplored

/-- Finite interval profile produced by one source threshold update. -/
def updatedProfile (D : RevealThresholdUpdateData ι) : FiniteRevealIntervalProfile ι where
  closedSupport := D.updatedClosedSupport
  openSupport := D.updatedOpenSupport
  lower := D.updatedLower
  upper := D.updatedUpper

@[simp]
theorem updatedProfile_closedSupport (D : RevealThresholdUpdateData ι) :
    D.updatedProfile.closedSupport = D.updatedClosedSupport :=
  rfl

@[simp]
theorem updatedProfile_openSupport (D : RevealThresholdUpdateData ι) :
    D.updatedProfile.openSupport = D.nextExplored :=
  rfl

@[simp]
theorem updatedProfile_lower (D : RevealThresholdUpdateData ι) :
    D.updatedProfile.lower = D.updatedLower :=
  rfl

@[simp]
theorem updatedProfile_upper (D : RevealThresholdUpdateData ι) :
    D.updatedProfile.upper = D.updatedUpper :=
  rfl

theorem updatedLower_eq_old_of_not_mem_ambient
    (D : RevealThresholdUpdateData ι) {e : ι} (he : e ∉ D.ambient) :
    D.updatedLower e = D.lower e := by
  simp [updatedLower, he]

theorem updatedLower_eq_incremented_of_mem_oldBoundary_not_nextExplored
    (D : RevealThresholdUpdateData ι) {e : ι}
    (heAmbient : e ∈ D.ambient) (heBoundary : e ∈ D.oldBoundary)
    (heNext : e ∉ D.nextExplored) :
    D.updatedLower e = D.incremented e := by
  simp [updatedLower, heAmbient, heBoundary, heNext]

theorem updatedLower_eq_density_of_mem_newBoundary
    (D : RevealThresholdUpdateData ι) {e : ι}
    (heAmbient : e ∈ D.ambient) (heNew : e ∈ D.nextBoundary)
    (heOld : e ∉ D.oldBoundary) :
    D.updatedLower e = D.density := by
  simp [updatedLower, heAmbient, heNew, heOld]

/-- An edge admitted to the successor explored set retains its previous lower endpoint.  The
new information at that coordinate is an upper bound; retaining the old lower bound is what
turns the state profile into the exact accumulated history interval. -/
theorem updatedLower_eq_old_of_mem_nextExplored
    (D : RevealThresholdUpdateData ι)
    (hdisjoint : Disjoint D.nextBoundary D.nextExplored)
    {e : ι} (he : e ∈ D.nextExplored) :
    D.updatedLower e = D.lower e := by
  by_cases heAmbient : e ∈ D.ambient
  · have heOldCase : e ∉ D.oldBoundary \ D.nextExplored := by
      intro h
      exact (Finset.mem_sdiff.mp h).2 he
    have heNewCase : e ∉ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient := by
      intro h
      exact Finset.disjoint_left.mp hdisjoint
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1 he
    simp [updatedLower, heAmbient, heOldCase, heNewCase]
  · exact D.updatedLower_eq_old_of_not_mem_ambient heAmbient

/-- A uniform upper bound on the old, incremented, and density thresholds is preserved by
equation (7.31). -/
theorem updatedLower_le_of_le
    (D : RevealThresholdUpdateData ι) (q : I)
    (hlower : ∀ e, D.lower e ≤ q)
    (hincremented : ∀ e, D.incremented e ≤ q)
    (hdensity : D.density ≤ q) (e : ι) :
    D.updatedLower e ≤ q := by
  by_cases heAmbient : e ∈ D.ambient
  · by_cases heOld : e ∈ D.oldBoundary \ D.nextExplored
    · simp [updatedLower, heAmbient, heOld, hincremented e]
    · by_cases heNew : e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient
      · simp [updatedLower, heAmbient, heOld, heNew, hdensity]
      · simp [updatedLower, heAmbient, heOld, heNew, hlower e]
  · simp [updatedLower, heAmbient, hlower e]

/-- Real-valued form of `updatedLower_le_of_le`, convenient when the prospective bound is an
arithmetic expression whose unit-interval membership is proved only at the end of a schedule. -/
theorem coe_updatedLower_le_of_le
    (D : RevealThresholdUpdateData ι) (q : ℝ)
    (hlower : ∀ e, (D.lower e : ℝ) ≤ q)
    (hincremented : ∀ e, (D.incremented e : ℝ) ≤ q)
    (hdensity : (D.density : ℝ) ≤ q) (e : ι) :
    (D.updatedLower e : ℝ) ≤ q := by
  by_cases heAmbient : e ∈ D.ambient
  · by_cases heOld : e ∈ D.oldBoundary \ D.nextExplored
    · simp [updatedLower, heAmbient, heOld, hincremented e]
    · by_cases heNew : e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient
      · simp [updatedLower, heAmbient, heOld, heNew, hdensity]
      · simp [updatedLower, heAmbient, heOld, heNew, hlower e]
  · simp [updatedLower, heAmbient, hlower e]

/-- Pointwise real-valued threshold bound.  Unlike the uniform helper above, this is suitable
for spatial reveal accounting where the available budget depends on the physical edge. -/
theorem coe_updatedLower_le_of_le_at
    (D : RevealThresholdUpdateData ι) (q : ℝ) (e : ι)
    (hlower : (D.lower e : ℝ) ≤ q)
    (hincremented : (D.incremented e : ℝ) ≤ q)
    (hdensity : (D.density : ℝ) ≤ q) :
    (D.updatedLower e : ℝ) ≤ q := by
  by_cases heAmbient : e ∈ D.ambient
  · by_cases heOld : e ∈ D.oldBoundary \ D.nextExplored
    · simp [updatedLower, heAmbient, heOld, hincremented]
    · by_cases heNew : e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient
      · simp [updatedLower, heAmbient, heOld, heNew, hdensity]
      · simp [updatedLower, heAmbient, heOld, heNew, hlower]
  · simp [updatedLower, heAmbient, hlower]

theorem updatedUpper_eq_old_of_mem_oldExplored
    (D : RevealThresholdUpdateData ι) {e : ι} (he : e ∈ D.oldExplored) :
    D.updatedUpper e = D.upper e := by
  simp [updatedUpper, he]

theorem updatedUpper_eq_incremented_of_mem_absorbedBoundary
    (D : RevealThresholdUpdateData ι) {e : ι}
    (heOld : e ∉ D.oldExplored) (heBoundary : e ∈ D.oldBoundary)
    (heNext : e ∈ D.nextExplored) :
    D.updatedUpper e = D.incremented e := by
  simp [updatedUpper, heOld, heBoundary, heNext]

theorem updatedUpper_eq_density_of_mem_newInterior
    (D : RevealThresholdUpdateData ι) {e : ι}
    (heOld : e ∉ D.oldExplored) (heBoundary : e ∉ D.oldBoundary)
    (heNext : e ∈ D.nextExplored) :
    D.updatedUpper e = D.density := by
  simp [updatedUpper, heOld, heBoundary, heNext]

/-- The lower thresholds can only increase under the source's local parameter inequalities. -/
theorem lower_le_updatedLower
    (D : RevealThresholdUpdateData ι)
    (hincrement : ∀ e ∈ D.oldBoundary \ D.nextExplored,
      D.lower e ≤ D.incremented e)
    (hdensity : ∀ e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient,
      D.lower e ≤ D.density) (e : ι) :
    D.lower e ≤ D.updatedLower e := by
  by_cases heAmbient : e ∈ D.ambient
  · by_cases heOld : e ∈ D.oldBoundary \ D.nextExplored
    · simp [updatedLower, heAmbient, heOld, hincrement e heOld]
    · by_cases heNew : e ∈ (D.nextBoundary \ D.oldBoundary) ∩ D.ambient
      · simp [updatedLower, heAmbient, heOld, heNew, hdensity e heNew]
      · simp [updatedLower, heAmbient, heOld, heNew]
  · simp [updatedLower, heAmbient]

/-- The upper thresholds can only decrease under the source's local parameter inequalities. -/
theorem updatedUpper_le_upper
    (D : RevealThresholdUpdateData ι)
    (hincrement : ∀ e ∈ D.oldBoundary ∩ D.nextExplored,
      D.incremented e ≤ D.upper e)
    (hdensity : ∀ e ∈ D.nextExplored \ (D.oldExplored ∪ D.oldBoundary),
      D.density ≤ D.upper e) (e : ι) :
    D.updatedUpper e ≤ D.upper e := by
  by_cases heOld : e ∈ D.oldExplored
  · simp [updatedUpper, heOld]
  · by_cases heBoundary : e ∈ D.oldBoundary ∩ D.nextExplored
    · simp [updatedUpper, heOld, heBoundary, hincrement e heBoundary]
    · by_cases heNew : e ∈ D.nextExplored \ (D.oldExplored ∪ D.oldBoundary)
      · simp [updatedUpper, heOld, heBoundary, heNew, hdensity e heNew]
      · simp [updatedUpper, heOld, heBoundary, heNew]

/-- The finite output profile states exactly the conjunction of the updated closed and open
coordinate inequalities; this is the form consumed by the interval-fiber partition. -/
theorem mem_updatedProfile_event_iff (D : RevealThresholdUpdateData ι) (X : ι → ℝ) :
    X ∈ D.updatedProfile.event ↔
      (∀ e ∈ D.updatedClosedSupport, (D.updatedLower e : ℝ) ≤ X e) ∧
        ∀ e ∈ D.nextExplored, X e < (D.updatedUpper e : ℝ) :=
  Iff.rfl

end RevealThresholdUpdateData

/-! ### Literal initial state and the displayed first update -/

/-- Equations (7.28): before the radial exploration no edge carries positive closed
information. -/
def initialRevealLower {ι : Type*} : ι → I :=
  fun _ ↦ 0

/-- Equation (7.29): the central seed is `p`-open and all other upper thresholds are one. -/
def initialRevealUpper {ι : Type*} [DecidableEq ι]
    (seedEdges : Finset ι) (p : I) : ι → I :=
  fun e ↦ if e ∈ seedEdges then p else 1

/-- Exact specialization of (7.31)--(7.32) after the central seed and simultaneous radial
exploration.  Here `delta` is already certified to lie in the unit interval. -/
def firstRadialRevealUpdate {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) : RevealThresholdUpdateData ι where
  oldExplored := seedEdges
  nextExplored := nextExplored
  oldBoundary := oldBoundary
  nextBoundary := nextBoundary
  ambient := ambient
  lower := initialRevealLower
  upper := initialRevealUpper seedEdges p
  incremented := fun _ ↦ delta
  density := p

@[simp]
theorem firstRadialRevealUpdate_lower {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).lower = initialRevealLower :=
  rfl

@[simp]
theorem firstRadialRevealUpdate_upper {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).upper = initialRevealUpper seedEdges p :=
  rfl

/-- Literal right-hand side of Grimmett's displayed equation (7.31). -/
theorem firstRadial_updatedLower_apply
    {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) (e : ι) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).updatedLower e =
      if e ∉ ambient then 0
      else if e ∈ oldBoundary \ nextExplored then delta
      else if e ∈ (nextBoundary \ oldBoundary) ∩ ambient then p
      else 0 :=
  rfl

/-- Literal right-hand side of Grimmett's displayed equation (7.32). -/
theorem firstRadial_updatedUpper_apply
    {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) (e : ι) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).updatedUpper e =
      if e ∈ seedEdges then initialRevealUpper seedEdges p e
      else if e ∈ oldBoundary ∩ nextExplored then delta
      else if e ∈ nextExplored \ (seedEdges ∪ oldBoundary) then p
      else initialRevealUpper seedEdges p e :=
  rfl

/-- Equation (7.27), lower-threshold half, for the displayed first update. -/
theorem initialRevealLower_le_firstRadial_updatedLower
    {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) (e : ι) :
    initialRevealLower e ≤
      (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
        p delta).updatedLower e :=
  (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
    p delta).updatedLower e |>.2.1

/-- Equation (7.27), upper-threshold half, for the displayed first update. -/
theorem firstRadial_updatedUpper_le_initialRevealUpper
    {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I) (e : ι) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
        p delta).updatedUpper e ≤ initialRevealUpper seedEdges p e := by
  let D := firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
    p delta
  by_cases heSeed : e ∈ seedEdges
  · simp [RevealThresholdUpdateData.updatedUpper, firstRadialRevealUpdate,
      initialRevealUpper, heSeed]
  · change (D.updatedUpper e : ℝ) ≤ (initialRevealUpper seedEdges p e : ℝ)
    rw [initialRevealUpper, if_neg heSeed]
    exact (D.updatedUpper e).2.2

/-- The displayed update remains a genuine interval whenever edge boundaries are disjoint from
their explored sets and the explored set only grows.  This checks the principal junk-value risk
in translating (7.31)--(7.32): the new lower threshold never exceeds the new upper threshold. -/
theorem firstRadial_updatedLower_le_updatedUpper
    {ι : Type*} [DecidableEq ι]
    (seedEdges nextExplored oldBoundary nextBoundary ambient : Finset ι)
    (p delta : I)
    (holdBoundary : Disjoint oldBoundary seedEdges)
    (hnextBoundary : Disjoint nextBoundary nextExplored)
    (e : ι) :
    (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
        p delta).updatedLower e ≤
      (firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
        p delta).updatedUpper e := by
  change
    ((firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).updatedLower e : ℝ) ≤
    ((firstRadialRevealUpdate seedEdges nextExplored oldBoundary nextBoundary ambient
      p delta).updatedUpper e : ℝ)
  rw [firstRadial_updatedLower_apply, firstRadial_updatedUpper_apply]
  have hold := Finset.disjoint_left.mp holdBoundary
  have hnext := Finset.disjoint_left.mp hnextBoundary
  have hp0 := p.2.1
  have hp1 := p.2.2
  have hdelta0 := delta.2.1
  have hdelta1 := delta.2.2
  by_cases heAmbient : e ∈ ambient <;>
    by_cases heOldBoundary : e ∈ oldBoundary <;>
    by_cases heNext : e ∈ nextExplored <;>
    by_cases heNewBoundary : e ∈ nextBoundary <;>
    by_cases heSeed : e ∈ seedEdges <;>
    simp_all [initialRevealUpper]

end Percolation
