import Percolation.Critical.DynamicRootInitialization
import Percolation.Critical.DynamicFramedRestartPartition

/-!
# Completing the special root block

The first root phase produces a central seed and `2d` radial seeded branches.  Grimmett then
performs one further restart from each selected radial seed into the corresponding half-way
box.  Only after all `2d` extensions succeed is the coarse root block complete.  This file
isolates the exact finite composition law for that second phase.  The concrete interval-fiber
constructor must instantiate its partitioned stages; no independence or conditional-probability
claim is hidden in this interface.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {C : Type*} [DecidableEq C]

/-- A source-counted family of the `2d` post-radial root extensions.  At each prefix, the
literal radial outer event intersected with the preceding successes is exactly partitioned into
the stage's reveal cells. -/
structure RootExtensionProgram
    (d : ℕ) (C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) where
  radialEvent : Set (CubicEdge d → ℝ)
  radialEvent_measurable : MeasurableSet radialEvent
  radialEvent_pos : 0 < (couplingMeasure (CubicEdge d)).real radialEvent
  stage : ℕ → PartitionedFramedRestartStage d C m n p delta epsilon
  partition_eq : ∀ j < 2 * d,
    radialEvent ∩
        finiteAdaptiveSuccessPrefix
          (fun (_history : List (Unit × Bool)) (_v : Unit) l ↦
            (stage l).successEvent) [] () j =
      (stage j).cellUnion

namespace RootExtensionProgram

variable {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (P : RootExtensionProgram d C m n p delta epsilon)

/-- Prefix event for the post-radial root extensions. -/
def prefixEvent (j : ℕ) : Set (CubicEdge d → ℝ) :=
  P.radialEvent ∩
    finiteAdaptiveSuccessPrefix
      (fun (_history : List (Unit × Bool)) (_v : Unit) l ↦
        (P.stage l).successEvent) [] () j

@[simp]
theorem prefixEvent_zero : P.prefixEvent 0 = P.radialEvent := by
  simp [prefixEvent]

/-- The literal completed root event after all `2d` extensions. -/
def completionEvent : Set (CubicEdge d → ℝ) :=
  P.prefixEvent (2 * d)

theorem measurableSet_prefixEvent (j : ℕ) : MeasurableSet (P.prefixEvent j) := by
  apply P.radialEvent_measurable.inter
  apply measurableSet_finiteAdaptiveSuccessPrefix
  intro _history _v l
  exact (P.stage l).measurableSet_successEvent

theorem measurableSet_completionEvent : MeasurableSet P.completionEvent :=
  P.measurableSet_prefixEvent (2 * d)

/-- One partitioned root extension retains its ratio-free factor on the literal preceding
prefix. -/
theorem prefixEvent_step_lower_bound
    (j : ℕ) (hj : j < 2 * d) :
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real (P.prefixEvent j) ≤
      (couplingMeasure (CubicEdge d)).real (P.prefixEvent (j + 1)) := by
  have hpartition : P.prefixEvent j = (P.stage j).cellUnion := by
    simpa [prefixEvent] using P.partition_eq j hj
  have hsucc : P.prefixEvent (j + 1) = (P.stage j).successEvent := by
    rw [prefixEvent, finiteAdaptiveSuccessPrefix_succ]
    calc
      P.radialEvent ∩
          ((P.stage j).successEvent ∩
            finiteAdaptiveSuccessPrefix
              (fun (_history : List (Unit × Bool)) (_v : Unit) l ↦
                (P.stage l).successEvent) [] () j) =
          (P.stage j).successEvent ∩ P.prefixEvent j := by
        ext X
        simp [prefixEvent, and_left_comm]
      _ = (P.stage j).successEvent ∩ (P.stage j).cellUnion := by
        rw [hpartition]
      _ = (P.stage j).successEvent :=
        Set.inter_eq_left.mpr (P.stage j).successEvent_subset_cellUnion
  rw [hpartition, hsucc]
  exact (P.stage j).success_lower_bound

/-- Exact root analogue of the second factor in (7.33). -/
theorem pow_mul_radialEvent_le_completionEvent (hepsilon : epsilon ≤ 1) :
    (1 - epsilon) ^ (2 * d) *
        (couplingMeasure (CubicEdge d)).real P.radialEvent ≤
      (couplingMeasure (CubicEdge d)).real P.completionEvent := by
  have h := pow_mul_measureReal_le_of_step P.prefixEvent (1 - epsilon)
    (sub_nonneg.mpr hepsilon) (2 * d)
    (fun j hj ↦ P.prefixEvent_step_lower_bound j hj)
  simpa [completionEvent] using h

/-- A positive radial event remains positive after all `2d` source extensions. -/
theorem completionEvent_pos (hepsilon1 : epsilon < 1) :
    0 < (couplingMeasure (CubicEdge d)).real P.completionEvent := by
  have hfactor : 0 < (1 - epsilon) ^ (2 * d) :=
    pow_pos (sub_pos.mpr hepsilon1) _
  exact (mul_pos hfactor P.radialEvent_pos).trans_le
    (P.pow_mul_radialEvent_le_completionEvent hepsilon1.le)

end RootExtensionProgram

/-- A common-radius restart package together with the concrete `2d` root-extension program.
The completed event, rather than the radial event alone, is the outer event supplied to the
subsequent non-root exploration. -/
structure CompletedRootBlockPackage
    (d : ℕ) (C : Type*) [DecidableEq C]
    (p : I) (delta epsilon : ℝ) where
  restart : DynamicBlockRestartPackage d p delta epsilon
  extension : RootExtensionProgram d C restart.m restart.n p delta epsilon
  radialEvent_eq : extension.radialEvent =
    rootRadialEvent d restart.m restart.n p delta

namespace CompletedRootBlockPackage

variable {d : ℕ} {p : I} {delta epsilon : ℝ}
    (P : CompletedRootBlockPackage d C p delta epsilon)

def initialEvent : Set (CubicEdge d → ℝ) := P.extension.completionEvent

theorem measurableSet_initialEvent : MeasurableSet P.initialEvent :=
  P.extension.measurableSet_completionEvent

theorem initialEvent_pos (hepsilon1 : epsilon < 1) :
    0 < (couplingMeasure (CubicEdge d)).real P.initialEvent :=
  P.extension.completionEvent_pos hepsilon1

end CompletedRootBlockPackage

end AdaptiveSiteExploration

end Percolation
