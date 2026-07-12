import Percolation.Bernoulli.CouplingSymmetry

/-!
# Symmetries for oriented dynamic steering

The reference restart theorem exits through a positive coordinate face at the origin.  A sign
flip in the chosen coordinate followed by translation transports it to either signed face at an
arbitrary block center, while `CouplingSymmetry` preserves the common-uniform probability law.
-/

namespace Percolation

/-- Flip exactly the selected coordinate when the requested direction is negative. -/
def cubicDirectionOrientationFlip {d : ℕ} (a : CubicDirection d) : Fin d → Bool :=
  fun j ↦ decide (j = a.1 ∧ a.2 = false)

/-- Graph automorphism taking the origin to `center` and the reference positive `a.1` step to
the signed step `a` from `center`. -/
def cubicDirectionOrientationIso {d : ℕ}
    (center : Cubic d) (a : CubicDirection d) :
    cubicGraph d ≃g cubicGraph d :=
  (cubicSignedCoordinateIso (cubicDirectionOrientationFlip a)).trans
    (cubicTranslationIso cubicOrigin center)

@[simp]
theorem cubicDirectionOrientationIso_origin
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso center a cubicOrigin = center := by
  ext j
  simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
    cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
    cubicTranslate, cubicOrigin]

theorem cubicDirectionOrientationIso_positiveStep
    {d : ℕ} (center : Cubic d) (a : CubicDirection d) :
    cubicDirectionOrientationIso center a
        (cubicStepFrom cubicOrigin (a.1, true)) =
      cubicStepFrom center a := by
  rcases a with ⟨i, positive⟩
  ext j
  by_cases hji : j = i
  · subst j
    cases positive <;>
      simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
        cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
        cubicTranslate, cubicOrigin, cubicStepFrom, cubicDirectionIncrement]
      <;> omega
  · simp [cubicDirectionOrientationIso, cubicSignedCoordinateIso,
      cubicSignedCoordinateEquiv, cubicDirectionOrientationFlip,
      cubicTranslate, cubicOrigin, cubicStepFrom, cubicDirectionIncrement, hji]

/-- Transport a reference uniform-label event to a restart centered at `center` and oriented in
direction `a`. -/
def orientedCouplingTransportEvent {d : ℕ}
    (center : Cubic d) (a : CubicDirection d)
    (A : Set (CubicEdge d → ℝ)) : Set (CubicEdge d → ℝ) :=
  cubicGraphIsoCouplingTransportEvent (cubicDirectionOrientationIso center a) A

theorem couplingMeasure_real_orientedTransportEvent
    {d : ℕ} (center : Cubic d) (a : CubicDirection d)
    {A : Set (CubicEdge d → ℝ)} (hA : MeasurableSet A) :
    (couplingMeasure (CubicEdge d)).real
        (orientedCouplingTransportEvent center a A) =
      (couplingMeasure (CubicEdge d)).real A :=
  couplingMeasure_real_cubicGraphIsoTransportEvent
    (cubicDirectionOrientationIso center a) hA

end Percolation
