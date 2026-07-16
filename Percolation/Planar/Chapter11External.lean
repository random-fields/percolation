import Percolation.Planar.SupercriticalCrossings
import Percolation.Planar.TubeDecay
import Percolation.Critical.ClusterSizeRate
import Percolation.Critical.ClusterDensityEndpoints
import Mathlib.Probability.CentralLimitTheorem

/-!
# External-reference boundary for Grimmett Chapter 11

The declarations in this file are deliberately axioms.  Each is a source-facing result whose
proof Grimmett either delegates to a reference outside the book or whose proof depends on the
planar-topological Proposition 11.2, for which Grimmett explicitly refers the reader to Kesten
(1982, p. 386).  Keeping the declarations together makes that transitive dependency visible in
`#print axioms`.

Results proved within the repository (including `p_c(ℤ²)=1/2`, Lemma 11.22, the RSW numerical
theorem, and Lemma 11.27) do not appear here.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real unitInterval

/-! ## Cluster-density duality -/

/-- **Grimmett, Theorem 11.4.**  The square-lattice cluster density satisfies the Sykes--Essam
duality identity.  Grimmett's proof uses the face/component correspondence attributed to Kesten
(1982, p. 244), in addition to externally cited planar topology and Euler's formula. -/
axiom openClustersPerVertex_square_duality (p : I) :
    openClustersPerVertex 2 p =
      openClustersPerVertex 2 (σ p) + 1 - 2 * (p : ℝ)

/-! ## Circuits surrounding finite clusters -/

/-- The source event that some finite open square-lattice circuit contains the whole box `B(n)`
in its interior.  Interior is encoded by the odd mod-two face index used throughout the planar
library. -/
def eventuallySurroundingOpenCircuitEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ x : SquareVertex, ∃ c : squareGraph.Walk x x,
    c.IsCycle ∧ walkIsOpen ω c ∧
      ∀ y ∈ cubicMetricBox 2 cubicOrigin n,
        closedSquareWalkFaceParity c y = 1}

/-- **Grimmett, Lemma 11.13.**  If percolation occurs, every fixed box is almost surely
surrounded by an open circuit.  The finite-cluster/dual-boundary step is Proposition 11.2, whose
proof the book delegates to Kesten (1982, p. 386). -/
axiom eventuallySurroundingOpenCircuit_probability_one
    {p : I} (hθ : 0 < theta 2 p) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (eventuallySurroundingOpenCircuitEvent n) = 1

/-! ## Many source-rectangle crossings -/

/-- **Grimmett, Lemma 11.22 (literal source rectangle).**  Above one half, the probability
that `[0,n+1] × [0,n]` has at most linearly many edge-disjoint open crossings is exponentially
small.  The book derives this from equation 11.20, whose planar crossing alternative is an
instance of the externally delegated Proposition 11.2.  The repository also proves the full
probabilistic argument for the centered-rectangle normalization in
`maxEdgeDisjointSquareRectangleCrossings_probability_le_exp`. -/
axiom maxEdgeDisjointGrimmettRectangleCrossings_probability_le_exp
    {p : I} (hp : (1 / 2 : ℝ) < p) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∀ n : ℕ, 1 ≤ n →
      (bernoulliBondMeasure 2 p).real
          {ω | (maxEdgeDisjointGrimmettRectangleCrossings n ω : ℝ) ≤ β * n} ≤
        Real.exp (-γ * n)

/-! ## Truncated connectivity -/

/-- The probability `τᶠₚ(0,eₙ)` that the origin has a finite open cluster containing the
axis vertex `eₙ`. -/
noncomputable def truncatedTwoPointConnectivity (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real
    (connectionEvent 2 cubicOrigin (cubicAxisVertex 2 n) ∩ finiteClusterEvent 2)

/-- Negative logarithm of the truncated axis connectivity. -/
noncomputable def truncatedConnectivityNegLog (p : I) (n : ℕ) : ℝ :=
  -Real.log (truncatedTwoPointConnectivity p n)

/-- The exponential rate associated with truncated connectivity. -/
noncomputable def truncatedConnectivityDecayRate (p : I) : ℝ :=
  sInf ((fun n : ℕ ↦ truncatedConnectivityNegLog p n / n) '' Set.Ici 1)

/-- The finite-cluster correlation length `ξᶠ(p)`, in `ℝ≥0∞` to retain the correct infinite
endpoint convention. -/
noncomputable def finiteCorrelationLength (p : I) : ℝ≥0∞ :=
  (ENNReal.ofReal (truncatedConnectivityDecayRate p))⁻¹

/-- The limit assertion in Grimmett, equation 11.23, for the truncated two-point function.
The comparison with surrounding dual circuits depends on Proposition 11.2. -/
axiom truncatedTwoPointConnectivity_logRate_tendsto
    {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    Tendsto (fun n : ℕ ↦ -Real.log (truncatedTwoPointConnectivity p n) / n)
      atTop (nhds (truncatedConnectivityDecayRate p))

/-- **Grimmett, Theorem 11.24.**  In the supercritical square lattice, finite-cluster
correlation length is half the subcritical dual correlation length.  Its proof uses the
externally delegated surrounding-circuit topology. -/
axiom finiteCorrelationLength_eq_half_correlationLength_complement
    {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    finiteCorrelationLength p = (2 : ℝ≥0∞)⁻¹ * correlationLength 2 (σ p)

/-- The positivity and finiteness conclusion included in Grimmett's Theorem 11.24. -/
theorem finiteCorrelationLength_pos_lt_top
    {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    0 < finiteCorrelationLength p ∧ finiteCorrelationLength p < ⊤ := by
  rw [finiteCorrelationLength_eq_half_correlationLength_complement hpHalf hpOne]
  have hσ0 : 0 < ((σ p : I) : ℝ) := by
    change 0 < 1 - (p : ℝ)
    linarith
  have hσpc : ((σ p : I) : ℝ) < cubicCriticalProbability 2 := by
    rw [cubicCriticalProbability_two_eq_half]
    change 1 - (p : ℝ) < 1 / 2
    linarith
  have hrate : 0 < boxRadiusDecayRate 2 (σ p) :=
    boxRadiusDecayRate_pos_of_lt_critical 2 (by omega) (σ p) hσ0 hσpc
  have hcorrelationPos : 0 < correlationLength 2 (σ p) := by
    rw [correlationLength, ENNReal.inv_pos]
    exact ENNReal.ofReal_ne_top
  have hcorrelationTop : correlationLength 2 (σ p) < ⊤ := by
    rw [correlationLength, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
    exact hrate
  constructor
  · exact ENNReal.mul_pos (by norm_num) hcorrelationPos.ne'
  · exact ENNReal.mul_lt_top (by norm_num) hcorrelationTop

/-- **Grimmett, Theorem 11.25.**  Supercritical finite clusters have a surface-order
stretched-exponential size distribution.  The proof encloses a finite cluster by the unique
dual circuit from Proposition 11.2. -/
axiom finiteClusterSizeProbability_le_exp_neg_sqrt_of_supercritical
    {p : I} (hpHalf : (1 / 2 : ℝ) < p) (hpOne : (p : ℝ) < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ,
      finiteClusterSizeProbability 2 p n ≤ Real.exp (-η * Real.sqrt n)

/-! ## Percolation on logarithmic subsets -/

/-- The subgraph `G(f) = {(x₁,x₂) : x₁,x₂≥0, x₂≤f(x₁)}` from Section 11.5. -/
def logarithmicProfileRegion (f : ℝ → ℝ) : Set SquareVertex :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (x 1 : ℝ) ≤ f (x 0)}

/-- **Grimmett, Theorem 11.55.**  If `f(u)/log u → a`, the profile graph has the unique
critical density `π∈(1/2,1)` satisfying `ξ(1-π)=a`.  The proof uses dual surrounding
circuits and therefore inherits Proposition 11.2's external topology. -/
axiom logarithmicProfileRegion_criticalProbability
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ u, 0 ≤ u → 0 ≤ f u)
    (hflog : Tendsto (fun u : ℝ ↦ f u / Real.log u) atTop (nhds a)) :
    ∃! q : I,
      (1 / 2 : ℝ) < q ∧ (q : ℝ) < 1 ∧
      regionCriticalProbability 2 (logarithmicProfileRegion f) = (q : ℝ) ∧
      correlationLength 2 (σ q) = ENNReal.ofReal a

/-! ## The externally sourced central limit theorem -/

/-- A finite square-lattice circuit together with its finite interior, represented by the
odd face-parity predicate. -/
structure SquareCircuitInterior where
  base : SquareVertex
  boundary : squareGraph.Walk base base
  isCycle : boundary.IsCycle
  interior : Finset SquareVertex
  mem_interior_iff : ∀ x, x ∈ interior ↔ closedSquareWalkFaceParity boundary x = 1

/-- The cluster-functional sum `Zₙ` in equation 11.67. -/
noncomputable def clusterFunctionalSum
    (c : ℕ → SquareCircuitInterior)
    (f : ℕ → Set SquareVertex → ℝ) (n : ℕ)
    (ω : EdgeConfiguration 2) : ℝ :=
  ∑ x ∈ (c n).interior, f n (cubicOpenClusterFrom 2 ω x)

/-- The usual standardized convergence-to-normal conclusion. -/
def SatisfiesCentralLimitTheorem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) : Prop :=
  TendstoInDistribution
    (fun n ω ↦ (Z n ω - P[Z n]) / Real.sqrt Var[Z n; P])
    atTop id (fun _ ↦ P) (gaussianReal 0 1)

/-- **Grimmett, Theorem 11.63.**  This theorem is stated without proof in the book, which
instead cites the method-of-moments and strong-mixing literature. -/
axiom clusterFunctionalSum_centralLimitTheorem
    (c : ℕ → SquareCircuitInterior)
    (f : ℕ → Set SquareVertex → ℝ) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpCritical : (p : ℝ) ≠ 1 / 2)
    (hc : Tendsto (fun n ↦ ((c n).interior.card : ℝ)) atTop atTop)
    (hfBounded : ∀ n, ∃ M : ℝ, ∀ C, |f n C| ≤ M)
    (hfMeasurable : ∀ n, Measurable (clusterFunctionalSum c f n))
    (hfInfinite : (1 / 2 : ℝ) < p →
      ∀ n C D, C.Infinite → D.Infinite → f n C = f n D)
    (hvariance : 0 < liminf
      (fun n ↦ Var[clusterFunctionalSum c f n; bernoulliBondMeasure 2 p] /
        (c n).interior.card) atTop) :
    SatisfiesCentralLimitTheorem (bernoulliBondMeasure 2 p)
      (clusterFunctionalSum c f)

/-! ## Power-law consequences of RSW -/

/-- The real moment of the origin-cluster size, with the infinite value represented by the
existing `ENNReal.toReal` convention.  At criticality Theorem 11.12 makes this faithful almost
surely. -/
noncomputable def clusterSizeRealMoment (d : ℕ) (p : I) (a : ℝ) : ℝ :=
  ∫ ω, (clusterSizeENNReal d ω).toReal ^ a ∂bernoulliBondMeasure d p

/-- **Grimmett, Theorem 11.89.**  Critical radius and size tails obey two-sided power bounds,
and a positive cluster-size moment is finite.  The proof uses Lemma 11.73, whose lowest-crossing
topology follows Russo (1981), as well as Proposition 11.2. -/
axiom squareCritical_powerLaw_bounds :
    ∃ A₁ a₁ A₂ a₂ a₃ : ℝ,
      0 < A₁ ∧ 0 < a₁ ∧ 0 < A₂ ∧ 0 < a₂ ∧ 0 < a₃ ∧
      (∀ n : ℕ, 1 ≤ n →
        (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          boxRadiusTail 2 squareHalfDensity n ∧
        boxRadiusTail 2 squareHalfDensity n ≤ A₁ * (n : ℝ) ^ (-a₁) ∧
        (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          clusterSizeAtLeast 2 squareHalfDensity n ∧
        clusterSizeAtLeast 2 squareHalfDensity n ≤ A₂ * (n : ℝ) ^ (-a₂)) ∧
      Integrable (fun ω ↦ (clusterSizeENNReal 2 ω).toReal ^ a₃)
        (bernoulliBondMeasure 2 squareHalfDensity)

/-- **Grimmett, Theorem 11.93.**  Near-critical power bounds for percolation probability,
susceptibility, and finite susceptibility.  This theorem depends on the externally sourced
critical power-law theorem above. -/
axiom squareNearCritical_powerLaw_bounds :
    ∃ A₄ a₄ A₅ a₅ A₆ A₇ a₇ : ℝ,
      0 < A₄ ∧ 0 < a₄ ∧ 0 < A₅ ∧ 0 < a₅ ∧
      0 < A₆ ∧ 0 < A₇ ∧ 0 < a₇ ∧
      (∀ p : I, (1 / 2 : ℝ) < p →
        theta 2 p ≤ A₄ * ((p : ℝ) - 1 / 2) ^ a₄) ∧
      (∀ p : I, (p : ℝ) < 1 / 2 →
        (susceptibility 2 p).toReal ≤ A₅ * (1 / 2 - (p : ℝ)) ^ (-a₅)) ∧
      (∀ p : I, (1 / 2 : ℝ) < p →
        A₆ * ((p : ℝ) - 1 / 2) ^ (-(1 / 4 : ℝ)) ≤
          (finiteSusceptibility 2 p).toReal ∧
        (finiteSusceptibility 2 p).toReal ≤
          A₇ * ((p : ℝ) - 1 / 2) ^ (-a₇))

end Percolation
