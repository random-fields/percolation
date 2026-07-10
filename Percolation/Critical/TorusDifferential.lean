import Percolation.Critical.TorusGhostField
import Percolation.Bernoulli.Russo

/-!
# Finite-volume ghost derivatives

The periodic ghost probability is written as two nested finite Bernoulli expectations.  Holding
the green set fixed gives Russo's formula in `p`; holding the edge set fixed gives the finite
difference formula in `γ`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval Topology

open Set

def torusHitEdgeTrace (d N : ℕ) (G : Finset (CubicTorus d N)) :
    Set (Finset (CubicTorusEdge d N)) :=
  {ω | ∃ y ∈ G, y ∈ cubicTorusOpenCluster d N (ω : Set (CubicTorusEdge d N))}

def torusHitGreenTrace (d N : ℕ) (ω : Finset (CubicTorusEdge d N)) :
    Set (Finset (CubicTorus d N)) :=
  {G | ∃ y ∈ G, y ∈ cubicTorusOpenCluster d N (ω : Set (CubicTorusEdge d N))}

theorem torusWalkIsOpen_mono {d N : ℕ}
    {ω η : CubicTorusEdgeConfiguration d N} (hωη : ω ⊆ η)
    {u v : CubicTorus d N} {w : (cubicTorusGraph d N).Walk u v}
    (hopen : torusWalkIsOpen ω w) : torusWalkIsOpen η w := by
  intro e he
  exact hωη (hopen e he)

theorem cubicTorusOpenCluster_mono {d N : ℕ}
    {ω η : CubicTorusEdgeConfiguration d N} (hωη : ω ⊆ η) :
    cubicTorusOpenCluster d N ω ⊆ cubicTorusOpenCluster d N η := by
  rintro y ⟨w, hw⟩
  exact ⟨w, torusWalkIsOpen_mono hωη hw⟩

theorem isIncreasingTrace_torusHitEdgeTrace (d N : ℕ) (G : Finset (CubicTorus d N)) :
    IsIncreasingTrace (torusHitEdgeTrace d N G) := by
  intro ω η hωη
  rintro ⟨y, hyG, hy⟩
  exact ⟨y, hyG, cubicTorusOpenCluster_mono (Finset.coe_subset.mpr hωη) hy⟩

theorem isIncreasingTrace_torusHitGreenTrace (d N : ℕ)
    (ω : Finset (CubicTorusEdge d N)) :
    IsIncreasingTrace (torusHitGreenTrace d N ω) := by
  intro G H hGH
  rintro ⟨y, hyG, hy⟩
  exact ⟨y, hGH hyG, hy⟩

def torusHitEdgeEvent (d N : ℕ) (G : Set (CubicTorus d N)) :
    Set (CubicTorusEdgeConfiguration d N) :=
  {ω | ∃ y ∈ G, y ∈ cubicTorusOpenCluster d N ω}

theorem dependsOn_torusHitEdgeEvent (d N : ℕ) (hN : 2 ≤ N)
    (G : Set (CubicTorus d N)) :
    DependsOn (cubicTorusEdgeFinset d N hN) (torusHitEdgeEvent d N G) := by
  intro ω η hagree
  have hωη : ω = η := by
    ext e
    exact hagree e (mem_cubicTorusEdgeFinset hN e)
  subst η
  rfl

theorem measurableSet_torusHitEdgeEvent (d N : ℕ) (hN : 2 ≤ N)
    (G : Set (CubicTorus d N)) : MeasurableSet (torusHitEdgeEvent d N G) :=
  (dependsOn_torusHitEdgeEvent d N hN G).measurableSet

theorem eventTrace_torusHitEdgeEvent (d N : ℕ) (G : Finset (CubicTorus d N)) :
    eventTrace (torusHitEdgeEvent d N (G : Set (CubicTorus d N))) =
      torusHitEdgeTrace d N G := by
  rfl

noncomputable def torusFixedGreenProbability (d N : ℕ) (hN : 2 ≤ N)
    (p : I) (G : Set (CubicTorus d N)) : ℝ :=
  finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
    (torusHitEdgeTrace d N (restrictTo (cubicTorusVertexFinset d N hN) G))

theorem torusHitEdgeEvent_restrict_vertices (d N : ℕ) (hN : 2 ≤ N)
    (G : Set (CubicTorus d N)) :
    torusHitEdgeEvent d N G = torusHitEdgeEvent d N
      (restrictTo (cubicTorusVertexFinset d N hN) G : Set (CubicTorus d N)) := by
  ext ω
  constructor
  · rintro ⟨y, hyG, hy⟩
    exact ⟨y, by simp [mem_restrictTo, hyG], hy⟩
  · rintro ⟨y, hyG, hy⟩
    exact ⟨y, (by simpa [mem_restrictTo] using hyG), hy⟩

theorem torusFixedGreenProbability_eq_measureReal (d N : ℕ) (hN : 2 ≤ N)
    (p : I) (G : Set (CubicTorus d N)) :
    torusFixedGreenProbability d N hN p G =
      (torusBondMeasure d N p).real (torusHitEdgeEvent d N G) := by
  rw [torusFixedGreenProbability, torusHitEdgeEvent_restrict_vertices d N hN G]
  unfold torusBondMeasure
  rw [(dependsOn_torusHitEdgeEvent d N hN _).setBernoulli_real_eq_finiteBernoulliProbability]
  rw [eventTrace_torusHitEdgeEvent]

theorem dependsOnFun_torusFixedGreenProbability (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    DependsOnFun (cubicTorusVertexFinset d N hN)
      (torusFixedGreenProbability d N hN p) := by
  intro G H hagree
  have htrace : restrictTo (cubicTorusVertexFinset d N hN) G =
      restrictTo (cubicTorusVertexFinset d N hN) H := by
    ext y
    simp only [mem_restrictTo]
    by_cases hy : y ∈ cubicTorusVertexFinset d N hN
    · simpa [hy] using hagree y hy
    · simp [hy]
  simp [torusFixedGreenProbability, htrace]

/-- The finite polynomial `θ_N(p,γ)`, expressed by first averaging the edge event for a fixed
green set and then averaging over green sets. -/
noncomputable def torusGhostThetaPolynomial (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ fun G ↦
    finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
      (torusHitEdgeTrace d N G)

/-- Formal `p` derivative of `θ_N`. -/
noncomputable def torusGhostThetaPDerivative (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ fun G ↦
    ∑ e ∈ cubicTorusEdgeFinset d N hN,
      finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
        (pivotalTrace (torusHitEdgeTrace d N G) e)

/-- Formal `γ` derivative of `θ_N`. -/
noncomputable def torusGhostThetaGammaDerivative (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  ∑ v ∈ cubicTorusVertexFinset d N hN,
    finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
      (traceDifference v fun G ↦
        finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
          (torusHitEdgeTrace d N G))

theorem finiteBernoulliProbability_torusHitGreenTrace (d N : ℕ) (hN : 2 ≤ N)
    (ω : Finset (CubicTorusEdge d N)) (γ : I) :
    finiteBernoulliProbability (cubicTorusVertexFinset d N hN) γ
        (torusHitGreenTrace d N ω) =
      1 - (1 - (γ : ℝ)) ^
        (cubicTorusOpenClusterFinset d N hN (ω : Set (CubicTorusEdge d N))).card := by
  let S := cubicTorusOpenClusterFinset d N hN (ω : Set (CubicTorusEdge d N))
  have hSV : S ⊆ cubicTorusVertexFinset d N hN := by
    dsimp only [S, cubicTorusOpenClusterFinset]
    exact restrictTo_subset _ _
  have h := finiteBernoulliProbability_hits_finset hSV γ
  have hevent : torusHitGreenTrace d N ω = {G : Finset (CubicTorus d N) |
      ∃ y ∈ S, y ∈ G} := by
    ext G
    simp only [torusHitGreenTrace, Set.mem_setOf_eq, S]
    constructor
    · rintro ⟨y, hyG, hyC⟩
      exact ⟨y, (mem_cubicTorusOpenClusterFinset hN).mpr hyC, hyG⟩
    · rintro ⟨y, hyS, hyG⟩
      exact ⟨y, hyG, (mem_cubicTorusOpenClusterFinset hN).mp hyS⟩
  rw [hevent]
  simpa only [S] using h

/-- The finite-volume cluster expansion (5.61), with the finite origin cluster read directly
from the edge configuration. -/
noncomputable def torusGhostThetaByCluster (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p fun ω ↦
    1 - (1 - γ) ^
      (cubicTorusOpenClusterFinset d N hN (ω : Set (CubicTorusEdge d N))).card

theorem torusGhostThetaPolynomial_eq_byCluster (d N : ℕ) (hN : 2 ≤ N)
    (p : ℝ) (γ : I) :
    torusGhostThetaPolynomial d N hN p γ = torusGhostThetaByCluster d N hN p γ := by
  unfold torusGhostThetaPolynomial torusGhostThetaByCluster finiteBernoulliProbability
  rw [finiteBernoulliExpectation_comm]
  apply finiteBernoulliExpectation_congr
  intro ω hω
  change finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
      (fun G ↦ (torusHitEdgeTrace d N G).indicator (fun _ ↦ (1 : ℝ)) ω) = _
  rw [show finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
      (fun G ↦ (torusHitEdgeTrace d N G).indicator (fun _ ↦ (1 : ℝ)) ω) =
      finiteBernoulliProbability (cubicTorusVertexFinset d N hN) γ
        (torusHitGreenTrace d N ω) by
    unfold finiteBernoulliProbability
    apply finiteBernoulliExpectation_congr
    intro G _hG
    rfl]
  exact finiteBernoulliProbability_torusHitGreenTrace d N hN ω γ

noncomputable def torusGhostThetaGammaDerivativeByCluster (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p fun ω ↦
    let k := (cubicTorusOpenClusterFinset d N hN
      (ω : Set (CubicTorusEdge d N))).card
    (k : ℝ) * (1 - γ) ^ (k - 1)

/-- Finite-volume green-free susceptibility from (5.60)–(5.63). -/
noncomputable def torusGhostSusceptibilityPolynomial (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p fun ω ↦
    let k := (cubicTorusOpenClusterFinset d N hN
      (ω : Set (CubicTorusEdge d N))).card
    (k : ℝ) * (1 - γ) ^ k

theorem torusGhostThetaByCluster_hasDerivAt_gamma (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) :
    HasDerivAt (torusGhostThetaByCluster d N hN p)
      (torusGhostThetaGammaDerivativeByCluster d N hN p γ) γ := by
  unfold torusGhostThetaByCluster torusGhostThetaGammaDerivativeByCluster
  unfold finiteBernoulliExpectation
  apply HasDerivAt.fun_sum
  intro ω hω
  let k := (cubicTorusOpenClusterFinset d N hN
    (ω : Set (CubicTorusEdge d N))).card
  have hpow := ((hasDerivAt_const γ 1).sub (hasDerivAt_id γ)).pow k
  have hterm : HasDerivAt (fun y : ℝ ↦ 1 - (1 - y) ^ k)
      ((k : ℝ) * (1 - γ) ^ (k - 1)) γ := by
    convert (hasDerivAt_const γ 1).sub hpow using 1 <;> simp [k] <;> ring
  simpa only [k] using hterm.const_mul
    (finiteBernoulliWeight (cubicTorusEdgeFinset d N hN) p ω)

theorem torusGhostThetaGammaDerivative_eq_byCluster (d N : ℕ) (hN : 2 ≤ N)
    (p γ : I) (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostThetaGammaDerivative d N hN p γ =
      torusGhostThetaGammaDerivativeByCluster d N hN p γ := by
  have heq : torusGhostThetaPolynomial d N hN p =ᶠ[𝓝 (γ : ℝ)]
      torusGhostThetaByCluster d N hN p := by
    filter_upwards [Ioo_mem_nhds hγ0 hγ1] with y hy
    let yI : I := ⟨y, hy.1.le, hy.2.le⟩
    exact torusGhostThetaPolynomial_eq_byCluster d N hN p yI
  have hcluster := (torusGhostThetaByCluster_hasDerivAt_gamma d N hN p γ).congr_of_eventuallyEq
    heq
  have horiginal : HasDerivAt (torusGhostThetaPolynomial d N hN p)
      (torusGhostThetaGammaDerivative d N hN p γ) γ := by
    unfold torusGhostThetaPolynomial torusGhostThetaGammaDerivative
    exact hasDerivAt_finiteBernoulliExpectation _ γ
  exact horiginal.unique hcluster

/-- Equation (5.63): `χ_N(p,γ)=(1-γ)∂_γ θ_N(p,γ)`. -/
theorem torusGhostSusceptibility_eq_one_sub_mul_gammaDerivative
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostSusceptibilityPolynomial d N hN p γ =
      (1 - (γ : ℝ)) * torusGhostThetaGammaDerivative d N hN p γ := by
  rw [torusGhostThetaGammaDerivative_eq_byCluster d N hN p γ hγ0 hγ1]
  unfold torusGhostSusceptibilityPolynomial torusGhostThetaGammaDerivativeByCluster
  rw [← finiteBernoulliExpectation_const_mul]
  apply finiteBernoulliExpectation_congr
  intro ω hω
  let k := (cubicTorusOpenClusterFinset d N hN
    (ω : Set (CubicTorusEdge d N))).card
  have hk : 0 < k := by
    apply Finset.card_pos.mpr
    exact ⟨cubicTorusOrigin d N,
      (mem_cubicTorusOpenClusterFinset hN).mpr
        (cubicTorusOrigin_mem_openCluster d N (ω : Set (CubicTorusEdge d N)))⟩
  change (k : ℝ) * (1 - (γ : ℝ)) ^ k =
    (1 - (γ : ℝ)) * ((k : ℝ) * (1 - (γ : ℝ)) ^ (k - 1))
  have hpow : (1 - (γ : ℝ)) ^ k = (1 - (γ : ℝ)) ^ (k - 1) * (1 - γ) := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
  rw [hpow]
  ring

theorem torusGhostThetaPolynomial_hasDerivAt_p (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) :
    HasDerivAt (fun q ↦ torusGhostThetaPolynomial d N hN q γ)
      (torusGhostThetaPDerivative d N hN p γ) p := by
  unfold torusGhostThetaPolynomial torusGhostThetaPDerivative
  unfold finiteBernoulliExpectation
  apply HasDerivAt.fun_sum
  intro G hG
  have hprob := hasDerivAt_finiteBernoulliProbability_sum_pivotal
    (E := cubicTorusEdgeFinset d N hN)
    (isIncreasingTrace_torusHitEdgeTrace d N G) p
  simpa using hprob.const_mul
    (finiteBernoulliWeight (cubicTorusVertexFinset d N hN) γ G)

theorem torusGhostThetaPolynomial_hasDerivAt_gamma (d N : ℕ) (hN : 2 ≤ N)
    (p γ : ℝ) :
    HasDerivAt (torusGhostThetaPolynomial d N hN p)
      (torusGhostThetaGammaDerivative d N hN p γ) γ := by
  unfold torusGhostThetaPolynomial torusGhostThetaGammaDerivative
  exact hasDerivAt_finiteBernoulliExpectation _ γ

/-- The nested finite polynomial is exactly the probabilistic torus ghost probability. -/
theorem torusGhostTheta_eq_polynomial (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    torusGhostTheta d N p γ = torusGhostThetaPolynomial d N hN p γ := by
  rw [torusGhostTheta, ← integral_indicator_one (measurableSet_torusGhostHitEvent d N hN)]
  unfold torusGhostMeasure
  rw [integral_prod_symm]
  · calc
      (∫ G : Set (CubicTorus d N),
          ∫ ω : CubicTorusEdgeConfiguration d N,
            (torusGhostHitEvent d N).indicator (fun _ ↦ (1 : ℝ)) (ω, G)
              ∂torusBondMeasure d N p
            ∂setBer((Set.univ : Set (CubicTorus d N)), γ)) =
          ∫ G : Set (CubicTorus d N), torusFixedGreenProbability d N hN p G
            ∂setBer((Set.univ : Set (CubicTorus d N)), γ) := by
        apply integral_congr_ae
        filter_upwards with G
        rw [show (fun ω : CubicTorusEdgeConfiguration d N ↦
            (torusGhostHitEvent d N).indicator (fun _ ↦ (1 : ℝ)) (ω, G)) =
            (torusHitEdgeEvent d N G).indicator (fun _ ↦ (1 : ℝ)) by
          funext ω
          have heq : (∃ y, y ∈ cubicTorusOpenCluster d N ω ∧ y ∈ G) ↔
              ∃ y, y ∈ G ∧ y ∈ cubicTorusOpenCluster d N ω := by
            exact exists_congr fun y ↦ and_comm
          have hmem : (ω, G) ∈ torusGhostHitEvent d N ↔
              ω ∈ torusHitEdgeEvent d N G := heq
          by_cases h : (ω, G) ∈ torusGhostHitEvent d N
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
          · rw [Set.indicator_of_notMem h,
              Set.indicator_of_notMem fun hr ↦ h (hmem.mpr hr)]]
        exact (integral_indicator_one (μ := torusBondMeasure d N p)
          (measurableSet_torusHitEdgeEvent d N hN G)).trans
            (torusFixedGreenProbability_eq_measureReal d N hN p G).symm
      _ = finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
          (fun s ↦ torusFixedGreenProbability d N hN p (s : Set (CubicTorus d N))) :=
        dependsOnFun_torusFixedGreenProbability d N hN p |>.integral_setBernoulli γ
      _ = torusGhostThetaPolynomial d N hN p γ := by
        unfold torusGhostThetaPolynomial
        apply finiteBernoulliExpectation_congr
        intro s hs
        simp [torusFixedGreenProbability,
          restrictTo_coe _ s (Finset.mem_powerset.mp hs)]
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_torusGhostHitEvent d N hN)

/-- Source-facing finite-volume `p` derivative. -/
theorem torusGhostTheta_hasDerivAt_p (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    HasDerivAt (fun q : ℝ ↦ torusGhostThetaPolynomial d N hN q γ)
      (torusGhostThetaPDerivative d N hN p γ) p :=
  torusGhostThetaPolynomial_hasDerivAt_p d N hN p γ

/-- Source-facing finite-volume `γ` derivative. -/
theorem torusGhostTheta_hasDerivAt_gamma (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    HasDerivAt (torusGhostThetaPolynomial d N hN p)
      (torusGhostThetaGammaDerivative d N hN p γ) γ :=
  torusGhostThetaPolynomial_hasDerivAt_gamma d N hN p γ

end Percolation
