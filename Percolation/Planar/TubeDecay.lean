import Percolation.Critical.RegionSymmetry
import Percolation.Critical.TwoPoint
import Mathlib.Analysis.Subadditive

/-!
# Connectivity decay in a square-lattice tube

This file formalizes the sequence-level core of Grimmett, Lemma 11.27.  The tube
`Tₖ = {x : ℤ² | |x₂| ≤ k}` is invariant under translations in the first coordinate, so FKG
gives the same supermultiplicative connection inequality as in the unrestricted lattice.
-/

namespace Percolation

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Grimmett's horizontal tube `Tₖ = {x : ℤ² | |x₂| ≤ k}`. -/
def squareTube (k : ℕ) : Set SquareVertex :=
  {x | (x 1).natAbs ≤ k}

@[simp]
theorem mem_squareTube_iff {k : ℕ} {x : SquareVertex} :
    x ∈ squareTube k ↔ (x 1).natAbs ≤ k :=
  Iff.rfl

@[simp]
theorem cubicOrigin_mem_squareTube (k : ℕ) :
    (cubicOrigin : SquareVertex) ∈ squareTube k := by
  simp [squareTube, cubicOrigin]

@[simp]
theorem cubicAxisVertex_two_mem_squareTube (k n : ℕ) :
    cubicAxisVertex 2 n ∈ squareTube k := by
  simp [squareTube, cubicAxisVertex]

/-- The constrained two-point function `Pₚ(0 ↔ eₙ in Tₖ)`. -/
noncomputable def tubeTwoPointConnectivity (p : I) (k n : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real
    (connectionEventWithinVertices 2 (squareTube k) cubicOrigin (cubicAxisVertex 2 n))

theorem tubeTwoPointConnectivity_nonneg (p : I) (k n : ℕ) :
    0 ≤ tubeTwoPointConnectivity p k n :=
  measureReal_nonneg

theorem tubeTwoPointConnectivity_le_one (p : I) (k n : ℕ) :
    tubeTwoPointConnectivity p k n ≤ 1 :=
  measureReal_le_one

@[simp]
theorem tubeTwoPointConnectivity_zero (p : I) (k : ℕ) :
    tubeTwoPointConnectivity p k 0 = 1 := by
  have haxis : cubicAxisVertex 2 0 = (cubicOrigin : SquareVertex) := by
    ext i
    simp [cubicAxisVertex, cubicOrigin]
  have heq : connectionEventWithinVertices 2 (squareTube k)
      cubicOrigin (cubicAxisVertex 2 0) = Set.univ := by
    rw [haxis]
    apply Set.eq_univ_of_forall
    intro omega
    refine ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], ?_⟩
    intro z hz
    simp at hz
    subst z
    exact cubicOrigin_mem_squareTube k
  simp [tubeTwoPointConnectivity, heq]

/-- Translation along the first coordinate preserves every horizontal tube. -/
theorem cubicGraphIsoRegion_translation_axis_squareTube (k m : ℕ) :
    cubicGraphIsoRegion
        (cubicTranslationIso cubicOrigin (cubicAxisVertex 2 m)) (squareTube k) =
      squareTube k := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [squareTube, cubicTranslationIso_apply, cubicTranslate,
      cubicAxisVertex, cubicOrigin] using hy
  · intro hx
    let y := cubicTranslate (cubicAxisVertex 2 m) cubicOrigin x
    refine ⟨y, ?_, ?_⟩
    · simpa [y, squareTube, cubicTranslate, cubicAxisVertex, cubicOrigin] using hx
    · ext i
      fin_cases i <;>
        simp [y, cubicTranslationIso_apply, cubicTranslate, cubicAxisVertex, cubicOrigin]

/-- Translating the second tube segment reduces it to a segment based at the origin. -/
theorem tubeTwoPointConnectivity_translate (p : I) (k m n : ℕ) :
    (bernoulliBondMeasure 2 p).real
        (connectionEventWithinVertices 2 (squareTube k)
          (cubicAxisVertex 2 m) (cubicAxisVertex 2 (m + n))) =
      tubeTwoPointConnectivity p k n := by
  let F := cubicTranslationIso cubicOrigin (cubicAxisVertex 2 m)
  have h := bernoulliBondMeasure_real_connectionEventWithinVertices_graphIso
    F (squareTube k) p cubicOrigin (cubicAxisVertex 2 n)
  rw [cubicGraphIsoRegion_translation_axis_squareTube] at h
  have h0 : F cubicOrigin = cubicAxisVertex 2 m := by
    simp [F, cubicTranslationIso_apply]
  have hn : F (cubicAxisVertex 2 n) = cubicAxisVertex 2 (m + n) := by
    simpa [F] using cubicTranslate_axisVertex_axisVertex (d := 2) (m := m) (n := n) (by omega)
  simpa [tubeTwoPointConnectivity, h0, hn] using h.symm

/-- FKG concatenation for tube connections. -/
theorem tubeTwoPointConnectivity_mul_le (p : I) (k m n : ℕ) :
    tubeTwoPointConnectivity p k m * tubeTwoPointConnectivity p k n ≤
      tubeTwoPointConnectivity p k (m + n) := by
  let em := cubicAxisVertex 2 m
  let emn := cubicAxisVertex 2 (m + n)
  let A := connectionEventWithinVertices 2 (squareTube k) cubicOrigin em
  let B := connectionEventWithinVertices 2 (squareTube k) em emn
  have hB : (bernoulliBondMeasure 2 p).real B = tubeTwoPointConnectivity p k n := by
    simpa [B, em, emn] using tubeTwoPointConnectivity_translate p k m n
  have hfkg := bernoulliBondMeasure_real_fkg p
    (isIncreasingEvent_connectionEventWithinVertices 2 (squareTube k) cubicOrigin em)
    (isIncreasingEvent_connectionEventWithinVertices 2 (squareTube k) em emn)
    (measurableSet_connectionEventWithinVertices 2 (squareTube k) cubicOrigin em)
    (measurableSet_connectionEventWithinVertices 2 (squareTube k) em emn)
  have hsubset : A ∩ B ⊆
      connectionEventWithinVertices 2 (squareTube k) cubicOrigin emn := by
    rintro omega ⟨⟨w, hw, hwTube⟩, ⟨q, hq, hqTube⟩⟩
    refine ⟨w.append q, walkIsOpen_append hw hq, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    exact (List.mem_append.mp hz).elim (hwTube z)
      (fun h ↦ hqTube z (List.mem_of_mem_tail h))
  calc
    tubeTwoPointConnectivity p k m * tubeTwoPointConnectivity p k n =
        (bernoulliBondMeasure 2 p).real A * (bernoulliBondMeasure 2 p).real B := by
      simp [tubeTwoPointConnectivity, A, hB, em]
    _ ≤ (bernoulliBondMeasure 2 p).real (A ∩ B) := hfkg
    _ ≤ tubeTwoPointConnectivity p k (m + n) := measureReal_mono hsubset

/-! ## A concrete straight path and positivity -/

private def squareStraightAxisWalk (n : ℕ) :
    squareGraph.Walk cubicOrigin (cubicAxisVertex 2 n) := by
  let steps : List (CubicDirection 2) := List.replicate n ((0 : Fin 2), true)
  let w := cubicWalkFrom (cubicOrigin : SquareVertex) steps
  have hend : cubicEndpointFrom cubicOrigin steps = cubicAxisVertex 2 n := by
    dsimp [steps]
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i <;> simp [cubicAxisVertex, cubicOrigin]
  exact w.copy rfl hend

private theorem squareStraightAxisWalk_length (n : ℕ) :
    (squareStraightAxisWalk n).length = n := by
  simp [squareStraightAxisWalk]

private theorem squareStraightAxisWalk_isPath (n : ℕ) :
    (squareStraightAxisWalk n).IsPath := by
  let steps : SelfAvoidingWalk 2 n := straightSelfAvoidingWalk (by omega) n
  simpa [steps, straightSelfAvoidingWalk, selfAvoidingWalkWalk,
    squareStraightAxisWalk] using selfAvoidingWalkWalk_isPath steps

private theorem squareStraightAxisWalk_support_mem_tube (k n : ℕ) :
    ∀ z ∈ (squareStraightAxisWalk n).support, z ∈ squareTube k := by
  intro z hz
  let steps : List (CubicDirection 2) := List.replicate n ((0 : Fin 2), true)
  have hz' : z ∈ cubicVerticesFrom (cubicOrigin : SquareVertex) steps := by
    simpa [squareStraightAxisWalk, steps] using hz
  have hcoord := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
    (cubicOrigin : SquareVertex) (0 : Fin 2) (1 : Fin 2) n (by decide) hz'
  simp [squareTube, cubicOrigin, hcoord]

/-- The straight tube path gives the elementary lower bound `pⁿ`. -/
theorem pow_le_tubeTwoPointConnectivity (p : I) (k n : ℕ) :
    (p : ℝ) ^ n ≤ tubeTwoPointConnectivity p k n := by
  let w := squareStraightAxisWalk n
  have hsub : {omega : EdgeConfiguration 2 | walkIsOpen omega w} ⊆
      connectionEventWithinVertices 2 (squareTube k) cubicOrigin (cubicAxisVertex 2 n) := by
    intro omega hw
    exact ⟨w, hw, squareStraightAxisWalk_support_mem_tube k n⟩
  calc
    (p : ℝ) ^ n =
        (bernoulliBondMeasure 2 p).real {omega : EdgeConfiguration 2 | walkIsOpen omega w} := by
      rw [bernoulliBondMeasure_real_walkIsOpen p w
        (squareStraightAxisWalk_isPath n).isTrail, squareStraightAxisWalk_length]
    _ ≤ tubeTwoPointConnectivity p k n := measureReal_mono hsub

theorem tubeTwoPointConnectivity_pos {p : I} (hp : 0 < (p : ℝ)) (k n : ℕ) :
    0 < tubeTwoPointConnectivity p k n :=
  (pow_pos hp n).trans_le (pow_le_tubeTwoPointConnectivity p k n)

/-! ## Fekete rate -/

/-- Negative logarithm of the tube connection probability. -/
noncomputable def tubeConnectivityNegLog (p : I) (k n : ℕ) : ℝ :=
  -Real.log (tubeTwoPointConnectivity p k n)

theorem tubeConnectivityNegLog_subadditive {p : I} (hp : 0 < (p : ℝ)) (k : ℕ) :
    Subadditive (tubeConnectivityNegLog p k) := by
  intro m n
  have hm := tubeTwoPointConnectivity_pos hp k m
  have hn := tubeTwoPointConnectivity_pos hp k n
  have hmn := tubeTwoPointConnectivity_pos hp k (m + n)
  have hmul := tubeTwoPointConnectivity_mul_le p k m n
  have hlog := Real.log_le_log (mul_pos hm hn) hmul
  rw [Real.log_mul hm.ne' hn.ne'] at hlog
  simpa [tubeConnectivityNegLog, add_comm] using neg_le_neg hlog

theorem tubeConnectivityNegLog_div_bddBelow (p : I) (k : ℕ) :
    BddBelow (Set.range fun n : ℕ ↦ tubeConnectivityNegLog p k n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · simp [hn]
  have hlog : Real.log (tubeTwoPointConnectivity p k n) ≤ 0 :=
    Real.log_nonpos (tubeTwoPointConnectivity_nonneg p k n)
      (tubeTwoPointConnectivity_le_one p k n)
  exact div_nonneg (neg_nonneg.mpr hlog) (Nat.cast_nonneg n)

/-- Grimmett's tube rate `φₖ(p)`. -/
noncomputable def tubeConnectivityDecayRate (p : I) (k : ℕ) : ℝ :=
  sInf ((fun n : ℕ ↦ tubeConnectivityNegLog p k n / n) '' Set.Ici 1)

/-- Existence of the logarithmic tube-connectivity rate, equation (11.28). -/
theorem tubeTwoPointConnectivity_logRate_tendsto
    {p : I} (hp : 0 < (p : ℝ)) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ -Real.log (tubeTwoPointConnectivity p k n) / n)
      atTop (nhds (tubeConnectivityDecayRate p k)) := by
  have hsub := tubeConnectivityNegLog_subadditive hp k
  have hlim := hsub.tendsto_lim (tubeConnectivityNegLog_div_bddBelow p k)
  simpa [tubeConnectivityNegLog, tubeConnectivityDecayRate, Subadditive.lim] using hlim

/-- Exact all-scale exponential upper bound, equation (11.29). -/
theorem tubeTwoPointConnectivity_le_exp_rate
    {p : I} (hp : 0 < (p : ℝ)) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    tubeTwoPointConnectivity p k n ≤
      Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k) := by
  have hsub := tubeConnectivityNegLog_subadditive hp k
  have hle := hsub.lim_le_div (tubeConnectivityNegLog_div_bddBelow p k) hn.ne'
  have hpos := tubeTwoPointConnectivity_pos hp k n
  rw [Subadditive.lim] at hle
  have hle' : tubeConnectivityDecayRate p k ≤ tubeConnectivityNegLog p k n / n := by
    simpa [tubeConnectivityDecayRate] using hle
  apply (Real.log_le_iff_le_exp hpos).mp
  have hnreal : (0 : ℝ) < n := by positivity
  have hmul := (le_div_iff₀ hnreal).mp hle'
  dsimp [tubeConnectivityNegLog] at hmul
  nlinarith

/-- The straight path bounds the tube rate above by `-log p`. -/
theorem tubeConnectivityDecayRate_le_neg_log
    {p : I} (hp : 0 < (p : ℝ)) (k : ℕ) :
    tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) := by
  have hle := (tubeConnectivityNegLog_subadditive hp k).lim_le_div
    (tubeConnectivityNegLog_div_bddBelow p k) (show (1 : ℕ) ≠ 0 by omega)
  rw [Subadditive.lim] at hle
  have hpow := pow_le_tubeTwoPointConnectivity p k 1
  have hlog := Real.log_le_log (by simpa using hp) hpow
  have hneg : tubeConnectivityNegLog p k 1 ≤ -Real.log (p : ℝ) := by
    simpa [tubeConnectivityNegLog] using neg_le_neg hlog
  simpa [tubeConnectivityDecayRate] using hle.trans (by simpa using hneg)

/-! ## Closed vertical cuts and strict positivity of the rate -/

@[simp]
theorem cubicStepFrom_squareVertex_horizontal (i y : ℤ) :
    cubicStepFrom (squareVertex i y) ((0 : Fin 2), true) = squareVertex (i + 1) y := by
  ext j
  fin_cases j <;> simp [squareVertex, cubicStepFrom, cubicDirectionIncrement]

/-- The horizontal bond from `(i,y)` to `(i+1,y)`. -/
def squareTubeCutEdge (i : ℕ) (y : ℤ) : SquareEdge :=
  cubicStepEdge (squareVertex i y) ((0 : Fin 2), true)

@[simp]
theorem coe_squareTubeCutEdge (i : ℕ) (y : ℤ) :
    (squareTubeCutEdge i y : Sym2 SquareVertex) =
      s(squareVertex i y, squareVertex (i + 1) y) := by
  simp [squareTubeCutEdge, cubicStepEdge]

/-- Distinct level/height pairs give distinct horizontal cut bonds. -/
theorem squareTubeCutEdge_pair_injective :
    Function.Injective (fun q : ℕ × ℤ ↦ squareTubeCutEdge q.1 q.2) := by
  rintro ⟨i, y⟩ ⟨j, z⟩ h
  have hval := congrArg Subtype.val h
  simp only [coe_squareTubeCutEdge] at hval
  rw [Sym2.eq_iff] at hval
  rcases hval with hdirect | hswap
  · have hi := congrFun hdirect.1 0
    have hy := congrFun hdirect.1 1
    simp at hi hy
    exact Prod.ext (by omega) (by omega)
  · have hij := congrFun hswap.1 0
    have hji := congrFun hswap.2 0
    simp at hij hji
    omega

/-- All `2k+1` horizontal bonds crossing from level `i` to `i+1` inside `Tₖ`. -/
noncomputable def squareTubeCutEdges (k i : ℕ) : Finset SquareEdge :=
  (Finset.Icc (-((k : ℕ) : ℤ)) (k : ℤ)).map
    ⟨fun y ↦ squareTubeCutEdge i y,
      fun y z h ↦ by
        have hp := squareTubeCutEdge_pair_injective
          (show squareTubeCutEdge (i, y).1 (i, y).2 =
            squareTubeCutEdge (i, z).1 (i, z).2 by simpa using h)
        exact congrArg Prod.snd hp⟩

theorem mem_squareTubeCutEdges_iff {k i : ℕ} {e : SquareEdge} :
    e ∈ squareTubeCutEdges k i ↔
      ∃ y : ℤ, -((k : ℕ) : ℤ) ≤ y ∧ y ≤ k ∧ e = squareTubeCutEdge i y := by
  classical
  constructor
  · intro he
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp he
    exact ⟨y, (Finset.mem_Icc.mp hy).1, (Finset.mem_Icc.mp hy).2, hye.symm⟩
  · rintro ⟨y, hy0, hyk, rfl⟩
    exact Finset.mem_map.mpr ⟨y, Finset.mem_Icc.mpr ⟨hy0, hyk⟩, rfl⟩

@[simp]
theorem card_squareTubeCutEdges (k i : ℕ) :
    (squareTubeCutEdges k i).card = 2 * k + 1 := by
  classical
  rw [squareTubeCutEdges, Finset.card_map, Int.card_Icc]
  have heq : ((k : ℤ) + 1 - -((k : ℤ))) = ((2 * k + 1 : ℕ) : ℤ) := by omega
  rw [heq]
  exact Int.toNat_natCast (2 * k + 1)

/-- Cut supports at different horizontal levels are disjoint. -/
theorem pairwiseDisjoint_squareTubeCutEdges (k : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) (squareTubeCutEdges k) := by
  intro i _hi j _hj hij
  change Disjoint (squareTubeCutEdges k i) (squareTubeCutEdges k j)
  rw [Finset.disjoint_left]
  intro e hei hej
  obtain ⟨y, _hy0, _hyk, rfl⟩ := mem_squareTubeCutEdges_iff.mp hei
  obtain ⟨z, _hz0, _hzk, heq⟩ := mem_squareTubeCutEdges_iff.mp hej
  have hp : (i, y) = (j, z) := squareTubeCutEdge_pair_injective (by simpa using heq)
  exact hij (congrArg Prod.fst hp)

/-- The event that an entire vertical cut in the tube is closed. -/
def squareTubeClosedCutEvent (k i : ℕ) : Set (EdgeConfiguration 2) :=
  closedEdgeSetEvent 2 (squareTubeCutEdges k i)

theorem dependsOn_squareTubeClosedCutEvent (k i : ℕ) :
    DependsOn (squareTubeCutEdges k i) (squareTubeClosedCutEvent k i) :=
  by
    intro omega eta hagree
    simp only [squareTubeClosedCutEvent, mem_closedEdgeSetEvent, Set.disjoint_left]
    constructor
    · intro h e he heeta
      exact h he ((hagree e he).mpr heeta)
    · intro h e he heomega
      exact h he ((hagree e he).mp heomega)

theorem measurableSet_squareTubeClosedCutEvent (k i : ℕ) :
    MeasurableSet (squareTubeClosedCutEvent k i) :=
  measurableSet_closedEdgeSetEvent 2 (squareTubeCutEdges k i)

theorem bernoulliBondMeasure_real_squareTubeClosedCutEvent
    (p : I) (k i : ℕ) :
    (bernoulliBondMeasure 2 p).real (squareTubeClosedCutEvent k i) =
      (1 - (p : ℝ)) ^ (2 * k + 1) := by
  rw [squareTubeClosedCutEvent, bernoulliBondMeasure_real_closedEdgeSetEvent,
    card_squareTubeCutEdges]

theorem iIndepSet_squareTubeClosedCutEvent (p : I) (k : ℕ) :
    iIndepSet (squareTubeClosedCutEvent k) (bernoulliBondMeasure 2 p) :=
  bernoulliBondMeasure_iIndepSet_of_pairwiseDisjoint_dependsOn p
    (squareTubeCutEdges k) (squareTubeClosedCutEvent k)
    (dependsOn_squareTubeClosedCutEvent k) (pairwiseDisjoint_squareTubeCutEdges k)

private theorem edge_eq_squareTubeCutEdge_of_crosses_level
    {u v : SquareVertex} (huv : squareGraph.Adj u v) {i : ℕ}
    (hu : u 0 ≤ i) (hv : (i : ℤ) < v 0) :
    ∃ y : ℤ, u = squareVertex i y ∧ v = squareVertex (i + 1) y ∧
      (⟨s(u, v), (SimpleGraph.mem_edgeSet squareGraph).mpr huv⟩ : SquareEdge) =
        squareTubeCutEdge i y := by
  obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom u v).mp huv
  rcases a with ⟨j, b⟩
  have hcoord := congrFun ha 0
  have hj : j = (0 : Fin 2) := by
    by_contra hne
    simp [cubicStepFrom, Ne.symm hne] at hcoord
    omega
  subst j
  have hb : b = true := by
    cases b
    · simp [cubicStepFrom, cubicDirectionIncrement] at hcoord
      omega
    · rfl
  subst b
  have hu0 : u 0 = i := by
    simp [cubicStepFrom, cubicDirectionIncrement] at hcoord
    omega
  let y := u 1
  have hueq : u = squareVertex i y := by
    rw [← squareVertex_eta u]
    simp [hu0, y]
  have hveq : v = squareVertex (i + 1) y := by
    rw [ha, hueq, cubicStepFrom_squareVertex_horizontal]
  refine ⟨y, hueq, hveq, ?_⟩
  apply Subtype.ext
  simp [hueq, hveq, squareTubeCutEdge, cubicStepEdge]

/-- A closed level cut prevents an open tube walk from passing to its right. -/
private theorem open_tube_walk_end_le_of_closed_cut
    {k i : ℕ} {omega : EdgeConfiguration 2} {u v : SquareVertex}
    (w : squareGraph.Walk u v) (hopen : walkIsOpen omega w)
    (htube : ∀ z ∈ w.support, z ∈ squareTube k)
    (hu : u 0 ≤ i) (hclosed : omega ∈ squareTubeClosedCutEvent k i) :
    v 0 ≤ i := by
  induction w with
  | nil => simpa using hu
  | @cons u₀ u₁ v₀ hu₀u₁ q ih =>
      by_cases hu₁ : u₁ 0 ≤ i
      · have hopenTail : walkIsOpen omega q := by
          intro e he
          exact hopen e (by simp [he])
        apply ih hopenTail
        · intro z hz
          exact htube z (by simp [hz])
        · exact hu₁
      · exfalso
        obtain ⟨y, huEq, hu₁Eq, hedge⟩ :=
          edge_eq_squareTubeCutEdge_of_crosses_level hu₀u₁ hu (lt_of_not_ge hu₁)
        have hu₀Tube : u₀ ∈ squareTube k := htube u₀ (by simp)
        have hyBound : -((k : ℕ) : ℤ) ≤ y ∧ y ≤ k := by
          have hnat : y.natAbs ≤ k := by simpa [huEq, squareTube] using hu₀Tube
          rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs] at hnat
          exact abs_le.mp hnat
        have hedgeMem : squareTubeCutEdge i y ∈ squareTubeCutEdges k i :=
          mem_squareTubeCutEdges_iff.mpr ⟨y, hyBound.1, hyBound.2, rfl⟩
        have hopenEdge : squareTubeCutEdge i y ∈ omega := by
          have hhead : (⟨s(u₀, u₁),
              (SimpleGraph.mem_edgeSet squareGraph).mpr hu₀u₁⟩ : SquareEdge) ∈ omega := by
            apply hopen
            simp
          simpa [hedge] using hhead
        have hdisj := (mem_closedEdgeSetEvent 2 (squareTubeCutEdges k i) omega).mp hclosed
        exact Set.disjoint_left.mp hdisj hedgeMem hopenEdge

/-- A tube connection from level `0` to level `n` avoids every closed cut before `n`. -/
theorem tubeConnection_subset_closedCuts_compl (k n : ℕ) :
    connectionEventWithinVertices 2 (squareTube k) cubicOrigin (cubicAxisVertex 2 n) ⊆
      ⋂ i ∈ Finset.range n, (squareTubeClosedCutEvent k i)ᶜ := by
  intro omega hconn
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro i hi hclosed
  rcases hconn with ⟨w, hopen, htube⟩
  have hend := open_tube_walk_end_le_of_closed_cut w hopen htube (by simp [cubicOrigin]) hclosed
  have hi' : i < n := Finset.mem_range.mp hi
  simp [cubicAxisVertex] at hend
  omega

/-- The independent closed cuts give the explicit upper bound from the proof of Lemma 11.27. -/
theorem tubeTwoPointConnectivity_le_closedCut_bound (p : I) (k n : ℕ) :
    tubeTwoPointConnectivity p k n ≤
      (1 - (1 - (p : ℝ)) ^ (2 * k + 1)) ^ n := by
  let mu := bernoulliBondMeasure 2 p
  let barrier := squareTubeClosedCutEvent k
  have hind : iIndepSet (fun i ↦ (barrier i)ᶜ) mu :=
    iIndepSet_compl (iIndepSet_squareTubeClosedCutEvent p k)
  have hfactor := hind.meas_biInter (Finset.range n)
  have hfactorReal :
      mu.real (⋂ i ∈ Finset.range n, (barrier i)ᶜ) =
        ∏ i ∈ Finset.range n, mu.real ((barrier i)ᶜ) := by
    simpa only [measureReal_def, ENNReal.toReal_prod] using congrArg ENNReal.toReal hfactor
  calc
    tubeTwoPointConnectivity p k n ≤
        mu.real (⋂ i ∈ Finset.range n, (barrier i)ᶜ) :=
      measureReal_mono (tubeConnection_subset_closedCuts_compl k n) (measure_ne_top _ _)
    _ = ∏ i ∈ Finset.range n, mu.real ((barrier i)ᶜ) := hfactorReal
    _ = ∏ _i ∈ Finset.range n, (1 - (1 - (p : ℝ)) ^ (2 * k + 1)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [measureReal_compl (measurableSet_squareTubeClosedCutEvent k i), probReal_univ,
        bernoulliBondMeasure_real_squareTubeClosedCutEvent]
    _ = (1 - (1 - (p : ℝ)) ^ (2 * k + 1)) ^ n := by simp

/-- The tube rate is strictly positive for every nontrivial density, equation (11.30). -/
theorem tubeConnectivityDecayRate_pos
    {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    0 < tubeConnectivityDecayRate p k := by
  let q := 1 - (1 - (p : ℝ)) ^ (2 * k + 1)
  have hbase0 : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hbase1 : 1 - (p : ℝ) ≤ 1 := by linarith [hp0]
  have hpow0 : 0 < (1 - (p : ℝ)) ^ (2 * k + 1) := pow_pos hbase0 _
  have hpow1 : (1 - (p : ℝ)) ^ (2 * k + 1) ≤ 1 :=
    pow_le_one₀ (by linarith) hbase1
  have hq0 : 0 < q := by
    dsimp [q]
    have hpowlt : (1 - (p : ℝ)) ^ (2 * k + 1) < 1 :=
      pow_lt_one₀ (by linarith) (by linarith) (by omega)
    linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  -- At `n=1`, the Fekete infimum is bounded below by the closed-cut exponential rate.
  have hall (n : ℕ) (hn : 0 < n) :
      -Real.log q ≤ tubeConnectivityNegLog p k n / n := by
    have hbound := tubeTwoPointConnectivity_le_closedCut_bound p k n
    have hconn := tubeTwoPointConnectivity_pos hp0 k n
    have hlogn := Real.log_le_log hconn hbound
    have hqn : 0 < q ^ n := pow_pos hq0 n
    have hlogpow : Real.log (q ^ n) = n * Real.log q := by
      rw [Real.log_pow]
    have hnR : (0 : ℝ) < n := by positivity
    rw [hlogpow] at hlogn
    dsimp [tubeConnectivityNegLog]
    apply (le_div_iff₀ hnR).2
    nlinarith
  have hleInf : -Real.log q ≤ tubeConnectivityDecayRate p k := by
    rw [tubeConnectivityDecayRate]
    apply le_csInf
    · exact ⟨tubeConnectivityNegLog p k 1,
        ⟨1, by simp, by simp⟩⟩
    · rintro _ ⟨n, hn, rfl⟩
      exact hall n (Nat.zero_lt_of_lt hn)
  exact (neg_pos.mpr (Real.log_neg hq0 hq1)).trans_le hleInf

/-- Combined positivity and finite real upper bound in Grimmett, equation (11.30). -/
theorem tubeConnectivityDecayRate_pos_and_le_neg_log
    {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    0 < tubeConnectivityDecayRate p k ∧
      tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) := by
  exact ⟨tubeConnectivityDecayRate_pos hp0 hp1 k,
    tubeConnectivityDecayRate_le_neg_log hp0 k⟩

/-! ## Increasing the tube width -/

theorem squareTube_mono {k l : ℕ} (hkl : k ≤ l) :
    squareTube k ⊆ squareTube l := by
  intro x hx
  exact hx.trans hkl

theorem tubeTwoPointConnectivity_mono_width (p : I) {k l : ℕ} (hkl : k ≤ l) (n : ℕ) :
    tubeTwoPointConnectivity p k n ≤ tubeTwoPointConnectivity p l n := by
  unfold tubeTwoPointConnectivity
  exact measureReal_mono
    (connectionEventWithinVertices_mono (squareTube_mono hkl)
      cubicOrigin (cubicAxisVertex 2 n))

theorem tubeTwoPointConnectivity_le_twoPointConnectivity (p : I) (k n : ℕ) :
    tubeTwoPointConnectivity p k n ≤
      twoPointConnectivity 2 p cubicOrigin (cubicAxisVertex 2 n) := by
  unfold tubeTwoPointConnectivity twoPointConnectivity
  exact measureReal_mono
    (connectionEventWithinVertices_subset_connectionEvent 2 (squareTube k)
      cubicOrigin (cubicAxisVertex 2 n))

/-- The tube decay rate is nonincreasing in its width. -/
theorem tubeConnectivityDecayRate_antitone
    {p : I} (hp : 0 < (p : ℝ)) : Antitone (tubeConnectivityDecayRate p) := by
  intro k l hkl
  apply le_of_tendsto_of_tendsto'
    (tubeTwoPointConnectivity_logRate_tendsto hp l)
    (tubeTwoPointConnectivity_logRate_tendsto hp k)
  intro n
  by_cases hn : n = 0
  · simp [hn]
  have hk := tubeTwoPointConnectivity_pos hp k n
  have hmono := tubeTwoPointConnectivity_mono_width p hkl n
  have hlog := Real.log_le_log hk hmono
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (Nat.cast_nonneg n)

/-- Every unrestricted finite connection is contained in some finite-width horizontal tube. -/
theorem iUnion_tubeConnectionEvent (n : ℕ) :
    (⋃ k : ℕ, connectionEventWithinVertices 2 (squareTube k)
        cubicOrigin (cubicAxisVertex 2 n)) =
      connectionEvent 2 cubicOrigin (cubicAxisVertex 2 n) := by
  apply Set.Subset.antisymm
  · intro omega h
    simp only [Set.mem_iUnion] at h
    obtain ⟨k, hk⟩ := h
    exact connectionEventWithinVertices_subset_connectionEvent 2 (squareTube k)
      cubicOrigin (cubicAxisVertex 2 n) hk
  · rintro omega ⟨w, hopen⟩
    let heights : List ℕ := w.support.map (fun z ↦ (z 1).natAbs)
    let k : ℕ := heights.foldr max 0
    have hsupport : ∀ z ∈ w.support, z ∈ squareTube k := by
      intro z hz
      have hzHeight : (z 1).natAbs ∈ heights :=
        List.mem_map.mpr ⟨z, hz, rfl⟩
      exact List.le_max_of_le hzHeight le_rfl
    exact Set.mem_iUnion.mpr ⟨k, w, hopen, hsupport⟩

/-- At a fixed displacement, constrained tube probabilities increase to the unrestricted
two-point function. -/
theorem tubeTwoPointConnectivity_tendsto_twoPointConnectivity
    (p : I) (n : ℕ) :
    Tendsto (fun k : ℕ ↦ tubeTwoPointConnectivity p k n) atTop
      (nhds (twoPointConnectivity 2 p cubicOrigin (cubicAxisVertex 2 n))) := by
  let mu := bernoulliBondMeasure 2 p
  let A : ℕ → Set (EdgeConfiguration 2) := fun k ↦
    connectionEventWithinVertices 2 (squareTube k) cubicOrigin (cubicAxisVertex 2 n)
  have hmono : Monotone A := by
    intro k l hkl
    exact connectionEventWithinVertices_mono (squareTube_mono hkl)
      cubicOrigin (cubicAxisVertex 2 n)
  have hENN : Tendsto (fun k : ℕ ↦ mu (A k)) atTop
      (nhds (mu (connectionEvent 2 cubicOrigin (cubicAxisVertex 2 n)))) := by
    have h := tendsto_measure_iUnion_atTop (μ := mu) hmono
    rw [iUnion_tubeConnectionEvent n] at h
    simpa only [Function.comp_apply] using h
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hENN
  simpa [tubeTwoPointConnectivity, twoPointConnectivity, mu, A,
    Measure.real] using hreal

/-- The normalized negative logarithm of the unrestricted axis connectivity is bounded above
by every tube rate. -/
theorem axisConnectivityDecayRate_le_tubeConnectivityDecayRate
    {p : I} (hp : 0 < (p : ℝ)) (k : ℕ) :
    axisConnectivityDecayRate 2 p ≤ tubeConnectivityDecayRate p k := by
  apply le_of_tendsto_of_tendsto'
    (twoPointConnectivity_axis_logRate_tendsto_aux (d := 2) (by omega) hp)
    (tubeTwoPointConnectivity_logRate_tendsto hp k)
  intro n
  by_cases hn : n = 0
  · simp [hn]
  have htube := tubeTwoPointConnectivity_pos hp k n
  have hle := tubeTwoPointConnectivity_le_twoPointConnectivity p k n
  have hlog := Real.log_le_log htube hle
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (Nat.cast_nonneg n)

/-- Grimmett, equation (11.31): tube decay rates decrease to the unrestricted axis rate. -/
theorem tubeConnectivityDecayRate_tendsto_axisConnectivityDecayRate
    {p : I} (hp : 0 < (p : ℝ)) :
    Tendsto (tubeConnectivityDecayRate p) atTop
      (nhds (axisConnectivityDecayRate 2 p)) := by
  let L := sInf (Set.range (tubeConnectivityDecayRate p))
  have hanti : Antitone (tubeConnectivityDecayRate p) :=
    tubeConnectivityDecayRate_antitone hp
  have hbdd : BddBelow (Set.range (tubeConnectivityDecayRate p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hnonneg : 0 ≤ tubeConnectivityDecayRate p k := by
      rw [tubeConnectivityDecayRate]
      apply le_csInf
      · exact ⟨tubeConnectivityNegLog p k 1, ⟨1, by simp, by simp⟩⟩
      · rintro _ ⟨n, hn, rfl⟩
        have hlogn : Real.log (tubeTwoPointConnectivity p k n) ≤ 0 :=
          Real.log_nonpos (tubeTwoPointConnectivity_nonneg p k n)
            (tubeTwoPointConnectivity_le_one p k n)
        exact div_nonneg (neg_nonneg.mpr hlogn) (Nat.cast_nonneg n)
    exact hnonneg
  have hImage : tubeConnectivityDecayRate p '' (Set.Ici 0 : Set ℕ) =
      Set.range (tubeConnectivityDecayRate p) := by
    ext x
    simp
  have hbdd0 : BddBelow
      (tubeConnectivityDecayRate p '' (Set.Ici 0 : Set ℕ)) := by
    rw [hImage]
    exact hbdd
  have hL : Tendsto (tubeConnectivityDecayRate p) atTop (nhds L) := by
    have h := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
      (k := 0) (hanti.antitoneOn _) hbdd0
    rw [hImage] at h
    exact h
  have haxisLeL : axisConnectivityDecayRate 2 p ≤ L := by
    exact ge_of_tendsto' hL
      (fun k ↦ axisConnectivityDecayRate_le_tubeConnectivityDecayRate hp k)
  have hLleEach (n : ℕ) (hn : 1 ≤ n) :
      L ≤ axisConnectivityNegLog 2 p n / n := by
    have hleft := tubeTwoPointConnectivity_tendsto_twoPointConnectivity p n
    have hright : Tendsto
        (fun k : ℕ ↦ Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k))
        atTop (nhds (Real.exp (-(n : ℝ) * L))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := -(n : ℝ))).mul hL)
    have hprob : twoPointConnectivity 2 p cubicOrigin (cubicAxisVertex 2 n) ≤
        Real.exp (-(n : ℝ) * L) := by
      exact le_of_tendsto_of_tendsto' hleft hright fun k ↦
        tubeTwoPointConnectivity_le_exp_rate hp k (by omega)
    have htau := twoPointConnectivity_pos 2 hp cubicOrigin (cubicAxisVertex 2 n)
    have hlog := (Real.log_le_iff_le_exp htau).mpr hprob
    have hnR : (0 : ℝ) < n := by positivity
    dsimp [axisConnectivityNegLog]
    apply (le_div_iff₀ hnR).2
    nlinarith
  have hLleAxis : L ≤ axisConnectivityDecayRate 2 p := by
    rw [axisConnectivityDecayRate]
    apply le_csInf
    · exact ⟨axisConnectivityNegLog 2 p 1,
        ⟨1, by simp, by simp⟩⟩
    · rintro _ ⟨n, hn, rfl⟩
      exact hLleEach n hn
  have hEq : L = axisConnectivityDecayRate 2 p :=
    le_antisymm hLleAxis haxisLeL
  simpa [hEq] using hL

/-- **Grimmett, Lemma 11.27.** The tube rate exists, gives an all-scale exponential upper
bound, is positive and finite for `0 < p < 1`, and decreases to the unrestricted rate. -/
theorem tubeConnectivityDecayRate_properties
    {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ -Real.log (tubeTwoPointConnectivity p k n) / n)
        atTop (nhds (tubeConnectivityDecayRate p k)) ∧
      (∀ n : ℕ, 1 ≤ n → tubeTwoPointConnectivity p k n ≤
        Real.exp (-(n : ℝ) * tubeConnectivityDecayRate p k)) ∧
      0 < tubeConnectivityDecayRate p k ∧
      tubeConnectivityDecayRate p k ≤ -Real.log (p : ℝ) ∧
      Antitone (tubeConnectivityDecayRate p) ∧
      Tendsto (tubeConnectivityDecayRate p) atTop
        (nhds (axisConnectivityDecayRate 2 p)) := by
  exact ⟨tubeTwoPointConnectivity_logRate_tendsto hp0 k,
    fun n hn ↦ tubeTwoPointConnectivity_le_exp_rate hp0 k (by omega),
    tubeConnectivityDecayRate_pos hp0 hp1 k,
    tubeConnectivityDecayRate_le_neg_log hp0 k,
    tubeConnectivityDecayRate_antitone hp0,
    tubeConnectivityDecayRate_tendsto_axisConnectivityDecayRate hp0⟩

end Percolation
