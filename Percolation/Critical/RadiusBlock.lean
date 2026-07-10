import Percolation.Critical.PivotalSausage
import Percolation.Critical.Translation

/-!
# Block decomposition for radius events

An open path reaching radius `n + m` splits at its first visit to the
`n`-sphere into two edge-disjoint witnesses.  BK then bounds the long-radius
tail by a sphere two-point sum times the `m`-radius tail.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators ENNReal

def radiusSplitEvent (d : ℕ) (x : Cubic d) (n m : ℕ) (y : Cubic d) :
    Set (EdgeConfiguration d) :=
  OpenWitnessDisjointOccurrence
    (connectionEventIn d (cubicMetricBallEdges d x n) x y)
    (radiusConnectionEvent d y m)

private theorem firstRadiusHitWalk_support_subset_ball {d n N : ℕ}
    {x : Cubic d} {omega : EdgeConfiguration d}
    (homega : omega ∈ radiusConnectionEvent d x N) (hnN : n ≤ N) :
    ∀ z ∈ (firstRadiusHitWalk homega hnN).support,
      z ∈ cubicMetricBall d x n := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  rcases hz with ⟨j, rfl, hj⟩
  let k := firstRadiusHitIndex homega hnN
  have hk := firstRadiusHitIndex_spec homega hnN
  have hjk : j ≤ k := by
    simpa [firstRadiusHitWalk, k, Nat.min_eq_left hk.1] using hj
  have hget : (firstRadiusHitWalk homega hnN).getVert j =
      (canonicalRadiusWitness homega).walk.getVert j := by
    simp [firstRadiusHitWalk, k, Nat.min_eq_right hjk]
  rw [hget, mem_cubicMetricBall_iff_l1Dist_le]
  rcases hjk.lt_or_eq with hjlt | rfl
  · apply Nat.le_of_lt
    apply lt_of_not_ge
    intro hge
    exact Nat.find_min (firstRadiusHit_exists homega hnN) hjlt ⟨by omega, hge⟩
  · exact (firstRadiusHit_dist_eq homega hnN).le

/-- Deterministic first-hit split behind the radius block inequality. -/
theorem radiusConnectionEvent_subset_biUnion_radiusSplitEvent
    {d n m : ℕ} {x : Cubic d} :
    radiusConnectionEvent d x (n + m) ⊆
      ⋃ y ∈ cubicMetricSphere d x n, radiusSplitEvent d x n m y := by
  intro omega homega
  let W := canonicalRadiusWitness homega
  have hnN : n ≤ n + m := Nat.le_add_right n m
  let k := firstRadiusHitIndex homega hnN
  let y := W.walk.getVert k
  let q := firstRadiusHitWalk homega hnN
  let r := W.walk.drop k
  have hydist : cubicL1Dist x y = n := by
    simpa [W, y, k] using firstRadiusHit_dist_eq homega hnN
  have hysphere : y ∈ cubicMetricSphere d x n := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    exact hydist
  have hqopen : walkIsOpen omega q :=
    walkIsOpen_take W.walk W.isOpen k
  have hropen : walkIsOpen omega r :=
    walkIsOpen_drop W.walk W.isOpen k
  have hradius : m ≤ cubicL1Dist y W.endpoint := by
    have htriangle := cubicL1Dist_triangle x y W.endpoint
    have hendpoint := mem_cubicMetricSphere_iff_l1Dist_eq.mp W.sphere_mem
    rw [hydist, hendpoint] at htriangle
    omega
  let H := walkEdgeFinset q
  let K := walkEdgeFinset r
  have hHK : Disjoint H K := by
    rw [Finset.disjoint_left]
    intro e heH heK
    have heq : (e : Sym2 (Cubic d)) ∈ q.edges :=
      (mem_walkEdgeFinset_iff q e).mp heH
    have her : (e : Sym2 (Cubic d)) ∈ r.edges :=
      (mem_walkEdgeFinset_iff r e).mp heK
    change (e : Sym2 (Cubic d)) ∈ (firstRadiusHitWalk homega hnN).edges at heq
    change (e : Sym2 (Cubic d)) ∈ (W.walk.drop k).edges at her
    rw [firstRadiusHitWalk, SimpleGraph.Walk.edges_take] at heq
    rw [SimpleGraph.Walk.edges_drop] at her
    exact (List.disjoint_take_drop W.isPath.isTrail.edges_nodup (le_refl k)) heq her
  have hHsub : (H : Set (CubicEdge d)) ⊆ omega := by
    intro e he
    exact hqopen e.1 ((mem_walkEdgeFinset_iff q e).mp he)
  have hKsub : (K : Set (CubicEdge d)) ⊆ omega := by
    intro e he
    exact hropen e.1 ((mem_walkEdgeFinset_iff r e).mp he)
  have hHconn : (H : Set (CubicEdge d)) ∈
      connectionEventIn d (cubicMetricBallEdges d x n) x y := by
    refine ⟨q, walkIsOpen_walkEdgeFinset q, ?_⟩
    apply walkEdgeFinset_subset_cubicMetricBallEdges_of_support q
    exact firstRadiusHitWalk_support_subset_ball homega hnN
  have hKradius : (K : Set (CubicEdge d)) ∈ radiusConnectionEvent d y m := by
    exact exists_open_walk_to_cubicMetricSphere_in_ball r
      (walkIsOpen_walkEdgeFinset r) hradius
  apply Set.mem_iUnion₂.mpr
  exact ⟨y, hysphere, H, K, hHK, hHsub, hKsub, hHconn, hKradius⟩

/-- The BK block inequality for a radius event, before choosing a good sphere. -/
theorem radiusTail_add_le_sphereConnectionSum_mul
    (d : ℕ) (p : I) (n m : ℕ) :
    radiusTail d p (n + m) ≤
      (∑ y ∈ cubicMetricSphere d cubicOrigin n,
        (bernoulliBondMeasure d p).real
          (connectionEvent d cubicOrigin y)) * radiusTail d p m := by
  let mu := bernoulliBondMeasure d p
  have hcover := radiusConnectionEvent_subset_biUnion_radiusSplitEvent
    (d := d) (x := cubicOrigin) (n := n) (m := m)
  have hunion : mu.real (radiusConnectionEvent d cubicOrigin (n + m)) ≤
      ∑ y ∈ cubicMetricSphere d cubicOrigin n,
        mu.real (radiusSplitEvent d cubicOrigin n m y) := by
    exact (measureReal_mono hcover (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le (cubicMetricSphere d cubicOrigin n)
        (radiusSplitEvent d cubicOrigin n m))
  calc
    radiusTail d p (n + m) ≤
        ∑ y ∈ cubicMetricSphere d cubicOrigin n,
          mu.real (radiusSplitEvent d cubicOrigin n m y) := hunion
    _ ≤ ∑ y ∈ cubicMetricSphere d cubicOrigin n,
        (mu.real (connectionEvent d cubicOrigin y) * radiusTail d p m) := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        mu.real (radiusSplitEvent d cubicOrigin n m y) ≤
            mu.real (connectionEventIn d
              (cubicMetricBallEdges d cubicOrigin n) cubicOrigin y) *
              mu.real (radiusConnectionEvent d y m) :=
          bernoulliBondMeasure_real_disjointOccurrence_le_mul p
            (isIncreasingEvent_connectionEventIn d
              (cubicMetricBallEdges d cubicOrigin n) cubicOrigin y)
            (isIncreasingEvent_radiusConnectionEvent d y m)
            (dependsOn_connectionEventIn d
              (cubicMetricBallEdges d cubicOrigin n) cubicOrigin y)
            (dependsOn_radiusConnectionEvent d y m)
        _ ≤ mu.real (connectionEvent d cubicOrigin y) *
              mu.real (radiusConnectionEvent d y m) := by
          apply mul_le_mul_of_nonneg_right
          · exact measureReal_mono (μ := mu)
              (connectionEventIn_subset d
                (cubicMetricBallEdges d cubicOrigin n) cubicOrigin y)
              (measure_ne_top mu _)
          · exact measureReal_nonneg
        _ = mu.real (connectionEvent d cubicOrigin y) * radiusTail d p m := by
          rw [bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail]
    _ = (∑ y ∈ cubicMetricSphere d cubicOrigin n,
        mu.real (connectionEvent d cubicOrigin y)) * radiusTail d p m := by
      rw [Finset.sum_mul]

/-! ### Consequences of finite susceptibility -/

/-- The total two-point mass on a metric sphere. -/
noncomputable def radiusSphereConnectionMass (d : ℕ) (p : I) (n : ℕ) : ℝ≥0∞ :=
  ∑ y ∈ cubicMetricSphere d cubicOrigin n,
    bernoulliBondMeasure d p (connectionEvent d cubicOrigin y)

/-- Every cubic vertex belongs to its unique metric sphere. -/
def cubicSphereSigmaEquiv (d : ℕ) :
    (Σ n : ℕ, {y : Cubic d // y ∈ cubicMetricSphere d cubicOrigin n}) ≃ Cubic d where
  toFun q := q.2.1
  invFun y := ⟨cubicL1Dist cubicOrigin y, ⟨y, by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]⟩⟩
  left_inv := by
    rintro ⟨n, y, hy⟩
    have hn : cubicL1Dist cubicOrigin y = n :=
      mem_cubicMetricSphere_iff_l1Dist_eq.mp hy
    subst n
    rfl
  right_inv := by
    intro y
    rfl

/-- Grouping the susceptibility two-point expansion by metric spheres loses no
mass. -/
theorem tsum_radiusSphereConnectionMass (d : ℕ) (p : I) :
    ∑' n : ℕ, radiusSphereConnectionMass d p n = susceptibility d p := by
  rw [susceptibility_eq_tsum_connection]
  calc
    ∑' n : ℕ, radiusSphereConnectionMass d p n =
        ∑' n : ℕ, ∑' y : {y : Cubic d //
          y ∈ cubicMetricSphere d cubicOrigin n},
            bernoulliBondMeasure d p (connectionEvent d cubicOrigin y.1) := by
      apply tsum_congr
      intro n
      simpa [radiusSphereConnectionMass] using
        (Finset.tsum_subtype (cubicMetricSphere d cubicOrigin n)
          (fun y ↦ bernoulliBondMeasure d p
            (connectionEvent d cubicOrigin y))).symm
    _ = ∑' q : (Σ n : ℕ, {y : Cubic d //
          y ∈ cubicMetricSphere d cubicOrigin n}),
        bernoulliBondMeasure d p (connectionEvent d cubicOrigin q.2.1) := by
      exact (ENNReal.tsum_sigma fun n
        (y : {y : Cubic d // y ∈ cubicMetricSphere d cubicOrigin n}) ↦
          bernoulliBondMeasure d p (connectionEvent d cubicOrigin y.1)).symm
    _ = ∑' y : Cubic d,
        bernoulliBondMeasure d p (connectionEvent d cubicOrigin y) := by
      simpa using (Equiv.tsum_eq (cubicSphereSigmaEquiv d)
        (fun y : Cubic d ↦ bernoulliBondMeasure d p
          (connectionEvent d cubicOrigin y)))

theorem radiusSphereConnectionMass_tendsto_zero_of_susceptibility_lt_top
    {d : ℕ} {p : I} (hchi : susceptibility d p < ⊤) :
    Filter.Tendsto (radiusSphereConnectionMass d p) Filter.atTop (nhds 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [tsum_radiusSphereConnectionMass]
  exact ne_of_lt hchi

theorem radiusSphereConnectionMass_toReal (d : ℕ) (p : I) (n : ℕ) :
    (radiusSphereConnectionMass d p n).toReal =
      ∑ y ∈ cubicMetricSphere d cubicOrigin n,
        (bernoulliBondMeasure d p).real
          (connectionEvent d cubicOrigin y) := by
  unfold radiusSphereConnectionMass
  rw [ENNReal.toReal_sum]
  · rfl
  · intro y hy
    exact measure_ne_top _ _

/-- Finite susceptibility yields a block scale whose crossing multiplier is at
most one half. -/
theorem exists_radius_block_contraction_of_susceptibility_lt_top
    {d : ℕ} {p : I} (hchi : susceptibility d p < ⊤) :
    ∃ R : ℕ, 0 < R ∧
      ∀ m : ℕ, radiusTail d p (R + m) ≤ (1 / 2 : ℝ) * radiusTail d p m := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      radiusSphereConnectionMass d p n < (1 / 2 : ℝ≥0∞) :=
    (tendsto_order.1
      (radiusSphereConnectionMass_tendsto_zero_of_susceptibility_lt_top hchi)).2
      _ (by norm_num)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hevent
  let R' := max R 1
  have hmass : radiusSphereConnectionMass d p R' < (1 / 2 : ℝ≥0∞) :=
    hR R' (le_max_left _ _)
  have hmassReal :
      ∑ y ∈ cubicMetricSphere d cubicOrigin R',
          (bernoulliBondMeasure d p).real
            (connectionEvent d cubicOrigin y) < (1 / 2 : ℝ) := by
    rw [← radiusSphereConnectionMass_toReal]
    have hreal := (ENNReal.toReal_lt_toReal
      (ne_of_lt (hmass.trans (by norm_num))) (by norm_num)).2 hmass
    norm_num at hreal ⊢
    exact hreal
  refine ⟨R', lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun m ↦ ?_⟩
  exact (radiusTail_add_le_sphereConnectionSum_mul d p R' m).trans
    (mul_le_mul_of_nonneg_right hmassReal.le measureReal_nonneg)

/-- Iterating the contracting block gives geometric decay on the block
subsequence. -/
theorem radiusTail_mul_block_le_pow_half_of_susceptibility_lt_top
    {d : ℕ} {p : I} (hchi : susceptibility d p < ⊤) :
    ∃ R : ℕ, 0 < R ∧ ∀ k : ℕ,
      radiusTail d p (k * R) ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨R, hR0, hcontract⟩ :=
    exists_radius_block_contraction_of_susceptibility_lt_top hchi
  refine ⟨R, hR0, ?_⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, add_comm]
      calc
        radiusTail d p (R + k * R) ≤
            (1 / 2 : ℝ) * radiusTail d p (k * R) := hcontract (k * R)
        _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by gcongr
        _ = (1 / 2 : ℝ) ^ (k + 1) := by ring

theorem closed_ballEdges_subset_compl_radiusConnectionEvent_one
    (d : ℕ) (x : Cubic d) :
    closedEdgeSetEvent d (cubicMetricBallEdges d x 1) ⊆
      (radiusConnectionEvent d x 1)ᶜ := by
  intro omega hclosed hA
  rcases hA with ⟨y, hy, w, hwopen, hwsub⟩
  cases w with
  | nil =>
      have hdist := mem_cubicMetricSphere_iff_l1Dist_eq.mp hy
      simp at hdist
  | @cons _ z _ hxz w =>
      let e : CubicEdge d :=
        ⟨s(x, z), by rw [SimpleGraph.mem_edgeSet]; exact hxz⟩
      have hewalk : (e : Sym2 (Cubic d)) ∈
          (SimpleGraph.Walk.cons hxz w).edges := by simp [e]
      have heball : e ∈ cubicMetricBallEdges d x 1 :=
        hwsub ((mem_walkEdgeFinset_iff _ e).mpr hewalk)
      have heopen : e ∈ omega := hwopen e.1 hewalk
      exact Set.disjoint_left.1 hclosed heball heopen

theorem radiusTail_one_lt_one {d : ℕ} {p : I} (hp1 : (p : ℝ) < 1) :
    radiusTail d p 1 < 1 := by
  let mu := bernoulliBondMeasure d p
  let E := cubicMetricBallEdges d cubicOrigin 1
  have hclosedPos : 0 < mu.real (closedEdgeSetEvent d E) := by
    rw [bernoulliBondMeasure_real_closedEdgeSetEvent]
    exact pow_pos (sub_pos.mpr hp1) E.card
  have hle : mu.real (closedEdgeSetEvent d E) ≤
      mu.real (radiusConnectionEvent d cubicOrigin 1)ᶜ :=
    measureReal_mono (μ := mu)
      (closed_ballEdges_subset_compl_radiusConnectionEvent_one d cubicOrigin)
      (measure_ne_top mu _)
  rw [measureReal_compl (measurableSet_radiusConnectionEvent d cubicOrigin 1),
    probReal_univ] at hle
  change radiusTail d p 1 < 1
  change mu.real (radiusConnectionEvent d cubicOrigin 1) < 1
  linarith

/-- Interpolate geometric decay on a positive block scale to a unit-prefactor
exponential bound at every radius.  This is the classical block argument used
after finite susceptibility is known. -/
theorem radiusTail_exponential_decay_of_susceptibility_lt_top
    {d : ℕ} {p : I} (hp1 : (p : ℝ) < 1)
    (hchi : susceptibility d p < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      radiusTail d p n ≤ Real.exp (-c * n) := by
  let g : ℕ → ℝ := radiusTail d p
  have hg0 : g 0 = 1 := radiusTail_zero d p
  have hg1lt : g 1 < 1 := radiusTail_one_lt_one hp1
  have hg_nonneg : ∀ n, 0 ≤ g n := fun _ ↦ measureReal_nonneg
  by_cases hg1zero : g 1 = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro n
    rcases n with _ | n
    · simp [g, hg0]
    · have hle : g (n + 1) ≤ g 1 :=
        radiusTail_antitone d p (by omega)
      rw [hg1zero] at hle
      exact hle.trans (Real.exp_pos _).le
  · have hg1pos : 0 < g 1 := lt_of_le_of_ne (hg_nonneg 1) (Ne.symm hg1zero)
    obtain ⟨R, hR0, hblock⟩ :=
      radiusTail_mul_block_le_pow_half_of_susceptibility_lt_top hchi
    let c₁ : ℝ := Real.log 2 / (2 * R)
    let c₂ : ℝ := -Real.log (g 1) / R
    let c : ℝ := min c₁ c₂
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR0
    have hc₁ : 0 < c₁ := by
      dsimp only [c₁]
      exact div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hRreal)
    have hlogg : Real.log (g 1) < 0 := Real.log_neg hg1pos hg1lt
    have hc₂ : 0 < c₂ := by
      dsimp only [c₂]
      exact div_pos (neg_pos.mpr hlogg) hRreal
    have hc : 0 < c := lt_min hc₁ hc₂
    refine ⟨c, hc, ?_⟩
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [g, hg0]
    by_cases hnR : n < R
    · have hgn : g n ≤ g 1 :=
        radiusTail_antitone d p (Nat.one_le_iff_ne_zero.mpr hn0)
      have hc_le : c ≤ c₂ := min_le_right _ _
      have hnRreal : (n : ℝ) ≤ R := by exact_mod_cast hnR.le
      have hcn : c * n ≤ -Real.log (g 1) := by
        have hc0 : 0 ≤ c := hc.le
        have hn0real : (0 : ℝ) ≤ n := by positivity
        calc
          c * (n : ℝ) ≤ c * R :=
            mul_le_mul_of_nonneg_left hnRreal hc0
          _ ≤ c₂ * R := mul_le_mul_of_nonneg_right hc_le hRreal.le
          _ = -Real.log (g 1) := by
            dsimp only [c₂]
            field_simp [hRreal.ne']
      calc
        g n ≤ g 1 := hgn
        _ = Real.exp (Real.log (g 1)) := (Real.exp_log hg1pos).symm
        _ ≤ Real.exp (-c * n) := by
          apply Real.exp_le_exp.mpr
          linarith
    · have hRn : R ≤ n := Nat.le_of_not_gt hnR
      let k := n / R
      have hkpos : 0 < k := Nat.div_pos hRn hR0
      have hkR : k * R ≤ n := Nat.div_mul_le_self n R
      have hgn : g n ≤ g (k * R) := radiusTail_antitone d p hkR
      have hgeom : g (k * R) ≤ (1 / 2 : ℝ) ^ k := hblock k
      have hmod : n % R < R := Nat.mod_lt n hR0
      have hdecomp : k * R + n % R = n := by
        simpa [k, Nat.mul_comm] using Nat.div_add_mod n R
      have hRle : R ≤ k * R := by
        simpa using Nat.mul_le_mul_right R (Nat.succ_le_iff.mpr hkpos)
      have hnTwo : n ≤ 2 * k * R := by
        calc
          n ≤ k * R + R := by omega
          _ ≤ k * R + k * R := Nat.add_le_add_left hRle _
          _ = 2 * k * R := by ring
      have hnTwoReal : (n : ℝ) ≤ 2 * k * R := by exact_mod_cast hnTwo
      have hc_le : c ≤ c₁ := min_le_left _ _
      have hck : c * n ≤ Real.log 2 * k := by
        have hc0 : 0 ≤ c := hc.le
        calc
          c * (n : ℝ) ≤ c * (2 * k * R) :=
            mul_le_mul_of_nonneg_left hnTwoReal hc0
          _ ≤ c₁ * (2 * k * R) := by
            apply mul_le_mul_of_nonneg_right hc_le
            positivity
          _ = Real.log 2 * k := by
            dsimp only [c₁]
            field_simp [hRreal.ne']
      have hhalfExp : (1 / 2 : ℝ) ^ k =
          Real.exp (-(Real.log 2) * k) := by
        calc
          (1 / 2 : ℝ) ^ k = (Real.exp (-Real.log 2)) ^ k := by
            congr 1
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            norm_num
          _ = Real.exp ((k : ℝ) * (-Real.log 2)) := by
            rw [← Real.exp_nat_mul]
          _ = Real.exp (-(Real.log 2) * k) := by
            congr 1
            ring
      calc
        g n ≤ g (k * R) := hgn
        _ ≤ (1 / 2 : ℝ) ^ k := hgeom
        _ = Real.exp (-(Real.log 2) * k) := hhalfExp
        _ ≤ Real.exp (-c * n) := by
          apply Real.exp_le_exp.mpr
          linarith

#print axioms radiusTail_mul_block_le_pow_half_of_susceptibility_lt_top
#print axioms radiusTail_exponential_decay_of_susceptibility_lt_top

#print axioms radiusTail_add_le_sphereConnectionSum_mul

end Percolation
