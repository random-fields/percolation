import Percolation.Critical.BoxTrifurcation
import Percolation.Critical.StaticCoalescence
import Percolation.Critical.StaticLargeCrossing

/-!
# Crossing boxes from uniqueness of the infinite cluster

This file develops the qualitative coalescence input in Grimmett's proof of Theorem 8.97.
Unlike the quantitative Chapter 7 estimates, the argument uses only almost-sure uniqueness.
-/

namespace Percolation

open Filter MeasureTheory
open scoped unitInterval

private theorem connectionEvent_trans_mem_supercritical
    {d : ℕ} {omega : EdgeConfiguration d} {x y z : Cubic d}
    (hxy : omega ∈ connectionEvent d x y) (hyz : omega ∈ connectionEvent d y z) :
    omega ∈ connectionEvent d x z := by
  obtain ⟨p, hp⟩ := hxy
  obtain ⟨q, hq⟩ := hyz
  exact ⟨p.append q, walkIsOpen_append hp hq⟩

private theorem connectionEvent_symm_mem_supercritical
    {d : ℕ} {omega : EdgeConfiguration d} {x y : Cubic d}
    (hxy : omega ∈ connectionEvent d x y) : omega ∈ connectionEvent d y x := by
  obtain ⟨p, hp⟩ := hxy
  exact ⟨p.reverse, walkIsOpen_reverse hp⟩

private theorem connectionEventIn_symm_mem_supercritical
    {d : ℕ} {E : Finset (CubicEdge d)} {omega : EdgeConfiguration d} {x y : Cubic d}
    (hxy : omega ∈ connectionEventIn d E x y) :
    omega ∈ connectionEventIn d E y x := by
  obtain ⟨w, hwOpen, hwEdges⟩ := hxy
  refine ⟨w.reverse, walkIsOpen_reverse hwOpen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  have he' : (e : Sym2 (Cubic d)) ∈ w.edges := by simpa using he
  exact hwEdges ((mem_walkEdgeFinset_iff w e).mpr he')

private theorem connectionEventIn_trans_mem_supercritical
    {d : ℕ} {E : Finset (CubicEdge d)} {omega : EdgeConfiguration d} {x y z : Cubic d}
    (hxy : omega ∈ connectionEventIn d E x y)
    (hyz : omega ∈ connectionEventIn d E y z) :
    omega ∈ connectionEventIn d E x z := by
  obtain ⟨p, hpOpen, hpEdges⟩ := hxy
  obtain ⟨q, hqOpen, hqEdges⟩ := hyz
  refine ⟨p.append q, walkIsOpen_append hpOpen hqOpen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append, List.mem_append] at he
  exact he.elim
    (fun hep ↦ hpEdges ((mem_walkEdgeFinset_iff p e).mpr hep))
    (fun heq ↦ hqEdges ((mem_walkEdgeFinset_iff q e).mpr heq))

/-- The event `LR(n)` from Grimmett's Theorem 8.97: an open path inside `B(n)` joins the
negative and positive faces perpendicular to coordinate `i`. -/
def leftRightCrossingEvent (d n : ℕ) (i : Fin d) : Set (EdgeConfiguration d) :=
  ⋃ x ∈ cubicBoxFace d cubicOrigin n i false,
    ⋃ y ∈ cubicBoxFace d cubicOrigin n i true,
      connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y

theorem measurableSet_leftRightCrossingEvent (d n : ℕ) (i : Fin d) :
    MeasurableSet (leftRightCrossingEvent d n i) := by
  apply (cubicBoxFace d cubicOrigin n i false).measurableSet_biUnion
  intro x hx
  apply (cubicBoxFace d cubicOrigin n i true).measurableSet_biUnion
  intro y hy
  exact (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y).measurableSet

theorem mem_leftRightCrossingEvent_iff
    {d n : ℕ} {i : Fin d} {omega : EdgeConfiguration d} :
    omega ∈ leftRightCrossingEvent d n i ↔
      ∃ x ∈ cubicBoxFace d cubicOrigin n i false,
        ∃ y ∈ cubicBoxFace d cubicOrigin n i true,
          omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨hxFace, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hyFace, hxy⟩ := Set.mem_iUnion.mp hy
    exact ⟨x, hxFace, y, hyFace, hxy⟩
  · rintro ⟨x, hxFace, y, hyFace, hxy⟩
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxFace,
      Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyFace, hxy⟩⟩⟩⟩

/-- Two specified vertices lie in infinite clusters but are not connected inside the box of
radius `N`. -/
def infinitePairNotConnectedInBoxEvent (d N : ℕ) (x y : Cubic d) :
    Set (EdgeConfiguration d) :=
  infiniteClusterVertexEvent d x ∩ infiniteClusterVertexEvent d y ∩
    (connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y)ᶜ

theorem measurableSet_infinitePairNotConnectedInBoxEvent (d N : ℕ) (x y : Cubic d) :
    MeasurableSet (infinitePairNotConnectedInBoxEvent d N x y) :=
  ((measurableSet_infiniteClusterVertexEvent d x).inter
    (measurableSet_infiniteClusterVertexEvent d y)).inter
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y).measurableSet.compl

theorem infinitePairNotConnectedInBoxEvent_antitone (d : ℕ) (x y : Cubic d) :
    Antitone fun N ↦ infinitePairNotConnectedInBoxEvent d N x y := by
  intro m n hmn omega homega
  refine ⟨homega.1, ?_⟩
  intro hconn
  exact homega.2 <| connectionEventIn_mono (cubicBoxEdges_mono_radius hmn) x y hconn

theorem iInter_infinitePairNotConnectedInBoxEvent_subset_uniqueness_compl
    (d : ℕ) (x y : Cubic d) :
    (⋂ N : ℕ, infinitePairNotConnectedInBoxEvent d N x y) ⊆
      (exactlyOneInfiniteOpenClusterEvent d)ᶜ := by
  intro omega homega hunique
  have hzero := Set.mem_iInter.mp homega 0
  obtain ⟨z, hzInf, hz⟩ := mem_exactlyOneInfiniteOpenClusterEvent_iff.mp hunique
  have hxy : omega ∈ connectionEvent d x y :=
    connectionEvent_trans_mem_supercritical
      (connectionEvent_symm_mem_supercritical (hz x hzero.1.1))
      (hz y hzero.1.2)
  obtain ⟨w, hwOpen⟩ := hxy
  let E := walkEdgeFinset w
  let N := cubicEdgeSetRadius E
  have hconn : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y :=
    ⟨w, hwOpen, cubicEdgeSet_subset_cubicBoxEdges_radius E⟩
  exact (Set.mem_iInter.mp homega N).2 hconn

/-- Under almost-sure uniqueness, the probability that two fixed infinite-cluster vertices have
not yet coalesced inside `B(N)` tends to zero. -/
theorem infinitePairNotConnectedInBox_probability_tendsto_zero
    {d : ℕ} (hd : 1 ≤ d) (p : I) (htheta : 0 < theta d p) (x y : Cubic d) :
    Tendsto (fun N ↦ (bernoulliBondMeasure d p).real
      (infinitePairNotConnectedInBoxEvent d N x y)) atTop (nhds 0) := by
  let mu := bernoulliBondMeasure d p
  let A := fun N ↦ infinitePairNotConnectedInBoxEvent d N x y
  have hmeasure : Tendsto (fun N ↦ mu (A N)) atTop (nhds (mu (⋂ N, A N))) :=
    tendsto_measure_iInter_atTop
      (fun N ↦ (measurableSet_infinitePairNotConnectedInBoxEvent d N x y).nullMeasurableSet)
      (infinitePairNotConnectedInBoxEvent_antitone d x y) ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun N ↦ mu.real (A N)) atTop (nhds (mu.real (⋂ N, A N))) := by
    simpa [Measure.real] using (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure
  have hunique : mu.real (exactlyOneInfiniteOpenClusterEvent d) = 1 :=
    unique_infiniteOpenCluster_almostSure_of_theta_pos hd p htheta
  have hcompl : mu.real (exactlyOneInfiniteOpenClusterEvent d)ᶜ = 0 := by
    rw [probReal_compl_eq_one_sub (measurableSet_exactlyOneInfiniteOpenClusterEvent d), hunique]
    norm_num
  have hinter : mu.real (⋂ N, A N) = 0 := le_antisymm
    ((measureReal_mono
      (iInter_infinitePairNotConnectedInBoxEvent_subset_uniqueness_compl d x y)).trans_eq hcompl)
    measureReal_nonneg
  simpa [A, mu, hinter] using hreal

theorem infiniteClusterCoalescenceEvent_compl_subset_iUnion_pairFailure
    (d m N : ℕ) :
    (infiniteClusterCoalescenceEvent d m N)ᶜ ⊆
      ⋃ x ∈ cubicMetricBox d cubicOrigin m,
        ⋃ y ∈ cubicMetricBox d cubicOrigin m,
          infinitePairNotConnectedInBoxEvent d N x y := by
  intro omega homega
  by_contra hnot
  apply homega
  rw [mem_infiniteClusterCoalescenceEvent_iff]
  intro x hx y hy hxInf hyInf
  by_contra hconn
  apply hnot
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
    Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ⟨⟨hxInf, hyInf⟩, hconn⟩⟩⟩⟩⟩

theorem bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_pairFailureSum
    (d m N : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real (infiniteClusterCoalescenceEvent d m N)ᶜ ≤
      ∑ x ∈ cubicMetricBox d cubicOrigin m,
        ∑ y ∈ cubicMetricBox d cubicOrigin m,
          (bernoulliBondMeasure d p).real (infinitePairNotConnectedInBoxEvent d N x y) := by
  let mu := bernoulliBondMeasure d p
  calc
    mu.real (infiniteClusterCoalescenceEvent d m N)ᶜ ≤
        mu.real (⋃ x ∈ cubicMetricBox d cubicOrigin m,
          ⋃ y ∈ cubicMetricBox d cubicOrigin m,
            infinitePairNotConnectedInBoxEvent d N x y) :=
      measureReal_mono
        (h₂ := measure_ne_top _ _)
        (infiniteClusterCoalescenceEvent_compl_subset_iUnion_pairFailure d m N)
    _ ≤ ∑ x ∈ cubicMetricBox d cubicOrigin m,
        mu.real (⋃ y ∈ cubicMetricBox d cubicOrigin m,
          infinitePairNotConnectedInBoxEvent d N x y) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ cubicMetricBox d cubicOrigin m,
        ∑ y ∈ cubicMetricBox d cubicOrigin m,
          mu.real (infinitePairNotConnectedInBoxEvent d N x y) := by
      exact Finset.sum_le_sum fun x _ ↦ measureReal_biUnion_finset_le _ _

/-- For a fixed inner box, all of its infinite-cluster vertices coalesce inside `B(N)` with
probability tending to one. -/
theorem infiniteClusterCoalescenceEvent_probability_tendsto_one_of_theta_pos
    {d : ℕ} (hd : 1 ≤ d) (p : I) (htheta : 0 < theta d p) (m : ℕ) :
    Tendsto (fun N ↦ (bernoulliBondMeasure d p).real
      (infiniteClusterCoalescenceEvent d m N)) atTop (nhds 1) := by
  let mu := bernoulliBondMeasure d p
  have hfailure : Tendsto (fun N ↦ mu.real (infiniteClusterCoalescenceEvent d m N)ᶜ)
      atTop (nhds 0) := by
    have hpair : ∀ x ∈ cubicMetricBox d cubicOrigin m,
        ∀ y ∈ cubicMetricBox d cubicOrigin m,
          Tendsto (fun N ↦ mu.real (infinitePairNotConnectedInBoxEvent d N x y))
            atTop (nhds 0) := by
      intro x hx y hy
      exact infinitePairNotConnectedInBox_probability_tendsto_zero hd p htheta x y
    have hsum : Tendsto (fun N ↦ ∑ x ∈ cubicMetricBox d cubicOrigin m,
        ∑ y ∈ cubicMetricBox d cubicOrigin m,
          mu.real (infinitePairNotConnectedInBoxEvent d N x y)) atTop (nhds 0) := by
      simpa using tendsto_finsetSum (cubicMetricBox d cubicOrigin m) fun x hx ↦
        tendsto_finsetSum (cubicMetricBox d cubicOrigin m) fun y hy ↦ hpair x hx y hy
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg)
      (Eventually.of_forall fun N ↦ ?_) hsum
    exact bernoulliBondMeasure_real_infiniteClusterCoalescenceEvent_compl_le_pairFailureSum
      d m N p
  have hEq : (fun N ↦ mu.real (infiniteClusterCoalescenceEvent d m N)) =
      fun N ↦ 1 - mu.real (infiniteClusterCoalescenceEvent d m N)ᶜ := by
    funext N
    rw [probReal_compl_eq_one_sub (measurableSet_infiniteClusterCoalescenceEvent d m N)]
    linarith
  rw [hEq]
  simpa [mu] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfailure

/-- If the inner infinite cluster reaches the two opposed faces and its two witnessing vertices
coalesce inside the outer box, then that outer box has a left-right crossing. -/
theorem reachesOppositeFaces_inter_coalescence_subset_leftRightCrossingEvent
    {d m N : ℕ} (i : Fin d) :
    innerInfiniteClusterReachesFaceEvent d m N i false ∩
        innerInfiniteClusterReachesFaceEvent d m N i true ∩
          infiniteClusterCoalescenceEvent d m N ⊆
      leftRightCrossingEvent d N i := by
  intro omega homega
  obtain ⟨⟨hnegative, hpositive⟩, hcoalesce⟩ := homega
  obtain ⟨x, hxBox, hxInfinite, u, huFace, hxu⟩ :=
    mem_innerInfiniteClusterReachesFaceEvent_iff.mp hnegative
  obtain ⟨y, hyBox, hyInfinite, v, hvFace, hyv⟩ :=
    mem_innerInfiniteClusterReachesFaceEvent_iff.mp hpositive
  have hxy : omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y :=
    (mem_infiniteClusterCoalescenceEvent_iff.mp hcoalesce)
      x hxBox y hyBox hxInfinite hyInfinite
  refine mem_leftRightCrossingEvent_iff.mpr ⟨u, huFace, v, hvFace, ?_⟩
  exact connectionEventIn_trans_mem_supercritical
    (connectionEventIn_symm_mem_supercritical hxu)
    (connectionEventIn_trans_mem_supercritical hxy hyv)

theorem leftRightCrossingEvent_compl_subset_faceFailures_union_coalescenceFailure
    {d m N : ℕ} (i : Fin d) :
    (leftRightCrossingEvent d N i)ᶜ ⊆
      (innerInfiniteClusterReachesFaceEvent d m N i false)ᶜ ∪
        (innerInfiniteClusterReachesFaceEvent d m N i true)ᶜ ∪
          (infiniteClusterCoalescenceEvent d m N)ᶜ := by
  intro omega hcross
  by_cases hnegative : omega ∈ innerInfiniteClusterReachesFaceEvent d m N i false
  · by_cases hpositive : omega ∈ innerInfiniteClusterReachesFaceEvent d m N i true
    · by_cases hcoalesce : omega ∈ infiniteClusterCoalescenceEvent d m N
      · exact (hcross <|
          reachesOppositeFaces_inter_coalescence_subset_leftRightCrossingEvent i
            ⟨⟨hnegative, hpositive⟩, hcoalesce⟩).elim
      · exact Or.inr hcoalesce
    · exact Or.inl (Or.inr hpositive)
  · exact Or.inl (Or.inl hnegative)

/-- Once a fixed inner box is chosen sufficiently large, every signed outer face is reached
with uniformly high probability, for every larger outer radius. -/
theorem exists_innerRadius_for_faceFailure_lt
    {d : ℕ} (hd : 1 ≤ d) (p : I) (htheta : 0 < theta d p)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∀ N, m ≤ N → ∀ i : Fin d, ∀ positive : Bool,
      (bernoulliBondMeasure d p).real
          (innerInfiniteClusterReachesFaceEvent d m N i positive)ᶜ < epsilon := by
  let mu := bernoulliBondMeasure d p
  by_cases hepsilonOne : 1 < epsilon
  · exact ⟨0, fun N hmN i positive ↦
      (measureReal_le_one.trans_lt hepsilonOne)⟩
  have hinner := innerHasInfiniteClusterVertexEvent_probability_tendsto_one hd p htheta
  have hempty : Tendsto
      (fun m ↦ mu.real (innerHasInfiniteClusterVertexEvent d m)ᶜ)
      atTop (nhds 0) := by
    have hEq : (fun m ↦ mu.real (innerHasInfiniteClusterVertexEvent d m)ᶜ) =
        fun m ↦ 1 - mu.real (innerHasInfiniteClusterVertexEvent d m) := by
      funext m
      rw [probReal_compl_eq_one_sub (measurableSet_innerHasInfiniteClusterVertexEvent d m)]
    rw [hEq]
    simpa [mu] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinner
  have hpowerPositive : 0 < epsilon ^ (2 * d) := pow_pos hepsilon _
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.1 hempty
    (epsilon ^ (2 * d)) hpowerPositive
  refine ⟨m, fun N hmN i positive ↦ ?_⟩
  let b := 1 - mu.real
    (innerInfiniteClusterReachesFaceEvent d m N ⟨0, Nat.zero_lt_one.trans_le hd⟩ true)
  have hbNonnegative : 0 ≤ b := sub_nonneg.mpr measureReal_le_one
  have hbPower : b ^ (2 * d) ≤
      mu.real (innerHasInfiniteClusterVertexEvent d m)ᶜ := by
    simpa [b, mu] using
      one_sub_referenceFaceProbability_pow_le_innerHasInfiniteClusterVertexEvent_compl
        (Nat.zero_lt_one.trans_le hd) hmN p
  have hemptyLt : mu.real (innerHasInfiniteClusterVertexEvent d m)ᶜ <
      epsilon ^ (2 * d) := by
    have h := hm m le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  have hbLt : b < epsilon := by
    by_contra hnot
    have hepsilonB : epsilon ≤ b := le_of_not_gt hnot
    have hpow := pow_le_pow_left₀ hepsilon.le hepsilonB (2 * d)
    linarith
  rw [probReal_compl_eq_one_sub
    (measurableSet_innerInfiniteClusterReachesFaceEvent d m N i positive),
    innerInfiniteClusterReachesFaceProbability_eq_reference
      (Nat.zero_lt_one.trans_le hd) p (i, positive)]
  exact hbLt

/-- Grimmett's Theorem 8.97. If the percolation probability is positive, the probability of
an open left-right crossing of `B(n)` tends to one. -/
theorem leftRightCrossing_probability_tendsto_one
    {d : ℕ} (hd : 2 ≤ d) (p : I) (htheta : 0 < theta d p) (i : Fin d) :
    Tendsto (fun n ↦ (bernoulliBondMeasure d p).real
      (leftRightCrossingEvent d n i)) atTop (nhds 1) := by
  let mu := bernoulliBondMeasure d p
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  obtain ⟨m, hm⟩ := exists_innerRadius_for_faceFailure_lt
    (by omega : 1 ≤ d) p htheta (show 0 < epsilon / 4 by positivity)
  have hcoalesce := infiniteClusterCoalescenceEvent_probability_tendsto_one_of_theta_pos
    (by omega : 1 ≤ d) p htheta m
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hcoalesce (epsilon / 2)
    (show 0 < epsilon / 2 by positivity)
  refine ⟨max m N, fun n hn ↦ ?_⟩
  have hmn : m ≤ n := le_trans (le_max_left m N) hn
  have hNn : N ≤ n := le_trans (le_max_right m N) hn
  have hnegative := hm n hmn i false
  have hpositive := hm n hmn i true
  have hcoalesceDist := hN n hNn
  have hcoalesceFailure :
      mu.real (infiniteClusterCoalescenceEvent d m n)ᶜ < epsilon / 2 := by
    rw [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr measureReal_le_one)] at hcoalesceDist
    rw [probReal_compl_eq_one_sub
      (measurableSet_infiniteClusterCoalescenceEvent d m n)]
    linarith
  have hfailure : mu.real (leftRightCrossingEvent d n i)ᶜ < epsilon := by
    calc
      mu.real (leftRightCrossingEvent d n i)ᶜ ≤
          mu.real ((innerInfiniteClusterReachesFaceEvent d m n i false)ᶜ ∪
            (innerInfiniteClusterReachesFaceEvent d m n i true)ᶜ ∪
              (infiniteClusterCoalescenceEvent d m n)ᶜ) :=
        measureReal_mono
          (leftRightCrossingEvent_compl_subset_faceFailures_union_coalescenceFailure i)
      _ ≤ mu.real (innerInfiniteClusterReachesFaceEvent d m n i false)ᶜ +
            mu.real (innerInfiniteClusterReachesFaceEvent d m n i true)ᶜ +
              mu.real (infiniteClusterCoalescenceEvent d m n)ᶜ := by
        calc
          _ ≤ mu.real ((innerInfiniteClusterReachesFaceEvent d m n i false)ᶜ ∪
                  (innerInfiniteClusterReachesFaceEvent d m n i true)ᶜ) +
                mu.real (infiniteClusterCoalescenceEvent d m n)ᶜ :=
            measureReal_union_le _ _
          _ ≤ _ := add_le_add_left (measureReal_union_le _ _) _
      _ < epsilon := by linarith
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr measureReal_le_one)]
  rw [probReal_compl_eq_one_sub (measurableSet_leftRightCrossingEvent d n i)] at hfailure
  linarith

end Percolation
