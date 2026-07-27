import Percolation.Critical.Trifurcation

/-!
# Coordinate-box trifurcation counting

This file gives the coordinate-box version of Grimmett's Burton--Keane surface-counting
argument.  Coordinate boxes have exact volume and an `O(n^(d-1))` surface bound, so this is the
form used in the final probability contradiction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval

/-- A nearest-neighbor walk which starts weakly inside and ends weakly outside a coordinate
box visits its surface.  The ambient walk may live in any subgraph of the cubic lattice. -/
theorem exists_mem_walk_support_cubicLInfDist_eq_of_le_of_ge
    {d n : ℕ} {G : SimpleGraph (Cubic d)} (hG : G ≤ cubicGraph d)
    {root u v : Cubic d} (w : G.Walk u v)
    (hu : cubicLInfDist root u ≤ n) (hv : n ≤ cubicLInfDist root v) :
    ∃ y ∈ w.support, cubicLInfDist root y = n := by
  induction w with
  | nil => exact ⟨_, by simp, le_antisymm hu hv⟩
  | @cons u₀ u₁ v₀ hu₀u₁ tail ih =>
      by_cases hlevel : cubicLInfDist root u₀ = n
      · exact ⟨u₀, by simp, hlevel⟩
      · have hlt : cubicLInfDist root u₀ < n := lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj u₀ u₁ := hG hu₀u₁
        obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom u₀ u₁).mp hadj
        have hu₁ : cubicLInfDist root u₁ ≤ n := by
          calc
            cubicLInfDist root u₁ ≤
                cubicLInfDist root u₀ + cubicLInfDist u₀ u₁ :=
              cubicLInfDist_triangle _ _ _
            _ ≤ cubicLInfDist root u₀ + 1 := by
              gcongr
              rw [ha]
              exact cubicLInfDist_stepFrom_le_one _ _
            _ ≤ n := by omega
        obtain ⟨y, hyTail, hyDist⟩ := ih hu₁ hv
        exact ⟨y, by simp [hyTail], hyDist⟩

/-- Vertices of a fixed open component on an origin-centered coordinate-box surface. -/
noncomputable def openComponentBoxSurface
    (d : ℕ) (omega : EdgeConfiguration d)
    (K : (cubicOpenGraph d omega).ConnectedComponent) (n : ℕ) : Finset (Cubic d) := by
  classical
  exact (cubicBoxSurface d cubicOrigin n).filter fun y ↦
    (cubicOpenGraph d omega).connectedComponentMk y = K

@[simp]
theorem mem_openComponentBoxSurface_iff
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {y : Cubic d} :
    y ∈ openComponentBoxSurface d omega K n ↔
      cubicLInfDist cubicOrigin y = n ∧
        (cubicOpenGraph d omega).connectedComponentMk y = K := by
  classical
  rw [openComponentBoxSurface, Finset.mem_filter, mem_cubicBoxSurface]

/-- Every infinite branch of an interior trifurcation reaches the common component boundary on
the outer coordinate-box surface. -/
theorem exists_openComponentBoxSurface_in_trifurcationBranch
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d}
    (hn : 1 ≤ n)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBox : cubicLInfDist cubicOrigin x ≤ n - 1)
    {C : ((cubicOpenGraph d omega).deleteIncidenceSet x).ConnectedComponent}
    (hC : C ∈ trifurcationBranchComponents (cubicOpenGraph d omega) x) :
    ∃ y ∈ openComponentBoxSurface d omega K n,
      ((cubicOpenGraph d omega).deleteIncidenceSet x).connectedComponentMk y = C := by
  classical
  let G := cubicOpenGraph d omega
  let H := G.deleteIncidenceSet x
  obtain ⟨u, hxu, huC⟩ :=
    exists_adjacent_of_mem_trifurcationBranchComponents hC
  have huBox : cubicLInfDist cubicOrigin u ≤ n := by
    have hadj : (cubicGraph d).Adj x u := (cubicOpenGraph_adj.mp hxu).choose
    obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom x u).mp hadj
    calc
      cubicLInfDist cubicOrigin u ≤
          cubicLInfDist cubicOrigin x + cubicLInfDist x u :=
        cubicLInfDist_triangle _ _ _
      _ ≤ cubicLInfDist cubicOrigin x + 1 := by
        gcongr
        rw [ha]
        exact cubicLInfDist_stepFrom_le_one _ _
      _ ≤ n := by omega
  have hnotSubset : ¬C.supp ⊆ (cubicMetricBox d cubicOrigin n : Set (Cubic d)) := by
    intro hsub
    exact (infinite_of_mem_trifurcationBranchComponents hC)
      ((cubicMetricBox d cubicOrigin n).finite_toSet.subset hsub)
  obtain ⟨v, hvC, hvOutside⟩ := Set.not_subset.mp hnotSubset
  have hvFar : n ≤ cubicLInfDist cubicOrigin v := by
    have hnotle : ¬cubicLInfDist cubicOrigin v ≤ n := by
      intro hle
      exact hvOutside (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
    omega
  have huv : H.Reachable u v := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact huC.trans ((C.mem_supp_iff v).mp hvC).symm
  obtain ⟨w⟩ := huv
  have hOpenLe : G ≤ cubicGraph d := by
    intro a b hab
    exact (cubicOpenGraph_adj.mp hab).choose
  have hHle : H ≤ cubicGraph d :=
    (SimpleGraph.deleteIncidenceSet_le G x).trans hOpenLe
  obtain ⟨y, hySupport, hyDist⟩ :=
    exists_mem_walk_support_cubicLInfDist_eq_of_le_of_ge hHle w huBox hvFar
  obtain ⟨q, _r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hySupport
  have huy : H.Reachable u y := ⟨q⟩
  have hyC : H.connectedComponentMk y = C :=
    (SimpleGraph.ConnectedComponent.sound huy).symm.trans huC
  have hxyG : G.Reachable x y := hxu.reachable.trans
    (huy.mono (SimpleGraph.deleteIncidenceSet_le G x))
  refine ⟨y, mem_openComponentBoxSurface_iff.mpr ⟨hyDist, ?_⟩, hyC⟩
  exact (SimpleGraph.ConnectedComponent.sound hxyG).symm.trans hxK

/-- Every vertex of the common box surface belongs to an infinite branch of an interior
trifurcation. -/
theorem openComponentBoxSurface_vertex_mem_trifurcationBranch
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x y : Cubic d}
    (hn : 1 ≤ n)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBox : cubicLInfDist cubicOrigin x ≤ n - 1)
    (hy : y ∈ openComponentBoxSurface d omega K n) :
    ((cubicOpenGraph d omega).deleteIncidenceSet x).connectedComponentMk y ∈
      trifurcationBranchComponents (cubicOpenGraph d omega) x := by
  have hyData := mem_openComponentBoxSurface_iff.mp hy
  have hxy : x ≠ y := by
    intro h
    subst y
    rw [hyData.1] at hxBox
    omega
  have hreach : (cubicOpenGraph d omega).Reachable x y := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact hxK.trans hyData.2.symm
  exact connectedComponentMk_mem_trifurcationBranchComponents_of_reachable_from
    hx hxy hreach

/-- Boundary partition induced by an interior trifurcation on a coordinate-box surface. -/
noncomputable def openBoxTrifurcationBoundaryPartition
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d}
    (hn : 1 ≤ n)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hxBox : cubicLInfDist cubicOrigin x ≤ n - 1) :
    ThreePartition (openComponentBoxSurface d omega K n) :=
  trifurcationBoundaryPartition (openComponentBoxSurface d omega K n) hx
    (fun _y _hy ↦ openComponentBoxSurface_vertex_mem_trifurcationBranch
      hn hx hxK hxBox _hy)
    (fun _C hC ↦ exists_openComponentBoxSurface_in_trifurcationBranch
      hn hxK hxBox hC)

/-- Boundary partitions of distinct interior trifurcations in one component are compatible. -/
theorem openBoxTrifurcationBoundaryPartition_compatible
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x z : Cubic d}
    (hn : 1 ≤ n) (hxz : x ≠ z)
    (hx : IsTrifurcationVertex (cubicOpenGraph d omega) x)
    (hz : IsTrifurcationVertex (cubicOpenGraph d omega) z)
    (hxK : (cubicOpenGraph d omega).connectedComponentMk x = K)
    (hzK : (cubicOpenGraph d omega).connectedComponentMk z = K)
    (hxBox : cubicLInfDist cubicOrigin x ≤ n - 1)
    (hzBox : cubicLInfDist cubicOrigin z ≤ n - 1) :
    (openBoxTrifurcationBoundaryPartition hn hx hxK hxBox).Compatible
      (openBoxTrifurcationBoundaryPartition hn hz hzK hzBox) := by
  let G := cubicOpenGraph d omega
  have hreachXZ : G.Reachable x z := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    exact hxK.trans hzK.symm
  have hzBranchX : (G.deleteIncidenceSet x).connectedComponentMk z ∈
      trifurcationBranchComponents G x :=
    connectedComponentMk_mem_trifurcationBranchComponents_of_reachable hxz hz hreachXZ
  have hxBranchZ : (G.deleteIncidenceSet z).connectedComponentMk x ∈
      trifurcationBranchComponents G z :=
    connectedComponentMk_mem_trifurcationBranchComponents_of_reachable
      hxz.symm hx hreachXZ.symm
  exact trifurcationBoundaryPartition_compatible hxz
    (openComponentBoxSurface d omega K n) hx hz
    (fun y hy ↦ openComponentBoxSurface_vertex_mem_trifurcationBranch
      hn hx hxK hxBox hy)
    (fun C hC ↦ exists_openComponentBoxSurface_in_trifurcationBranch
      hn hxK hxBox hC)
    (fun y hy ↦ openComponentBoxSurface_vertex_mem_trifurcationBranch
      hn hz hzK hzBox hy)
    (fun C hC ↦ exists_openComponentBoxSurface_in_trifurcationBranch
      hn hzK hzBox hC)
    hzBranchX hxBranchZ

/-- Interior trifurcations belonging to one fixed open component of a coordinate box. -/
noncomputable def openTrifurcationsInComponentBox
    (d : ℕ) (omega : EdgeConfiguration d)
    (K : (cubicOpenGraph d omega).ConnectedComponent) (n : ℕ) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBox d cubicOrigin (n - 1)).filter fun x ↦
    IsTrifurcationVertex (cubicOpenGraph d omega) x ∧
      (cubicOpenGraph d omega).connectedComponentMk x = K

@[simp]
theorem mem_openTrifurcationsInComponentBox_iff
    {d n : ℕ} {omega : EdgeConfiguration d}
    {K : (cubicOpenGraph d omega).ConnectedComponent} {x : Cubic d} :
    x ∈ openTrifurcationsInComponentBox d omega K n ↔
      cubicLInfDist cubicOrigin x ≤ n - 1 ∧
        IsTrifurcationVertex (cubicOpenGraph d omega) x ∧
          (cubicOpenGraph d omega).connectedComponentMk x = K := by
  classical
  rw [openTrifurcationsInComponentBox, Finset.mem_filter,
    mem_cubicMetricBox_iff_lInfDist_le]

/-- Coordinate-box form of equation (8.6): a fixed component has at most its number of
surface vertices minus two interior trifurcations. -/
theorem openTrifurcationsInComponentBox_card_le
    {d n : ℕ} {omega : EdgeConfiguration d}
    (K : (cubicOpenGraph d omega).ConnectedComponent) (hn : 1 ≤ n) :
    (openTrifurcationsInComponentBox d omega K n).card ≤
      (openComponentBoxSurface d omega K n).card - 2 := by
  classical
  let T := openTrifurcationsInComponentBox d omega K n
  let Y := openComponentBoxSurface d omega K n
  let part : {x // x ∈ T} → ThreePartition Y := fun x ↦
    openBoxTrifurcationBoundaryPartition hn
      (mem_openTrifurcationsInComponentBox_iff.mp x.2).2.1
      (mem_openTrifurcationsInComponentBox_iff.mp x.2).2.2
      (mem_openTrifurcationsInComponentBox_iff.mp x.2).1
  have hpartCompat {x z : {x // x ∈ T}} (hxz : x ≠ z) :
      (part x).Compatible (part z) := by
    have hxData := mem_openTrifurcationsInComponentBox_iff.mp x.2
    have hzData := mem_openTrifurcationsInComponentBox_iff.mp z.2
    apply openBoxTrifurcationBoundaryPartition_compatible hn
      (fun h ↦ hxz (Subtype.ext h))
      hxData.2.1 hzData.2.1 hxData.2.2 hzData.2.2 hxData.1 hzData.1
  have hpartInj : Function.Injective part := by
    intro x z hEq
    by_contra hxz
    have hcompat := hpartCompat hxz
    rw [hEq] at hcompat
    exact ThreePartition.not_compatible_self _ hcompat
  let emb : {x // x ∈ T} ↪ ThreePartition Y := ⟨part, hpartInj⟩
  let F : Finset (ThreePartition Y) := T.attach.map emb
  have hFcard : F.card = T.card := by simp [F]
  have hFcompat : (F : Set (ThreePartition Y)).Pairwise ThreePartition.Compatible := by
    intro P hP Q hQ hPQ
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hP
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_map.mp hQ
    apply hpartCompat
    intro hxz
    apply hPQ
    exact congrArg emb hxz
  rw [← hFcard]
  exact ThreePartition.compatibleThreePartitions_card_le F hFcompat

/-- All open trifurcations in the inner coordinate box. -/
noncomputable def openTrifurcationsInBox
    (d : ℕ) (omega : EdgeConfiguration d) (n : ℕ) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBox d cubicOrigin (n - 1)).filter fun x ↦
    IsTrifurcationVertex (cubicOpenGraph d omega) x

@[simp]
theorem mem_openTrifurcationsInBox_iff
    {d n : ℕ} {omega : EdgeConfiguration d} {x : Cubic d} :
    x ∈ openTrifurcationsInBox d omega n ↔
      cubicLInfDist cubicOrigin x ≤ n - 1 ∧
        IsTrifurcationVertex (cubicOpenGraph d omega) x := by
  classical
  rw [openTrifurcationsInBox, Finset.mem_filter,
    mem_cubicMetricBox_iff_lInfDist_le]

/-- Summed coordinate-box form of (8.6): the number of inner trifurcations is at most the
outer box-surface cardinality. -/
theorem openTrifurcationsInBox_card_le_surface
    {d n : ℕ} (omega : EdgeConfiguration d) (hn : 1 ≤ n) :
    (openTrifurcationsInBox d omega n).card ≤
      (cubicBoxSurface d cubicOrigin n).card := by
  classical
  let G := cubicOpenGraph d omega
  let T := openTrifurcationsInBox d omega n
  let surface := cubicBoxSurface d cubicOrigin n
  let component : Cubic d → G.ConnectedComponent := G.connectedComponentMk
  let components := T.image component
  have hfiber (K : G.ConnectedComponent) :
      T.filter (fun x ↦ component x = K) =
        openTrifurcationsInComponentBox d omega K n := by
    ext x
    simp [T, component, mem_openTrifurcationsInBox_iff,
      mem_openTrifurcationsInComponentBox_iff]
    tauto
  have hsurfaceFiber (K : G.ConnectedComponent) :
      (surface.filter fun y ↦ component y = K).card =
        (openComponentBoxSurface d omega K n).card := by
    change ((cubicBoxSurface d cubicOrigin n).filter fun y ↦
      (cubicOpenGraph d omega).connectedComponentMk y = K).card = _
    rfl
  calc
    T.card = ∑ K ∈ components, (T.filter fun x ↦ component x = K).card := by
      exact Finset.card_eq_sum_card_image component T
    _ = ∑ K ∈ components,
        (openTrifurcationsInComponentBox d omega K n).card := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [hfiber]
    _ ≤ ∑ K ∈ components, (openComponentBoxSurface d omega K n).card := by
      apply Finset.sum_le_sum
      intro K _hK
      exact (openTrifurcationsInComponentBox_card_le K hn).trans (Nat.sub_le _ _)
    _ = ∑ K ∈ components, (surface.filter fun y ↦ component y = K).card := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [hsurfaceFiber]
    _ = (surface.filter fun y ↦ component y ∈ components).card :=
      Finset.sum_card_fiberwise_eq_card_filter surface components component
    _ ≤ surface.card := Finset.card_filter_le _ _

/-- A finite sum of event indicators counts exactly the indices whose events occur. -/
theorem sum_eventIndicator_eq_card_filter
    {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (S : Finset α) (A : α → Set Ω) (omega : Ω)
    [DecidablePred fun x ↦ omega ∈ A x] :
    ∑ x ∈ S, eventIndicator (A x) omega =
      ((S.filter fun x ↦ omega ∈ A x).card : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      rw [Finset.sum_insert hx]
      by_cases hA : omega ∈ A x
      · rw [eventIndicator, Set.indicator_of_mem hA, ih]
        have hxfilter : x ∉ S.filter fun y ↦ omega ∈ A y := by
          exact fun h ↦ hx (Finset.mem_filter.mp h).1
        rw [show (insert x S).filter (fun y ↦ omega ∈ A y) =
            insert x (S.filter fun y ↦ omega ∈ A y) by
          ext y
          by_cases hyx : y = x <;> simp [hyx, hA]]
        rw [Finset.card_insert_of_notMem hxfilter]
        push_cast
        ring
      · rw [eventIndicator, Set.indicator_of_notMem hA, zero_add, ih]
        have hfilter : (insert x S).filter (fun y ↦ omega ∈ A y) =
            S.filter fun y ↦ omega ∈ A y := by
          ext y
          by_cases hyx : y = x <;> simp [hyx, hA]
        rw [hfilter]

/-- Averaged Burton--Keane estimate.  The volume times the probability of one fixed strong
trifurcation witness is bounded by the coordinate-box surface cardinality. -/
theorem box_card_mul_strongTrifurcationProbability_le_surface
    {d n : ℕ} (hd : 0 < d) (p : I) (x : Cubic d) (hn : 1 ≤ n) :
    ((cubicMetricBox d cubicOrigin (n - 1)).card : ℝ) *
        (bernoulliBondMeasure d p).real (strongTrifurcationEvent d x) ≤
      ((cubicBoxSurface d cubicOrigin n).card : ℝ) := by
  classical
  let μ := bernoulliBondMeasure d p
  let B := cubicMetricBox d cubicOrigin (n - 1)
  let A (y : Cubic d) := translatedStrongTrifurcationEvent d x y
  let f : EdgeConfiguration d → ℝ := fun omega ↦
    ∑ y ∈ B, eventIndicator (A y) omega
  let M : ℝ := (cubicBoxSurface d cubicOrigin n).card
  have hAmeas (y : Cubic d) : MeasurableSet (A y) := by
    exact measurableSet_translatedStrongTrifurcationEvent d x y
  have htermInt (y : Cubic d) (hy : y ∈ B) :
      Integrable (eventIndicator (A y)) μ :=
    (integrable_const (1 : ℝ)).indicator (hAmeas y)
  have hfInt : Integrable f μ := by
    exact integrable_finsetSum B htermInt
  have hMInt : Integrable (fun _ : EdgeConfiguration d ↦ M) μ := integrable_const M
  have hpoint (omega : EdgeConfiguration d) : f omega ≤ M := by
    let W := B.filter fun y ↦ omega ∈ A y
    have hWB : W ⊆ openTrifurcationsInBox d omega n := by
      intro y hy
      have hyData := Finset.mem_filter.mp hy
      apply mem_openTrifurcationsInBox_iff.mpr
      refine ⟨mem_cubicMetricBox_iff_lInfDist_le.mp hyData.1, ?_⟩
      exact translatedStrongTrifurcationEvent_subset_trifurcationEvent d x y hyData.2
    have hcard : W.card ≤ (cubicBoxSurface d cubicOrigin n).card :=
      (Finset.card_le_card hWB).trans
        (openTrifurcationsInBox_card_le_surface omega hn)
    change (∑ y ∈ B, eventIndicator (A y) omega) ≤
      ((cubicBoxSurface d cubicOrigin n).card : ℝ)
    rw [sum_eventIndicator_eq_card_filter]
    exact_mod_cast hcard
  have hint := integral_mono hfInt hMInt hpoint
  have hfIntegral : ∫ omega, f omega ∂μ =
      (B.card : ℝ) * μ.real (strongTrifurcationEvent d x) := by
    rw [show (∫ omega, f omega ∂μ) =
        ∑ y ∈ B, ∫ omega, eventIndicator (A y) omega ∂μ by
      exact integral_finsetSum B htermInt]
    simp_rw [integral_eventIndicator (hAmeas _)]
    simp only [μ, A]
    simp_rw [bernoulliBondMeasure_real_translatedStrongTrifurcationEvent p x]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hMIntegral : ∫ _omega : EdgeConfiguration d, M ∂μ = M := by
    simp [μ]
  rw [hfIntegral, hMIntegral] at hint
  exact hint

/-- The surface-to-volume estimate forces the probability of every strong trifurcation event
to vanish. -/
theorem bernoulliBondMeasure_real_strongTrifurcationEvent_eq_zero
    {d : ℕ} (hd : 1 ≤ d) (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (strongTrifurcationEvent d x) = 0 := by
  let q := (bernoulliBondMeasure d p).real (strongTrifurcationEvent d x)
  apply le_antisymm ?_ measureReal_nonneg
  by_contra hq
  have hqpos : 0 < q := lt_of_not_ge hq
  let C : ℝ := 2 * d * 3 ^ (d - 1)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ C < q * (n : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (C / q)
    refine ⟨max 1 n, by omega, ?_⟩
    have hn' : C / q < (max 1 n : ℕ) :=
      hn.trans_le (by exact_mod_cast Nat.le_max_right 1 n)
    have hn'' : C / q < (max 1 n : ℝ) := by exact_mod_cast hn'
    simpa [mul_comm] using (div_lt_iff₀ hqpos).mp hn''
  have hmain := box_card_mul_strongTrifurcationProbability_le_surface
    (p := p) (x := x) (n := n) (by omega : 0 < d) hn.1
  have hbox : n ^ d ≤ (cubicMetricBox d cubicOrigin (n - 1)).card := by
    rw [cubicMetricBox_card]
    exact Nat.pow_le_pow_left (by omega) d
  have hsurface := cubicBoxSurface_card_le (by omega : 0 < d) cubicOrigin
    (n := n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn.1
  have hpow : ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) ≤
      (3 : ℝ) ^ (d - 1) * (n : ℝ) ^ (d - 1) := by
    have hbase : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) := by
      push_cast
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
      nlinarith
    exact (pow_le_pow_left₀ (by positivity) hbase _).trans_eq (mul_pow 3 (n : ℝ) _)
  have hbound : (n : ℝ) ^ d * q ≤
      C * (n : ℝ) ^ (d - 1) := by
    calc
      (n : ℝ) ^ d * q ≤
          ((cubicMetricBox d cubicOrigin (n - 1)).card : ℝ) * q := by
        gcongr
        exact_mod_cast hbox
      _ ≤ ((cubicBoxSurface d cubicOrigin n).card : ℝ) := hmain
      _ ≤ (2 * d * (2 * n + 1) ^ (d - 1) : ℕ) := by exact_mod_cast hsurface
      _ ≤ C * (n : ℝ) ^ (d - 1) := by
        calc
          ((2 * d * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) =
              (2 * (d : ℝ)) * (((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)) := by
            push_cast
            ring
          _ ≤ (2 * (d : ℝ)) *
              ((3 : ℝ) ^ (d - 1) * (n : ℝ) ^ (d - 1)) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = C * (n : ℝ) ^ (d - 1) := by
            dsimp [C]
            ring
  have hfactorPos : 0 < (n : ℝ) ^ (d - 1) := pow_pos hnpos _
  have hrewrite : (n : ℝ) ^ d =
      (n : ℝ) ^ (d - 1) * n := by
    calc
      (n : ℝ) ^ d = (n : ℝ) ^ ((d - 1) + 1) := by
        congr 1
        omega
      _ = (n : ℝ) ^ (d - 1) * n := pow_succ _ _
  rw [hrewrite, mul_assoc] at hbound
  have hqle : q * (n : ℝ) ≤ C := by
    apply le_of_mul_le_mul_left _ hfactorPos
    simpa [mul_assoc, mul_comm, mul_left_comm] using hbound
  exact (not_le_of_gt hn.2) hqle

/-- Every finite coordinate box induces a connected cubic region. -/
theorem cubicRegionGraph_cubicMetricBox_connected
    (d : ℕ) (c : Cubic d) (n : ℕ) :
    (cubicRegionGraph d (cubicMetricBox d c n : Set (Cubic d))).Connected := by
  apply cubicRegionGraph_connected_of_coordinateConvex
  · exact ⟨c, by simp [mem_cubicMetricBox]⟩
  · intro x hx y hy z hz
    change x ∈ cubicMetricBox d c n at hx
    change y ∈ cubicMetricBox d c n at hy
    change z ∈ cubicMetricBox d c n
    rw [mem_cubicMetricBox] at hx hy ⊢
    intro i
    have hxi := hx i
    have hyi := hy i
    rcases hz i with hzi | hzi <;> constructor <;> omega

/-- Infinite multiplicity is impossible at a nondegenerate Bernoulli parameter: if three
infinite clusters occurred almost surely, finite energy would create a positive-probability
trifurcation, contradicting the surface-to-volume theorem. -/
theorem not_atLeast_three_infiniteOpenClusters_almostSure
    {d : ℕ} (hd : 1 ≤ d) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hthree : (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d 3) = 1) : False := by
  classical
  have hthreePos : 0 < (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d 3) := by rw [hthree]; norm_num
  obtain ⟨x, hxpos⟩ :=
    exists_infiniteOpenClusterWitness_measureReal_pos_of_atLeast p hthreePos
  let n := ∑ i : Fin 3, cubicLInfDist cubicOrigin (x i)
  let B := cubicMetricBox d cubicOrigin n
  have hxB : ∀ i, x i ∈ B := by
    intro i
    rw [mem_cubicMetricBox_iff_lInfDist_le]
    exact Finset.single_le_sum
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin 3))) ↦
        Nat.zero_le (cubicLInfDist cubicOrigin (x j)))
      (Finset.mem_univ i)
  obtain ⟨u, _huB, huPos⟩ := exists_strongTrifurcation_measureReal_pos_of_witness
    hp0 hp1 (cubicRegionGraph_cubicMetricBox_connected d cubicOrigin n) hxB hxpos
  have huZero := bernoulliBondMeasure_real_strongTrifurcationEvent_eq_zero hd p u
  exact (ne_of_gt huPos) huZero

/-- Interior-parameter uniqueness in event form: the probability of two or more infinite open
clusters is zero. -/
theorem bernoulliBondMeasure_real_atLeast_two_infiniteOpenClusters_eq_zero
    {d : ℕ} (hd : 1 ≤ d) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (bernoulliBondMeasure d p).real
      (atLeastInfiniteOpenClustersEvent d 2) = 0 := by
  rcases bernoulliBondMeasure_real_atLeastInfiniteOpenClustersEvent_eq_zero_or_one
      hd p 2 with hzero | hone
  · exact hzero
  · rcases bernoulliBondMeasure_real_atLeastInfiniteOpenClustersEvent_eq_zero_or_one
        hd p 3 with hthreeZero | hthreeOne
    · exact (not_finite_infiniteOpenCluster_multiplicity
        (k := 2) (by omega) hp0 hp1 hone hthreeZero).elim
    · exact (not_atLeast_three_infiniteOpenClusters_almostSure
        hd hp0 hp1 hthreeOne).elim

/-- In the fully open configuration there is exactly one infinite component in every positive
dimension. -/
theorem univ_mem_exactlyOneInfiniteOpenClusterEvent
    {d : ℕ} (hd : 1 ≤ d) :
    (Set.univ : EdgeConfiguration d) ∈ exactlyOneInfiniteOpenClusterEvent d := by
  classical
  let axis : ℕ → Cubic d := cubicAxisVertex d
  have haxis : Function.Injective axis := by
    intro m n hmn
    have hdist := congrArg (cubicL1Dist (cubicOrigin : Cubic d)) hmn
    simpa [axis, cubicL1Dist_origin_axisVertex (by omega : 0 < d)] using hdist
  letI : Infinite (Cubic d) := Infinite.of_injective axis haxis
  have hcluster : cubicOpenClusterFrom d (Set.univ : EdgeConfiguration d) cubicOrigin =
      Set.univ := by
    ext y
    simp only [cubicOpenClusterFrom, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨w⟩ := nonempty_cubicWalk d cubicOrigin y
    exact ⟨w, fun _e _he ↦ Set.mem_univ _⟩
  apply mem_exactlyOneInfiniteOpenClusterEvent_iff.mpr
  refine ⟨cubicOrigin, ?_, ?_⟩
  · change (cubicOpenClusterFrom d (Set.univ : EdgeConfiguration d) cubicOrigin).Infinite
    rw [hcluster]
    exact Set.infinite_univ
  · intro y _hy
    obtain ⟨w⟩ := nonempty_cubicWalk d cubicOrigin y
    exact ⟨w, fun _e _he ↦ Set.mem_univ _⟩

/-- The fully open Bernoulli law assigns probability one to uniqueness. -/
theorem bernoulliBondMeasure_one_real_exactlyOneInfiniteOpenClusterEvent
    {d : ℕ} (hd : 1 ≤ d) :
    (bernoulliBondMeasure d (1 : I)).real
      (exactlyOneInfiniteOpenClusterEvent d) = 1 := by
  rw [bernoulliBondMeasure, setBernoulli_one, Measure.real,
    Measure.dirac_apply' _ (measurableSet_exactlyOneInfiniteOpenClusterEvent d)]
  simp [univ_mem_exactlyOneInfiniteOpenClusterEvent hd]

/-- The event of at least one infinite component is the root-free percolation event. -/
theorem atLeast_one_infiniteOpenClustersEvent_eq_globalExistence (d : ℕ) :
    atLeastInfiniteOpenClustersEvent d 1 =
      {omega | hasInfiniteOpenClusterInVertices d Set.univ omega} := by
  ext omega
  rw [mem_atLeastInfiniteOpenClustersEvent_iff]
  change (1 : ℕ∞) ≤ numberOfInfiniteOpenClusters d omega ↔
    hasInfiniteOpenClusterInVertices d Set.univ omega
  rw [ENat.one_le_iff_ne_zero, numberOfInfiniteOpenClusters_ne_zero_iff]
  simp only [hasInfiniteOpenClusterInVertices, Set.mem_univ, true_and,
    cubicOpenClusterWithinVertices_univ, hasInfiniteOpenClusterFrom]

/-- **Grimmett, Theorem 8.1 (uniqueness of the infinite open cluster).**  Whenever the
rooted percolation probability is positive, there is almost surely exactly one infinite open
cluster. -/
theorem unique_infiniteOpenCluster_almostSure_of_theta_pos
    {d : ℕ} (hd : 1 ≤ d) (p : I) (htheta : 0 < theta d p) :
    (bernoulliBondMeasure d p).real
      (exactlyOneInfiniteOpenClusterEvent d) = 1 := by
  by_cases hpone : (p : ℝ) = 1
  · have hp : p = (1 : I) := Subtype.ext hpone
    subst p
    exact bernoulliBondMeasure_one_real_exactlyOneInfiniteOpenClusterEvent hd
  · have hp0 : 0 < (p : ℝ) := by
      by_contra hnot
      have hpzero : (p : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hnot) p.property.1
      have hzero := thetaFrom_eq_zero_of_coe_eq_zero d hpzero cubicOrigin
      have : theta d p = 0 := by simpa using hzero
      exact (ne_of_gt htheta) this
    have hp1 : (p : ℝ) < 1 := lt_of_le_of_ne p.property.2 hpone
    letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
    have hexist : regionHasInfiniteClusterProbability d Set.univ p = 1 :=
      regionHasInfiniteClusterProbability_univ_eq_one_of_theta_pos d p htheta
    have hone : (bernoulliBondMeasure d p).real
        (atLeastInfiniteOpenClustersEvent d 1) = 1 := by
      rw [atLeast_one_infiniteOpenClustersEvent_eq_globalExistence]
      exact hexist
    have htwo : (bernoulliBondMeasure d p).real
        (atLeastInfiniteOpenClustersEvent d 2) = 0 :=
      bernoulliBondMeasure_real_atLeast_two_infiniteOpenClusters_eq_zero
        hd hp0 hp1
    have hexact := bernoulliBondMeasure_real_exactlyKInfiniteOpenClustersEvent_eq_one
      (k := 1) p hone htwo
    have hevents : exactlyKInfiniteOpenClustersEvent d 1 =
        exactlyOneInfiniteOpenClusterEvent d := by
      ext omega
      rw [mem_exactlyKInfiniteOpenClustersEvent_iff]
      rfl
    rwa [hevents] at hexact

end Percolation
