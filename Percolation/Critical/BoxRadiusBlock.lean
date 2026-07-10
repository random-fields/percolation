import Percolation.Critical.BoxFaces

/-!
# Block decomposition for coordinate-box radius events

This is the BK half of Grimmett's proof of Theorem 6.10, equations (6.19)--(6.21).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators ENNReal

def boxRadiusSplitEvent (d : ℕ) (x : Cubic d) (m n : ℕ) (y : Cubic d) :
    Set (EdgeConfiguration d) :=
  OpenWitnessDisjointOccurrence
    (connectionEventIn d (cubicBoxEdges d x m) x y)
    (boxRadiusConnectionEvent d y n)

/-- Deterministic first-hit decomposition behind the box-radius BK inequality. -/
theorem boxRadiusConnectionEvent_subset_biUnion_boxRadiusSplitEvent
    {d m n : ℕ} {x : Cubic d} :
    boxRadiusConnectionEvent d x (m + n) ⊆
      ⋃ y ∈ cubicBoxSurface d x m, boxRadiusSplitEvent d x m n y := by
  intro ω hω
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at hω
  rcases hω with ⟨v, hv, w, hwopen⟩
  let P : (cubicGraph d).Walk x v := w.toPath
  have hPpath : P.IsPath := w.toPath.2
  have hPopen : walkIsOpen ω P := walkIsOpen_toPath w hwopen
  have hexit : ∃ k : ℕ, k ≤ P.length ∧ m ≤ cubicLInfDist x (P.getVert k) := by
    refine ⟨P.length, le_rfl, ?_⟩
    have hvdist : cubicLInfDist x v = m + n := mem_cubicBoxSurface.mp hv
    simpa [P, hvdist] using Nat.le_add_right m n
  let k := Nat.find hexit
  have hk : k ≤ P.length ∧ m ≤ cubicLInfDist x (P.getVert k) := Nat.find_spec hexit
  have hkdist : cubicLInfDist x (P.getVert k) = m := by
    by_cases hkzero : k = 0
    · have hm : m = 0 := by simpa [hkzero] using hk.2
      simp [hkzero, hm]
    · let j := k - 1
      have hksucc : k = j + 1 := by omega
      have hjfind : j < Nat.find hexit := by change j < k; omega
      have hjlt : cubicLInfDist x (P.getVert j) < m := by
        apply lt_of_not_ge
        intro hj
        exact Nat.find_min hexit hjfind ⟨by omega, hj⟩
      have hjlen : j < P.length := by omega
      have hadj := P.adj_getVert_succ hjlen
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
      have hupper : cubicLInfDist x (P.getVert (j + 1)) ≤ m := by
        calc
          cubicLInfDist x (P.getVert (j + 1)) ≤
              cubicLInfDist x (P.getVert j) +
                cubicLInfDist (P.getVert j) (P.getVert (j + 1)) :=
            cubicLInfDist_triangle _ _ _
          _ ≤ cubicLInfDist x (P.getVert j) + 1 := by
            gcongr
            rw [ha]
            exact cubicLInfDist_stepFrom_le_one _ _
          _ ≤ m := by omega
      rw [hksucc]
      exact le_antisymm hupper (by simpa [hksucc] using hk.2)
  let y := P.getVert k
  let q := P.take k
  let r := P.drop k
  have hqopen : walkIsOpen ω q := walkIsOpen_take P hPopen k
  have hropen : walkIsOpen ω r := walkIsOpen_drop P hPopen k
  have hq_length : q.length = k := by simp [q, Nat.min_eq_left hk.1]
  have hq_support : ∀ z ∈ q.support, z ∈ cubicMetricBox d x m := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    rcases hz with ⟨j, rfl, hj⟩
    have hjk : j ≤ k := by simpa [q, Nat.min_eq_left hk.1] using hj
    have hget : q.getVert j = P.getVert j := by simp [q, Nat.min_eq_right hjk]
    rw [hget, mem_cubicMetricBox_iff_lInfDist_le]
    rcases hjk.lt_or_eq with hjlt | rfl
    · apply Nat.le_of_lt
      apply lt_of_not_ge
      intro hge
      exact Nat.find_min hexit hjlt ⟨by omega, hge⟩
    · exact hkdist.le
  have hyradius : n ≤ cubicLInfDist y v := by
    have htri := cubicLInfDist_triangle x y v
    have hvdist := mem_cubicBoxSurface.mp hv
    change cubicLInfDist x y = m at hkdist
    rw [hkdist, hvdist] at htri
    omega
  let H := walkEdgeFinset q
  let K := walkEdgeFinset r
  have hHK : Disjoint H K := by
    rw [Finset.disjoint_left]
    intro e heH heK
    have heq : (e : Sym2 (Cubic d)) ∈ q.edges := (mem_walkEdgeFinset_iff q e).mp heH
    have her : (e : Sym2 (Cubic d)) ∈ r.edges := (mem_walkEdgeFinset_iff r e).mp heK
    change (e : Sym2 (Cubic d)) ∈ (P.take k).edges at heq
    change (e : Sym2 (Cubic d)) ∈ (P.drop k).edges at her
    rw [SimpleGraph.Walk.edges_take] at heq
    rw [SimpleGraph.Walk.edges_drop] at her
    exact (List.disjoint_take_drop hPpath.isTrail.edges_nodup (le_refl k)) heq her
  have hHsub : (H : Set (CubicEdge d)) ⊆ ω := by
    intro e he
    exact hqopen e.1 ((mem_walkEdgeFinset_iff q e).mp he)
  have hKsub : (K : Set (CubicEdge d)) ⊆ ω := by
    intro e he
    exact hropen e.1 ((mem_walkEdgeFinset_iff r e).mp he)
  have hHconn : (H : Set (CubicEdge d)) ∈
      connectionEventIn d (cubicBoxEdges d x m) x y := by
    refine ⟨q, walkIsOpen_walkEdgeFinset q, ?_⟩
    exact walkEdgeFinset_subset_cubicBoxEdges_of_support q hq_support
  have hKradius : (K : Set (CubicEdge d)) ∈ boxRadiusConnectionEvent d y n := by
    exact exists_open_walk_to_cubicBoxSurface_in_box r
      (walkIsOpen_walkEdgeFinset r) hyradius
  apply Set.mem_iUnion₂.mpr
  exact ⟨y, mem_cubicBoxSurface.mpr hkdist, H, K, hHK, hHsub, hKsub, hHconn, hKradius⟩

theorem connectionEvent_subset_boxRadiusConnectionEvent_of_mem_surface
    {d m : ℕ} {x y : Cubic d} (hy : y ∈ cubicBoxSurface d x m) :
    connectionEvent d x y ⊆ boxRadiusConnectionEvent d x m := by
  intro ω hω
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
  exact ⟨y, hy, hω⟩

/-- Equation (6.21) before inserting the explicit surface-cardinality estimate. -/
theorem boxRadiusTail_add_le_surface_card_mul
    (d : ℕ) (p : I) (m n : ℕ) :
    boxRadiusTail d p (m + n) ≤
      (cubicBoxSurface d cubicOrigin m).card *
        (boxRadiusTail d p m * boxRadiusTail d p n) := by
  let μ := bernoulliBondMeasure d p
  have hcover := boxRadiusConnectionEvent_subset_biUnion_boxRadiusSplitEvent
    (d := d) (x := cubicOrigin) (m := m) (n := n)
  have hunion : μ.real (boxRadiusConnectionEvent d cubicOrigin (m + n)) ≤
      ∑ y ∈ cubicBoxSurface d cubicOrigin m,
        μ.real (boxRadiusSplitEvent d cubicOrigin m n y) := by
    exact (measureReal_mono hcover (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le (cubicBoxSurface d cubicOrigin m)
        (boxRadiusSplitEvent d cubicOrigin m n))
  calc
    boxRadiusTail d p (m + n) ≤
        ∑ y ∈ cubicBoxSurface d cubicOrigin m,
          μ.real (boxRadiusSplitEvent d cubicOrigin m n y) := hunion
    _ ≤ ∑ _y ∈ cubicBoxSurface d cubicOrigin m,
        (boxRadiusTail d p m * boxRadiusTail d p n) := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        μ.real (boxRadiusSplitEvent d cubicOrigin m n y) ≤
            μ.real (connectionEventIn d
              (cubicBoxEdges d cubicOrigin m) cubicOrigin y) *
              μ.real (boxRadiusConnectionEvent d y n) :=
          bernoulliBondMeasure_real_disjointOccurrence_le_mul p
            (isIncreasingEvent_connectionEventIn d
              (cubicBoxEdges d cubicOrigin m) cubicOrigin y)
            (isIncreasingEvent_boxRadiusConnectionEvent d y n)
            (dependsOn_connectionEventIn d
              (cubicBoxEdges d cubicOrigin m) cubicOrigin y)
            (dependsOn_boxRadiusConnectionEvent d y n)
        _ ≤ μ.real (connectionEvent d cubicOrigin y) *
              μ.real (boxRadiusConnectionEvent d y n) := by
          apply mul_le_mul_of_nonneg_right
          · exact measureReal_mono (μ := μ) (connectionEventIn_subset d _ cubicOrigin y)
              (measure_ne_top μ _)
          · exact measureReal_nonneg
        _ ≤ boxRadiusTail d p m * μ.real (boxRadiusConnectionEvent d y n) := by
          apply mul_le_mul_of_nonneg_right
          · exact measureReal_mono
              (connectionEvent_subset_boxRadiusConnectionEvent_of_mem_surface hy)
              (measure_ne_top μ _)
          · exact measureReal_nonneg
        _ = boxRadiusTail d p m * boxRadiusTail d p n := by
          rw [bernoulliBondMeasure_real_boxRadiusConnectionEvent_eq_boxRadiusTail]
    _ = (cubicBoxSurface d cubicOrigin m).card *
        (boxRadiusTail d p m * boxRadiusTail d p n) := by simp

/-- Grimmett's equation (6.21) with equation (6.28)'s explicit polynomial factor. -/
theorem boxRadiusTail_add_le_polynomial_mul
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) :
    boxRadiusTail d p (m + n) ≤
      (2 * d * (2 * m + 1) ^ (d - 1)) *
        (boxRadiusTail d p m * boxRadiusTail d p n) := by
  calc
    boxRadiusTail d p (m + n) ≤
        (cubicBoxSurface d cubicOrigin m).card *
          (boxRadiusTail d p m * boxRadiusTail d p n) :=
      boxRadiusTail_add_le_surface_card_mul d p m n
    _ ≤ (2 * d * (2 * m + 1) ^ (d - 1)) *
          (boxRadiusTail d p m * boxRadiusTail d p n) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast cubicBoxSurface_card_le hd cubicOrigin
      · exact mul_nonneg measureReal_nonneg measureReal_nonneg

/-! ### The FKG lower block inequality -/

theorem connectionEvent_inter_boxFaceConnectionEvent_subset_boxRadiusConnectionEvent_add
    {d m n : ℕ} {x : Cubic d} {i : Fin d} {positive : Bool}
    (hx : x ∈ cubicBoxFace d cubicOrigin m i positive) :
    connectionEvent d cubicOrigin x ∩ boxFaceConnectionEvent d x n i positive ⊆
      boxRadiusConnectionEvent d cubicOrigin (m + n) := by
  rintro ω ⟨⟨w, hw⟩, y, hy, q, hq⟩
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
  exact ⟨y, mem_cubicBoxSurface_add_of_mem_faces hx hy,
    w.append q, walkIsOpen_append hw hq⟩

theorem boxRadiusTail_le_surfaceConnectionSum (d : ℕ) (p : I) (m : ℕ) :
    boxRadiusTail d p m ≤
      ∑ x ∈ cubicBoxSurface d cubicOrigin m,
        (bernoulliBondMeasure d p).real (connectionEvent d cubicOrigin x) := by
  let μ := bernoulliBondMeasure d p
  have hcover : boxRadiusConnectionEvent d cubicOrigin m ⊆
      ⋃ x ∈ cubicBoxSurface d cubicOrigin m, connectionEvent d cubicOrigin x := by
    intro ω hω
    rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at hω
    rcases hω with ⟨x, hx, hconn⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hconn⟩
  exact (measureReal_mono hcover (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le (cubicBoxSurface d cubicOrigin m)
      (connectionEvent d cubicOrigin))

/-- Equation (6.27) in multiplicative form, before replacing the surface cardinality by its
polynomial upper bound. -/
theorem boxRadiusTail_mul_le_two_mul_card_mul_surface_card_mul_add
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) (i0 : Fin d) :
    boxRadiusTail d p m * boxRadiusTail d p n ≤
      (2 * d * (cubicBoxSurface d cubicOrigin m).card) *
        boxRadiusTail d p (m + n) := by
  let μ := bernoulliBondMeasure d p
  let gamma := boxFaceTail d p n i0 true
  have hpoint : ∀ x ∈ cubicBoxSurface d cubicOrigin m,
      μ.real (connectionEvent d cubicOrigin x) * gamma ≤
        boxRadiusTail d p (m + n) := by
    intro x hx
    have hxfaces := cubicBoxSurface_subset_faces (x := cubicOrigin) hd hx
    rw [cubicBoxFaces, Finset.mem_biUnion] at hxfaces
    rcases hxfaces with ⟨i, _hi, hiface⟩
    rw [Finset.mem_union] at hiface
    rcases hiface with hpos | hneg
    · have hfaceProb : μ.real (boxFaceConnectionEvent d x n i true) = gamma := by
        rw [bernoulliBondMeasure_real_boxFaceConnectionEvent_eq_boxFaceTail]
        dsimp only [gamma]
        simpa using boxFaceTail_permutation p (Equiv.swap i i0) i true
      calc
        μ.real (connectionEvent d cubicOrigin x) * gamma =
            μ.real (connectionEvent d cubicOrigin x) *
              μ.real (boxFaceConnectionEvent d x n i true) := by rw [hfaceProb]
        _ ≤ μ.real (connectionEvent d cubicOrigin x ∩
              boxFaceConnectionEvent d x n i true) :=
          bernoulliBondMeasure_real_fkg p
            (isIncreasingEvent_connectionEvent d cubicOrigin x)
            (isIncreasingEvent_boxFaceConnectionEvent d x n i true)
            (measurableSet_connectionEvent d cubicOrigin x)
            (measurableSet_boxFaceConnectionEvent d x n i true)
        _ ≤ boxRadiusTail d p (m + n) := by
          exact measureReal_mono
            (connectionEvent_inter_boxFaceConnectionEvent_subset_boxRadiusConnectionEvent_add
              hpos)
    · have hfaceProb : μ.real (boxFaceConnectionEvent d x n i false) = gamma := by
        rw [bernoulliBondMeasure_real_boxFaceConnectionEvent_eq_boxFaceTail]
        dsimp only [gamma]
        rw [← boxFaceTail_true_eq_false p i]
        simpa using boxFaceTail_permutation p (Equiv.swap i i0) i true
      calc
        μ.real (connectionEvent d cubicOrigin x) * gamma =
            μ.real (connectionEvent d cubicOrigin x) *
              μ.real (boxFaceConnectionEvent d x n i false) := by rw [hfaceProb]
        _ ≤ μ.real (connectionEvent d cubicOrigin x ∩
              boxFaceConnectionEvent d x n i false) :=
          bernoulliBondMeasure_real_fkg p
            (isIncreasingEvent_connectionEvent d cubicOrigin x)
            (isIncreasingEvent_boxFaceConnectionEvent d x n i false)
            (measurableSet_connectionEvent d cubicOrigin x)
            (measurableSet_boxFaceConnectionEvent d x n i false)
        _ ≤ boxRadiusTail d p (m + n) := by
          exact measureReal_mono
            (connectionEvent_inter_boxFaceConnectionEvent_subset_boxRadiusConnectionEvent_add
              hneg)
  have hsum :
      (∑ x ∈ cubicBoxSurface d cubicOrigin m,
          μ.real (connectionEvent d cubicOrigin x)) * gamma ≤
        (cubicBoxSurface d cubicOrigin m).card * boxRadiusTail d p (m + n) := by
    calc
      (∑ x ∈ cubicBoxSurface d cubicOrigin m,
          μ.real (connectionEvent d cubicOrigin x)) * gamma =
          ∑ x ∈ cubicBoxSurface d cubicOrigin m,
            (μ.real (connectionEvent d cubicOrigin x) * gamma) := by rw [Finset.sum_mul]
      _ ≤ ∑ _x ∈ cubicBoxSurface d cubicOrigin m,
          boxRadiusTail d p (m + n) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpoint x hx
      _ = (cubicBoxSurface d cubicOrigin m).card *
          boxRadiusTail d p (m + n) := by simp
  have hbetaGamma : boxRadiusTail d p m * gamma ≤
      (cubicBoxSurface d cubicOrigin m).card * boxRadiusTail d p (m + n) := by
    exact (mul_le_mul_of_nonneg_right
      (boxRadiusTail_le_surfaceConnectionSum d p m) measureReal_nonneg).trans hsum
  have hbetaFace := boxRadiusTail_le_two_mul_card_mul_boxFaceTail (n := n) hd p i0
  calc
    boxRadiusTail d p m * boxRadiusTail d p n ≤
        boxRadiusTail d p m * (2 * d * gamma) := by
      exact mul_le_mul_of_nonneg_left hbetaFace measureReal_nonneg
    _ = (2 * d) * (boxRadiusTail d p m * gamma) := by ring
    _ ≤ (2 * d) * ((cubicBoxSurface d cubicOrigin m).card *
          boxRadiusTail d p (m + n)) := by
      exact mul_le_mul_of_nonneg_left hbetaGamma (by positivity)
    _ = (2 * d * (cubicBoxSurface d cubicOrigin m).card) *
          boxRadiusTail d p (m + n) := by ring

/-- Equation (6.27) with the explicit equation (6.28) surface estimate. -/
theorem boxRadiusTail_mul_le_polynomial_mul_add
    {d : ℕ} (hd : 0 < d) (p : I) (m n : ℕ) (i0 : Fin d) :
    boxRadiusTail d p m * boxRadiusTail d p n ≤
      (4 * d ^ 2 * (2 * m + 1) ^ (d - 1)) *
        boxRadiusTail d p (m + n) := by
  calc
    boxRadiusTail d p m * boxRadiusTail d p n ≤
        (2 * d * (cubicBoxSurface d cubicOrigin m).card) *
          boxRadiusTail d p (m + n) :=
      boxRadiusTail_mul_le_two_mul_card_mul_surface_card_mul_add hd p m n i0
    _ ≤ (4 * d ^ 2 * (2 * m + 1) ^ (d - 1)) *
          boxRadiusTail d p (m + n) := by
      apply mul_le_mul_of_nonneg_right
      · have hcoeff : 2 * d * (cubicBoxSurface d cubicOrigin m).card ≤
            4 * d ^ 2 * (2 * m + 1) ^ (d - 1) := by
          calc
            2 * d * (cubicBoxSurface d cubicOrigin m).card ≤
                2 * d * (2 * d * (2 * m + 1) ^ (d - 1)) :=
              Nat.mul_le_mul_left (2 * d) (cubicBoxSurface_card_le hd cubicOrigin)
            _ = 4 * d ^ 2 * (2 * m + 1) ^ (d - 1) := by ring
        exact_mod_cast hcoeff
      · exact measureReal_nonneg

#print axioms boxRadiusTail_add_le_polynomial_mul
#print axioms boxRadiusTail_mul_le_polynomial_mul_add

end Percolation
