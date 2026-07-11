import Percolation.Critical.Regions
import Percolation.Bernoulli.UpwardDistance
import Percolation.Planar.Projection

/-!
# Finite thick-slab connection regions

This file defines the two finite regions in Grimmett (7.76)--(7.77):

* `finiteThickSlabSVertices d n L = [-n,n]² × [0,L]^(d-2)`;
* `finiteThickSlabTVertices d n L = [-n,n]^(d-1) × [0,L]`.

They are represented as finsets so that later FKG products, finite-energy modifications, and
uniform connection estimates have explicit finite supports.  The public membership lemmas are
the source-facing coordinate descriptions and remain meaningful outside the source range
`3 ≤ d`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The finite thick slab `S_n(L) = [-n,n]² × [0,L]^(d-2)` from (7.76). -/
noncomputable def finiteThickSlabSVertices (d n L : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin (max n L)).filter fun x ↦
    ∀ i : Fin d,
      if i.val < 2 then (x i).natAbs ≤ n else 0 ≤ x i ∧ x i ≤ L

/-- The finite thick slab `T_n(L) = [-n,n]^(d-1) × [0,L]` from (7.77). -/
noncomputable def finiteThickSlabTVertices (d n L : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin (max n L)).filter fun x ↦
    ∀ i : Fin d,
      if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ L else (x i).natAbs ≤ n

@[simp]
theorem mem_finiteThickSlabSVertices_iff {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabSVertices d n L ↔
      ∀ i : Fin d,
        if i.val < 2 then (x i).natAbs ≤ n else 0 ≤ x i ∧ x i ≤ L := by
  classical
  rw [finiteThickSlabSVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicMetricBox]
    intro i
    simp only [cubicOrigin, zero_sub, zero_add]
    have hi := h i
    split at hi
    · have habs : |x i| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hi
      have hnmax : (n : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_left n L
      exact ⟨(neg_le_neg hnmax).trans (neg_le_of_abs_le habs),
        (le_of_abs_le habs).trans hnmax⟩
    · have hLmax : (L : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_right n L
      constructor <;> omega

@[simp]
theorem mem_finiteThickSlabTVertices_iff {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabTVertices d n L ↔
      ∀ i : Fin d,
        if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ L else (x i).natAbs ≤ n := by
  classical
  rw [finiteThickSlabTVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicMetricBox]
    intro i
    simp only [cubicOrigin, zero_sub, zero_add]
    have hi := h i
    split at hi
    · have hLmax : (L : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_right n L
      constructor <;> omega
    · have habs : |x i| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hi
      have hnmax : (n : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_left n L
      exact ⟨(neg_le_neg hnmax).trans (neg_le_of_abs_le habs),
        (le_of_abs_le habs).trans hnmax⟩

theorem finiteThickSlabSVertices_subset_box (d n L : ℕ) :
    (finiteThickSlabSVertices d n L : Set (Cubic d)) ⊆
      cubicMetricBox d cubicOrigin (max n L) := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem finiteThickSlabTVertices_subset_box (d n L : ℕ) :
    (finiteThickSlabTVertices d n L : Set (Cubic d)) ⊆
      cubicMetricBox d cubicOrigin (max n L) := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Open connection constrained to `S_n(L)`. -/
def finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d (finiteThickSlabSVertices d n L : Set (Cubic d)) x y

/-- Open connection constrained to `T_n(L)`. -/
def finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d (finiteThickSlabTVertices d n L : Set (Cubic d)) x y

theorem measurableSet_finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    MeasurableSet (finiteThickSlabSConnectionEvent d n L x y) :=
  measurableSet_connectionEventWithinVertices d _ x y

theorem measurableSet_finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    MeasurableSet (finiteThickSlabTConnectionEvent d n L x y) :=
  measurableSet_connectionEventWithinVertices d _ x y

theorem isIncreasingEvent_finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    IsIncreasingEvent (finiteThickSlabSConnectionEvent d n L x y) :=
  isIncreasingEvent_connectionEventWithinVertices d _ x y

theorem isIncreasingEvent_finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    IsIncreasingEvent (finiteThickSlabTConnectionEvent d n L x y) :=
  isIncreasingEvent_connectionEventWithinVertices d _ x y

@[simp]
theorem finiteThickSlabSConnectionEvent_self {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L) :
    finiteThickSlabSConnectionEvent d n L x x = Set.univ := by
  ext ω
  constructor
  · exact fun _ ↦ Set.mem_univ ω
  · intro _
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using hx⟩

@[simp]
theorem finiteThickSlabTConnectionEvent_self {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L) :
    finiteThickSlabTConnectionEvent d n L x x = Set.univ := by
  ext ω
  constructor
  · exact fun _ ↦ Set.mem_univ ω
  · intro _
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using hx⟩

/-- Source-facing lower-bound package for the two conclusions (7.79)--(7.80). -/
def UniformFiniteSlabConnectionLowerBound
    (d : ℕ) (p : I) (L : ℕ) (δ : ℝ) : Prop :=
  (∀ n, 1 ≤ n → ∀ x ∈ finiteThickSlabSVertices d n L,
    ∀ y ∈ finiteThickSlabSVertices d n L,
      δ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y)) ∧
  (∀ n, 1 ≤ n → ∀ x ∈ finiteThickSlabTVertices d n L,
    ∀ y ∈ finiteThickSlabTVertices d n L,
      δ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabTConnectionEvent d n L x y))

/-! ### The corner box and the four events in (7.82) -/

/-- The finite corner box `U_m(L) = [0,m]² × [0,L]^(d-2)`. -/
noncomputable def slabCornerBoxVertices (d m L : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin (max m L)).filter fun x ↦
    ∀ i : Fin d,
      if i.val < 2 then 0 ≤ x i ∧ x i ≤ m else 0 ≤ x i ∧ x i ≤ L

@[simp]
theorem mem_slabCornerBoxVertices_iff {d m L : ℕ} {x : Cubic d} :
    x ∈ slabCornerBoxVertices d m L ↔
      ∀ i : Fin d,
        if i.val < 2 then 0 ≤ x i ∧ x i ≤ m else 0 ≤ x i ∧ x i ≤ L := by
  classical
  rw [slabCornerBoxVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicMetricBox]
    intro i
    simp only [cubicOrigin, zero_sub, zero_add]
    have hi := h i
    split at hi
    · have hmmax : (m : ℤ) ≤ (max m L : ℕ) := by
        exact_mod_cast Nat.le_max_left m L
      constructor <;> omega
    · have hLmax : (L : ℤ) ≤ (max m L : ℕ) := by
        exact_mod_cast Nat.le_max_right m L
      constructor <;> omega

/-- The four planar corners `x₁₃,x₃₂,x₂₄,x₄₁`, in cyclic order. -/
def slabCornerVertex (d m : ℕ) (k : Fin 4) : Cubic d := fun i ↦
  if i.val = 0 then
    if k.val = 1 ∨ k.val = 2 then m else 0
  else if i.val = 1 then
    if k.val = 2 ∨ k.val = 3 then m else 0
  else 0

theorem slabCornerVertex_mem (d m L : ℕ) (k : Fin 4) :
    slabCornerVertex d m k ∈ slabCornerBoxVertices d m L := by
  rw [mem_slabCornerBoxVertices_iff]
  intro i
  simp only [slabCornerVertex]
  split_ifs <;> omega

/-- The target face paired with a corner in the four events of (7.82): right, top, left,
bottom, respectively. -/
noncomputable def slabCornerTargetFace
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) : Finset (Cubic d) :=
  (slabCornerBoxVertices d m L).filter fun x ↦
    if k.val = 0 then x ⟨0, by omega⟩ = m
    else if k.val = 1 then x ⟨1, hd⟩ = m
    else if k.val = 2 then x ⟨0, by omega⟩ = 0
    else x ⟨1, hd⟩ = 0

theorem slabCornerTargetFace_subset
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) :
    slabCornerTargetFace d hd m L k ⊆ slabCornerBoxVertices d m L :=
  Finset.filter_subset _ _

/-- One of the four corner-to-opposite-face connection events in (7.82). -/
def slabCornerConnectionEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) : Set (EdgeConfiguration d) :=
  ⋃ y ∈ slabCornerTargetFace d hd m L k,
    connectionEventWithinVertices d (slabCornerBoxVertices d m L : Set (Cubic d))
      (slabCornerVertex d m k) y

theorem measurableSet_slabCornerConnectionEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) :
    MeasurableSet (slabCornerConnectionEvent d hd m L k) :=
  (slabCornerTargetFace d hd m L k).measurableSet_biUnion fun y _hy ↦
    measurableSet_connectionEventWithinVertices d _ _ y

theorem isIncreasingEvent_slabCornerConnectionEvent
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) :
    IsIncreasingEvent (slabCornerConnectionEvent d hd m L k) := by
  intro ω η hωη hω
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hyFace, hconn⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyFace,
    isIncreasingEvent_connectionEventWithinVertices d _ _ y hωη hconn⟩⟩

/-- Simultaneous occurrence of all four events in (7.82). -/
def allSlabCornerConnectionEvents
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ k ∈ (Finset.univ : Finset (Fin 4)), slabCornerConnectionEvent d hd m L k

theorem measurableSet_allSlabCornerConnectionEvents
    (d : ℕ) (hd : 2 ≤ d) (m L : ℕ) :
    MeasurableSet (allSlabCornerConnectionEvents d hd m L) :=
  (Finset.univ : Finset (Fin 4)).measurableSet_biInter fun k _hk ↦
    measurableSet_slabCornerConnectionEvent d hd m L k

/-- Iterated FKG for the four corner events, the measure-theoretic content of (7.82). -/
theorem prod_slabCornerConnectionProbabilities_le_all
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) :
    (∏ k : Fin 4, (bernoulliBondMeasure d p).real
      (slabCornerConnectionEvent d hd m L k)) ≤
        (bernoulliBondMeasure d p).real
          (allSlabCornerConnectionEvents d hd m L) := by
  simpa [allSlabCornerConnectionEvents] using
    bernoulliBondMeasure_prod_le_real_biInter_fkg' p
      (J := (Finset.univ : Finset (Fin 4)))
      (fun k _hk ↦ isIncreasingEvent_slabCornerConnectionEvent d hd m L k)
      (fun k _hk ↦ measurableSet_slabCornerConnectionEvent d hd m L k)

/-- If each of the four events has probability at least `δ`, their intersection has probability
at least `δ⁴`.  Taking `δ=θ/2` gives the displayed lower bound (7.82). -/
theorem slabCornerConnection_lowerBound_pow_four
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p).real
      (slabCornerConnectionEvent d hd m L k)) :
    δ ^ 4 ≤ (bernoulliBondMeasure d p).real
      (allSlabCornerConnectionEvents d hd m L) := by
  calc
    δ ^ 4 = ∏ _k : Fin 4, δ := by simp
    _ ≤ ∏ k : Fin 4, (bernoulliBondMeasure d p).real
        (slabCornerConnectionEvent d hd m L k) := by
      exact Finset.prod_le_prod (fun _ _ ↦ hδ) (fun k _ ↦ hprob k)
    _ ≤ (bernoulliBondMeasure d p).real
        (allSlabCornerConnectionEvents d hd m L) :=
      prod_slabCornerConnectionProbabilities_le_all d hd p m L

/-- All four distinguished corners belong to one open cluster inside `U_m(L)`. -/
def allSlabCornersConnectedEvent
    (d m L : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ k ∈ (Finset.univ : Finset (Fin 4)),
    connectionEventWithinVertices d (slabCornerBoxVertices d m L : Set (Cubic d))
      (slabCornerVertex d m ⟨0, by decide⟩) (slabCornerVertex d m k)

theorem measurableSet_allSlabCornersConnectedEvent
    (d m L : ℕ) :
    MeasurableSet (allSlabCornersConnectedEvent d m L) :=
  (Finset.univ : Finset (Fin 4)).measurableSet_biInter fun _k _hk ↦
    measurableSet_connectionEventWithinVertices d _ _ _

theorem isIncreasingEvent_allSlabCornersConnectedEvent
    (d m L : ℕ) :
    IsIncreasingEvent (allSlabCornersConnectedEvent d m L) := by
  intro ω η hωη hω
  simp only [allSlabCornersConnectedEvent, Set.mem_iInter] at hω ⊢
  intro k hk
  exact isIncreasingEvent_connectionEventWithinVertices d _ _ _ hωη (hω k hk)

/-- Fixed-edge finite-energy repair.  If an increasing event `A`, together with opening every
edge of a fixed finite set `E`, forces `B`, then `P(A) p^|E| ≤ P(B)`.  The path-dependent repair
in (7.83) needs an additional finite-energy distance argument; this lemma deliberately does not
pretend that Grimmett's random repair set is fixed. -/
theorem bernoulliBondMeasure_real_mul_pow_card_le_of_inter_openEdgeSet_subset
    {d : ℕ} (p : I) {A B : Set (EdgeConfiguration d)} (E : Finset (CubicEdge d))
    (hAinc : IsIncreasingEvent A) (hAm : MeasurableSet A)
    (hsub : A ∩ openEdgeSetEvent d E ⊆ B) :
    (bernoulliBondMeasure d p).real A * (p : ℝ) ^ E.card ≤
      (bernoulliBondMeasure d p).real B := by
  calc
    (bernoulliBondMeasure d p).real A * (p : ℝ) ^ E.card =
        (bernoulliBondMeasure d p).real A *
          (bernoulliBondMeasure d p).real (openEdgeSetEvent d E) := by
      rw [bernoulliBondMeasure_real_openEdgeSetEvent]
    _ ≤ (bernoulliBondMeasure d p).real (A ∩ openEdgeSetEvent d E) :=
      bernoulliBondMeasure_real_fkg p hAinc
        (by intro ω η hωη hω e he; exact hωη (hω he)) hAm
        (measurableSet_openEdgeSetEvent d E)
    _ ≤ (bernoulliBondMeasure d p).real B :=
      measureReal_mono hsub (measure_ne_top _ _)

/-- Fixed-bridge consequence of (7.82).  This is the probability algebra in (7.83) once a
single repair set is supplied; the source's path-dependent bounded repair remains a separate
geometric/finite-energy obligation. -/
theorem slabCornersConnected_probability_ge_of_fixedBridge
    (d : ℕ) (hd : 2 ≤ d) (p : I) (m L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p).real
      (slabCornerConnectionEvent d hd m L k))
    (E : Finset (CubicEdge d))
    (hbridge : allSlabCornerConnectionEvents d hd m L ∩ openEdgeSetEvent d E ⊆
      allSlabCornersConnectedEvent d m L) :
    δ ^ 4 * (p : ℝ) ^ E.card ≤
      (bernoulliBondMeasure d p).real
        (allSlabCornersConnectedEvent d m L) := by
  calc
    δ ^ 4 * (p : ℝ) ^ E.card ≤
        (bernoulliBondMeasure d p).real
            (allSlabCornerConnectionEvents d hd m L) * (p : ℝ) ^ E.card := by
      exact mul_le_mul_of_nonneg_right
        (slabCornerConnection_lowerBound_pow_four d hd p m L hδ hprob)
        (pow_nonneg p.2.1 _)
    _ ≤ (bernoulliBondMeasure d p).real
        (allSlabCornersConnectedEvent d m L) :=
      bernoulliBondMeasure_real_mul_pow_card_le_of_inter_openEdgeSet_subset p E
        (by
          intro ω η hωη hω
          simp only [allSlabCornerConnectionEvents, Set.mem_iInter] at hω ⊢
          intro k hk
          exact isIncreasingEvent_slabCornerConnectionEvent d hd m L k hωη (hω k hk))
        (measurableSet_allSlabCornerConnectionEvents d hd m L) hbridge

/-- Path-dependent finite-energy consequence of (7.82), using the exact upward-distance
inequality (2.49).  Once the geometric inclusion is proved with
`K = 4 * (d - 2) * L`, this is the probability estimate (7.83). -/
theorem slabCornersConnected_probability_ge_of_boundedRepair
    (d : ℕ) (hd : 2 ≤ d) {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂)
    (m L K : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ k : Fin 4, δ ≤ (bernoulliBondMeasure d p₁).real
      (slabCornerConnectionEvent d hd m L k))
    (hrepair : allSlabCornerConnectionEvents d hd m L ⊆
      upwardDistanceAtMost K (allSlabCornersConnectedEvent d m L)) :
    (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ K * δ ^ 4 ≤
      (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) := by
  let c : ℝ := (((p₂ : ℝ) - p₁) / (1 - (p₁ : ℝ))) ^ K
  have hc : 0 ≤ c := by
    apply pow_nonneg
    exact div_nonneg (sub_nonneg.mpr h12.le) (sub_nonneg.mpr p₁.2.2)
  have hA := slabCornerConnection_lowerBound_pow_four d hd p₁ m L hδ hprob
  have hmono : (bernoulliBondMeasure d p₁).real
      (allSlabCornerConnectionEvents d hd m L) ≤
      (bernoulliBondMeasure d p₁).real
        (upwardDistanceAtMost K (allSlabCornersConnectedEvent d m L)) :=
    measureReal_mono hrepair (measure_ne_top _ _)
  calc
    c * δ ^ 4 ≤ c * (bernoulliBondMeasure d p₁).real
        (allSlabCornerConnectionEvents d hd m L) :=
      mul_le_mul_of_nonneg_left hA hc
    _ ≤ c * (bernoulliBondMeasure d p₁).real
        (upwardDistanceAtMost K (allSlabCornersConnectedEvent d m L)) :=
      mul_le_mul_of_nonneg_left hmono hc
    _ ≤ (bernoulliBondMeasure d p₂).real
        (allSlabCornersConnectedEvent d m L) := by
      simpa [c] using
        (isIncreasingEvent_allSlabCornersConnectedEvent d m L).bernoulliBondMeasure_real_upwardDistanceAtMost_le
          (measurableSet_allSlabCornersConnectedEvent d m L) h12 K

/-! ### Quantitative transverse lifts of projected intersections -/

/-- Bounded upward repairs for two within-region connections compose additively.  Both repair
sets are selected from the original configuration; their union is still disjoint from it, and
increasingness of walk openness lets both witnesses live in the union repair. -/
theorem mem_upwardDistanceAtMost_connectionWithinVertices_trans
    {d r s : ℕ} {A : Set (Cubic d)} {x y z : Cubic d} {ω : EdgeConfiguration d}
    (hxy : ω ∈ upwardDistanceAtMost r (connectionEventWithinVertices d A x y))
    (hyz : ω ∈ upwardDistanceAtMost s (connectionEventWithinVertices d A y z)) :
    ω ∈ upwardDistanceAtMost (r + s) (connectionEventWithinVertices d A x z) := by
  classical
  rcases hxy with ⟨D, hDcard, hDdisj, p, hpopen, hpA⟩
  rcases hyz with ⟨E, hEcard, hEdisj, q, hqopen, hqA⟩
  refine ⟨D ∪ E, (Finset.card_union_le D E).trans (Nat.add_le_add hDcard hEcard), ?_,
    p.append q, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro e he heω
    rw [Finset.mem_coe, Finset.mem_union] at he
    rcases he with heD | heE
    · exact Set.disjoint_left.mp hDdisj (Finset.mem_coe.mpr heD) heω
    · exact Set.disjoint_left.mp hEdisj (Finset.mem_coe.mpr heE) heω
  · apply walkIsOpen_append
    · intro e he
      rcases hpopen e he with heω | heD
      · exact Or.inl heω
      · exact Or.inr (Finset.mem_coe.mpr
          (Finset.mem_union_left E (Finset.mem_coe.mp heD)))
    · intro e he
      rcases hqopen e he with heω | heE
      · exact Or.inl heω
      · exact Or.inr (Finset.mem_coe.mpr
          (Finset.mem_union_right D (Finset.mem_coe.mp heE)))
  · intro u hu
    rw [SimpleGraph.Walk.mem_support_append_iff] at hu
    exact hu.elim (hpA u) (hqA u)

/-- Two vertices of `U_m(L)` with the same first two coordinates are at Manhattan distance at
most `(d-2)L`. -/
theorem cubicL1Dist_le_sub_two_mul_of_mem_slabCorner_of_agree_first_two
    {d m L : ℕ} (hd : 2 ≤ d) {u v : Cubic d}
    (hu : u ∈ slabCornerBoxVertices d m L)
    (hv : v ∈ slabCornerBoxVertices d m L)
    (hagrees : ∀ i : Fin d, i.val < 2 → u i = v i) :
    cubicL1Dist u v ≤ (d - 2) * L := by
  classical
  rw [cubicL1Dist]
  calc
    (∑ i : Fin d, (v i - u i).natAbs) ≤
        ∑ i : Fin d, if i.val < 2 then 0 else L := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : i.val < 2
      · simp [hi, hagrees i hi]
      · simp only [hi, ↓reduceIte]
        have hui := mem_slabCornerBoxVertices_iff.mp hu i
        have hvi := mem_slabCornerBoxVertices_iff.mp hv i
        rw [if_neg hi] at hui hvi
        apply Int.ofNat_le.mp
        rw [Int.natCast_natAbs, abs_le]
        constructor <;> omega
    _ = (d - 2) * L := by
      have hlt : ((Finset.univ : Finset (Fin d)).filter
          fun i ↦ i.val < 2).card = 2 := by
        have h := Fin.card_filter_val_lt (n := d) (m := 2)
        simpa [Nat.min_eq_right hd] using h
      have hge : ((Finset.univ : Finset (Fin d)).filter
          fun i ↦ ¬ i.val < 2).card = d - 2 := by
        have hpartition := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin d))) (p := fun i ↦ i.val < 2)
        simp only [hlt, Finset.card_univ, Fintype.card_fin] at hpartition
        omega
      rw [show (∑ i : Fin d, if i.val < 2 then 0 else L) =
          ∑ i ∈ (Finset.univ : Finset (Fin d)).filter (fun i ↦ ¬ i.val < 2), L by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hi : i.val < 2 <;> simp [hi]]
      rw [Finset.sum_const, nsmul_eq_mul, hge]
      simp

/-- A projected intersection can be lifted inside `U_m(L)` by a self-avoiding transverse walk
of length at most `(d-2)L`. -/
theorem exists_transverse_cubicPath_in_slabCorner
    {d m L : ℕ} (hd : 2 ≤ d) {u v : Cubic d}
    (hu : u ∈ slabCornerBoxVertices d m L)
    (hv : v ∈ slabCornerBoxVertices d m L)
    (hagrees : ∀ i : Fin d, i.val < 2 → u i = v i) :
    ∃ w : (cubicGraph d).Walk u v,
      w.IsPath ∧ w.length ≤ (d - 2) * L ∧
        ∀ z ∈ w.support, z ∈ slabCornerBoxVertices d m L := by
  obtain ⟨w, hwlen, hwbetween⟩ :=
    exists_cubicWalk_length_eq_l1Dist_support_between d u v
  let q : (cubicGraph d).Walk u v := w.toPath
  have hqlen : q.length ≤ w.length := by
    simpa [q, SimpleGraph.Walk.toPath] using SimpleGraph.Walk.length_bypass_le w
  refine ⟨q, by simp [q], hqlen.trans (hwlen.trans_le
    (cubicL1Dist_le_sub_two_mul_of_mem_slabCorner_of_agree_first_two
      hd hu hv hagrees)), ?_⟩
  intro z hz
  have hzbetween := hwbetween z (w.support_toPath_subset hz)
  rw [mem_slabCornerBoxVertices_iff]
  intro i
  have hui := mem_slabCornerBoxVertices_iff.mp hu i
  have hvi := mem_slabCornerBoxVertices_iff.mp hv i
  by_cases hi : i.val < 2
  · rw [if_pos hi] at hui hvi ⊢
    rcases hzbetween i with hzbetween | hzbetween <;> omega
  · rw [if_neg hi] at hui hvi ⊢
    rcases hzbetween i with hzbetween | hzbetween <;> omega

/-- Opening at most `(d-2)L` currently closed transverse bonds joins two lifted vertices whose
first two coordinates agree.  This is the local repair used at each projected planar
intersection in the proof of (7.83). -/
theorem mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_agree_first_two
    {d m L : ℕ} (hd : 2 ≤ d) {u v : Cubic d}
    (hu : u ∈ slabCornerBoxVertices d m L)
    (hv : v ∈ slabCornerBoxVertices d m L)
    (hagrees : ∀ i : Fin d, i.val < 2 → u i = v i)
    (ω : EdgeConfiguration d) :
    ω ∈ upwardDistanceAtMost ((d - 2) * L)
      (connectionEventWithinVertices d
        (slabCornerBoxVertices d m L : Set (Cubic d)) u v) := by
  classical
  obtain ⟨w, hwPath, hwlen, hwsupport⟩ :=
    exists_transverse_cubicPath_in_slabCorner hd hu hv hagrees
  let D : Finset (CubicEdge d) := (walkEdgeFinset w).filter fun e ↦ e ∉ ω
  refine ⟨D, ?_, ?_, ?_⟩
  · calc
      D.card ≤ (walkEdgeFinset w).card := Finset.card_filter_le _ _
      _ = w.length := walkEdgeFinset_card_of_isTrail hwPath.isTrail
      _ ≤ (d - 2) * L := hwlen
  · rw [Set.disjoint_left]
    intro e heD heω
    exact (Finset.mem_filter.mp (Finset.mem_coe.mp heD)).2 heω
  · refine ⟨w, ?_, hwsupport⟩
    intro e he
    let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
    have heE : e' ∈ walkEdgeFinset w := (mem_walkEdgeFinset_iff w e').mpr he
    by_cases heω : e' ∈ ω
    · exact Or.inl heω
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨heE, heω⟩))

/-- If two open slab-corner walks meet after projection to the first two coordinates, opening at
most `(d-2)L` transverse edges joins their starting vertices.  This is the exact two-path merge
operation used four times in Figure 7.14. -/
theorem mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_projected_inter
    {d m L : ℕ} (hd : 2 ≤ d) {x₁ y₁ x₂ y₂ : Cubic d}
    (w₁ : (cubicGraph d).Walk x₁ y₁) (w₂ : (cubicGraph d).Walk x₂ y₂)
    (hw₁A : ∀ z ∈ w₁.support, z ∈ slabCornerBoxVertices d m L)
    (hw₂A : ∀ z ∈ w₂.support, z ∈ slabCornerBoxVertices d m L)
    (hinter : ∃ z, z ∈ (projectCubicWalkFirstTwo hd w₁).support ∧
      z ∈ (projectCubicWalkFirstTwo hd w₂).support)
    (ω : EdgeConfiguration d) (hw₁open : walkIsOpen ω w₁)
    (hw₂open : walkIsOpen ω w₂) :
    ω ∈ upwardDistanceAtMost ((d - 2) * L)
      (connectionEventWithinVertices d
        (slabCornerBoxVertices d m L : Set (Cubic d)) x₁ x₂) := by
  have hinter' := (projectCubicWalkFirstTwo_support_inter_iff hd w₁ w₂).mp hinter
  obtain ⟨u, hu₁, v, hv₂, huv⟩ := hinter'
  have huA := hw₁A u hu₁
  have hvA := hw₂A v hv₂
  rcases mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_agree_first_two
      hd huA hvA huv ω with ⟨D, hDcard, hDdisj, q, hqopen, hqA⟩
  let p₁ := w₁.takeUntil u hu₁
  let p₂ := (w₂.takeUntil v hv₂).reverse
  have hp₁openω : walkIsOpen ω p₁ :=
    walkIsOpen_of_edges_subset hw₁open (w₁.edges_takeUntil_subset hu₁)
  have hp₂openω : walkIsOpen ω p₂ :=
    walkIsOpen_reverse
      (walkIsOpen_of_edges_subset hw₂open (w₂.edges_takeUntil_subset hv₂))
  have hp₁open : walkIsOpen (ω ∪ (D : Set (CubicEdge d))) p₁ := by
    intro e he
    exact Or.inl (hp₁openω e he)
  have hp₂open : walkIsOpen (ω ∪ (D : Set (CubicEdge d))) p₂ := by
    intro e he
    exact Or.inl (hp₂openω e he)
  refine ⟨D, hDcard, hDdisj, p₁.append (q.append p₂),
    walkIsOpen_append hp₁open (walkIsOpen_append hqopen hp₂open), ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz | hz
  · exact hw₁A z ((w₁.support_takeUntil_subset_support hu₁) hz)
  · exact hqA z hz
  · have hz' : z ∈ (w₂.takeUntil v hv₂).support := by
      simpa [p₂] using hz
    exact hw₂A z ((w₂.support_takeUntil_subset_support hv₂) hz')

/-- Three bounded repairs joining consecutive corners can be performed simultaneously.  The
same union repair witnesses all four root-to-corner connections, so repair costs are not
double-counted. -/
theorem mem_upwardDistanceAtMost_allSlabCornersConnectedEvent_of_chain
    {d m L K : ℕ} {ω : EdgeConfiguration d}
    (h01 : ω ∈ upwardDistanceAtMost K
      (connectionEventWithinVertices d (slabCornerBoxVertices d m L : Set (Cubic d))
        (slabCornerVertex d m ⟨0, by decide⟩) (slabCornerVertex d m ⟨1, by decide⟩)))
    (h12 : ω ∈ upwardDistanceAtMost K
      (connectionEventWithinVertices d (slabCornerBoxVertices d m L : Set (Cubic d))
        (slabCornerVertex d m ⟨1, by decide⟩) (slabCornerVertex d m ⟨2, by decide⟩)))
    (h23 : ω ∈ upwardDistanceAtMost K
      (connectionEventWithinVertices d (slabCornerBoxVertices d m L : Set (Cubic d))
        (slabCornerVertex d m ⟨2, by decide⟩) (slabCornerVertex d m ⟨3, by decide⟩))) :
    ω ∈ upwardDistanceAtMost (3 * K) (allSlabCornersConnectedEvent d m L) := by
  classical
  rcases h01 with ⟨D01, hD01card, hD01disj, p01, hp01open, hp01A⟩
  rcases h12 with ⟨D12, hD12card, hD12disj, p12, hp12open, hp12A⟩
  rcases h23 with ⟨D23, hD23card, hD23disj, p23, hp23open, hp23A⟩
  let D := (D01 ∪ D12) ∪ D23
  have hDcard : D.card ≤ 3 * K := by
    dsimp [D]
    calc
      ((D01 ∪ D12) ∪ D23).card ≤ (D01 ∪ D12).card + D23.card :=
        Finset.card_union_le _ _
      _ ≤ (D01.card + D12.card) + D23.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (K + K) + K := Nat.add_le_add (Nat.add_le_add hD01card hD12card) hD23card
      _ = 3 * K := by omega
  have hDdisj : Disjoint (D : Set (CubicEdge d)) ω := by
    rw [Set.disjoint_left]
    intro e heD heω
    have heD' : e ∈ (D01 ∪ D12) ∪ D23 := Finset.mem_coe.mp heD
    rcases Finset.mem_union.mp heD' with he0112 | he23
    · rcases Finset.mem_union.mp he0112 with he01 | he12
      · exact Set.disjoint_left.mp hD01disj (Finset.mem_coe.mpr he01) heω
      · exact Set.disjoint_left.mp hD12disj (Finset.mem_coe.mpr he12) heω
    · exact Set.disjoint_left.mp hD23disj (Finset.mem_coe.mpr he23) heω
  have hp01open' : walkIsOpen (ω ∪ (D : Set (CubicEdge d))) p01 := by
    intro e he
    rcases hp01open e he with heω | he01
    · exact Or.inl heω
    · exact Or.inr (Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_coe.mp he01))))
  have hp12open' : walkIsOpen (ω ∪ (D : Set (CubicEdge d))) p12 := by
    intro e he
    rcases hp12open e he with heω | he12
    · exact Or.inl heω
    · exact Or.inr (Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_coe.mp he12))))
  have hp23open' : walkIsOpen (ω ∪ (D : Set (CubicEdge d))) p23 := by
    intro e he
    rcases hp23open e he with heω | he23
    · exact Or.inl heω
    · exact Or.inr (Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_coe.mp he23)))
  refine ⟨D, hDcard, hDdisj, ?_⟩
  simp only [allSlabCornersConnectedEvent, Set.mem_iInter]
  intro k _hk
  fin_cases k
  · exact ⟨SimpleGraph.Walk.nil, by intro e he; simp at he, by
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact slabCornerVertex_mem d m L ⟨0, by decide⟩⟩
  · exact ⟨p01, hp01open', hp01A⟩
  · exact ⟨p01.append p12, walkIsOpen_append hp01open' hp12open', by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      exact hz.elim (hp01A z) (hp12A z)⟩
  · exact ⟨(p01.append p12).append p23,
      walkIsOpen_append (walkIsOpen_append hp01open' hp12open') hp23open', by
        intro z hz
        rw [SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.mem_support_append_iff] at hz
        exact hz.elim (fun hz' ↦ hz'.elim (hp01A z) (hp12A z)) (hp23A z)⟩

/-- Figure 7.14 reduced to its three projected-intersection obligations.  Consecutive projected
walks are repaired transversely and the repairs are united without double counting.  The proof
actually costs `3(d-2)L`; the public conclusion retains Grimmett's stated `4(d-2)L` bound. -/
theorem mem_upwardDistanceAtMost_allSlabCornersConnectedEvent_of_projected_chain
    {d m L : ℕ} (hd : 2 ≤ d) {y₀ y₁ y₂ y₃ : Cubic d}
    (w₀ : (cubicGraph d).Walk (slabCornerVertex d m ⟨0, by decide⟩) y₀)
    (w₁ : (cubicGraph d).Walk (slabCornerVertex d m ⟨1, by decide⟩) y₁)
    (w₂ : (cubicGraph d).Walk (slabCornerVertex d m ⟨2, by decide⟩) y₂)
    (w₃ : (cubicGraph d).Walk (slabCornerVertex d m ⟨3, by decide⟩) y₃)
    (hw₀A : ∀ z ∈ w₀.support, z ∈ slabCornerBoxVertices d m L)
    (hw₁A : ∀ z ∈ w₁.support, z ∈ slabCornerBoxVertices d m L)
    (hw₂A : ∀ z ∈ w₂.support, z ∈ slabCornerBoxVertices d m L)
    (hw₃A : ∀ z ∈ w₃.support, z ∈ slabCornerBoxVertices d m L)
    (h01 : ∃ z, z ∈ (projectCubicWalkFirstTwo hd w₀).support ∧
      z ∈ (projectCubicWalkFirstTwo hd w₁).support)
    (h12 : ∃ z, z ∈ (projectCubicWalkFirstTwo hd w₁).support ∧
      z ∈ (projectCubicWalkFirstTwo hd w₂).support)
    (h23 : ∃ z, z ∈ (projectCubicWalkFirstTwo hd w₂).support ∧
      z ∈ (projectCubicWalkFirstTwo hd w₃).support)
    (ω : EdgeConfiguration d) (hw₀open : walkIsOpen ω w₀)
    (hw₁open : walkIsOpen ω w₁) (hw₂open : walkIsOpen ω w₂)
    (hw₃open : walkIsOpen ω w₃) :
    ω ∈ upwardDistanceAtMost (4 * ((d - 2) * L))
      (allSlabCornersConnectedEvent d m L) := by
  let K := (d - 2) * L
  have hrepair01 :=
    mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_projected_inter
      hd w₀ w₁ hw₀A hw₁A h01 ω hw₀open hw₁open
  have hrepair12 :=
    mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_projected_inter
      hd w₁ w₂ hw₁A hw₂A h12 ω hw₁open hw₂open
  have hrepair23 :=
    mem_upwardDistanceAtMost_connectionWithin_slabCorner_of_projected_inter
      hd w₂ w₃ hw₂A hw₃A h23 ω hw₂open hw₃open
  have hchain := mem_upwardDistanceAtMost_allSlabCornersConnectedEvent_of_chain
    (K := K) hrepair01 hrepair12 hrepair23
  apply upwardDistanceAtMost_mono_radius (A := allSlabCornersConnectedEvent d m L)
      (show 3 * K ≤ 4 * K by omega)
  simpa [K] using hchain

/-! ### Exact witness-level reduction of Figure 7.14 -/

/-- Concrete open-walk witness for one of the four corner-to-face events in (7.82). -/
structure SlabCornerConnectionWitness
    {d : ℕ} (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) (ω : EdgeConfiguration d) where
  target : Cubic d
  target_mem : target ∈ slabCornerTargetFace d hd m L k
  walk : (cubicGraph d).Walk (slabCornerVertex d m k) target
  isOpen : walkIsOpen ω walk
  support_subset : ∀ z ∈ walk.support, z ∈ slabCornerBoxVertices d m L

theorem mem_slabCornerConnectionEvent_iff_nonempty_witness
    {d : ℕ} (hd : 2 ≤ d) (m L : ℕ) (k : Fin 4) (ω : EdgeConfiguration d) :
    ω ∈ slabCornerConnectionEvent d hd m L k ↔
      Nonempty (SlabCornerConnectionWitness hd m L k ω) := by
  constructor
  · intro hω
    simp only [slabCornerConnectionEvent, Set.mem_iUnion] at hω
    obtain ⟨y, hy, hconn⟩ := hω
    obtain ⟨w, hwopen, hwbox⟩ := hconn
    exact ⟨⟨y, hy, w, hwopen, hwbox⟩⟩
  · rintro ⟨W⟩
    exact Set.mem_iUnion.mpr ⟨W.target,
      Set.mem_iUnion.mpr ⟨W.target_mem,
        ⟨W.walk, W.isOpen, W.support_subset⟩⟩⟩

/-- A simultaneous choice of the four open walks occurring in (7.82). -/
abbrev SlabCornerConnectionWitnessFamily
    {d : ℕ} (hd : 2 ≤ d) (m L : ℕ) (ω : EdgeConfiguration d) :=
  (k : Fin 4) → SlabCornerConnectionWitness hd m L k ω

/-- Membership in the four-event intersection supplies a concrete family of four walk
witnesses.  This removes all event-level and choice bookkeeping from the planar step. -/
theorem mem_allSlabCornerConnectionEvents_iff_nonempty_witnessFamily
    {d : ℕ} (hd : 2 ≤ d) (m L : ℕ) (ω : EdgeConfiguration d) :
    ω ∈ allSlabCornerConnectionEvents d hd m L ↔
      Nonempty (SlabCornerConnectionWitnessFamily hd m L ω) := by
  constructor
  · intro hω
    simp only [allSlabCornerConnectionEvents, Set.mem_iInter] at hω
    let W : SlabCornerConnectionWitnessFamily hd m L ω := fun k ↦
      Classical.choice ((mem_slabCornerConnectionEvent_iff_nonempty_witness
        hd m L k ω).mp (hω k (Finset.mem_univ k)))
    exact ⟨W⟩
  · rintro ⟨W⟩
    simp only [allSlabCornerConnectionEvents, Set.mem_iInter]
    intro k _hk
    exact (mem_slabCornerConnectionEvent_iff_nonempty_witness hd m L k ω).mpr ⟨W k⟩

/-- The three exact projected-support intersections depicted in Figure 7.14. -/
def SlabCornerConnectionWitnessFamily.HasProjectedChain
    {d : ℕ} {hd : 2 ≤ d} {m L : ℕ} {ω : EdgeConfiguration d}
    (W : SlabCornerConnectionWitnessFamily hd m L ω) : Prop :=
  (∃ z, z ∈ (projectCubicWalkFirstTwo hd (W ⟨0, by decide⟩).walk).support ∧
      z ∈ (projectCubicWalkFirstTwo hd (W ⟨1, by decide⟩).walk).support) ∧
  (∃ z, z ∈ (projectCubicWalkFirstTwo hd (W ⟨1, by decide⟩).walk).support ∧
      z ∈ (projectCubicWalkFirstTwo hd (W ⟨2, by decide⟩).walk).support) ∧
  (∃ z, z ∈ (projectCubicWalkFirstTwo hd (W ⟨2, by decide⟩).walk).support ∧
      z ∈ (projectCubicWalkFirstTwo hd (W ⟨3, by decide⟩).walk).support)

/-- Endpoint oracle: at zero planar scale all four projected walks have the same start, so the
projected-chain conclusion is automatic. -/
theorem SlabCornerConnectionWitnessFamily.hasProjectedChain_zero
    {d L : ℕ} {hd : 2 ≤ d} {ω : EdgeConfiguration d}
    (W : SlabCornerConnectionWitnessFamily hd 0 L ω) :
    W.HasProjectedChain := by
  let z : SquareVertex := fun _ ↦ 0
  have hz (k : Fin 4) :
      cubicFirstTwoProjection hd (slabCornerVertex d 0 k) = z := by
    ext i
    simp [z, cubicFirstTwoProjection, cubicRestrict, slabCornerVertex]
  have hmem (k : Fin 4) :
      z ∈ (projectCubicWalkFirstTwo hd (W k).walk).support := by
    rw [← hz k]
    exact (projectCubicWalkFirstTwo hd (W k).walk).start_mem_support
  exact ⟨⟨z, hmem ⟨0, by decide⟩, hmem ⟨1, by decide⟩⟩,
    ⟨z, hmem ⟨1, by decide⟩, hmem ⟨2, by decide⟩⟩,
    ⟨z, hmem ⟨2, by decide⟩, hmem ⟨3, by decide⟩⟩⟩

/-- Once the pure planar projected-chain fact is supplied for the extracted witnesses, the
bounded transverse repair proves (7.83)'s deterministic inclusion with Grimmett's exact
`4(d-2)L` budget. -/
theorem SlabCornerConnectionWitnessFamily.mem_upwardDistanceAtMost_of_hasProjectedChain
    {d : ℕ} {hd : 2 ≤ d} {m L : ℕ} {ω : EdgeConfiguration d}
    (W : SlabCornerConnectionWitnessFamily hd m L ω)
    (hchain : W.HasProjectedChain) :
    ω ∈ upwardDistanceAtMost (4 * ((d - 2) * L))
      (allSlabCornersConnectedEvent d m L) := by
  rcases hchain with ⟨h01, h12, h23⟩
  exact mem_upwardDistanceAtMost_allSlabCornersConnectedEvent_of_projected_chain
    hd
    (W ⟨0, by decide⟩).walk
    (W ⟨1, by decide⟩).walk
    (W ⟨2, by decide⟩).walk
    (W ⟨3, by decide⟩).walk
    (W ⟨0, by decide⟩).support_subset
    (W ⟨1, by decide⟩).support_subset
    (W ⟨2, by decide⟩).support_subset
    (W ⟨3, by decide⟩).support_subset
    h01 h12 h23 ω
    (W ⟨0, by decide⟩).isOpen
    (W ⟨1, by decide⟩).isOpen
    (W ⟨2, by decide⟩).isOpen
    (W ⟨3, by decide⟩).isOpen

end Percolation
