import Percolation.Planar.SquareThresholdExact
import Percolation.Planar.CrossingMenger
import Percolation.Critical.StaticManyCrossings

/-!
# Many supercritical square-lattice crossings

This file proves the quantitative input to Grimmett, Lemma 11.22.  The lower-density
rectangle-crossing failure is identified, by the exact planar crossing alternative, with a
subcritical crossing probability.  Exponential subcritical radius decay and ACCFR sprinkling
then turn that estimate into an exponential lower-tail bound for the maximal number of
edge-disjoint crossings.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped unitInterval

/-- Grimmett's source rectangle is contained in the centered rectangle used by the reusable
finite Menger interface. -/
theorem grimmettRectangleCrossingEvent_subset_squareRectangleCrossingEvent (n : ℕ) :
    grimmettRectangleCrossingEvent n ⊆ squareRectangleCrossingEvent (n + 1) n := by
  intro ω hω
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion] at hω
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := hω
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
  have hx' : x ∈ squareRectangleLeft (n + 1) n := by
    rw [mem_squareRectangleLeft_iff]
    have h := mem_grimmettRectangleLeft_iff.mp hx
    exact ⟨h.1, by omega, h.2.2⟩
  have hy' : y ∈ squareRectangleRight (n + 1) n := by
    rw [mem_squareRectangleRight_iff]
    have h := mem_grimmettRectangleRight_iff.mp hy
    exact ⟨h.1, by omega, h.2.2⟩
  refine ⟨x, hx', y, hy', w, hwOpen, ?_⟩
  intro e he
  have heG := hwEdges he
  rw [squareRectangleEdges, Finset.mem_filter]
  rw [grimmettRectangleEdges, Finset.mem_filter] at heG
  refine ⟨?_, ?_, ?_⟩
  · simpa [Nat.max_eq_left (by omega : n ≤ n + 1)] using heG.1
  · have h := mem_grimmettRectangleVertices_iff.mp heG.2.1
    exact mem_squareRectangleVertices_iff.mpr ⟨h.1, h.2.1, by omega, h.2.2.2⟩
  · have h := mem_grimmettRectangleVertices_iff.mp heG.2.2
    exact mem_squareRectangleVertices_iff.mpr ⟨h.1, h.2.1, by omega, h.2.2.2⟩

structure OpenGrimmettRectangleCrossing (n : ℕ) (ω : EdgeConfiguration 2) where
  start : SquareVertex
  finish : SquareVertex
  walk : squareGraph.Walk start finish
  start_mem : start ∈ grimmettRectangleLeft n
  finish_mem : finish ∈ grimmettRectangleRight n
  isOpen : walkIsOpen ω walk
  edges_subset : walkEdgeFinset walk ⊆ grimmettRectangleEdges n

/-- Existence of `k` pairwise edge-disjoint crossings of the source rectangle. -/
def HasEdgeDisjointGrimmettRectangleCrossings
    (n k : ℕ) (ω : EdgeConfiguration 2) : Prop :=
  ∃ C : Fin k → OpenGrimmettRectangleCrossing n ω,
    Pairwise fun i j ↦
      Disjoint (walkEdgeFinset (C i).walk) (walkEdgeFinset (C j).walk)

theorem hasEdgeDisjointGrimmettRectangleCrossings_zero
    (n : ℕ) (ω : EdgeConfiguration 2) :
    HasEdgeDisjointGrimmettRectangleCrossings n 0 ω := by
  exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩

private theorem OpenGrimmettRectangleCrossing.start_ne_finish
    {n : ℕ} {ω : EdgeConfiguration 2} (C : OpenGrimmettRectangleCrossing n ω) :
    C.start ≠ C.finish := by
  intro h
  have hs := (mem_grimmettRectangleLeft_iff.mp C.start_mem).1
  have ht := (mem_grimmettRectangleRight_iff.mp C.finish_mem).1
  rw [h] at hs
  omega

private theorem OpenGrimmettRectangleCrossing.edgeFinset_nonempty
    {n : ℕ} {ω : EdgeConfiguration 2} (C : OpenGrimmettRectangleCrossing n ω) :
    (walkEdgeFinset C.walk).Nonempty := by
  have hn : ¬ C.walk.Nil := SimpleGraph.Walk.not_nil_of_ne C.start_ne_finish
  have hedges : C.walk.edges ≠ [] := SimpleGraph.Walk.edges_eq_nil.not.mpr hn
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil C.walk.edges hedges
  let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
  exact ⟨e', (mem_walkEdgeFinset_iff C.walk e').mpr he⟩

/-- Any disjoint family is bounded by the finite number of source-rectangle edges. -/
theorem hasEdgeDisjointGrimmettRectangleCrossings_le_edge_card
    {n k : ℕ} {ω : EdgeConfiguration 2}
    (h : HasEdgeDisjointGrimmettRectangleCrossings n k ω) :
    k ≤ (grimmettRectangleEdges n).card := by
  classical
  obtain ⟨C, hC⟩ := h
  let chosen : ∀ i : Fin k, SquareEdge := fun i ↦
    Classical.choose (C i).edgeFinset_nonempty
  have chosen_mem (i : Fin k) : chosen i ∈ walkEdgeFinset (C i).walk :=
    Classical.choose_spec (C i).edgeFinset_nonempty
  let f : Fin k → {e // e ∈ grimmettRectangleEdges n} := fun i ↦
    ⟨chosen i, (C i).edges_subset (chosen_mem i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hd := hC hne
    have heq : chosen i = chosen j := Subtype.ext_iff.mp hij
    exact Finset.disjoint_left.mp hd (chosen_mem i) (heq ▸ chosen_mem j)
  simpa [f] using Fintype.card_le_of_injective f hf

/-- Grimmett's `M_{n+1}`: the maximum number of edge-disjoint open left-right crossings of
`[0,n+1] × [0,n]`. -/
noncomputable def maxEdgeDisjointGrimmettRectangleCrossings
    (n : ℕ) (ω : EdgeConfiguration 2) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k ↦ HasEdgeDisjointGrimmettRectangleCrossings n k ω)
    (grimmettRectangleEdges n).card

theorem hasEdgeDisjointGrimmettRectangleCrossings_max
    (n : ℕ) (ω : EdgeConfiguration 2) :
    HasEdgeDisjointGrimmettRectangleCrossings n
      (maxEdgeDisjointGrimmettRectangleCrossings n ω) ω := by
  classical
  exact Nat.findGreatest_spec
    (P := fun k ↦ HasEdgeDisjointGrimmettRectangleCrossings n k ω)
    (m := 0) (Nat.zero_le _) (hasEdgeDisjointGrimmettRectangleCrossings_zero n ω)

theorem hasEdgeDisjointGrimmettRectangleCrossings_iff_le_max
    {n k : ℕ} (ω : EdgeConfiguration 2) :
    HasEdgeDisjointGrimmettRectangleCrossings n k ω ↔
      k ≤ maxEdgeDisjointGrimmettRectangleCrossings n ω := by
  classical
  constructor
  · intro hk
    exact Nat.le_findGreatest
      (hasEdgeDisjointGrimmettRectangleCrossings_le_edge_card hk) hk
  · intro hk
    obtain ⟨C, hC⟩ := hasEdgeDisjointGrimmettRectangleCrossings_max n ω
    let ι : Fin k → Fin (maxEdgeDisjointGrimmettRectangleCrossings n ω) :=
      Fin.castLE hk
    refine ⟨fun i ↦ C (ι i), ?_⟩
    intro i j hij
    apply hC
    intro heq
    exact hij (Fin.castLE_injective hk heq)

/-- The direct ACCFR estimate before optimizing the number of crossings. -/
theorem maxEdgeDisjointSquareRectangleCrossings_lowerTail_le
    {p₁ p₂ : I} (h₁₂ : (p₁ : ℝ) < p₂)
    {r n : ℕ} (hr : 1 ≤ r) :
    (bernoulliBondMeasure 2 p₂).real
        {ω | maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω ≤ r} ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ r *
        (1 - (bernoulliBondMeasure 2 p₁).real
          (squareRectangleCrossingEvent (n + 1) n)) := by
  exact bernoulliBondMeasure_real_maxCrossings_le_le h₁₂ hr (by omega)

/-! ## Finite-scale strictness -/

/-- The horizontal lattice walk along the row with second coordinate `y`. -/
private noncomputable def squareHorizontalRowWalk (m : ℕ) (y : ℤ) :
    squareGraph.Walk (squareVertex 0 y) (squareVertex m y) := by
  let steps : List (CubicDirection 2) := List.replicate m ((0 : Fin 2), true)
  let w := cubicWalkFrom (squareVertex 0 y) steps
  have hend : cubicEndpointFrom (squareVertex 0 y) steps = squareVertex m y := by
    dsimp [steps]
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i <;> simp [squareVertex]
  exact w.copy rfl hend

private theorem squareHorizontalRowWalk_support_second
    (m : ℕ) (y : ℤ) {z : SquareVertex}
    (hz : z ∈ (squareHorizontalRowWalk m y).support) : z 1 = y := by
  let steps : List (CubicDirection 2) := List.replicate m ((0 : Fin 2), true)
  have hz' : z ∈ cubicVerticesFrom (squareVertex 0 y) steps := by
    simpa [squareHorizontalRowWalk, steps] using hz
  simpa [squareVertex] using
    (cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex 0 y) (0 : Fin 2) (1 : Fin 2) m (by decide) hz')

private theorem squareHorizontalRowWalk_support_mem
    {m n : ℕ} {y : ℤ} (hy0 : 0 ≤ y) (hyn : y ≤ n) :
    ∀ z ∈ (squareHorizontalRowWalk m y).support,
      z ∈ squareRectangleVertices m n := by
  intro z hz
  let steps : List (CubicDirection 2) := List.replicate m ((0 : Fin 2), true)
  have hz' : z ∈ cubicVerticesFrom (squareVertex 0 y) steps := by
    simpa [squareHorizontalRowWalk, steps] using hz
  have hx := cubicVerticesFrom_replicate_pos_coord_between
    (squareVertex 0 y) (0 : Fin 2) m hz'
  have hy := squareHorizontalRowWalk_support_second m y hz
  rw [mem_squareRectangleVertices_iff]
  constructor
  · simpa [squareVertex] using hx.1
  constructor
  · simpa [squareVertex] using hx.2
  constructor <;> omega

/-- Opening every edge in the centered rectangle produces at least `n+1` disjoint horizontal
row crossings. -/
theorem openEdgeSetEvent_squareRectangle_subset_manyCrossings (n : ℕ) :
    openEdgeSetEvent 2 (squareRectangleEdges (n + 1) n) ⊆
      {ω | n + 1 ≤ maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω} := by
  intro ω hω
  apply (hasEdgeDisjointSquareRectangleCrossings_iff_le_max (by omega) ω).mp
  let C : Fin (n + 1) → OpenSquareRectangleCrossing (n + 1) n ω := fun i ↦
    { start := squareVertex 0 i
      finish := squareVertex (n + 1) i
      walk := squareHorizontalRowWalk (n + 1) i
      start_mem := by
        rw [mem_squareRectangleLeft_iff]
        simp [squareVertex]
        omega
      finish_mem := by
        rw [mem_squareRectangleRight_iff]
        simp [squareVertex]
        omega
      isOpen := by
        intro e he
        apply hω
        apply walkEdgeFinset_subset_squareRectangleEdges_of_support _
          (squareHorizontalRowWalk_support_mem (m := n + 1) (y := i) (by omega) (by omega))
        exact (mem_walkEdgeFinset_iff _ _).mpr he
      edges_subset := walkEdgeFinset_subset_squareRectangleEdges_of_support _
        (squareHorizontalRowWalk_support_mem (m := n + 1) (y := i) (by omega) (by omega)) }
  refine ⟨C, ?_⟩
  intro i j hij
  rw [Finset.disjoint_left]
  intro e hei hej
  have heI : e.1 ∈ (C i).walk.edges := (mem_walkEdgeFinset_iff _ _).mp hei
  have heJ : e.1 ∈ (C j).walk.edges := (mem_walkEdgeFinset_iff _ _).mp hej
  have hvi : e.1.out.1 ∈ (C i).walk.support :=
    (C i).walk.mem_support_of_mem_edges heI (Sym2.out_fst_mem e.1)
  have hvj : e.1.out.1 ∈ (C j).walk.support :=
    (C j).walk.mem_support_of_mem_edges heJ (Sym2.out_fst_mem e.1)
  have hi := squareHorizontalRowWalk_support_second (n + 1) i hvi
  have hj := squareHorizontalRowWalk_support_second (n + 1) j hvj
  exact hij (Fin.ext (by omega))

/-- At positive density, every finite lower-tail event which excludes all-open configurations
has probability strictly below one. -/
theorem maxEdgeDisjointSquareRectangleCrossings_lowerTail_lt_one
    {p : I} (hp : 0 < (p : ℝ)) {r n : ℕ} (hrn : r ≤ n) :
    (bernoulliBondMeasure 2 p).real
        {ω | maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω ≤ r} < 1 := by
  let E := squareRectangleEdges (n + 1) n
  have hsubset :
      {ω | maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω ≤ r} ⊆
        (openEdgeSetEvent 2 E)ᶜ := by
    intro ω hω hopen
    have hmany := openEdgeSetEvent_squareRectangle_subset_manyCrossings n hopen
    change maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω ≤ r at hω
    change n + 1 ≤ maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω at hmany
    omega
  have hm :
      (bernoulliBondMeasure 2 p).real
          {ω | maxEdgeDisjointSquareRectangleCrossings (n + 1) n ω ≤ r} ≤
        (bernoulliBondMeasure 2 p).real (openEdgeSetEvent 2 E)ᶜ :=
    measureReal_mono hsubset (measure_ne_top (bernoulliBondMeasure 2 p) _)
  have hEmeas : MeasurableSet (openEdgeSetEvent 2 E) :=
    measurableSet_openEdgeSetEvent 2 E
  rw [measureReal_compl hEmeas, probReal_univ,
    bernoulliBondMeasure_real_openEdgeSetEvent] at hm
  have hpow : 0 < (p : ℝ) ^ E.card := pow_pos hp E.card
  linarith

/-! ## Exponential optimization -/

private theorem tendsto_nat_succ_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * Real.exp (-c * (n + 1)))
      atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscale : Tendsto (fun n : ℕ ↦ c * (n + 1 : ℝ)) atTop atTop :=
    hcast.const_mul_atTop hc
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hmul : Tendsto
      (fun n : ℕ ↦ c⁻¹ * ((c * (n + 1 : ℝ)) ^ 1 * Real.exp (-(c * (n + 1)))))
      atTop (nhds (c⁻¹ * 0)) :=
    tendsto_const_nhds.mul hbase
  convert hmul using 1
  · funext n
    field_simp [hc.ne']
  · simp

/-- A finite list of probabilities, each strictly below one, admits one positive exponential
rate. -/
private theorem exists_finite_exponential_rate
    (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, 1 ≤ n → q n < 1) :
    ∀ N : ℕ, ∃ γ : ℝ, 0 < γ ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N →
      q n ≤ Real.exp (-γ * n) := by
  intro N
  induction N with
  | zero =>
      exact ⟨1, by norm_num, fun n hn hn0 ↦ by omega⟩
  | succ N ih =>
      obtain ⟨γ₀, hγ₀, hγ₀bound⟩ := ih
      by_cases hq : q (N + 1) = 0
      · let γ := min γ₀ 1
        refine ⟨γ, lt_min hγ₀ (by norm_num), ?_⟩
        intro n hn hnN
        by_cases hne : n = N + 1
        · subst n
          rw [hq]
          exact (Real.exp_pos _).le
        · have hnle : n ≤ N := by omega
          calc
            q n ≤ Real.exp (-γ₀ * n) := hγ₀bound n hn hnle
            _ ≤ Real.exp (-γ * n) := by
              apply Real.exp_le_exp.mpr
              have hmin : γ ≤ γ₀ := min_le_left _ _
              have hnnonneg : (0 : ℝ) ≤ n := by positivity
              nlinarith
      · have hqpos : 0 < q (N + 1) := lt_of_le_of_ne (hq0 (N + 1)) (Ne.symm hq)
        have hqlog : Real.log (q (N + 1)) < 0 :=
          (Real.log_neg hqpos (hq1 (N + 1) (by omega)))
        let γ₁ := -Real.log (q (N + 1)) / (N + 1 : ℝ)
        have hγ₁ : 0 < γ₁ := div_pos (neg_pos.mpr hqlog) (by positivity)
        let γ := min γ₀ γ₁
        refine ⟨γ, lt_min hγ₀ hγ₁, ?_⟩
        intro n hn hnN
        by_cases hne : n = N + 1
        · subst n
          have heq : Real.exp (-γ₁ * (N + 1 : ℝ)) = q (N + 1) := by
            rw [show -γ₁ * (N + 1 : ℝ) = Real.log (q (N + 1)) by
              dsimp [γ₁]
              field_simp]
            exact Real.exp_log hqpos
          have hbound : q (N + 1) ≤ Real.exp (-γ * (N + 1 : ℝ)) := by
            calc
              q (N + 1) = Real.exp (-γ₁ * (N + 1 : ℝ)) := heq.symm
              _ ≤ Real.exp (-γ * (N + 1 : ℝ)) := by
                apply Real.exp_le_exp.mpr
                have hmin : γ ≤ γ₁ := min_le_right _ _
                have hNnonneg : (0 : ℝ) ≤ N + 1 := by positivity
                nlinarith
          simpa only [Nat.cast_add, Nat.cast_one] using hbound
        · have hnle : n ≤ N := by omega
          calc
            q n ≤ Real.exp (-γ₀ * n) := hγ₀bound n hn hnle
            _ ≤ Real.exp (-γ * n) := by
              apply Real.exp_le_exp.mpr
              have hmin : γ ≤ γ₀ := min_le_left _ _
              have hnnonneg : (0 : ℝ) ≤ n := by positivity
              nlinarith

/-- An eventual exponential bound plus strict finite-scale bounds can be made uniform at every
positive integer scale. -/
private theorem exists_uniform_exponential_rate
    (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, 1 ≤ n → q n < 1)
    {a : ℝ} (ha : 0 < a)
    (htail : ∀ᶠ n : ℕ in atTop, q n ≤ Real.exp (-a * n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ n : ℕ, 1 ≤ n → q n ≤ Real.exp (-γ * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  obtain ⟨γ₀, hγ₀, hfinite⟩ := exists_finite_exponential_rate q hq0 hq1 N
  let γ := min γ₀ a
  refine ⟨γ, lt_min hγ₀ ha, ?_⟩
  intro n hn
  by_cases hnN : n ≤ N
  · calc
      q n ≤ Real.exp (-γ₀ * n) := hfinite n hn hnN
      _ ≤ Real.exp (-γ * n) := by
        apply Real.exp_le_exp.mpr
        have hmin : γ ≤ γ₀ := min_le_left _ _
        have hnnonneg : (0 : ℝ) ≤ n := by positivity
        nlinarith
  · calc
      q n ≤ Real.exp (-a * n) := hN n (by omega)
      _ ≤ Real.exp (-γ * n) := by
        apply Real.exp_le_exp.mpr
        have hmin : γ ≤ a := min_le_right _ _
        have hnnonneg : (0 : ℝ) ≤ n := by positivity
        nlinarith

end Percolation
