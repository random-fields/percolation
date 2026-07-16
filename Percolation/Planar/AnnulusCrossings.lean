import Percolation.Planar.IndependentBarriers
import Percolation.Critical.BoxRadius

/-!
# Square-annulus radial crossings

The annular events in this file use only edges whose two endpoints lie between the inner and
outer coordinate-box surfaces.  Geometrically separated annuli therefore have literally
disjoint Bernoulli coordinate supports, which is the independence input for the critical RSW
argument.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Square-lattice edges whose two endpoints have `L∞` radius between `inner` and `outer`. -/
noncomputable def squareAnnulusEdges (inner outer : ℕ) : Finset SquareEdge :=
  (cubicBoxEdges 2 cubicOrigin outer).filter fun e ↦
    inner ≤ cubicLInfDist cubicOrigin e.1.out.1 ∧
      inner ≤ cubicLInfDist cubicOrigin e.1.out.2

theorem mem_squareAnnulusEdges_iff {inner outer : ℕ} {e : SquareEdge} :
    e ∈ squareAnnulusEdges inner outer ↔
      e ∈ cubicBoxEdges 2 cubicOrigin outer ∧
        inner ≤ cubicLInfDist cubicOrigin e.1.out.1 ∧
        inner ≤ cubicLInfDist cubicOrigin e.1.out.2 := by
  classical
  simp [squareAnnulusEdges]

/-- An open radial crossing from the inner to the outer surface of a square annulus. -/
def squareAnnulusRadialCrossingEvent (inner outer : ℕ) :
    Set (EdgeConfiguration 2) :=
  ⋃ x ∈ cubicBoxSurface 2 cubicOrigin inner,
    ⋃ y ∈ cubicBoxSurface 2 cubicOrigin outer,
      connectionEventIn 2 (squareAnnulusEdges inner outer) x y

theorem dependsOn_squareAnnulusRadialCrossingEvent (inner outer : ℕ) :
    DependsOn (squareAnnulusEdges inner outer)
      (squareAnnulusRadialCrossingEvent inner outer) := by
  intro ω η hωη
  simp only [squareAnnulusRadialCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareAnnulusEdges inner outer) x y hωη).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareAnnulusEdges inner outer) x y hωη).mpr hxy⟩

theorem measurableSet_squareAnnulusRadialCrossingEvent (inner outer : ℕ) :
    MeasurableSet (squareAnnulusRadialCrossingEvent inner outer) :=
  (dependsOn_squareAnnulusRadialCrossingEvent inner outer).measurableSet

theorem isIncreasingEvent_squareAnnulusRadialCrossingEvent (inner outer : ℕ) :
    IsIncreasingEvent (squareAnnulusRadialCrossingEvent inner outer) := by
  intro ω η hωη
  simp only [squareAnnulusRadialCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2 (squareAnnulusEdges inner outer) x y hωη hxy⟩

/-- Failure of a radial open crossing is the finite decreasing barrier event used below. -/
def squareAnnulusBarrierEvent (inner outer : ℕ) : Set (EdgeConfiguration 2) :=
  (squareAnnulusRadialCrossingEvent inner outer)ᶜ

theorem dependsOn_squareAnnulusBarrierEvent (inner outer : ℕ) :
    DependsOn (squareAnnulusEdges inner outer)
      (squareAnnulusBarrierEvent inner outer) :=
  (dependsOn_squareAnnulusRadialCrossingEvent inner outer).compl

theorem measurableSet_squareAnnulusBarrierEvent (inner outer : ℕ) :
    MeasurableSet (squareAnnulusBarrierEvent inner outer) :=
  (dependsOn_squareAnnulusBarrierEvent inner outer).measurableSet

theorem isDecreasingEvent_squareAnnulusBarrierEvent (inner outer : ℕ) :
    IsDecreasingEvent (squareAnnulusBarrierEvent inner outer) :=
  (isIncreasingEvent_squareAnnulusRadialCrossingEvent inner outer).compl

/-- Annular edge supports are disjoint when the first outer radius lies strictly below the
second inner radius. -/
theorem disjoint_squareAnnulusEdges_of_outer_lt_inner
    {inner₁ outer₁ inner₂ outer₂ : ℕ} (hsep : outer₁ < inner₂) :
    Disjoint (squareAnnulusEdges inner₁ outer₁ : Set SquareEdge)
      (squareAnnulusEdges inner₂ outer₂ : Set SquareEdge) := by
  rw [Set.disjoint_left]
  intro e he₁ he₂
  have he₁' := mem_squareAnnulusEdges_iff.mp he₁
  have he₂' := mem_squareAnnulusEdges_iff.mp he₂
  have houtBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
    he₁'.1 (Sym2.out_fst_mem e.1)
  have hout : cubicLInfDist cubicOrigin e.1.out.1 ≤ outer₁ :=
    mem_cubicMetricBox_iff_lInfDist_le.mp houtBox
  have hin : inner₂ ≤ cubicLInfDist cubicOrigin e.1.out.1 := he₂'.2.1
  omega

set_option maxHeartbeats 800000 in
/-- Every infinite origin cluster crosses each nondegenerate square annulus.  The witness is the
segment after the last exit from the inner box and before the first hit of the outer surface, so
all of its edges lie in the literal annular support. -/
theorem hasInfiniteOpenCluster_mem_squareAnnulusRadialCrossingEvent
    {inner outer : ℕ} (hio : inner < outer)
    {omega : EdgeConfiguration 2} (hinfinite : hasInfiniteOpenCluster 2 omega) :
    omega ∈ squareAnnulusRadialCrossingEvent inner outer := by
  classical
  have hcluster : (cubicOpenClusterFrom 2 omega cubicOrigin).Infinite := hinfinite
  obtain ⟨far, hfarCluster, hfarOutside⟩ :=
    hcluster.exists_notMem_finset (cubicMetricBox 2 cubicOrigin outer)
  have hfarDist : outer ≤ cubicLInfDist cubicOrigin far := by
    apply le_of_lt
    exact lt_of_not_ge fun hle ↦
      hfarOutside (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
  obtain ⟨w, hwOpen⟩ := hfarCluster
  obtain ⟨y, hySurface, q, hqOpen, hqEdges⟩ :=
    exists_open_walk_to_cubicBoxSurface_in_box w hwOpen hfarDist
  have hqSupport : ∀ z ∈ q.support, z ∈ cubicMetricBox 2 cubicOrigin outer :=
    walk_support_subset_cubicMetricBox_of_edges
      (by simp) q hqEdges
  let r := q.reverse
  have hexit : ∃ k : ℕ,
      k ≤ r.length ∧ cubicLInfDist cubicOrigin (r.getVert k) ≤ inner := by
    refine ⟨r.length, le_rfl, ?_⟩
    change cubicLInfDist cubicOrigin (q.reverse.getVert q.reverse.length) ≤ inner
    rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.getVert_reverse]
    simp
  let k := Nat.find hexit
  have hk : k ≤ r.length ∧
      cubicLInfDist cubicOrigin (r.getVert k) ≤ inner := Nat.find_spec hexit
  have hkne : k ≠ 0 := by
    intro hkzero
    have hstart : r.getVert k = y := by simp [hkzero, r]
    have hyDist : cubicLInfDist cubicOrigin y = outer :=
      mem_cubicBoxSurface.mp hySurface
    rw [hstart, hyDist] at hk
    omega
  let j := k - 1
  have hksucc : k = j + 1 := by omega
  have hjlt : j < k := by omega
  have hjlen : j < r.length := hjlt.trans_le hk.1
  have hjOutside : inner < cubicLInfDist cubicOrigin (r.getVert j) := by
    apply lt_of_not_ge
    intro hjInside
    exact Nat.find_min hexit hjlt ⟨hjlen.le, hjInside⟩
  have hadj := r.adj_getVert_succ hjlen
  have hstep : cubicLInfDist (r.getVert j) (r.getVert (j + 1)) ≤ 1 := by
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
    rw [ha]
    exact cubicLInfDist_stepFrom_le_one _ _
  have hprevLe : cubicLInfDist cubicOrigin (r.getVert j) ≤
      cubicLInfDist cubicOrigin (r.getVert (j + 1)) + 1 := by
    have hstep' : cubicLInfDist (r.getVert (j + 1)) (r.getVert j) ≤ 1 := by
      rw [cubicLInfDist_comm]
      exact hstep
    exact (cubicLInfDist_triangle cubicOrigin (r.getVert (j + 1)) (r.getVert j)).trans
      (Nat.add_le_add_left hstep' _)
  have hkDist : cubicLInfDist cubicOrigin (r.getVert k) = inner := by
    rw [hksucc] at hk ⊢
    omega
  let segment := r.take k
  have hsegmentLength : segment.length = k := by
    simp [segment, Nat.min_eq_left hk.1]
  have hsegmentBounds : ∀ z ∈ segment.support,
      inner ≤ cubicLInfDist cubicOrigin z ∧
        cubicLInfDist cubicOrigin z ≤ outer := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨m, hm, hmle⟩ := hz
    subst z
    have hmk : m ≤ k := by omega
    have hget : segment.getVert m = r.getVert m := by
      simp [segment, Nat.min_eq_right hmk]
    rw [hget]
    constructor
    · by_cases hmk' : m = k
      · simpa [hmk'] using hkDist.ge
      · have hmlt : m < k := lt_of_le_of_ne hmk hmk'
        exact le_of_lt (lt_of_not_ge fun hmInside ↦
          Nat.find_min hexit hmlt ⟨(hmle.trans_eq hsegmentLength).trans hk.1, hmInside⟩)
    · have hrMem : r.getVert m ∈ r.support := r.getVert_mem_support m
      have hqMem : r.getVert m ∈ q.support := by
        change q.reverse.getVert m ∈ q.reverse.support at hrMem
        rw [SimpleGraph.Walk.support_reverse] at hrMem
        exact List.mem_reverse.mp hrMem
      exact mem_cubicMetricBox_iff_lInfDist_le.mp (hqSupport _ hqMem)
  let radial : squareGraph.Walk (r.getVert k) y :=
    segment.reverse.copy (by simp) rfl
  have hradialOpen : walkIsOpen omega radial := by
    apply (walkIsOpen_copy segment.reverse
      (by simp) rfl).mpr
    exact walkIsOpen_reverse (walkIsOpen_take r (walkIsOpen_reverse hqOpen) k)
  have hradialSupport : ∀ z ∈ radial.support,
      inner ≤ cubicLInfDist cubicOrigin z ∧
        cubicLInfDist cubicOrigin z ≤ outer := by
    intro z hz
    have hz' : z ∈ segment.reverse.support := by simpa [radial] using hz
    rw [SimpleGraph.Walk.support_reverse] at hz'
    exact hsegmentBounds z (List.mem_reverse.mp hz')
  simp only [squareAnnulusRadialCrossingEvent, Set.mem_iUnion]
  refine ⟨r.getVert k, mem_cubicBoxSurface.mpr hkDist, y, hySurface,
    radial, hradialOpen, ?_⟩
  have houterEdges : walkEdgeFinset radial ⊆ cubicBoxEdges 2 cubicOrigin outer :=
    walkEdgeFinset_subset_cubicBoxEdges_of_support radial
      (fun z hz ↦ mem_cubicMetricBox_iff_lInfDist_le.mpr (hradialSupport z hz).2)
  intro e he
  rw [mem_squareAnnulusEdges_iff]
  refine ⟨houterEdges he, ?_, ?_⟩
  · exact (hradialSupport e.1.out.1
      (radial.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff radial e).mp he)
        (Sym2.out_fst_mem e.1))).1
  · exact (hradialSupport e.1.out.2
      (radial.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff radial e).mp he)
        (Sym2.out_snd_mem e.1))).1

private theorem three_mul_four_pow_lt_four_pow {i j : ℕ} (hij : i < j) :
    3 * 4 ^ i < 4 ^ j := by
  have hpos : 0 < 4 ^ i := Nat.pow_pos (by omega)
  calc
    3 * 4 ^ i < 4 * 4 ^ i := by omega
    _ = 4 ^ (i + 1) := by rw [pow_succ]; omega
    _ ≤ 4 ^ j := Nat.pow_le_pow_right (by omega) (by omega)

/-- The scale-`k` annulus used for the critical barrier argument is `B(3·4^k) \ B(4^k)`. -/
noncomputable def criticalAnnulusEdges (k : ℕ) : Finset SquareEdge :=
  squareAnnulusEdges (4 ^ k) (3 * 4 ^ k)

/-- Critical geometric annuli have pairwise-disjoint edge supports. -/
theorem pairwiseDisjoint_criticalAnnulusEdges :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) criticalAnnulusEdges := by
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · simpa [criticalAnnulusEdges] using
      (disjoint_squareAnnulusEdges_of_outer_lt_inner
        (inner₁ := 4 ^ i) (outer₁ := 3 * 4 ^ i)
        (inner₂ := 4 ^ j) (outer₂ := 3 * 4 ^ j)
        (three_mul_four_pow_lt_four_pow hij'))
  · simpa [criticalAnnulusEdges] using
      (disjoint_squareAnnulusEdges_of_outer_lt_inner
        (inner₁ := 4 ^ j) (outer₁ := 3 * 4 ^ j)
        (inner₂ := 4 ^ i) (outer₂ := 3 * 4 ^ i)
        (three_mul_four_pow_lt_four_pow hji')).symm

/-- The scale-`k` critical radial-crossing event. -/
def criticalAnnulusRadialCrossingEvent (k : ℕ) : Set (EdgeConfiguration 2) :=
  squareAnnulusRadialCrossingEvent (4 ^ k) (3 * 4 ^ k)

/-- The scale-`k` critical barrier event. -/
def criticalAnnulusBarrierEvent (k : ℕ) : Set (EdgeConfiguration 2) :=
  squareAnnulusBarrierEvent (4 ^ k) (3 * 4 ^ k)

theorem dependsOn_criticalAnnulusBarrierEvent (k : ℕ) :
    DependsOn (criticalAnnulusEdges k) (criticalAnnulusBarrierEvent k) :=
  dependsOn_squareAnnulusBarrierEvent _ _

/-- The critical barrier events are mutually independent under every Bernoulli bond density. -/
theorem iIndepSet_criticalAnnulusBarrierEvent (p : I) :
    iIndepSet criticalAnnulusBarrierEvent (bernoulliBondMeasure 2 p) :=
  bernoulliBondMeasure_iIndepSet_of_pairwiseDisjoint_dependsOn p
    criticalAnnulusEdges criticalAnnulusBarrierEvent
    dependsOn_criticalAnnulusBarrierEvent pairwiseDisjoint_criticalAnnulusEdges

/-- An infinite origin cluster crosses every critical annulus and hence avoids every critical
barrier. -/
theorem hasInfiniteOpenCluster_subset_iInter_criticalAnnulusBarrierEvent_compl :
    {omega : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 omega} ⊆
      ⋂ k, (criticalAnnulusBarrierEvent k)ᶜ := by
  intro omega hinfinite
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro k hbarrier
  have hpow : 0 < 4 ^ k := Nat.pow_pos (by omega)
  have hcross := hasInfiniteOpenCluster_mem_squareAnnulusRadialCrossingEvent
    (inner := 4 ^ k) (outer := 3 * 4 ^ k) (by omega) hinfinite
  exact hbarrier hcross

/-- A scale-uniform positive lower bound for the critical annular barriers implies Grimmett,
Lemma 11.12.  RSW and self-duality provide the lower bound in the planar layer. -/
theorem theta_two_eq_zero_of_criticalAnnulusBarrier_probability
    (p : I) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hprob : ∀ k,
      δ ≤ (bernoulliBondMeasure 2 p).real (criticalAnnulusBarrierEvent k)) :
    theta 2 p = 0 := by
  apply theta_eq_zero_of_iIndep_barriers p criticalAnnulusBarrierEvent
    (fun k ↦ (dependsOn_criticalAnnulusBarrierEvent k).measurableSet)
    (iIndepSet_criticalAnnulusBarrierEvent p) hδ0 hδ1 hprob
  exact hasInfiniteOpenCluster_subset_iInter_criticalAnnulusBarrierEvent_compl

end Percolation
