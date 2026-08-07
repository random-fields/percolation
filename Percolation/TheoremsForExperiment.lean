import Percolation.Extensions.MixedPercolation
import Percolation.Core.CubicWalkLevel
import Percolation.Planar.CriticalSelfDuality
import Percolation.Planar.Inhomogeneous
import Percolation.Planar.RSWNumeric
import Percolation.Planar.TriangularPeierlsProbability

/-!
# Theorem statements for the percolation experiment

This module collects three source-facing theorem targets requested for an experiment. Existing
square-lattice and RSW definitions are reused; the homogeneous triangular model and
Duminil-Copin's asymmetric rectangle are named here because those exact source objects did not
yet have dedicated APIs.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ## Grimmett, Theorem 3.7 -/

/-- Homogeneous Bernoulli bond percolation on the triangular lattice `T`, obtained by assigning
the same density to its horizontal, vertical, and north-east diagonal bonds. -/
noncomputable def triangularBondMeasure (p : I) : Measure TriangularConfiguration :=
  inhomogeneousTriangularBondMeasure p p p

/-- The probability that the origin cluster is infinite in homogeneous triangular-lattice bond
percolation. -/
noncomputable def triangularTheta (p : I) : ℝ :=
  (triangularBondMeasure p).real {omega | (triangularOpenCluster omega).Infinite}

/-- The bond critical probability of the triangular lattice, using Grimmett's supremum
normalization `sup {p : theta(p) = 0}`. -/
noncomputable def triangularCriticalProbability : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | triangularTheta p = 0}) : Set ℝ)

private theorem inhomogeneousTriangularEdgeDensity_self (p : I) :
    inhomogeneousTriangularEdgeDensity p p p = fun _ : TriangularEdge ↦ p := by
  funext e
  simp [inhomogeneousTriangularEdgeDensity]

private theorem inhomogeneousTriangularBondMeasure_self_eq_setBernoulli (p : I) :
    inhomogeneousTriangularBondMeasure p p p =
      setBernoulli (Set.univ : Set TriangularEdge) p := by
  rw [inhomogeneousTriangularBondMeasure, inhomogeneousTriangularEdgeDensity_self,
    inhomogeneousSetBernoulli_const]

private theorem triangularOpenGraph_eq_mixedOpenGraph_all_sites
    (bonds : TriangularConfiguration) :
    triangularOpenGraph bonds = mixedOpenGraph triangularGraph (Set.univ, bonds) := by
  ext x y
  simp only [triangularOpenGraph, mixedOpenGraph, Set.mem_univ, true_and]

private theorem triangularOpenCluster_eq_mixedOpenCluster_all_sites
    (bonds : TriangularConfiguration) :
    triangularOpenCluster bonds =
      mixedOpenCluster triangularGraph (Set.univ, bonds) cubicOrigin := by
  ext x
  simp only [triangularOpenCluster, mixedOpenCluster, Set.mem_setOf_eq]
  rw [← triangularOpenGraph_eq_mixedOpenGraph_all_sites bonds]
  rfl

private theorem inhomogeneousTriangularTheta_self_eq_mixedTheta (p : I) :
    inhomogeneousTriangularTheta p p p =
      mixedTheta triangularGraph cubicOrigin (1 : I) p := by
  let A : Set (MixedConfiguration triangularGraph) :=
    {omega | (mixedOpenCluster triangularGraph omega cubicOrigin).Infinite}
  have hA : MeasurableSet A :=
    measurableSet_infinite_mixedOpenCluster triangularGraph cubicOrigin
  have hpre :
      (fun bonds : TriangularConfiguration ↦
        ((Set.univ : Set SquareVertex), bonds)) ⁻¹' A =
        {bonds | (triangularOpenCluster bonds).Infinite} := by
    ext bonds
    simpa [A] using
      (congrArg Set.Infinite
        (triangularOpenCluster_eq_mixedOpenCluster_all_sites bonds)).symm
  unfold mixedTheta mixedPercolationMeasure
  rw [setBernoulli_one, Measure.dirac_prod]
  rw [Measure.real, Measure.map_apply (by fun_prop) hA, hpre]
  rw [inhomogeneousTriangularTheta,
    inhomogeneousTriangularBondMeasure_self_eq_setBernoulli]
  rfl

private theorem triangularTheta_mono : Monotone triangularTheta := by
  intro p q hpq
  change inhomogeneousTriangularTheta p p p ≤ inhomogeneousTriangularTheta q q q
  rw [inhomogeneousTriangularTheta_self_eq_mixedTheta p,
    inhomogeneousTriangularTheta_self_eq_mixedTheta q]
  exact mixedTheta_mono triangularGraph cubicOrigin le_rfl hpq

private theorem triangularTheta_zero : triangularTheta (0 : I) = 0 := by
  change inhomogeneousTriangularTheta (0 : I) (0 : I) (0 : I) = 0
  rw [inhomogeneousTriangularTheta_self_eq_mixedTheta]
  exact mixedTheta_bond_zero triangularGraph cubicOrigin (1 : I)

private theorem triangularTheta_subhalf_pos :
    0 < triangularTheta triangularPeierlsSubhalfDensity := by
  exact inhomogeneousTriangularBondMeasure_real_originInfinite_pos_subhalf

/-- **Grimmett, Percolation (2nd ed.), Theorem 3.7.**  The bond critical probability of the
triangular lattice is strictly smaller than that of the square lattice. -/
theorem grimmett_theorem_3_7 :
    triangularCriticalProbability < cubicCriticalProbability 2 := by
  let Z : Set ℝ :=
    (fun p : I ↦ (p : ℝ)) '' {p : I | triangularTheta p = 0}
  have hZne : Z.Nonempty := by
    exact ⟨0, ⟨(0 : I), triangularTheta_zero, rfl⟩⟩
  have hpc_le : triangularCriticalProbability ≤ (499 / 1000 : ℝ) := by
    rw [triangularCriticalProbability]
    apply csSup_le hZne
    rintro q ⟨p, hpzero, rfl⟩
    change triangularTheta p = 0 at hpzero
    by_contra hpnot
    have hpgt : (499 / 1000 : ℝ) < (p : ℝ) := lt_of_not_ge hpnot
    have hsub_le : triangularPeierlsSubhalfDensity ≤ p := by
      apply Subtype.coe_le_coe.mp
      simpa [triangularPeierlsSubhalfDensity] using hpgt.le
    have hmono := triangularTheta_mono hsub_le
    linarith [triangularTheta_subhalf_pos]
  calc
    triangularCriticalProbability ≤ (499 / 1000 : ℝ) := hpc_le
    _ < (1 / 2 : ℝ) := by norm_num
    _ = cubicCriticalProbability 2 := cubicCriticalProbability_two_eq_half.symm

/-! ## Grimmett, Theorem 11.70 -/

/-- The explicit lower-bound expression in Grimmett's equation (11.71). -/
noncomputable def grimmettRSWLowerBound (tau : ℝ) : ℝ :=
  (tau * (1 - Real.sqrt (1 - tau)) ^ 4) ^ 12

/-- **Grimmett, Percolation (2nd ed.), Theorem 11.70 (RSW).**  If `tau` is the probability
of a left-right crossing of `B(l)`, then the probability of an open circuit in
`B(3l) \ B(l)` surrounding the origin is at least the quantity in equation (11.71). -/
theorem grimmett_theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) (tau : ℝ)
    (htau : rswSquareCrossingProbability p l = tau) :
    grimmettRSWLowerBound tau ≤ rswAnnulusOpenCircuitProbability p l := by
  subst tau
  unfold grimmettRSWLowerBound
  convert rswAnnulusOpenCircuitProbability_ge p l hl using 1
  ring

/-! ## Duminil-Copin, Proposition 2.14 -/

/-- The vertices of `[-n,n] × [-n,2n]` in the square lattice. -/
noncomputable def duminilCopinRectangleVertices (n : ℕ) : Finset SquareVertex :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).product
    (Finset.Icc (-(n : ℤ)) (2 * (n : ℤ)))).map squareVertexEmbedding

@[simp]
theorem mem_duminilCopinRectangleVertices_iff {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinRectangleVertices n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧
        -(n : ℤ) ≤ x 1 ∧ x 1 ≤ 2 * (n : ℤ) := by
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, habx⟩ := Finset.mem_map.mp hx
    have hab' := Finset.mem_product.mp hab
    have ha := Finset.mem_Icc.mp hab'.1
    have hb := Finset.mem_Icc.mp hab'.2
    have h0 : a = x 0 := by
      simpa [squareVertexEmbedding] using congrFun habx 0
    have h1 : b = x 1 := by
      simpa [squareVertexEmbedding] using congrFun habx 1
    simpa [h0, h1] using And.intro ha.1 (And.intro ha.2 hb)
  · rintro ⟨hx0, hx0', hx1, hx1'⟩
    refine Finset.mem_map.mpr ⟨(x 0, x 1), ?_, squareVertex_eta x⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hx0, hx0'⟩, Finset.mem_Icc.mpr ⟨hx1, hx1'⟩⟩

/-- The bottom side `[-n,n] × {-n}` of Duminil-Copin's rectangle. -/
noncomputable def duminilCopinRectangleBottom (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦ x 1 = -(n : ℤ)

@[simp]
theorem mem_duminilCopinRectangleBottom_iff {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinRectangleBottom n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ x 1 = -(n : ℤ) := by
  simp only [duminilCopinRectangleBottom, Finset.mem_filter,
    mem_duminilCopinRectangleVertices_iff]
  omega

/-- The top side `[-n,n] × {2n}` of Duminil-Copin's rectangle. -/
noncomputable def duminilCopinRectangleTop (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦ x 1 = 2 * (n : ℤ)

@[simp]
theorem mem_duminilCopinRectangleTop_iff {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinRectangleTop n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ x 1 = 2 * (n : ℤ) := by
  simp only [duminilCopinRectangleTop, Finset.mem_filter,
    mem_duminilCopinRectangleVertices_iff]
  omega

/-- All square-lattice bonds whose endpoints lie in `[-n,n] × [-n,2n]`. -/
noncomputable def duminilCopinRectangleEdges (n : ℕ) : Finset SquareEdge :=
  (cubicBoxEdges 2 cubicOrigin (2 * n)).filter fun e ↦
    e.1.out.1 ∈ duminilCopinRectangleVertices n ∧
      e.1.out.2 ∈ duminilCopinRectangleVertices n

theorem walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support
    {n : ℕ} {x y : SquareVertex} (w : squareGraph.Walk x y)
    (hrect : ∀ z ∈ w.support, z ∈ duminilCopinRectangleVertices n) :
    walkEdgeFinset w ⊆ duminilCopinRectangleEdges n := by
  classical
  have hbox : walkEdgeFinset w ⊆ cubicBoxEdges 2 cubicOrigin (2 * n) :=
    walkEdgeFinset_subset_cubicBoxEdges_of_support w fun z hz ↦ by
      rw [mem_cubicMetricBox]
      have hz' := mem_duminilCopinRectangleVertices_iff.mp (hrect z hz)
      intro i
      fin_cases i <;> simp [cubicOrigin] <;> omega
  intro e he
  rw [duminilCopinRectangleEdges, Finset.mem_filter]
  refine ⟨hbox he, ?_, ?_⟩
  · apply hrect e.1.out.1
    apply w.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff w e).mp he)
    exact Sym2.out_fst_mem e.1
  · apply hrect e.1.out.2
    apply w.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff w e).mp he)
    exact Sym2.out_snd_mem e.1

/-- The vertical open-crossing event `C_v([-n,n] × [-n,2n])`. -/
def duminilCopinVerticalCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ duminilCopinRectangleBottom n, ⋃ y ∈ duminilCopinRectangleTop n,
    connectionEventIn 2 (duminilCopinRectangleEdges n) x y

/-- The probability of Duminil-Copin's vertical rectangle-crossing event. -/
noncomputable def duminilCopinVerticalCrossingProbability (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (duminilCopinVerticalCrossingEvent n)

/-! ### Finite source events for the bridge proof -/

/-- The central square `[0,n] × [0,n]` in Proposition 2.14. -/
noncomputable def duminilCopinCentralSquareVertices (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ (n : ℤ)

@[simp]
private theorem mem_duminilCopinCentralSquareVertices_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinCentralSquareVertices n ↔
      0 ≤ x 0 ∧ x 0 ≤ n ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  simp only [duminilCopinCentralSquareVertices, Finset.mem_filter,
    mem_duminilCopinRectangleVertices_iff]
  omega

/-- Internal bonds of the central square. -/
noncomputable def duminilCopinCentralSquareEdges (n : ℕ) : Finset SquareEdge :=
  (duminilCopinRectangleEdges n).filter fun e ↦
    e.1.out.1 ∈ duminilCopinCentralSquareVertices n ∧
      e.1.out.2 ∈ duminilCopinCentralSquareVertices n

/-- Left side of the central square. -/
noncomputable def duminilCopinCentralSquareLeft (n : ℕ) : Finset SquareVertex :=
  (duminilCopinCentralSquareVertices n).filter fun x ↦ x 0 = 0

/-- Right side of the central square. -/
noncomputable def duminilCopinCentralSquareRight (n : ℕ) : Finset SquareVertex :=
  (duminilCopinCentralSquareVertices n).filter fun x ↦ x 0 = (n : ℤ)

/-- Bottom side of the central square. -/
noncomputable def duminilCopinCentralSquareBottom (n : ℕ) : Finset SquareVertex :=
  (duminilCopinCentralSquareVertices n).filter fun x ↦ x 1 = 0

/-- Top side of the central square. -/
noncomputable def duminilCopinCentralSquareTop (n : ℕ) : Finset SquareVertex :=
  (duminilCopinCentralSquareVertices n).filter fun x ↦ x 1 = (n : ℤ)

@[simp]
private theorem mem_duminilCopinCentralSquareLeft_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinCentralSquareLeft n ↔
      x 0 = 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  simp only [duminilCopinCentralSquareLeft, Finset.mem_filter,
    mem_duminilCopinCentralSquareVertices_iff]
  omega

@[simp]
private theorem mem_duminilCopinCentralSquareRight_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinCentralSquareRight n ↔
      x 0 = n ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  simp only [duminilCopinCentralSquareRight, Finset.mem_filter,
    mem_duminilCopinCentralSquareVertices_iff]
  omega

@[simp]
private theorem mem_duminilCopinCentralSquareBottom_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinCentralSquareBottom n ↔
      0 ≤ x 0 ∧ x 0 ≤ n ∧ x 1 = 0 := by
  simp only [duminilCopinCentralSquareBottom, Finset.mem_filter,
    mem_duminilCopinCentralSquareVertices_iff]
  omega

@[simp]
private theorem mem_duminilCopinCentralSquareTop_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinCentralSquareTop n ↔
      0 ≤ x 0 ∧ x 0 ≤ n ∧ x 1 = n := by
  simp only [duminilCopinCentralSquareTop, Finset.mem_filter,
    mem_duminilCopinCentralSquareVertices_iff]
  omega

/-- Internal bonds of the lower square `[-n,n]²`. -/
noncomputable def duminilCopinLowerSquareEdges (n : ℕ) : Finset SquareEdge :=
  (duminilCopinRectangleEdges n).filter fun e ↦
    e.1.out.1 1 ≤ (n : ℤ) ∧ e.1.out.2 1 ≤ (n : ℤ)

/-- The top side `[-n,n] × {n}` of the lower square. -/
noncomputable def duminilCopinLowerSquareTop (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦ x 1 = (n : ℤ)

@[simp]
private theorem mem_duminilCopinLowerSquareTop_iff
    {n : ℕ} {x : SquareVertex} :
    x ∈ duminilCopinLowerSquareTop n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ x 1 = (n : ℤ) := by
  simp only [duminilCopinLowerSquareTop, Finset.mem_filter,
    mem_duminilCopinRectangleVertices_iff]
  omega

/-- Internal bonds of the upper rectangle `[-n,n] × [0,2n]`. -/
noncomputable def duminilCopinUpperRectangleEdges (n : ℕ) : Finset SquareEdge :=
  (duminilCopinRectangleEdges n).filter fun e ↦
    0 ≤ e.1.out.1 1 ∧ 0 ≤ e.1.out.2 1

/-- A vertical crossing of the central square. -/
def duminilCopinCentralVerticalCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ duminilCopinCentralSquareBottom n,
    ⋃ y ∈ duminilCopinCentralSquareTop n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) x y

/-- A bottom-to-top crossing of the lower square `[-n,n]²`. -/
private def duminilCopinLowerSquareVerticalCrossingEvent
    (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ duminilCopinRectangleBottom n,
    ⋃ y ∈ duminilCopinLowerSquareTop n,
      connectionEventIn 2 (duminilCopinLowerSquareEdges n) x y

/-- A horizontal crossing of the central square. -/
private def duminilCopinCentralHorizontalCrossingEvent
    (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ duminilCopinCentralSquareLeft n,
    ⋃ y ∈ duminilCopinCentralSquareRight n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) x y

/-- The lower bridge `B_n`: a central-square cluster touches both horizontal sides and is
connected inside the lower square to the bottom side of the target rectangle. -/
def duminilCopinLowerBridgeEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ z ∈ duminilCopinCentralSquareVertices n,
    (⋃ b ∈ duminilCopinRectangleBottom n,
      connectionEventIn 2 (duminilCopinLowerSquareEdges n) b z) ∩
    (⋃ l ∈ duminilCopinCentralSquareLeft n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) l z) ∩
    (⋃ r ∈ duminilCopinCentralSquareRight n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) z r)

/-- The reflected upper bridge `\widetilde B_n`. -/
def duminilCopinUpperBridgeEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ z ∈ duminilCopinCentralSquareVertices n,
    (⋃ t ∈ duminilCopinRectangleTop n,
      connectionEventIn 2 (duminilCopinUpperRectangleEdges n) z t) ∩
    (⋃ l ∈ duminilCopinCentralSquareLeft n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) l z) ∩
    (⋃ r ∈ duminilCopinCentralSquareRight n,
      connectionEventIn 2 (duminilCopinCentralSquareEdges n) z r)

private theorem walkEdgeFinset_append_subset
    {u v w : SquareVertex} {p : squareGraph.Walk u v}
    {q : squareGraph.Walk v w} {E : Finset SquareEdge}
    (hp : walkEdgeFinset p ⊆ E) (hq : walkEdgeFinset q ⊆ E) :
    walkEdgeFinset (p.append q) ⊆ E := by
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  rcases he with he | he
  · exact hp ((mem_walkEdgeFinset_iff p e).mpr he)
  · exact hq ((mem_walkEdgeFinset_iff q e).mpr he)

private theorem exists_openSquareWalk_between_support
    {ω : EdgeConfiguration 2} {u v x y : SquareVertex}
    (w : squareGraph.Walk u v) (hwOpen : walkIsOpen ω w)
    (hx : x ∈ w.support) (hy : y ∈ w.support) :
    ∃ q : squareGraph.Walk x y,
      walkIsOpen ω q ∧ walkEdgeFinset q ⊆ walkEdgeFinset w := by
  let q := (w.takeUntil x hx).reverse.append (w.takeUntil y hy)
  refine ⟨q, ?_, ?_⟩
  · apply walkIsOpen_append
    · exact walkIsOpen_reverse
        (walkIsOpen_of_edges_subset hwOpen (w.edges_takeUntil_subset hx))
    · exact walkIsOpen_of_edges_subset hwOpen (w.edges_takeUntil_subset hy)
  · apply walkEdgeFinset_append_subset
    · intro e he
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] at he
      exact (mem_walkEdgeFinset_iff w e).mpr (w.edges_takeUntil_subset hx he)
    · intro e he
      rw [mem_walkEdgeFinset_iff] at he
      exact (mem_walkEdgeFinset_iff w e).mpr (w.edges_takeUntil_subset hy he)

private theorem walk_support_mem_duminilCopinCentralSquare_of_edges
    {n : ℕ} {u v : SquareVertex} (hv : v ∈ duminilCopinCentralSquareVertices n)
    (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ duminilCopinCentralSquareEdges n) :
    ∀ z ∈ w.support, z ∈ duminilCopinCentralSquareVertices n := by
  classical
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hv
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    have heCentral : ee ∈ duminilCopinCentralSquareEdges n :=
      hw ((mem_walkEdgeFinset_iff w ee).mpr he)
    have hends := (Finset.mem_filter.mp heCentral).2
    change z ∈ (ee : Sym2 SquareVertex) at hze
    rw [← ee.1.out_eq, Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact hends.1
    · exact hends.2

private theorem measurableSet_duminilCopinCentralVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (duminilCopinCentralVerticalCrossingEvent n) := by
  apply (duminilCopinCentralSquareBottom n).measurableSet_biUnion
  intro x _hx
  apply (duminilCopinCentralSquareTop n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (duminilCopinCentralSquareEdges n) x y).measurableSet

private theorem measurableSet_duminilCopinLowerSquareVerticalCrossingEvent (n : ℕ) :
    MeasurableSet (duminilCopinLowerSquareVerticalCrossingEvent n) := by
  apply (duminilCopinRectangleBottom n).measurableSet_biUnion
  intro x _hx
  apply (duminilCopinLowerSquareTop n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (duminilCopinLowerSquareEdges n) x y).measurableSet

private theorem measurableSet_duminilCopinCentralHorizontalCrossingEvent (n : ℕ) :
    MeasurableSet (duminilCopinCentralHorizontalCrossingEvent n) := by
  apply (duminilCopinCentralSquareLeft n).measurableSet_biUnion
  intro x _hx
  apply (duminilCopinCentralSquareRight n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (duminilCopinCentralSquareEdges n) x y).measurableSet

private theorem measurableSet_duminilCopinLowerBridgeEvent (n : ℕ) :
    MeasurableSet (duminilCopinLowerBridgeEvent n) := by
  apply (duminilCopinCentralSquareVertices n).measurableSet_biUnion
  intro z _hz
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · apply (duminilCopinRectangleBottom n).measurableSet_biUnion
      intro b _hb
      exact (dependsOn_connectionEventIn 2
        (duminilCopinLowerSquareEdges n) b z).measurableSet
    · apply (duminilCopinCentralSquareLeft n).measurableSet_biUnion
      intro l _hl
      exact (dependsOn_connectionEventIn 2
        (duminilCopinCentralSquareEdges n) l z).measurableSet
  · apply (duminilCopinCentralSquareRight n).measurableSet_biUnion
    intro r _hr
    exact (dependsOn_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) z r).measurableSet

private theorem measurableSet_duminilCopinUpperBridgeEvent (n : ℕ) :
    MeasurableSet (duminilCopinUpperBridgeEvent n) := by
  apply (duminilCopinCentralSquareVertices n).measurableSet_biUnion
  intro z _hz
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · apply (duminilCopinRectangleTop n).measurableSet_biUnion
      intro t _ht
      exact (dependsOn_connectionEventIn 2
        (duminilCopinUpperRectangleEdges n) z t).measurableSet
    · apply (duminilCopinCentralSquareLeft n).measurableSet_biUnion
      intro l _hl
      exact (dependsOn_connectionEventIn 2
        (duminilCopinCentralSquareEdges n) l z).measurableSet
  · apply (duminilCopinCentralSquareRight n).measurableSet_biUnion
    intro r _hr
    exact (dependsOn_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) z r).measurableSet

private theorem isIncreasingEvent_duminilCopinCentralVerticalCrossingEvent (n : ℕ) :
    IsIncreasingEvent (duminilCopinCentralVerticalCrossingEvent n) := by
  intro omega eta hmono
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) x y hmono hxy⟩

private theorem isIncreasingEvent_duminilCopinLowerSquareVerticalCrossingEvent (n : ℕ) :
    IsIncreasingEvent (duminilCopinLowerSquareVerticalCrossingEvent n) := by
  intro omega eta hmono
  simp only [duminilCopinLowerSquareVerticalCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (duminilCopinLowerSquareEdges n) x y hmono hxy⟩

private theorem isIncreasingEvent_duminilCopinCentralHorizontalCrossingEvent (n : ℕ) :
    IsIncreasingEvent (duminilCopinCentralHorizontalCrossingEvent n) := by
  intro omega eta hmono
  simp only [duminilCopinCentralHorizontalCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) x y hmono hxy⟩

private theorem isIncreasingEvent_duminilCopinLowerBridgeEvent (n : ℕ) :
    IsIncreasingEvent (duminilCopinLowerBridgeEvent n) := by
  intro omega eta hmono
  simp only [duminilCopinLowerBridgeEvent, Set.mem_iUnion, Set.mem_inter_iff]
  rintro ⟨z, hz, ⟨⟨b, hb, hbz⟩, l, hl, hlz⟩, r, hr, hzr⟩
  exact ⟨z, hz,
    ⟨⟨b, hb, isIncreasingEvent_connectionEventIn 2
      (duminilCopinLowerSquareEdges n) b z hmono hbz⟩,
      l, hl, isIncreasingEvent_connectionEventIn 2
        (duminilCopinCentralSquareEdges n) l z hmono hlz⟩,
    r, hr, isIncreasingEvent_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) z r hmono hzr⟩

private theorem isIncreasingEvent_duminilCopinUpperBridgeEvent (n : ℕ) :
    IsIncreasingEvent (duminilCopinUpperBridgeEvent n) := by
  intro omega eta hmono
  simp only [duminilCopinUpperBridgeEvent, Set.mem_iUnion, Set.mem_inter_iff]
  rintro ⟨z, hz, ⟨⟨t, ht, hzt⟩, l, hl, hlz⟩, r, hr, hzr⟩
  exact ⟨z, hz,
    ⟨⟨t, ht, isIncreasingEvent_connectionEventIn 2
      (duminilCopinUpperRectangleEdges n) z t hmono hzt⟩,
      l, hl, isIncreasingEvent_connectionEventIn 2
        (duminilCopinCentralSquareEdges n) l z hmono hlz⟩,
    r, hr, isIncreasingEvent_connectionEventIn 2
      (duminilCopinCentralSquareEdges n) z r hmono hzr⟩

/-! The exact half-probability Grimmett rectangle at index `n - 1` quarter-turns into a
vertical crossing of the central square. -/

private def duminilCopinCentralQuarterTurnIso : squareGraph ≃g squareGraph :=
  cubicCoordinatePermutationIso squareCoordinateSwap

@[simp]
private theorem duminilCopinCentralQuarterTurnIso_zero (x : SquareVertex) :
    duminilCopinCentralQuarterTurnIso x 0 = x 1 := by
  simp [duminilCopinCentralQuarterTurnIso, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv_apply, squareCoordinateSwap]

@[simp]
private theorem duminilCopinCentralQuarterTurnIso_one (x : SquareVertex) :
    duminilCopinCentralQuarterTurnIso x 1 = x 0 := by
  simp [duminilCopinCentralQuarterTurnIso, cubicCoordinatePermutationIso,
    cubicCoordinatePermutationEquiv_apply, squareCoordinateSwap]

private theorem duminilCopinCentralQuarterTurnIso_mem_centralSquare
    {n : ℕ} {x : SquareVertex}
    (hx : x ∈ duminilCopinCentralSquareVertices n) :
    duminilCopinCentralQuarterTurnIso x ∈
      duminilCopinCentralSquareVertices n := by
  rw [mem_duminilCopinCentralSquareVertices_iff] at hx ⊢
  simp only [duminilCopinCentralQuarterTurnIso_zero,
    duminilCopinCentralQuarterTurnIso_one]
  omega

private theorem duminilCopinCentralQuarterTurnIso_image_centralEdges_subset
    (n : ℕ) :
    (duminilCopinCentralSquareEdges n).image
        duminilCopinCentralQuarterTurnIso.mapEdgeSet ⊆
      duminilCopinCentralSquareEdges n := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  have hfEnds := (Finset.mem_filter.mp hf).2
  have hmapped : ∀ z ∈
      (duminilCopinCentralQuarterTurnIso.mapEdgeSet f : Sym2 SquareVertex),
      z ∈ duminilCopinCentralSquareVertices n := by
    intro z hz
    change z ∈ Sym2.map duminilCopinCentralQuarterTurnIso
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [← f.1.out_eq, Sym2.mem_iff] at hu
    apply duminilCopinCentralQuarterTurnIso_mem_centralSquare
    exact hu.elim (fun h ↦ h ▸ hfEnds.1) (fun h ↦ h ▸ hfEnds.2)
  rw [duminilCopinCentralSquareEdges, Finset.mem_filter]
  refine ⟨?_, hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
  rw [duminilCopinRectangleEdges, Finset.mem_filter]
  refine ⟨mem_cubicBoxEdges_of_endpoints ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_cubicMetricBox]
    have hz' := mem_duminilCopinCentralSquareVertices_iff.mp (hmapped z hz)
    intro i
    fin_cases i <;> simp [cubicOrigin] <;> omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_fst_mem _))
    omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_snd_mem _))
    omega

private theorem duminilCopinCentralQuarterTurnVerticalEvent_subset_horizontal
    (n : ℕ) :
    cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
        (duminilCopinCentralVerticalCrossingEvent n) ⊆
      duminilCopinCentralHorizontalCrossingEvent n := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinCentralQuarterTurnIso omega ∈
    duminilCopinCentralVerticalCrossingEvent n at homega
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, hxy⟩ := homega
  simp only [duminilCopinCentralHorizontalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinCentralQuarterTurnIso x, ?_,
    duminilCopinCentralQuarterTurnIso y, ?_, ?_⟩
  · rw [mem_duminilCopinCentralSquareLeft_iff]
    have hx' := mem_duminilCopinCentralSquareBottom_iff.mp hx
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  · rw [mem_duminilCopinCentralSquareRight_iff]
    have hy' := mem_duminilCopinCentralSquareTop_iff.mp hy
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  · apply connectionEventIn_mono
      (duminilCopinCentralQuarterTurnIso_image_centralEdges_subset n)
    exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      duminilCopinCentralQuarterTurnIso
      (duminilCopinCentralSquareEdges n) omega x y).mp hxy

private theorem duminilCopinCentralQuarterTurnIso_mem_square
    {n : ℕ} {x : SquareVertex} (hn : 1 ≤ n)
    (hx : x ∈ grimmettRectangleVertices (n - 1)) :
    duminilCopinCentralQuarterTurnIso x ∈ duminilCopinCentralSquareVertices n := by
  rw [mem_duminilCopinCentralSquareVertices_iff]
  have hx' := mem_grimmettRectangleVertices_iff.mp hx
  simp only [duminilCopinCentralQuarterTurnIso_zero,
    duminilCopinCentralQuarterTurnIso_one]
  omega

private theorem duminilCopinCentralQuarterTurnIso_image_edges_subset
    (n : ℕ) (hn : 1 ≤ n) :
    (grimmettRectangleEdges (n - 1)).image
        duminilCopinCentralQuarterTurnIso.mapEdgeSet ⊆
      duminilCopinCentralSquareEdges n := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [duminilCopinCentralSquareEdges, Finset.mem_filter]
  have hmapped : ∀ z ∈
      (duminilCopinCentralQuarterTurnIso.mapEdgeSet f : Sym2 SquareVertex),
      z ∈ duminilCopinCentralSquareVertices n := by
    intro z hz
    change z ∈ Sym2.map duminilCopinCentralQuarterTurnIso
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact duminilCopinCentralQuarterTurnIso_mem_square hn
      (endpoint_mem_grimmettRectangleVertices_of_edge_mem hf hu)
  refine ⟨?_, hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
  rw [duminilCopinRectangleEdges, Finset.mem_filter]
  refine ⟨mem_cubicBoxEdges_of_endpoints ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_cubicMetricBox]
    have hz' := mem_duminilCopinCentralSquareVertices_iff.mp (hmapped z hz)
    intro i
    fin_cases i <;> simp [cubicOrigin] <;> omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_fst_mem _))
    omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_snd_mem _))
    omega

private theorem duminilCopinCentralQuarterTurnEvent_subset
    (n : ℕ) (hn : 1 ≤ n) :
    cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
        (grimmettRectangleCrossingEvent (n - 1)) ⊆
      duminilCopinCentralVerticalCrossingEvent n := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinCentralQuarterTurnIso omega ∈
    grimmettRectangleCrossingEvent (n - 1) at homega
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, hxy⟩ := homega
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinCentralQuarterTurnIso x, ?_,
    duminilCopinCentralQuarterTurnIso y, ?_, ?_⟩
  · rw [mem_duminilCopinCentralSquareBottom_iff]
    have hx' := mem_grimmettRectangleLeft_iff.mp hx
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  · rw [mem_duminilCopinCentralSquareTop_iff]
    have hy' := mem_grimmettRectangleRight_iff.mp hy
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  · apply connectionEventIn_mono
      (duminilCopinCentralQuarterTurnIso_image_edges_subset n hn)
    exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      duminilCopinCentralQuarterTurnIso
      (grimmettRectangleEdges (n - 1)) omega x y).mp hxy

/-- At an even index, Grimmett's self-dual rectangle is one column wider than the central
square.  Stop a crossing at its first visit to the nearer column before applying the
quarter-turn. -/
private theorem duminilCopinCentralQuarterTurnEvenEvent_subset
    (k : ℕ) :
    cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
        (grimmettRectangleCrossingEvent (2 * k)) ⊆
      duminilCopinCentralVerticalCrossingEvent (2 * k) := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinCentralQuarterTurnIso omega ∈
    grimmettRectangleCrossingEvent (2 * k) at homega
  simp only [grimmettRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := homega
  have hxCoords := mem_grimmettRectangleLeft_iff.mp hx
  have hyCoords := mem_grimmettRectangleRight_iff.mp hy
  obtain ⟨z, q, hzLevel, hqSide, hqSupport, hqPrefix⟩ :=
    exists_cubicWalk_edgePrefix_to_level_of_le_end (G := squareGraph) le_rfl
      w (0 : Fin 2) (2 * (k : ℤ)) (by omega) (by omega)
  have hxRect : x ∈ grimmettRectangleVertices (2 * k) := by
    rw [mem_grimmettRectangleVertices_iff]
    omega
  have hwSupport : ∀ u ∈ w.support, u ∈ grimmettRectangleVertices (2 * k) :=
    walk_support_subset_grimmettRectangleVertices_of_edges hxRect w hwEdges
  let Q := q.map duminilCopinCentralQuarterTurnIso.toHom
  have hqOpen : walkIsOpen
      (cubicGraphIsoConfigurationPullback duminilCopinCentralQuarterTurnIso omega) q :=
    walkIsOpen_of_edges_subset hwOpen hqPrefix.subset
  have hQOpen : walkIsOpen omega Q :=
    walkIsOpen_map_cubicGraphIso duminilCopinCentralQuarterTurnIso q hqOpen
  have hQSupport : ∀ u ∈ Q.support,
      u ∈ duminilCopinCentralSquareVertices (2 * k) := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
    rw [mem_duminilCopinCentralSquareVertices_iff]
    have hvRect := mem_grimmettRectangleVertices_iff.mp
      (hwSupport v (hqSupport v hv))
    have hvSide := hqSide v hv
    change 0 ≤ duminilCopinCentralQuarterTurnIso v 0 ∧
      duminilCopinCentralQuarterTurnIso v 0 ≤ (2 * k : ℕ) ∧
      0 ≤ duminilCopinCentralQuarterTurnIso v 1 ∧
      duminilCopinCentralQuarterTurnIso v 1 ≤ (2 * k : ℕ)
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  have hQRectangle : walkEdgeFinset Q ⊆ duminilCopinRectangleEdges (2 * k) :=
    walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support Q fun u hu ↦ by
      rw [mem_duminilCopinRectangleVertices_iff]
      have hu' := mem_duminilCopinCentralSquareVertices_iff.mp (hQSupport u hu)
      omega
  have hQEdges : walkEdgeFinset Q ⊆ duminilCopinCentralSquareEdges (2 * k) := by
    intro e he
    rw [duminilCopinCentralSquareEdges, Finset.mem_filter]
    refine ⟨hQRectangle he, ?_, ?_⟩
    · apply hQSupport e.1.out.1
      apply Q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff Q e).mp he)
      exact Sym2.out_fst_mem e.1
    · apply hQSupport e.1.out.2
      apply Q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff Q e).mp he)
      exact Sym2.out_snd_mem e.1
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinCentralQuarterTurnIso x, ?_,
    duminilCopinCentralQuarterTurnIso z, ?_, Q, hQOpen, hQEdges⟩
  · rw [mem_duminilCopinCentralSquareBottom_iff]
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega
  · rw [mem_duminilCopinCentralSquareTop_iff]
    have hzRect := mem_grimmettRectangleVertices_iff.mp
      (hwSupport z (hqSupport z q.end_mem_support))
    simp only [duminilCopinCentralQuarterTurnIso_zero,
      duminilCopinCentralQuarterTurnIso_one]
    omega

private theorem half_le_duminilCopinCentralVerticalCrossingProbability
    (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (duminilCopinCentralVerticalCrossingEvent n) := by
  rcases n.even_or_odd' with ⟨k, hk | hk⟩
  · subst n
    have hkPos : 0 < k := by omega
    calc
      (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (grimmettRectangleCrossingEvent (2 * k)) :=
        half_le_grimmettRectangleCrossingProbability_even k hkPos
      _ = (bernoulliBondMeasure 2 squareHalfDensity).real
          (cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
            (grimmettRectangleCrossingEvent (2 * k))) := by
        rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
          duminilCopinCentralQuarterTurnIso
          (measurableSet_grimmettRectangleCrossingEvent (2 * k))]
      _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (duminilCopinCentralVerticalCrossingEvent (2 * k)) :=
        measureReal_mono (duminilCopinCentralQuarterTurnEvenEvent_subset k)
          (measure_ne_top _ _)
  · subst n
    have hkPos : 0 < k := by omega
    calc
      (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (grimmettRectangleCrossingEvent (2 * k)) :=
        half_le_grimmettRectangleCrossingProbability_even k hkPos
      _ = (bernoulliBondMeasure 2 squareHalfDensity).real
          (cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
            (grimmettRectangleCrossingEvent (2 * k))) := by
        rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
          duminilCopinCentralQuarterTurnIso
          (measurableSet_grimmettRectangleCrossingEvent (2 * k))]
      _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
          (duminilCopinCentralVerticalCrossingEvent (2 * k + 1)) := by
        apply measureReal_mono _ (measure_ne_top _ _)
        simpa using duminilCopinCentralQuarterTurnEvent_subset (2 * k + 1) (by omega)

/-! Translate the central square at scale `2n` to the lower square `[-n,n]²`.  This supplies
the exact-half full-square crossing input used by the Figure 2.3 contact argument. -/

private def duminilCopinCentralToLowerSquareIso (n : ℕ) :
    squareGraph ≃g squareGraph :=
  cubicTranslationIso cubicOrigin (squareVertex (-(n : ℤ)) (-(n : ℤ)))

@[simp]
private theorem duminilCopinCentralToLowerSquareIso_zero
    (n : ℕ) (x : SquareVertex) :
    duminilCopinCentralToLowerSquareIso n x 0 = x 0 - (n : ℤ) := by
  simp [duminilCopinCentralToLowerSquareIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex, sub_eq_add_neg]

@[simp]
private theorem duminilCopinCentralToLowerSquareIso_one
    (n : ℕ) (x : SquareVertex) :
    duminilCopinCentralToLowerSquareIso n x 1 = x 1 - (n : ℤ) := by
  simp [duminilCopinCentralToLowerSquareIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex, sub_eq_add_neg]

private theorem duminilCopinCentralToLowerSquareEvent_subset (n : ℕ) :
    cubicGraphIsoEvent (duminilCopinCentralToLowerSquareIso n)
        (duminilCopinCentralVerticalCrossingEvent (2 * n)) ⊆
      duminilCopinLowerSquareVerticalCrossingEvent n := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback
      (duminilCopinCentralToLowerSquareIso n) omega ∈
    duminilCopinCentralVerticalCrossingEvent (2 * n) at homega
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := homega
  let F := duminilCopinCentralToLowerSquareIso n
  let q := w.map F.toHom
  have hqOpen : walkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso F w hwOpen
  have hwSupport : ∀ z ∈ w.support,
      z ∈ duminilCopinCentralSquareVertices (2 * n) :=
    walk_support_mem_duminilCopinCentralSquare_of_edges
      (Finset.mem_of_subset (Finset.filter_subset _ _) hy) w hwEdges
  have hqSupport : ∀ z ∈ q.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨u, hu, rfl⟩
    have hu' := mem_duminilCopinCentralSquareVertices_iff.mp (hwSupport u hu)
    change -(n : ℤ) ≤ F u 0 ∧ F u 0 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ F u 1 ∧ F u 1 ≤ (n : ℤ)
    simp only [F, duminilCopinCentralToLowerSquareIso_zero,
      duminilCopinCentralToLowerSquareIso_one]
    omega
  have hqRectangle : walkEdgeFinset q ⊆ duminilCopinRectangleEdges n :=
    walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support q fun z hz ↦ by
      rw [mem_duminilCopinRectangleVertices_iff]
      have hz' := hqSupport z hz
      omega
  have hqEdges : walkEdgeFinset q ⊆ duminilCopinLowerSquareEdges n := by
    intro e he
    rw [duminilCopinLowerSquareEdges, Finset.mem_filter]
    refine ⟨hqRectangle he, ?_, ?_⟩
    · exact (hqSupport e.1.out.1 (q.mem_support_of_mem_edges
        ((mem_walkEdgeFinset_iff q e).mp he) (Sym2.out_fst_mem e.1))).2.2.2
    · exact (hqSupport e.1.out.2 (q.mem_support_of_mem_edges
        ((mem_walkEdgeFinset_iff q e).mp he) (Sym2.out_snd_mem e.1))).2.2.2
  simp only [duminilCopinLowerSquareVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨F x, ?_, F y, ?_, q, hqOpen, hqEdges⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    have hx' := mem_duminilCopinCentralSquareBottom_iff.mp hx
    simp only [F, duminilCopinCentralToLowerSquareIso_zero,
      duminilCopinCentralToLowerSquareIso_one]
    omega
  · rw [mem_duminilCopinLowerSquareTop_iff]
    have hy' := mem_duminilCopinCentralSquareTop_iff.mp hy
    simp only [F, duminilCopinCentralToLowerSquareIso_zero,
      duminilCopinCentralToLowerSquareIso_one]
    omega

private theorem half_le_duminilCopinLowerSquareVerticalCrossingProbability
    (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (duminilCopinLowerSquareVerticalCrossingEvent n) := by
  let F := duminilCopinCentralToLowerSquareIso n
  calc
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinCentralVerticalCrossingEvent (2 * n)) :=
      half_le_duminilCopinCentralVerticalCrossingProbability (2 * n) (by omega)
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent F
          (duminilCopinCentralVerticalCrossingEvent (2 * n))) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity F
        (measurableSet_duminilCopinCentralVerticalCrossingEvent (2 * n))]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinLowerSquareVerticalCrossingEvent n) :=
      measureReal_mono (duminilCopinCentralToLowerSquareEvent_subset n)
        (measure_ne_top _ _)

private theorem half_le_duminilCopinCentralHorizontalCrossingProbability
    (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
      (duminilCopinCentralHorizontalCrossingEvent n) := by
  calc
    (1 / 2 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinCentralVerticalCrossingEvent n) :=
      half_le_duminilCopinCentralVerticalCrossingProbability n hn
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent duminilCopinCentralQuarterTurnIso
          (duminilCopinCentralVerticalCrossingEvent n)) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
        duminilCopinCentralQuarterTurnIso
        (measurableSet_duminilCopinCentralVerticalCrossingEvent n)]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinCentralHorizontalCrossingEvent n) :=
      measureReal_mono
        (duminilCopinCentralQuarterTurnVerticalEvent_subset_horizontal n)
        (measure_ne_top _ _)

/-- Every central horizontal crossing contains a simple crossing normalized at its last visit
to the left side and first subsequent visit to the right side. -/
private theorem exists_duminilCopinNormalizedCentralHorizontalPath_of_mem
    {n : ℕ} {ω : EdgeConfiguration 2}
    (hω : ω ∈ duminilCopinCentralHorizontalCrossingEvent n) :
    ∃ x ∈ duminilCopinCentralSquareLeft n,
      ∃ y ∈ duminilCopinCentralSquareRight n,
        ∃ q : squareGraph.Walk x y,
          walkIsOpen ω q ∧ q.IsPath ∧
          walkEdgeFinset q ⊆ duminilCopinCentralSquareEdges n ∧
          (∀ z ∈ q.support, z 0 = 0 → z = x) ∧
          (∀ z ∈ q.support, z 0 = (n : ℤ) → z = y) ∧
          ∀ z ∈ q.support, z ≠ x → z ≠ y →
            0 < z 0 ∧ z 0 < (n : ℤ) := by
  simp only [duminilCopinCentralHorizontalCrossingEvent, Set.mem_iUnion] at hω
  obtain ⟨u, hu, v, hv, w, hwOpen, hwEdges⟩ := hω
  have huCoords := mem_duminilCopinCentralSquareLeft_iff.mp hu
  have hvCoords := mem_duminilCopinCentralSquareRight_iff.mp hv
  obtain ⟨x, y, q, hxLevel, hyLevel, hqOpen, hqPath,
      _hqEdgesOriginal, hqSupport, hxUnique, hyUnique⟩ :=
    exists_open_cubicPath_between_levels_normalized w hwOpen
      (0 : Fin 2) 0 (n : ℤ) (by omega) (by omega) (by omega)
  have hvCentral : v ∈ duminilCopinCentralSquareVertices n := by
    rw [mem_duminilCopinCentralSquareVertices_iff]
    omega
  have hwSupport : ∀ z ∈ w.support,
      z ∈ duminilCopinCentralSquareVertices n :=
    walk_support_mem_duminilCopinCentralSquare_of_edges hvCentral w hwEdges
  have hqCentral : ∀ z ∈ q.support,
      z ∈ duminilCopinCentralSquareVertices n := by
    intro z hz
    exact hwSupport z (hqSupport z hz).2.2
  have hxCentral := mem_duminilCopinCentralSquareVertices_iff.mp
    (hqCentral x q.start_mem_support)
  have hyCentral := mem_duminilCopinCentralSquareVertices_iff.mp
    (hqCentral y q.end_mem_support)
  have hxLeft : x ∈ duminilCopinCentralSquareLeft n := by
    rw [mem_duminilCopinCentralSquareLeft_iff]
    omega
  have hyRight : y ∈ duminilCopinCentralSquareRight n := by
    rw [mem_duminilCopinCentralSquareRight_iff]
    omega
  have hqRectangle : walkEdgeFinset q ⊆ duminilCopinRectangleEdges n :=
    walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support q fun z hz ↦ by
      rw [mem_duminilCopinRectangleVertices_iff]
      have hz' := mem_duminilCopinCentralSquareVertices_iff.mp (hqCentral z hz)
      omega
  have hqEdges : walkEdgeFinset q ⊆ duminilCopinCentralSquareEdges n := by
    intro e he
    rw [duminilCopinCentralSquareEdges, Finset.mem_filter]
    refine ⟨hqRectangle he, ?_, ?_⟩
    · apply hqCentral e.1.out.1
      apply q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff q e).mp he)
      exact Sym2.out_fst_mem e.1
    · apply hqCentral e.1.out.2
      apply q.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff q e).mp he)
      exact Sym2.out_snd_mem e.1
  refine ⟨x, hxLeft, y, hyRight, q, hqOpen, hqPath, hqEdges,
    hxUnique, hyUnique, ?_⟩
  intro z hz hzx hzy
  have hzData := hqSupport z hz
  have hz0ne : z 0 ≠ 0 := fun hz0 ↦ hzx (hxUnique z hz hz0)
  have hznne : z 0 ≠ (n : ℤ) := fun hzn ↦ hzy (hyUnique z hz hzn)
  omega

/-! A normalized central horizontal crossing and its reflection in the vertical axis form the
barrier used in the left panel of Figure 2.3.  The following lemmas keep this incidence step
separate from the later stopping-fiber locality argument. -/

private def duminilCopinVerticalAxisReflectionIso : squareGraph ≃g squareGraph :=
  cubicCoordinateReflectionIso (0 : Fin 2)

@[simp]
private theorem duminilCopinVerticalAxisReflectionIso_zero (x : SquareVertex) :
    duminilCopinVerticalAxisReflectionIso x 0 = -x 0 := by
  simp [duminilCopinVerticalAxisReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv]

@[simp]
private theorem duminilCopinVerticalAxisReflectionIso_one (x : SquareVertex) :
    duminilCopinVerticalAxisReflectionIso x 1 = x 1 := by
  simp [duminilCopinVerticalAxisReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv]

/-- Reflect a central left--right walk, traverse the reflected copy from left to the axis, and
then traverse the original copy from the axis to the right. -/
private def duminilCopinReflectedHorizontalBarrier
    {x y : SquareVertex} (q : squareGraph.Walk x y) (hx : x 0 = 0) :
    squareGraph.Walk (duminilCopinVerticalAxisReflectionIso y) y :=
  (((q.map duminilCopinVerticalAxisReflectionIso.toHom).reverse).copy rfl (by
      apply duminilCopinVerticalAxisReflectionIso.injective
      ext i
      fin_cases i
      · simp [hx]
      · simp)).append q

private theorem duminilCopinReflectedHorizontalBarrier_support_coordinates
    {n : ℕ} {x y z : SquareVertex} (q : squareGraph.Walk x y)
    (hx : x 0 = 0)
    (hq : ∀ u ∈ q.support,
      0 ≤ u 0 ∧ u 0 ≤ (n : ℤ) ∧ 0 ≤ u 1 ∧ u 1 ≤ (n : ℤ))
    (hz : z ∈ (duminilCopinReflectedHorizontalBarrier q hx).support) :
    -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  simp only [duminilCopinReflectedHorizontalBarrier,
    SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_map,
    List.mem_append, List.mem_reverse, List.mem_map] at hz
  rcases hz with hz | hz
  · rcases hz with ⟨u, hu, rfl⟩
    have hu' := hq u hu
    change -(n : ℤ) ≤ -u 0 ∧ -u 0 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ u 1 ∧ u 1 ≤ (n : ℤ)
    omega
  · have hz' := hq z (List.mem_of_mem_tail hz)
    omega

private def duminilCopinLowerSquareNormalizeIso (n : ℕ) :
    squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex (-(n : ℤ)) (-(n : ℤ))) cubicOrigin

@[simp]
private theorem duminilCopinLowerSquareNormalizeIso_zero
    (n : ℕ) (x : SquareVertex) :
    duminilCopinLowerSquareNormalizeIso n x 0 = x 0 + (n : ℤ) := by
  simp [duminilCopinLowerSquareNormalizeIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

@[simp]
private theorem duminilCopinLowerSquareNormalizeIso_one
    (n : ℕ) (x : SquareVertex) :
    duminilCopinLowerSquareNormalizeIso n x 1 = x 1 + (n : ℤ) := by
  simp [duminilCopinLowerSquareNormalizeIso, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

/-- Centered-coordinate form of the discrete rectangle incidence theorem. -/
private theorem squareWalk_support_inter_centeredSquare
    {n : ℕ} {a b c d : ℤ}
    (ha : -(n : ℤ) ≤ a) (ha' : a ≤ (n : ℤ))
    (hb : -(n : ℤ) ≤ b) (hb' : b ≤ (n : ℤ))
    (hc : -(n : ℤ) ≤ c) (hc' : c ≤ (n : ℤ))
    (hd : -(n : ℤ) ≤ d) (hd' : d ≤ (n : ℤ))
    (p : squareGraph.Walk (squareVertex (-(n : ℤ)) a)
      (squareVertex (n : ℤ) b))
    (q : squareGraph.Walk (squareVertex c (-(n : ℤ)))
      (squareVertex d (n : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hqbox : ∀ z ∈ q.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ)) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let F := duminilCopinLowerSquareNormalizeIso n
  let P : squareGraph.Walk (squareVertex 0 (a + n))
      (squareVertex (2 * (n : ℤ)) (b + n)) :=
    (p.map F.toHom).copy (by
      ext i
      fin_cases i <;> simp [F, squareVertex] <;> ring) (by
      ext i
      fin_cases i <;> simp [F, squareVertex] <;> ring)
  let Q : squareGraph.Walk (squareVertex (c + n) 0)
      (squareVertex (d + n) (2 * (n : ℤ))) :=
    (q.map F.toHom).copy (by
      ext i
      fin_cases i <;> simp [F, squareVertex] <;> ring) (by
      ext i
      fin_cases i <;> simp [F, squareVertex] <;> ring)
  have hPbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    simp only [P, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨u, hu, rfl⟩
    have hu' := hpbox u hu
    change 0 ≤ duminilCopinLowerSquareNormalizeIso n u 0 ∧
      duminilCopinLowerSquareNormalizeIso n u 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ duminilCopinLowerSquareNormalizeIso n u 1 ∧
      duminilCopinLowerSquareNormalizeIso n u 1 ≤ 2 * (n : ℤ)
    simp only [duminilCopinLowerSquareNormalizeIso_zero,
      duminilCopinLowerSquareNormalizeIso_one]
    omega
  have hQbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨u, hu, rfl⟩
    have hu' := hqbox u hu
    change 0 ≤ duminilCopinLowerSquareNormalizeIso n u 0 ∧
      duminilCopinLowerSquareNormalizeIso n u 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ duminilCopinLowerSquareNormalizeIso n u 1 ∧
      duminilCopinLowerSquareNormalizeIso n u 1 ≤ 2 * (n : ℤ)
    simp only [duminilCopinLowerSquareNormalizeIso_zero,
      duminilCopinLowerSquareNormalizeIso_one]
    omega
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (le_refl (2 * n)) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) P Q hPbox hQbox
  have hzPmap : z ∈ (p.map F.toHom).support := by
    simpa [P] using hzP
  have hzQmap : z ∈ (q.map F.toHom).support := by
    simpa [Q] using hzQ
  rw [SimpleGraph.Walk.support_map] at hzPmap hzQmap
  rcases List.mem_map.mp hzPmap with ⟨zp, hzp, hzpMap⟩
  rcases List.mem_map.mp hzQmap with ⟨zq, hzq, hzqMap⟩
  have hpq : zp = zq := F.injective (hzpMap.trans hzqMap.symm)
  exact ⟨zp, hzp, hpq ▸ hzq⟩

/-- Every bottom--top crossing of the lower square meets the normalized reflected barrier. -/
private theorem duminilCopin_verticalWalk_meets_reflectedHorizontalBarrier
    {n : ℕ} {x y vb vt : SquareVertex}
    (q : squareGraph.Walk x y) (hx : x 0 = 0) (hy : y 0 = (n : ℤ))
    (hq : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (V : squareGraph.Walk vb vt)
    (hvb : vb 1 = -(n : ℤ)) (hvt : vt 1 = (n : ℤ))
    (hV : ∀ z ∈ V.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ)) :
    ∃ z, z ∈ (duminilCopinReflectedHorizontalBarrier q hx).support ∧
      z ∈ V.support := by
  let B := duminilCopinReflectedHorizontalBarrier q hx
  let B' : squareGraph.Walk (squareVertex (-(n : ℤ)) (y 1))
      (squareVertex (n : ℤ) (y 1)) := B.copy (by
        ext i
        fin_cases i
        · simp [B, hy]
        · simp [B, squareVertex]) (by
        ext i
        fin_cases i <;> simp [B, hy, squareVertex])
  let V' : squareGraph.Walk (squareVertex (vb 0) (-(n : ℤ)))
      (squareVertex (vt 0) (n : ℤ)) := V.copy (by
        ext i
        fin_cases i <;> simp [squareVertex, hvb]) (by
        ext i
        fin_cases i <;> simp [squareVertex, hvt])
  have hB' : ∀ z ∈ B'.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    apply duminilCopinReflectedHorizontalBarrier_support_coordinates q hx hq
    simpa [B', B] using hz
  have hV' : ∀ z ∈ V'.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    exact hV z (by simpa [V'] using hz)
  obtain ⟨z, hzB, hzV⟩ := squareWalk_support_inter_centeredSquare
    (by have := hq y q.end_mem_support; omega)
    (by have := hq y q.end_mem_support; omega)
    (by have := hq y q.end_mem_support; omega)
    (by have := hq y q.end_mem_support; omega)
    (by have := hV vb V.start_mem_support; omega)
    (by have := hV vb V.start_mem_support; omega)
    (by have := hV vt V.end_mem_support; omega)
    (by have := hV vt V.end_mem_support; omega)
    B' V' hB' hV'
  exact ⟨z, by simpa [B', B] using hzB, by simpa [V'] using hzV⟩

/-- A walk using only lower-square bonds stays in `[-n,n]²`. -/
private theorem walk_support_coordinates_duminilCopinLowerSquare_of_edges
    {n : ℕ} {u v : SquareVertex}
    (hv : v ∈ duminilCopinLowerSquareTop n)
    (w : squareGraph.Walk u v)
    (hw : walkEdgeFinset w ⊆ duminilCopinLowerSquareEdges n) :
    ∀ z ∈ w.support,
      -(n : ℤ) ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  classical
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · have hv' := mem_duminilCopinLowerSquareTop_iff.mp hv
    omega
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    have heLower : ee ∈ duminilCopinLowerSquareEdges n :=
      hw ((mem_walkEdgeFinset_iff w ee).mpr he)
    have heData := Finset.mem_filter.mp heLower
    have heRect := Finset.mem_filter.mp heData.1
    change z ∈ (ee : Sym2 SquareVertex) at hze
    rw [← ee.1.out_eq, Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · have hrect := mem_duminilCopinRectangleVertices_iff.mp heRect.2.1
      omega
    · have hrect := mem_duminilCopinRectangleVertices_iff.mp heRect.2.2
      omega

/-- Event-level form of `V4a`: every open lower-square crossing meets the reflected barrier of
a normalized central horizontal crossing. -/
private theorem duminilCopinLowerSquareCrossing_meets_reflectedHorizontalBarrier
    {n : ℕ} {omega : EdgeConfiguration 2} {x y : SquareVertex}
    (q : squareGraph.Walk x y) (hx : x 0 = 0) (hy : y 0 = (n : ℤ))
    (hq : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ (n : ℤ) ∧ 0 ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (hcross : omega ∈ duminilCopinLowerSquareVerticalCrossingEvent n) :
    ∃ vb ∈ duminilCopinRectangleBottom n,
      ∃ vt ∈ duminilCopinLowerSquareTop n,
        ∃ V : squareGraph.Walk vb vt,
          walkIsOpen omega V ∧
          walkEdgeFinset V ⊆ duminilCopinLowerSquareEdges n ∧
          ∃ z, z ∈ (duminilCopinReflectedHorizontalBarrier q hx).support ∧
            z ∈ V.support := by
  simp only [duminilCopinLowerSquareVerticalCrossingEvent, Set.mem_iUnion] at hcross
  obtain ⟨vb, hvb, vt, hvt, V, hVOpen, hVEdges⟩ := hcross
  have hvb' := mem_duminilCopinRectangleBottom_iff.mp hvb
  have hvt' := mem_duminilCopinLowerSquareTop_iff.mp hvt
  have hVSupport :=
    walk_support_coordinates_duminilCopinLowerSquare_of_edges hvt V hVEdges
  obtain ⟨z, hzBarrier, hzV⟩ :=
    duminilCopin_verticalWalk_meets_reflectedHorizontalBarrier q hx hy hq V
      hvb'.2.2 hvt'.2.2 hVSupport
  exact ⟨vb, hvb, vt, hvt, V, hVOpen, hVEdges, z, hzBarrier, hzV⟩

/-! Reflection in the horizontal line `y = n / 2` transports the lower bridge into the upper
bridge.  Only event inclusion is needed for the probability lower bound. -/

private def duminilCopinBridgeReflectionIso (n : ℕ) : squareGraph ≃g squareGraph :=
  (cubicCoordinateReflectionIso (1 : Fin 2)).trans
    (cubicTranslationIso cubicOrigin (squareVertex 0 n))

@[simp]
private theorem duminilCopinBridgeReflectionIso_zero (n : ℕ) (x : SquareVertex) :
    duminilCopinBridgeReflectionIso n x 0 = x 0 := by
  simp [duminilCopinBridgeReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]

@[simp]
private theorem duminilCopinBridgeReflectionIso_one (n : ℕ) (x : SquareVertex) :
    duminilCopinBridgeReflectionIso n x 1 = (n : ℤ) - x 1 := by
  simp [duminilCopinBridgeReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply, cubicTranslate,
    cubicOrigin, squareVertex]
  ring

private theorem duminilCopinBridgeReflectionIso_mem_upperVertex
    {n : ℕ} {x : SquareVertex}
    (hx : x ∈ duminilCopinRectangleVertices n) :
    duminilCopinBridgeReflectionIso n x ∈ duminilCopinRectangleVertices n := by
  rw [mem_duminilCopinRectangleVertices_iff]
  have hx' := mem_duminilCopinRectangleVertices_iff.mp hx
  simp only [duminilCopinBridgeReflectionIso_zero,
    duminilCopinBridgeReflectionIso_one]
  omega

private theorem duminilCopinBridgeReflectionIso_mem_central
    {n : ℕ} {x : SquareVertex}
    (hx : x ∈ duminilCopinCentralSquareVertices n) :
    duminilCopinBridgeReflectionIso n x ∈
      duminilCopinCentralSquareVertices n := by
  rw [mem_duminilCopinCentralSquareVertices_iff]
  have hx' := mem_duminilCopinCentralSquareVertices_iff.mp hx
  simp only [duminilCopinBridgeReflectionIso_zero,
    duminilCopinBridgeReflectionIso_one]
  omega

private theorem duminilCopinBridgeReflectionIso_image_lowerEdges_subset
    (n : ℕ) :
    (duminilCopinLowerSquareEdges n).image
        (duminilCopinBridgeReflectionIso n).mapEdgeSet ⊆
      duminilCopinUpperRectangleEdges n := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [duminilCopinLowerSquareEdges, Finset.mem_filter] at hf
  rw [duminilCopinUpperRectangleEdges, Finset.mem_filter]
  have hmapped : ∀ z ∈
      (((duminilCopinBridgeReflectionIso n).mapEdgeSet f : SquareEdge) :
        Sym2 SquareVertex),
      z ∈ duminilCopinRectangleVertices n := by
    intro z hz
    change z ∈ Sym2.map (duminilCopinBridgeReflectionIso n)
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hu' : u ∈ duminilCopinRectangleVertices n := by
      have hend := (Finset.mem_filter.mp hf.1).2
      rw [← f.1.out_eq, Sym2.mem_iff] at hu
      exact hu.elim (fun h ↦ h ▸ hend.1) (fun h ↦ h ▸ hend.2)
    exact duminilCopinBridgeReflectionIso_mem_upperVertex hu'
  have hmapped_nonneg : ∀ z ∈
      (((duminilCopinBridgeReflectionIso n).mapEdgeSet f : SquareEdge) :
        Sym2 SquareVertex), 0 ≤ z 1 := by
    intro z hz
    change z ∈ Sym2.map (duminilCopinBridgeReflectionIso n)
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have huRect : u ∈ duminilCopinRectangleVertices n := by
      have hend := (Finset.mem_filter.mp hf.1).2
      rw [← f.1.out_eq, Sym2.mem_iff] at hu
      exact hu.elim (fun h ↦ h ▸ hend.1) (fun h ↦ h ▸ hend.2)
    have huy : u 1 ≤ (n : ℤ) := by
      rw [← f.1.out_eq, Sym2.mem_iff] at hu
      rcases hu with rfl | rfl
      · exact hf.2.1
      · exact hf.2.2
    have huBounds := mem_duminilCopinRectangleVertices_iff.mp huRect
    simp only [duminilCopinBridgeReflectionIso_one]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [duminilCopinRectangleEdges, Finset.mem_filter]
    refine ⟨mem_cubicBoxEdges_of_endpoints ?_, ?_, ?_⟩
    · intro z hz
      rw [mem_cubicMetricBox]
      have hz' := mem_duminilCopinRectangleVertices_iff.mp (hmapped z hz)
      intro i
      fin_cases i <;> simp [cubicOrigin] <;> omega
    · exact hmapped _ (Sym2.out_fst_mem _)
    · exact hmapped _ (Sym2.out_snd_mem _)
  · exact hmapped_nonneg _ (Sym2.out_fst_mem _)
  · exact hmapped_nonneg _ (Sym2.out_snd_mem _)

private theorem duminilCopinBridgeReflectionIso_image_centralEdges_subset
    (n : ℕ) :
    (duminilCopinCentralSquareEdges n).image
        (duminilCopinBridgeReflectionIso n).mapEdgeSet ⊆
      duminilCopinCentralSquareEdges n := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [duminilCopinCentralSquareEdges, Finset.mem_filter] at hf ⊢
  have hmapped : ∀ z ∈
      (((duminilCopinBridgeReflectionIso n).mapEdgeSet f : SquareEdge) :
        Sym2 SquareVertex),
      z ∈ duminilCopinCentralSquareVertices n := by
    intro z hz
    change z ∈ Sym2.map (duminilCopinBridgeReflectionIso n)
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [← f.1.out_eq, Sym2.mem_iff] at hu
    rcases hu with rfl | rfl
    · exact duminilCopinBridgeReflectionIso_mem_central hf.2.1
    · exact duminilCopinBridgeReflectionIso_mem_central hf.2.2
  refine ⟨?_, hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
  rw [duminilCopinRectangleEdges, Finset.mem_filter]
  refine ⟨mem_cubicBoxEdges_of_endpoints ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_cubicMetricBox]
    have hz' := mem_duminilCopinCentralSquareVertices_iff.mp (hmapped z hz)
    intro i
    fin_cases i <;> simp [cubicOrigin] <;> omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_fst_mem _))
    omega
  · rw [mem_duminilCopinRectangleVertices_iff]
    have h := mem_duminilCopinCentralSquareVertices_iff.mp
      (hmapped _ (Sym2.out_snd_mem _))
    omega

private theorem duminilCopinBridgeReflectionEvent_subset (n : ℕ) :
    cubicGraphIsoEvent (duminilCopinBridgeReflectionIso n)
        (duminilCopinLowerBridgeEvent n) ⊆
      duminilCopinUpperBridgeEvent n := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback (duminilCopinBridgeReflectionIso n) omega ∈
    duminilCopinLowerBridgeEvent n at homega
  simp only [duminilCopinLowerBridgeEvent, Set.mem_iUnion,
    Set.mem_inter_iff] at homega
  obtain ⟨z, hz, ⟨⟨b, hb, hbz⟩, l, hl, hlz⟩, r, hr, hzr⟩ := homega
  simp only [duminilCopinUpperBridgeEvent, Set.mem_iUnion, Set.mem_inter_iff]
  refine ⟨duminilCopinBridgeReflectionIso n z,
    duminilCopinBridgeReflectionIso_mem_central hz, ?_,
    duminilCopinBridgeReflectionIso n r, ?_, ?_⟩
  · refine ⟨⟨duminilCopinBridgeReflectionIso n b, ?_, ?_⟩,
      duminilCopinBridgeReflectionIso n l, ?_, ?_⟩
    · rw [mem_duminilCopinRectangleTop_iff]
      have hb' := mem_duminilCopinRectangleBottom_iff.mp hb
      simp only [duminilCopinBridgeReflectionIso_zero,
        duminilCopinBridgeReflectionIso_one]
      omega
    · apply connectionEventIn_mono
        (duminilCopinBridgeReflectionIso_image_lowerEdges_subset n)
      have hmap :=
        (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
          (duminilCopinBridgeReflectionIso n)
          (duminilCopinLowerSquareEdges n) omega b z).mp hbz
      obtain ⟨w, hwOpen, hwEdges⟩ := hmap
      refine ⟨w.reverse, walkIsOpen_reverse hwOpen, ?_⟩
      intro e he
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] at he
      exact hwEdges ((mem_walkEdgeFinset_iff w e).mpr he)
    · rw [mem_duminilCopinCentralSquareLeft_iff]
      have hl' := mem_duminilCopinCentralSquareLeft_iff.mp hl
      simp only [duminilCopinBridgeReflectionIso_zero,
        duminilCopinBridgeReflectionIso_one]
      omega
    · apply connectionEventIn_mono
        (duminilCopinBridgeReflectionIso_image_centralEdges_subset n)
      exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
        (duminilCopinBridgeReflectionIso n)
        (duminilCopinCentralSquareEdges n) omega l z).mp hlz
  · rw [mem_duminilCopinCentralSquareRight_iff]
    have hr' := mem_duminilCopinCentralSquareRight_iff.mp hr
    simp only [duminilCopinBridgeReflectionIso_zero,
      duminilCopinBridgeReflectionIso_one]
    omega
  · apply connectionEventIn_mono
      (duminilCopinBridgeReflectionIso_image_centralEdges_subset n)
    exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      (duminilCopinBridgeReflectionIso n)
      (duminilCopinCentralSquareEdges n) omega z r).mp hzr

private theorem lowerBridgeProbability_le_upperBridgeProbability
    (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinLowerBridgeEvent n) ≤
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinUpperBridgeEvent n) := by
  calc
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinLowerBridgeEvent n) =
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent (duminilCopinBridgeReflectionIso n)
          (duminilCopinLowerBridgeEvent n)) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
        (duminilCopinBridgeReflectionIso n)
        (measurableSet_duminilCopinLowerBridgeEvent n)]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinUpperBridgeEvent n) :=
      measureReal_mono (duminilCopinBridgeReflectionEvent_subset n)
        (measure_ne_top _ _)

private theorem duminilCopinSourceIntersection_subset_verticalCrossing
    (n : ℕ) :
    duminilCopinCentralVerticalCrossingEvent n ∩
        duminilCopinLowerBridgeEvent n ∩ duminilCopinUpperBridgeEvent n ⊆
      duminilCopinVerticalCrossingEvent n := by
  intro omega homega
  rcases homega with ⟨⟨hcentral, hlower⟩, hupper⟩
  simp only [duminilCopinCentralVerticalCrossingEvent, Set.mem_iUnion] at hcentral
  obtain ⟨vb, hvb, vt, hvt, hV⟩ := hcentral
  obtain ⟨V, hVOpen, hVEdges⟩ := hV
  simp only [duminilCopinLowerBridgeEvent, Set.mem_iUnion,
    Set.mem_inter_iff] at hlower
  obtain ⟨zL, hzL, ⟨⟨b, hb, hbzL⟩, lL, hlL, hlLzL⟩,
    rL, hrL, hzLrL⟩ := hlower
  obtain ⟨wb, hwbOpen, hwbEdges⟩ := hbzL
  obtain ⟨wlL, hwlLOpen, hwlLEdges⟩ := hlLzL
  obtain ⟨wrL, hwrLOpen, hwrLEdges⟩ := hzLrL
  simp only [duminilCopinUpperBridgeEvent, Set.mem_iUnion,
    Set.mem_inter_iff] at hupper
  obtain ⟨zU, hzU, ⟨⟨t, ht, hzUt⟩, lU, hlU, hlUzU⟩,
    rU, hrU, hzUrU⟩ := hupper
  obtain ⟨wt, hwtOpen, hwtEdges⟩ := hzUt
  obtain ⟨wlU, hwlUOpen, hwlUEdges⟩ := hlUzU
  obtain ⟨wrU, hwrUOpen, hwrUEdges⟩ := hzUrU

  let HL := wlL.append wrL
  let HU := wlU.append wrU
  have hHLOpen : walkIsOpen omega HL :=
    walkIsOpen_append hwlLOpen hwrLOpen
  have hHUOpen : walkIsOpen omega HU :=
    walkIsOpen_append hwlUOpen hwrUOpen
  have hHLEdges : walkEdgeFinset HL ⊆ duminilCopinCentralSquareEdges n :=
    walkEdgeFinset_append_subset hwlLEdges hwrLEdges
  have hHUEdges : walkEdgeFinset HU ⊆ duminilCopinCentralSquareEdges n :=
    walkEdgeFinset_append_subset hwlUEdges hwrUEdges
  have hHLSupport : ∀ z ∈ HL.support,
      z ∈ duminilCopinCentralSquareVertices n :=
    walk_support_mem_duminilCopinCentralSquare_of_edges
      (Finset.mem_of_subset (Finset.filter_subset _ _) hrL) HL hHLEdges
  have hHUSupport : ∀ z ∈ HU.support,
      z ∈ duminilCopinCentralSquareVertices n :=
    walk_support_mem_duminilCopinCentralSquare_of_edges
      (Finset.mem_of_subset (Finset.filter_subset _ _) hrU) HU hHUEdges
  have hVSupport : ∀ z ∈ V.support,
      z ∈ duminilCopinCentralSquareVertices n :=
    walk_support_mem_duminilCopinCentralSquare_of_edges
      (Finset.mem_of_subset (Finset.filter_subset _ _) hvt) V hVEdges

  have hlL' := mem_duminilCopinCentralSquareLeft_iff.mp hlL
  have hrL' := mem_duminilCopinCentralSquareRight_iff.mp hrL
  have hlU' := mem_duminilCopinCentralSquareLeft_iff.mp hlU
  have hrU' := mem_duminilCopinCentralSquareRight_iff.mp hrU
  have hvb' := mem_duminilCopinCentralSquareBottom_iff.mp hvb
  have hvt' := mem_duminilCopinCentralSquareTop_iff.mp hvt
  let HL' : squareGraph.Walk (squareVertex 0 (lL 1))
      (squareVertex (n : ℤ) (rL 1)) := HL.copy (by
        ext i
        fin_cases i <;> simp [squareVertex, hlL'.1]) (by
        ext i
        fin_cases i <;> simp [squareVertex, hrL'.1])
  let HU' : squareGraph.Walk (squareVertex 0 (lU 1))
      (squareVertex (n : ℤ) (rU 1)) := HU.copy (by
        ext i
        fin_cases i <;> simp [squareVertex, hlU'.1]) (by
        ext i
        fin_cases i <;> simp [squareVertex, hrU'.1])
  let V' : squareGraph.Walk (squareVertex (vb 0) 0)
      (squareVertex (vt 0) (n : ℤ)) := V.copy (by
        ext i
        fin_cases i <;> simp [squareVertex, hvb'.2.2]) (by
        ext i
        fin_cases i <;> simp [squareVertex, hvt'.2.2])
  have hHL'Support : ∀ z ∈ HL'.support,
      0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    exact mem_duminilCopinCentralSquareVertices_iff.mp
      (hHLSupport z (by simpa [HL'] using hz))
  have hHU'Support : ∀ z ∈ HU'.support,
      0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    exact mem_duminilCopinCentralSquareVertices_iff.mp
      (hHUSupport z (by simpa [HU'] using hz))
  have hV'Support : ∀ z ∈ V'.support,
      0 ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    exact mem_duminilCopinCentralSquareVertices_iff.mp
      (hVSupport z (by simpa [V'] using hz))
  obtain ⟨cL, hcLHL, hcLV⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (le_refl n) hlL'.2.1 hlL'.2.2 hrL'.2.1 hrL'.2.2
      hvb'.1 hvb'.2.1 hvt'.1 hvt'.2.1 HL' V' hHL'Support hV'Support
  obtain ⟨cU, hcUHU, hcUV⟩ :=
    squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
      (le_refl n) hlU'.2.1 hlU'.2.2 hrU'.2.1 hrU'.2.2
      hvb'.1 hvb'.2.1 hvt'.1 hvt'.2.1 HU' V' hHU'Support hV'Support
  have hcLHL' : cL ∈ HL.support := by simpa [HL'] using hcLHL
  have hcLV' : cL ∈ V.support := by simpa [V'] using hcLV
  have hcUHU' : cU ∈ HU.support := by simpa [HU'] using hcUHU
  have hcUV' : cU ∈ V.support := by simpa [V'] using hcUV
  have hzLHL : zL ∈ HL.support := by
    simp [HL]
  have hzUHU : zU ∈ HU.support := by
    simp [HU]
  obtain ⟨qL, hqLOpen, hqLEdges⟩ :=
    exists_openSquareWalk_between_support HL hHLOpen hzLHL hcLHL'
  obtain ⟨qV, hqVOpen, hqVEdges⟩ :=
    exists_openSquareWalk_between_support V hVOpen hcLV' hcUV'
  obtain ⟨qU, hqUOpen, hqUEdges⟩ :=
    exists_openSquareWalk_between_support HU hHUOpen hcUHU' hzUHU
  let W := wb.append (qL.append (qV.append (qU.append wt)))
  have hWOpen : walkIsOpen omega W :=
    walkIsOpen_append hwbOpen
      (walkIsOpen_append hqLOpen
        (walkIsOpen_append hqVOpen (walkIsOpen_append hqUOpen hwtOpen)))
  have hCentralRect : duminilCopinCentralSquareEdges n ⊆
      duminilCopinRectangleEdges n := fun _ he ↦ (Finset.mem_filter.mp he).1
  have hLowerRect : duminilCopinLowerSquareEdges n ⊆
      duminilCopinRectangleEdges n := fun _ he ↦ (Finset.mem_filter.mp he).1
  have hUpperRect : duminilCopinUpperRectangleEdges n ⊆
      duminilCopinRectangleEdges n := fun _ he ↦ (Finset.mem_filter.mp he).1
  have hWEdges : walkEdgeFinset W ⊆ duminilCopinRectangleEdges n := by
    apply walkEdgeFinset_append_subset (hwbEdges.trans hLowerRect)
    apply walkEdgeFinset_append_subset (hqLEdges.trans (hHLEdges.trans hCentralRect))
    apply walkEdgeFinset_append_subset (hqVEdges.trans (hVEdges.trans hCentralRect))
    apply walkEdgeFinset_append_subset (hqUEdges.trans (hHUEdges.trans hCentralRect))
    exact hwtEdges.trans hUpperRect
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  exact ⟨b, hb, t, ht, W, hWOpen, hWEdges⟩

private theorem duminilCopinVerticalCrossingProbability_ge_of_lowerBridge
    (n : ℕ) (hn : 2 ≤ n)
    (hbridge : (1 / 8 : ℝ) ≤
      (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinLowerBridgeEvent n)) :
    (1 / 128 : ℝ) ≤
      duminilCopinVerticalCrossingProbability squareHalfDensity n := by
  let mu := bernoulliBondMeasure 2 squareHalfDensity
  let C := duminilCopinCentralVerticalCrossingEvent n
  let L := duminilCopinLowerBridgeEvent n
  let U := duminilCopinUpperBridgeEvent n
  have hCL : mu.real C * mu.real L ≤ mu.real (C ∩ L) :=
    bernoulliBondMeasure_real_fkg squareHalfDensity
      (isIncreasingEvent_duminilCopinCentralVerticalCrossingEvent n)
      (isIncreasingEvent_duminilCopinLowerBridgeEvent n)
      (measurableSet_duminilCopinCentralVerticalCrossingEvent n)
      (measurableSet_duminilCopinLowerBridgeEvent n)
  have hCLU : mu.real (C ∩ L) * mu.real U ≤ mu.real ((C ∩ L) ∩ U) :=
    bernoulliBondMeasure_real_fkg squareHalfDensity
      ((isIncreasingEvent_duminilCopinCentralVerticalCrossingEvent n).inter
        (isIncreasingEvent_duminilCopinLowerBridgeEvent n))
      (isIncreasingEvent_duminilCopinUpperBridgeEvent n)
      ((measurableSet_duminilCopinCentralVerticalCrossingEvent n).inter
        (measurableSet_duminilCopinLowerBridgeEvent n))
      (measurableSet_duminilCopinUpperBridgeEvent n)
  have hC : (1 / 2 : ℝ) ≤ mu.real C :=
    half_le_duminilCopinCentralVerticalCrossingProbability n hn
  have hL : (1 / 8 : ℝ) ≤ mu.real L := hbridge
  have hU : (1 / 8 : ℝ) ≤ mu.real U :=
    hbridge.trans (lowerBridgeProbability_le_upperBridgeProbability n)
  unfold duminilCopinVerticalCrossingProbability
  calc
    (1 / 128 : ℝ) = (1 / 2 : ℝ) * (1 / 8) * (1 / 8) := by norm_num
    _ ≤ (mu.real C * mu.real L) * mu.real U := by
      gcongr
    _ ≤ mu.real (C ∩ L) * mu.real U :=
      mul_le_mul_of_nonneg_right hCL measureReal_nonneg
    _ ≤ mu.real ((C ∩ L) ∩ U) := hCLU
    _ ≤ mu.real (duminilCopinVerticalCrossingEvent n) :=
      measureReal_mono (duminilCopinSourceIntersection_subset_verticalCrossing n)
        (measure_ne_top _ _)

/-! A direct transport of the repository's boundary-free `3n × 2n` RSW event supplies the
same hard-direction geometry inside Duminil-Copin's full rectangle.  This is useful both as a
sanity check on the coordinate transcription and as the existing lowest-crossing input for the
remaining numerical estimate. -/

private def duminilCopinQuarterTurnIso (n : ℕ) : squareGraph ≃g squareGraph :=
  (cubicCoordinatePermutationIso squareCoordinateSwap).trans
    (cubicTranslationIso cubicOrigin (squareVertex 0 (-(n : ℤ))))

@[simp]
private theorem duminilCopinQuarterTurnIso_zero (n : ℕ) (x : SquareVertex) :
    duminilCopinQuarterTurnIso n x 0 = x 1 := by
  simp [duminilCopinQuarterTurnIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap]

@[simp]
private theorem duminilCopinQuarterTurnIso_one (n : ℕ) (x : SquareVertex) :
    duminilCopinQuarterTurnIso n x 1 = x 0 - n := by
  simp [duminilCopinQuarterTurnIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

private theorem duminilCopinQuarterTurnIso_mem_rectangle
    {n : ℕ} {x : SquareVertex}
    (hx : x ∈ squareRectangleVertices (3 * n) n) :
    duminilCopinQuarterTurnIso n x ∈ duminilCopinRectangleVertices n := by
  rw [mem_duminilCopinRectangleVertices_iff]
  have h := mem_squareRectangleVertices_iff.mp hx
  simp only [duminilCopinQuarterTurnIso_zero, duminilCopinQuarterTurnIso_one]
  omega

private theorem duminilCopinQuarterTurnIso_image_edges_subset (n : ℕ) :
    (squareBoundaryFreeRectangleEdges (3 * n) n).image
        (duminilCopinQuarterTurnIso n).mapEdgeSet ⊆
      duminilCopinRectangleEdges n := by
  classical
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf
  rw [duminilCopinRectangleEdges, Finset.mem_filter]
  have hmapped : ∀ z ∈
      ((duminilCopinQuarterTurnIso n).mapEdgeSet f : Sym2 SquareVertex),
      z ∈ duminilCopinRectangleVertices n := by
    intro z hz
    change z ∈ Sym2.map (duminilCopinQuarterTurnIso n)
      (f : Sym2 SquareVertex) at hz
    rw [Sym2.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact duminilCopinQuarterTurnIso_mem_rectangle
      (endpoint_mem_squareRectangle_of_edge_mem hf.1 hw)
  refine ⟨mem_cubicBoxEdges_of_endpoints ?_,
    hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
  intro z hz
  rw [mem_cubicMetricBox]
  have hz' := mem_duminilCopinRectangleVertices_iff.mp (hmapped z hz)
  intro i
  fin_cases i <;> simp [cubicOrigin] <;> omega

private theorem duminilCopin_rswThreeHalves_placement_subset (n : ℕ) :
    cubicGraphIsoEvent (duminilCopinQuarterTurnIso n)
        (rswThreeHalvesCrossingEvent n) ⊆
      duminilCopinVerticalCrossingEvent n := by
  intro omega homega
  change cubicGraphIsoConfigurationPullback (duminilCopinQuarterTurnIso n) omega ∈
    squareBoundaryFreeRectangleCrossingEvent (3 * n) n at homega
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion] at homega
  obtain ⟨x, hx, y, hy, hxy⟩ := homega
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinQuarterTurnIso n x, ?_,
    duminilCopinQuarterTurnIso n y, ?_, ?_⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    have hx' := mem_squareRectangleLeft_iff.mp hx
    simp only [duminilCopinQuarterTurnIso_zero, duminilCopinQuarterTurnIso_one]
    omega
  · rw [mem_duminilCopinRectangleTop_iff]
    have hy' := mem_squareRectangleRight_iff.mp hy
    simp only [duminilCopinQuarterTurnIso_zero, duminilCopinQuarterTurnIso_one]
    omega
  · apply connectionEventIn_mono (duminilCopinQuarterTurnIso_image_edges_subset n)
    exact (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      (duminilCopinQuarterTurnIso n)
      (squareBoundaryFreeRectangleEdges (3 * n) n) omega x y).mp hxy

private theorem rswThreeHalvesCrossingProbability_le_duminilCopin
    (p : I) (n : ℕ) :
    rswThreeHalvesCrossingProbability p n ≤
      duminilCopinVerticalCrossingProbability p n := by
  unfold rswThreeHalvesCrossingProbability duminilCopinVerticalCrossingProbability
  rw [← bernoulliBondMeasure_real_cubicGraphIsoEvent p
    (duminilCopinQuarterTurnIso n)
    (measurableSet_rswThreeHalvesCrossingEvent n)]
  exact measureReal_mono (duminilCopin_rswThreeHalves_placement_subset n)
    (measure_ne_top _ _)

private theorem duminilCopinVerticalCrossingProbability_ge_rsw
    (p : I) (n : ℕ) :
    (1 - Real.sqrt (1 - rswSquareCrossingProbability p n)) ^ 3 ≤
      duminilCopinVerticalCrossingProbability p n :=
  (rswThreeHalvesCrossingProbability_ge p n).trans
    (rswThreeHalvesCrossingProbability_le_duminilCopin p n)

private def duminilCopinCentralVerticalWalk (n : ℕ) :
    squareGraph.Walk (squareVertex 0 (-(n : ℤ)))
      (squareVertex 0 (2 * (n : ℤ))) :=
  (cubicWalkFrom (squareVertex 0 (-(n : ℤ)))
    (List.replicate (3 * n) ((1 : Fin 2), true))).copy rfl (by
      rw [cubicEndpointFrom_replicate_pos]
      ext i
      fin_cases i <;> simp [squareVertex]
      omega)

private theorem duminilCopinCentralVerticalWalk_isPath (n : ℕ) :
    (duminilCopinCentralVerticalWalk n).IsPath := by
  have hraw : (cubicWalkFrom (squareVertex 0 (-(n : ℤ)))
      (List.replicate (3 * n) ((1 : Fin 2), true))).IsPath :=
    cubicWalkFrom_isPath
      (cubicVerticesFrom_replicate_pos_nodup
        (squareVertex 0 (-(n : ℤ))) (1 : Fin 2) (3 * n))
  simpa [duminilCopinCentralVerticalWalk] using hraw

private theorem duminilCopinCentralVerticalWalk_support
    {n : ℕ} {z : SquareVertex} (hz : z ∈ (duminilCopinCentralVerticalWalk n).support) :
    z ∈ duminilCopinRectangleVertices n := by
  have hz' : z ∈ cubicVerticesFrom (squareVertex 0 (-(n : ℤ)))
      (List.replicate (3 * n) ((1 : Fin 2), true)) := by
    simpa [duminilCopinCentralVerticalWalk, SimpleGraph.Walk.support_copy,
      cubicWalkFrom_support] using hz
  have h0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
    (squareVertex 0 (-(n : ℤ))) (1 : Fin 2) (0 : Fin 2) (3 * n) (by decide) hz'
  have h1 := cubicVerticesFrom_replicate_pos_coord_between
    (squareVertex 0 (-(n : ℤ))) (1 : Fin 2) (3 * n) hz'
  rw [mem_duminilCopinRectangleVertices_iff]
  simp [squareVertex] at h0 h1 ⊢
  omega

private theorem duminilCopinCentralVerticalWalk_open_subset (n : ℕ) :
    {omega | walkIsOpen omega (duminilCopinCentralVerticalWalk n)} ⊆
      duminilCopinVerticalCrossingEvent n := by
  intro omega hopen
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨squareVertex 0 (-(n : ℤ)), ?_, squareVertex 0 (2 * (n : ℤ)), ?_,
    duminilCopinCentralVerticalWalk n, hopen, ?_⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    simp [squareVertex]
  · rw [mem_duminilCopinRectangleTop_iff]
    simp [squareVertex]
  · exact walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support
      (duminilCopinCentralVerticalWalk n)
      (fun z hz ↦ duminilCopinCentralVerticalWalk_support hz)

private theorem duminilCopinVerticalCrossingProbability_ge_straightPath (n : ℕ) :
    (1 / 2 : ℝ) ^ (3 * n) ≤
      duminilCopinVerticalCrossingProbability squareHalfDensity n := by
  unfold duminilCopinVerticalCrossingProbability
  calc
    (1 / 2 : ℝ) ^ (3 * n) = (bernoulliBondMeasure 2 squareHalfDensity).real
        {omega | walkIsOpen omega (duminilCopinCentralVerticalWalk n)} := by
      symm
      rw [bernoulliBondMeasure_real_walkIsOpen squareHalfDensity
        (duminilCopinCentralVerticalWalk n)
        (duminilCopinCentralVerticalWalk_isPath n).isTrail]
      simp [duminilCopinCentralVerticalWalk, coe_squareHalfDensity]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinVerticalCrossingEvent n) :=
      measureReal_mono (duminilCopinCentralVerticalWalk_open_subset n)
        (measure_ne_top _ _)

/-! At scale three, the four-fresh-edge Grimmett witness fits across the target rectangle after
a quarter-turn.  This discharges the last small scale for which a direct finite witness has a
stronger bound than `1 / 128`; the uniform argument for larger scales still requires the
highest-crossing stopping geometry recorded in the pictorial-proof expansion. -/

private def duminilCopinThreeFreshIso : squareGraph ≃g squareGraph :=
  (cubicCoordinatePermutationIso squareCoordinateSwap).trans
    (cubicTranslationIso cubicOrigin (squareVertex (-2) (-1)))

@[simp]
private theorem duminilCopinThreeFreshIso_zero (x : SquareVertex) :
    duminilCopinThreeFreshIso x 0 = x 1 - 2 := by
  simp [duminilCopinThreeFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

@[simp]
private theorem duminilCopinThreeFreshIso_one (x : SquareVertex) :
    duminilCopinThreeFreshIso x 1 = x 0 - 1 := by
  simp [duminilCopinThreeFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

set_option maxRecDepth 4000 in
private theorem duminilCopinThreeFreshEvent_subset :
    cubicGraphIsoEvent duminilCopinThreeFreshIso
        (grimmettRectangleFreshCrossingEventFour 4) ⊆
      duminilCopinVerticalCrossingEvent 3 := by
  classical
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinThreeFreshIso omega ∈
    grimmettRectangleFreshCrossingEventFour 4 at homega
  simp only [grimmettRectangleFreshCrossingEventFour,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at homega
  obtain ⟨s, hs, hcyl, hfresh⟩ := homega
  let W := selectedGrimmettRectangleTraceCrossing 4 ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalkFour W).map duminilCopinThreeFreshIso.toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback duminilCopinThreeFreshIso omega)
      (grimmettTraceExtendedWalkFour W) :=
    selectedGrimmettTraceExtendedWalkFour_isOpen hs hcyl hfresh
  have hopen : walkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso duminilCopinThreeFreshIso
      (grimmettTraceExtendedWalkFour W) hsource
  have hsupport : ∀ z ∈ q.support, z ∈ duminilCopinRectangleVertices 3 := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hb := grimmettTraceExtendedWalkFour_support_bounds W hu
    rw [mem_duminilCopinRectangleVertices_iff]
    change (-3 : ℤ) ≤ duminilCopinThreeFreshIso u 0 ∧
      duminilCopinThreeFreshIso u 0 ≤ 3 ∧
      (-3 : ℤ) ≤ duminilCopinThreeFreshIso u 1 ∧
      duminilCopinThreeFreshIso u 1 ≤ 6
    simp only [duminilCopinThreeFreshIso_zero, duminilCopinThreeFreshIso_one]
    omega
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinThreeFreshIso (grimmettTraceLeftSecondOuterVertex W), ?_,
    duminilCopinThreeFreshIso (grimmettTraceRightSecondOuterVertex W), ?_,
    q, hopen, ?_⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp only [duminilCopinThreeFreshIso_zero, duminilCopinThreeFreshIso_one]
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs']
    omega
  · rw [mem_duminilCopinRectangleTop_iff]
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp only [duminilCopinThreeFreshIso_zero, duminilCopinThreeFreshIso_one]
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf']
    omega
  · exact walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support q hsupport

private theorem duminilCopinVerticalCrossingProbability_three_ge_one_thirty_second :
    (1 / 32 : ℝ) ≤
      duminilCopinVerticalCrossingProbability squareHalfDensity 3 := by
  unfold duminilCopinVerticalCrossingProbability
  calc
    (1 / 32 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleFreshCrossingEventFour (2 * 2)) :=
      one_thirty_second_le_grimmettRectangleFreshCrossingEventFour_half 2 (by omega)
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent duminilCopinThreeFreshIso
          (grimmettRectangleFreshCrossingEventFour 4)) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
        duminilCopinThreeFreshIso
        (measurableSet_grimmettRectangleFreshCrossingEventFour 4)]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinVerticalCrossingEvent 3) :=
      measureReal_mono duminilCopinThreeFreshEvent_subset (measure_ne_top _ _)

private def duminilCopinFourFreshIso : squareGraph ≃g squareGraph :=
  (cubicCoordinatePermutationIso squareCoordinateSwap).trans
    (cubicTranslationIso cubicOrigin (squareVertex (-4) (-3)))

@[simp]
private theorem duminilCopinFourFreshIso_zero (x : SquareVertex) :
    duminilCopinFourFreshIso x 0 = x 1 - 4 := by
  simp [duminilCopinFourFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

@[simp]
private theorem duminilCopinFourFreshIso_one (x : SquareVertex) :
    duminilCopinFourFreshIso x 1 = x 0 - 3 := by
  simp [duminilCopinFourFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

set_option maxRecDepth 4000 in
private theorem duminilCopinFourFreshEvent_subset :
    cubicGraphIsoEvent duminilCopinFourFreshIso
        (grimmettRectangleFreshCrossingEventThree 8) ⊆
      duminilCopinVerticalCrossingEvent 4 := by
  classical
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinFourFreshIso omega ∈
    grimmettRectangleFreshCrossingEventThree 8 at homega
  simp only [grimmettRectangleFreshCrossingEventThree,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at homega
  obtain ⟨s, hs, hcyl, hfresh⟩ := homega
  let W := selectedGrimmettRectangleTraceCrossing 8 ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalkThree W).map duminilCopinFourFreshIso.toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback duminilCopinFourFreshIso omega)
      (grimmettTraceExtendedWalkThree W) :=
    selectedGrimmettTraceExtendedWalkThree_isOpen hs hcyl hfresh
  have hopen : walkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso duminilCopinFourFreshIso
      (grimmettTraceExtendedWalkThree W) hsource
  have hsupport : ∀ z ∈ q.support, z ∈ duminilCopinRectangleVertices 4 := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hb := grimmettTraceExtendedWalkThree_support_bounds W hu
    rw [mem_duminilCopinRectangleVertices_iff]
    change (-4 : ℤ) ≤ duminilCopinFourFreshIso u 0 ∧
      duminilCopinFourFreshIso u 0 ≤ 4 ∧
      (-4 : ℤ) ≤ duminilCopinFourFreshIso u 1 ∧
      duminilCopinFourFreshIso u 1 ≤ 8
    simp only [duminilCopinFourFreshIso_zero, duminilCopinFourFreshIso_one]
    omega
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinFourFreshIso (grimmettTraceLeftOuterVertex W), ?_,
    duminilCopinFourFreshIso (grimmettTraceRightSecondOuterVertex W), ?_,
    q, hopen, ?_⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp only [duminilCopinFourFreshIso_zero, duminilCopinFourFreshIso_one]
    simp [grimmettTraceLeftOuterVertex, cubicStepFrom, cubicDirectionIncrement, hs']
    omega
  · rw [mem_duminilCopinRectangleTop_iff]
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp only [duminilCopinFourFreshIso_zero, duminilCopinFourFreshIso_one]
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf']
    omega
  · exact walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support q hsupport

private theorem duminilCopinVerticalCrossingProbability_four_ge_one_sixteenth :
    (1 / 16 : ℝ) ≤
      duminilCopinVerticalCrossingProbability squareHalfDensity 4 := by
  unfold duminilCopinVerticalCrossingProbability
  calc
    (1 / 16 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleFreshCrossingEventThree (2 * 4)) :=
      one_sixteenth_le_bernoulliBondMeasure_real_grimmettRectangleFreshCrossingEventThree
        4 (by omega)
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent duminilCopinFourFreshIso
          (grimmettRectangleFreshCrossingEventThree 8)) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
        duminilCopinFourFreshIso
        (measurableSet_grimmettRectangleFreshCrossingEventThree 8)]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinVerticalCrossingEvent 4) :=
      measureReal_mono duminilCopinFourFreshEvent_subset (measure_ne_top _ _)

private def duminilCopinFiveFreshIso : squareGraph ≃g squareGraph :=
  (cubicCoordinatePermutationIso squareCoordinateSwap).trans
    (cubicTranslationIso cubicOrigin (squareVertex (-5) (-3)))

@[simp]
private theorem duminilCopinFiveFreshIso_zero (x : SquareVertex) :
    duminilCopinFiveFreshIso x 0 = x 1 - 5 := by
  simp [duminilCopinFiveFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

@[simp]
private theorem duminilCopinFiveFreshIso_one (x : SquareVertex) :
    duminilCopinFiveFreshIso x 1 = x 0 - 3 := by
  simp [duminilCopinFiveFreshIso, cubicCoordinatePermutationIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex,
    squareCoordinateSwap, sub_eq_add_neg]

set_option maxRecDepth 10000 in
private theorem duminilCopinFiveFreshEvent_subset :
    cubicGraphIsoEvent duminilCopinFiveFreshIso
        (grimmettRectangleFreshCrossingEventFour 10) ⊆
      duminilCopinVerticalCrossingEvent 5 := by
  classical
  intro omega homega
  change cubicGraphIsoConfigurationPullback duminilCopinFiveFreshIso omega ∈
    grimmettRectangleFreshCrossingEventFour 10 at homega
  simp only [grimmettRectangleFreshCrossingEventFour,
    adaptiveFreshOpenExtensionEvent, Set.mem_iUnion, Set.mem_inter_iff] at homega
  obtain ⟨s, hs, hcyl, hfresh⟩ := homega
  let W := selectedGrimmettRectangleTraceCrossing 10 ⟨s, hs⟩
  let q := (grimmettTraceExtendedWalkFour W).map duminilCopinFiveFreshIso.toHom
  have hsource : walkIsOpen
      (cubicGraphIsoConfigurationPullback duminilCopinFiveFreshIso omega)
      (grimmettTraceExtendedWalkFour W) :=
    selectedGrimmettTraceExtendedWalkFour_isOpen hs hcyl hfresh
  have hopen : walkIsOpen omega q :=
    walkIsOpen_map_cubicGraphIso duminilCopinFiveFreshIso
      (grimmettTraceExtendedWalkFour W) hsource
  have hsupport : ∀ z ∈ q.support, z ∈ duminilCopinRectangleVertices 5 := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hb := grimmettTraceExtendedWalkFour_support_bounds W hu
    rw [mem_duminilCopinRectangleVertices_iff]
    change (-5 : ℤ) ≤ duminilCopinFiveFreshIso u 0 ∧
      duminilCopinFiveFreshIso u 0 ≤ 5 ∧
      (-5 : ℤ) ≤ duminilCopinFiveFreshIso u 1 ∧
      duminilCopinFiveFreshIso u 1 ≤ 10
    simp only [duminilCopinFiveFreshIso_zero, duminilCopinFiveFreshIso_one]
    omega
  simp only [duminilCopinVerticalCrossingEvent, Set.mem_iUnion]
  refine ⟨duminilCopinFiveFreshIso (grimmettTraceLeftSecondOuterVertex W), ?_,
    duminilCopinFiveFreshIso (grimmettTraceRightSecondOuterVertex W), ?_,
    q, hopen, ?_⟩
  · rw [mem_duminilCopinRectangleBottom_iff]
    have hs' := mem_grimmettRectangleLeft_iff.mp W.start_mem
    simp only [duminilCopinFiveFreshIso_zero, duminilCopinFiveFreshIso_one]
    simp [grimmettTraceLeftSecondOuterVertex, grimmettTraceLeftOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hs']
    omega
  · rw [mem_duminilCopinRectangleTop_iff]
    have hf' := mem_grimmettRectangleRight_iff.mp W.finish_mem
    simp only [duminilCopinFiveFreshIso_zero, duminilCopinFiveFreshIso_one]
    simp [grimmettTraceRightSecondOuterVertex, grimmettTraceRightOuterVertex,
      cubicStepFrom, cubicDirectionIncrement, hf']
    omega
  · exact walkEdgeFinset_subset_duminilCopinRectangleEdges_of_support q hsupport

private theorem duminilCopinVerticalCrossingProbability_five_ge_one_thirty_second :
    (1 / 32 : ℝ) ≤
      duminilCopinVerticalCrossingProbability squareHalfDensity 5 := by
  unfold duminilCopinVerticalCrossingProbability
  calc
    (1 / 32 : ℝ) ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleFreshCrossingEventFour (2 * 5)) :=
      one_thirty_second_le_grimmettRectangleFreshCrossingEventFour_half 5 (by omega)
    _ = (bernoulliBondMeasure 2 squareHalfDensity).real
        (cubicGraphIsoEvent duminilCopinFiveFreshIso
          (grimmettRectangleFreshCrossingEventFour 10)) := by
      rw [bernoulliBondMeasure_real_cubicGraphIsoEvent squareHalfDensity
        duminilCopinFiveFreshIso
        (measurableSet_grimmettRectangleFreshCrossingEventFour 10)]
    _ ≤ (bernoulliBondMeasure 2 squareHalfDensity).real
        (duminilCopinVerticalCrossingEvent 5) :=
      measureReal_mono duminilCopinFiveFreshEvent_subset (measure_ne_top _ _)

/-- **Duminil-Copin, Graphical Representations of Lattice Spin Models, Proposition 2.14.**
At density `1/2`, the probability of a vertical crossing of `[-n,n] × [-n,2n]` is at least
`1/128` for every positive integer `n`. -/
theorem duminilCopin_proposition_2_14 (n : ℕ) (hn : 1 ≤ n) :
    (1 / 128 : ℝ) ≤ duminilCopinVerticalCrossingProbability squareHalfDensity n := by
  rcases hn.eq_or_lt with rfl | hn
  · exact (by norm_num : (1 / 128 : ℝ) ≤ (1 / 2) ^ (3 * 1)).trans
      (duminilCopinVerticalCrossingProbability_ge_straightPath 1)
  · have hn2 : 2 ≤ n := by omega
    rcases hn2.eq_or_lt with rfl | hn2
    · exact (by norm_num : (1 / 128 : ℝ) ≤ (1 / 2) ^ (3 * 2)).trans
        (duminilCopinVerticalCrossingProbability_ge_straightPath 2)
    · have hn3 : 3 ≤ n := by omega
      rcases hn3.eq_or_lt with rfl | hn3
      · exact (by norm_num : (1 / 128 : ℝ) ≤ 1 / 32).trans
          duminilCopinVerticalCrossingProbability_three_ge_one_thirty_second
      · have hn4 : 4 ≤ n := by omega
        rcases hn4.eq_or_lt with rfl | hn4
        · exact (by norm_num : (1 / 128 : ℝ) ≤ 1 / 16).trans
            duminilCopinVerticalCrossingProbability_four_ge_one_sixteenth
        · have hn5 : 5 ≤ n := by omega
          rcases hn5.eq_or_lt with rfl | hn5
          · exact (by norm_num : (1 / 128 : ℝ) ≤ 1 / 32).trans
              duminilCopinVerticalCrossingProbability_five_ge_one_thirty_second
          · have hn6 : 6 ≤ n := by omega
            apply duminilCopinVerticalCrossingProbability_ge_of_lowerBridge n (by omega)
            sorry

end Percolation
