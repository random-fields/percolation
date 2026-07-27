import Percolation.Extensions.ContinuumApproximation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Finite.Lattice

/-!
# Deterministic geometry of the Boolean model

This file constructs the literal continuum graph of radius-one balls and the many-to-one cube
projection used in Grimmett (12.37)--(12.41).  The probability law is deliberately separate:
the statements here apply to every locally finite point configuration.
-/

namespace Percolation

open Set SimpleGraph

/-- Euclidean points in dimension `d`, in the coordinate representation used by the chapter. -/
abbrev ContinuumPoint (d : ℕ) := Fin d → ℝ

/-- The coordinate formula used in the chapter is the ordinary Euclidean metric. -/
theorem coordinateEuclideanDist_eq_dist {d : ℕ} (u v : ContinuumPoint d) :
    coordinateEuclideanDist u v =
      dist (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
  rw [EuclideanSpace.dist_eq]
  unfold coordinateEuclideanDist
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Real.dist_eq]
  simpa using (sq_abs (u i - v i)).symm

theorem coordinateEuclideanDist_triangle {d : ℕ} (u v w : ContinuumPoint d) :
    coordinateEuclideanDist u w ≤
      coordinateEuclideanDist u v + coordinateEuclideanDist v w := by
  simp only [coordinateEuclideanDist_eq_dist]
  exact dist_triangle _ _ _

/-- The Euclidean distance is bounded by the coordinate `L¹` distance. -/
theorem coordinateEuclideanDist_le_sum_abs {d : ℕ} (u v : ContinuumPoint d) :
    coordinateEuclideanDist u v ≤ ∑ i, |u i - v i| := by
  unfold coordinateEuclideanDist
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      (∑ i, (u i - v i) ^ 2) = ∑ i, |u i - v i| ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (sq_abs (u i - v i)).symm
      _ ≤ (∑ i, |u i - v i|) ^ 2 := by
        simpa only [Finset.sum_const_zero, Finset.sum_const]
          using (Finset.sum_sq_le_sq_sum_of_nonneg
            (s := Finset.univ) (f := fun i : Fin d ↦ |u i - v i|)
            (fun i _hi ↦ abs_nonneg (u i - v i)))

/-- Index of the half-open mesh cube containing a continuum point. -/
noncomputable def continuumCubeIndex {d : ℕ} (n : ℕ) (u : ContinuumPoint d) : Cubic d :=
  fun i ↦ ⌊(n : ℝ) * u i + 1 / 2⌋

/-- The floor convention really places every point in its indexed half-open cube. -/
theorem continuumPoint_mem_indexCube {d n : ℕ} (hn : 0 < n) (u : ContinuumPoint d) :
    u ∈ continuumElementaryCube n (continuumCubeIndex n u) := by
  intro i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ((⌊(n : ℝ) * u i + 1 / 2⌋ : ℤ) : ℝ) ≤
      (n : ℝ) * u i + 1 / 2 := Int.floor_le _
  have hlt : (n : ℝ) * u i + 1 / 2 <
      ((⌊(n : ℝ) * u i + 1 / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one ((n : ℝ) * u i + 1 / 2)
  constructor <;> unfold continuumCubeCenter continuumCubeIndex
  · rw [sub_le_iff_le_add, div_le_iff₀ hnR]
    field_simp at hfloor ⊢
    linarith
  · rw [← sub_lt_iff_lt_add, lt_div_iff₀ hnR]
    field_simp at hlt ⊢
    linarith

/-- Membership in a positive-mesh half-open cube determines its integer index uniquely. -/
theorem continuumCubeIndex_eq_of_mem {d n : ℕ} (hn : 0 < n)
    {u : ContinuumPoint d} {x : Cubic d}
    (hu : u ∈ continuumElementaryCube n x) :
    continuumCubeIndex n u = x := by
  funext i
  unfold continuumCubeIndex
  rw [Int.floor_eq_iff]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo := (hu i).1
  have hhi := (hu i).2
  unfold continuumCubeCenter at hlo hhi
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  constructor
  · field_simp [hnne] at hlo ⊢
    linarith
  · field_simp [hnne] at hhi ⊢
    linarith

theorem continuumElementaryCube_unique {d n : ℕ} (hn : 0 < n)
    {u : ContinuumPoint d} {x y : Cubic d}
    (hux : u ∈ continuumElementaryCube n x)
    (huy : u ∈ continuumElementaryCube n y) : x = y := by
  rw [← continuumCubeIndex_eq_of_mem hn hux,
    ← continuumCubeIndex_eq_of_mem hn huy]

/-- Two points of one positive-mesh elementary cube differ by at most one mesh width in each
coordinate. -/
theorem abs_sub_le_inv_of_mem_continuumElementaryCube
    {d n : ℕ} (hn : 0 < n) {x : Cubic d} {u v : ContinuumPoint d}
    (hu : u ∈ continuumElementaryCube n x)
    (hv : v ∈ continuumElementaryCube n x) (i : Fin d) :
    |u i - v i| ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huLow := (hu i).1
  have huHigh := (hu i).2.le
  have hvLow := (hv i).1
  have hvHigh := (hv i).2.le
  have hwidth : (2 : ℝ) * (1 / (2 * n)) = 1 / n := by
    field_simp
  rw [abs_le]
  constructor <;> unfold continuumCubeCenter at huLow huHigh hvLow hvHigh <;> linarith

/-- The diameter of a mesh cube is at most `d/n`.  The source only needs a deterministic error
tending to zero; this `L¹` bound avoids introducing a square-root normalization. -/
theorem coordinateEuclideanDist_le_card_div_of_mem_continuumElementaryCube
    {d n : ℕ} (hn : 0 < n) {x : Cubic d} {u v : ContinuumPoint d}
    (hu : u ∈ continuumElementaryCube n x)
    (hv : v ∈ continuumElementaryCube n x) :
    coordinateEuclideanDist u v ≤ d / (n : ℝ) := by
  refine (coordinateEuclideanDist_le_sum_abs u v).trans ?_
  calc
    (∑ i : Fin d, |u i - v i|) ≤ ∑ _i : Fin d, (1 / (n : ℝ)) := by
      exact Finset.sum_le_sum fun i _hi ↦
        abs_sub_le_inv_of_mem_continuumElementaryCube hn hu hv i
    _ = d / (n : ℝ) := by simp [div_eq_mul_inv]

/-- Sharp Euclidean diameter of a mesh cube.  This is the `sqrt d / n` error used in
Grimmett's enlargement factor following (12.45). -/
theorem coordinateEuclideanDist_le_sqrt_card_div_of_mem_continuumElementaryCube
    {d n : ℕ} (hn : 0 < n) {x : Cubic d} {u v : ContinuumPoint d}
    (hu : u ∈ continuumElementaryCube n x)
    (hv : v ∈ continuumElementaryCube n x) :
    coordinateEuclideanDist u v ≤ Real.sqrt d / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold coordinateEuclideanDist
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      (∑ i : Fin d, (u i - v i) ^ 2) ≤
          ∑ _i : Fin d, (1 / (n : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
          (abs_sub_le_inv_of_mem_continuumElementaryCube hn hu hv i)
      _ = (d : ℝ) * (1 / (n : ℝ)) ^ 2 := by simp
      _ = (Real.sqrt d / (n : ℝ)) ^ 2 := by
        field_simp [ne_of_gt hnR]
        rw [Real.sq_sqrt (by positivity)]

/-- The graph of overlapping closed balls of an arbitrary radius. -/
def continuumPointGraphAtRadius {d : ℕ} (radius : ℝ)
    (P : Set (ContinuumPoint d)) : SimpleGraph P where
  Adj x y := x ≠ y ∧ coordinateEuclideanDist x.1 y.1 ≤ 2 * radius
  symm := by
    rintro x y ⟨hxy, hdist⟩
    exact ⟨hxy.symm, (coordinateEuclideanDist_comm _ _).le.trans hdist⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

@[simp]
theorem continuumPointGraphAtRadius_adj {d : ℕ} {radius : ℝ}
    {P : Set (ContinuumPoint d)} {x y : P} :
    (continuumPointGraphAtRadius radius P).Adj x y ↔
      x ≠ y ∧ coordinateEuclideanDist x.1 y.1 ≤ 2 * radius := Iff.rfl

/-- The graph of overlapping closed radius-one balls centred at points of `P`. -/
def continuumPointGraph {d : ℕ} (P : Set (ContinuumPoint d)) : SimpleGraph P where
  Adj x y := x ≠ y ∧ coordinateEuclideanDist x.1 y.1 ≤ 2
  symm := by
    rintro x y ⟨hxy, hdist⟩
    exact ⟨hxy.symm, (coordinateEuclideanDist_comm _ _).le.trans hdist⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

@[simp]
theorem continuumPointGraph_adj {d : ℕ} {P : Set (ContinuumPoint d)} {x y : P} :
    (continuumPointGraph P).Adj x y ↔
      x ≠ y ∧ coordinateEuclideanDist x.1 y.1 ≤ 2 := Iff.rfl

/-- Mesh cubes containing at least one point of `P`. -/
def continuumOccupiedCubeSet {d : ℕ} (P : Set (ContinuumPoint d)) (n : ℕ) :
    Set (Cubic d) :=
  {x | ∃ u ∈ P, u ∈ continuumElementaryCube n x}

theorem continuumCubeIndex_mem_occupied {d n : ℕ} (hn : 0 < n)
    {P : Set (ContinuumPoint d)} {u : ContinuumPoint d} (hu : u ∈ P) :
    continuumCubeIndex n u ∈ continuumOccupiedCubeSet P n :=
  ⟨u, hu, continuumPoint_mem_indexCube hn u⟩

/-- Overlapping balls project either to the same cube or to adjacent vertices of `L_n`. -/
theorem continuumCubeIndex_eq_or_approximationAdj {d n : ℕ} (hn : 0 < n)
    {u v : ContinuumPoint d} (hdist : coordinateEuclideanDist u v ≤ 2) :
    continuumCubeIndex n u = continuumCubeIndex n v ∨
      (continuumApproximationGraph d n).Adj
        (continuumCubeIndex n u) (continuumCubeIndex n v) := by
  by_cases huv : continuumCubeIndex n u = continuumCubeIndex n v
  · exact Or.inl huv
  · exact Or.inr ⟨huv, u, continuumPoint_mem_indexCube hn u,
      v, continuumPoint_mem_indexCube hn v, hdist⟩

/-- The occupied approximation graph. -/
def continuumOccupiedApproximationGraph {d : ℕ}
    (P : Set (ContinuumPoint d)) (n : ℕ) : SimpleGraph (continuumOccupiedCubeSet P n) :=
  (continuumApproximationGraph d n).induce (continuumOccupiedCubeSet P n)

/-- A deterministic point of every occupied mesh cube.  The choice is used only for the reverse
geometric comparison; injectivity follows from disjointness of the half-open cubes. -/
noncomputable def continuumOccupiedCubeRepresentative {d n : ℕ}
    (P : Set (ContinuumPoint d)) (x : continuumOccupiedCubeSet P n) : P :=
  ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩

theorem continuumOccupiedCubeRepresentative_mem {d n : ℕ}
    (P : Set (ContinuumPoint d)) (x : continuumOccupiedCubeSet P n) :
    (continuumOccupiedCubeRepresentative P x).1 ∈
      continuumElementaryCube n x.1 :=
  (Classical.choose_spec x.2).2

theorem continuumOccupiedCubeRepresentative_injective {d n : ℕ} (hn : 0 < n)
    (P : Set (ContinuumPoint d)) :
    Function.Injective (continuumOccupiedCubeRepresentative (n := n) P) := by
  intro x y hxy
  apply Subtype.ext
  apply continuumElementaryCube_unique hn
  · exact continuumOccupiedCubeRepresentative_mem P x
  · rw [hxy]
    exact continuumOccupiedCubeRepresentative_mem P y

/-- Adjacent occupied approximation cubes have representatives at distance at most the original
diameter plus twice the sharp Euclidean mesh error. -/
theorem continuumOccupiedCubeRepresentative_dist_le_of_adj
    {d n : ℕ} (hn : 0 < n) {P : Set (ContinuumPoint d)}
    {x y : continuumOccupiedCubeSet P n}
    (hxy : (continuumOccupiedApproximationGraph P n).Adj x y) :
    coordinateEuclideanDist
        (continuumOccupiedCubeRepresentative P x).1
        (continuumOccupiedCubeRepresentative P y).1 ≤
      2 + 2 * (Real.sqrt d / (n : ℝ)) := by
  obtain ⟨_hxy, u, hu, v, hv, huv⟩ := continuumApproximationGraph_adj.mp
    (SimpleGraph.induce_adj.mp hxy)
  have hxu := coordinateEuclideanDist_le_sqrt_card_div_of_mem_continuumElementaryCube
    hn (continuumOccupiedCubeRepresentative_mem P x) hu
  have hvy := coordinateEuclideanDist_le_sqrt_card_div_of_mem_continuumElementaryCube
    hn hv (continuumOccupiedCubeRepresentative_mem P y)
  have htriangle₁ := coordinateEuclideanDist_triangle
    (continuumOccupiedCubeRepresentative P x).1 u
    (continuumOccupiedCubeRepresentative P y).1
  have htriangle₂ := coordinateEuclideanDist_triangle u v
    (continuumOccupiedCubeRepresentative P y).1
  linarith

/-- The occupied approximation graph embeds homomorphically into the continuum graph after
enlarging ball radius by Grimmett's sharp mesh error `sqrt d / n`. -/
noncomputable def continuumOccupiedApproximationToEnlargedContinuumHom
    {d n : ℕ} (hn : 0 < n) (P : Set (ContinuumPoint d)) :
    continuumOccupiedApproximationGraph P n →g
      continuumPointGraphAtRadius (1 + Real.sqrt d / (n : ℝ)) P where
  toFun := continuumOccupiedCubeRepresentative P
  map_rel' := by
    intro x y hxy
    refine continuumPointGraphAtRadius_adj.mpr ⟨?_, ?_⟩
    · exact (continuumOccupiedCubeRepresentative_injective hn P).ne hxy.ne
    · have hdist := continuumOccupiedCubeRepresentative_dist_le_of_adj hn hxy
      convert hdist using 1 <;> ring

/-- A continuum walk projects to reachability in the occupied approximation graph; repeated
cube indices are contracted by the reflexive branch. -/
theorem continuumWalk_projects_to_reachable
    {d n : ℕ} (hn : 0 < n) {P : Set (ContinuumPoint d)}
    {x y : P} (w : (continuumPointGraph P).Walk x y) :
    (continuumOccupiedApproximationGraph P n).Reachable
      ⟨continuumCubeIndex n x.1, continuumCubeIndex_mem_occupied hn x.2⟩
      ⟨continuumCubeIndex n y.1, continuumCubeIndex_mem_occupied hn y.2⟩ := by
  induction w with
  | @nil u =>
      exact SimpleGraph.Reachable.refl
        (G := continuumOccupiedApproximationGraph P n)
        (u := ⟨continuumCubeIndex n u.1, continuumCubeIndex_mem_occupied hn u.2⟩)
  | @cons u v z huv w ih =>
      let uI : continuumOccupiedCubeSet P n :=
        ⟨continuumCubeIndex n u.1, continuumCubeIndex_mem_occupied hn u.2⟩
      let vI : continuumOccupiedCubeSet P n :=
        ⟨continuumCubeIndex n v.1, continuumCubeIndex_mem_occupied hn v.2⟩
      have huvIndex := continuumCubeIndex_eq_or_approximationAdj hn
        (continuumPointGraph_adj.mp huv).2
      have huvReach : (continuumOccupiedApproximationGraph P n).Reachable uI vI := by
        rcases huvIndex with heq | hadj
        · have huvI : uI = vI := by
            apply Subtype.ext
            exact heq
          rw [huvI]
        · exact (SimpleGraph.induce_adj.mpr hadj).reachable
      exact huvReach.trans ih

/-- A point configuration is locally finite at mesh `n` if every elementary cube contains only
finitely many of its points. -/
def ContinuumCubeLocallyFinite {d : ℕ} (P : Set (ContinuumPoint d)) (n : ℕ) : Prop :=
  ∀ x : Cubic d, (P ∩ continuumElementaryCube n x).Finite

/-- Vertices in the continuum component of a point `x`. -/
def continuumPointCluster {d : ℕ} {P : Set (ContinuumPoint d)} (x : P) : Set P :=
  {y | (continuumPointGraph P).Reachable x y}

/-- Vertices in the continuum component at an arbitrary ball radius. -/
def continuumPointClusterAtRadius {d : ℕ} (radius : ℝ)
    {P : Set (ContinuumPoint d)} (x : P) : Set P :=
  {y | (continuumPointGraphAtRadius radius P).Reachable x y}

/-- Existence of an infinite cluster of overlapping radius-one balls. -/
def HasInfiniteContinuumCluster {d : ℕ} (P : Set (ContinuumPoint d)) : Prop :=
  ∃ x : P, (continuumPointCluster x).Infinite

/-- Existence of an infinite continuum cluster at an arbitrary ball radius. -/
def HasInfiniteContinuumClusterAtRadius {d : ℕ}
    (radius : ℝ) (P : Set (ContinuumPoint d)) : Prop :=
  ∃ x : P, (continuumPointClusterAtRadius radius x).Infinite

/-- Existence of an infinite occupied cluster in the mesh approximation. -/
def HasInfiniteOccupiedApproximationCluster {d : ℕ}
    (P : Set (ContinuumPoint d)) (n : ℕ) : Prop :=
  ∃ x : continuumOccupiedCubeSet P n,
    {y | (continuumOccupiedApproximationGraph P n).Reachable x y}.Infinite

/-- Reverse deterministic comparison behind (12.45): an infinite occupied cluster in `L_n`
produces an infinite Boolean cluster after the radius is enlarged from `1` to
`1 + sqrt d / n`, exactly as in the source. -/
theorem hasInfiniteContinuumClusterAtRadius_of_occupiedApproximation
    {d n : ℕ} (hn : 0 < n) {P : Set (ContinuumPoint d)}
    (hinf : HasInfiniteOccupiedApproximationCluster P n) :
    HasInfiniteContinuumClusterAtRadius (1 + Real.sqrt d / (n : ℝ)) P := by
  obtain ⟨x, hxinf⟩ := hinf
  let f := continuumOccupiedCubeRepresentative (n := n) P
  let hom := continuumOccupiedApproximationToEnlargedContinuumHom hn P
  have himage : (f '' {y |
      (continuumOccupiedApproximationGraph P n).Reachable x y}).Infinite :=
    hxinf.image (continuumOccupiedCubeRepresentative_injective hn P).injOn
  refine ⟨f x, himage.mono ?_⟩
  rintro z ⟨y, hy, rfl⟩
  exact SimpleGraph.Reachable.map hom hy

theorem finite_continuumCubeIndex_fiber
    {d n : ℕ} (hn : 0 < n) {P : Set (ContinuumPoint d)}
    (hlocal : ContinuumCubeLocallyFinite P n) (z : Cubic d) :
    {u : P | continuumCubeIndex n u.1 = z}.Finite := by
  apply Set.Finite.of_finite_image (f := fun u : P ↦ u.1)
  · apply (hlocal z).subset
    rintro v ⟨u, hu, rfl⟩
    exact ⟨u.2, by
      rw [← hu]
      exact continuumPoint_mem_indexCube hn u.1⟩
  · exact Subtype.val_injective.injOn

/-- Deterministic content of the implication preceding (12.39): an infinite Boolean cluster
projects to an infinite open cluster of `L_n`. -/
theorem hasInfiniteOccupiedApproximationCluster_of_continuum
    {d n : ℕ} (hn : 0 < n) {P : Set (ContinuumPoint d)}
    (hlocal : ContinuumCubeLocallyFinite P n)
    (hinf : HasInfiniteContinuumCluster P) :
    HasInfiniteOccupiedApproximationCluster P n := by
  obtain ⟨x, hxinf⟩ := hinf
  let f : P → continuumOccupiedCubeSet P n := fun u ↦
    ⟨continuumCubeIndex n u.1, continuumCubeIndex_mem_occupied hn u.2⟩
  let C : Set P := continuumPointCluster x
  have himage : (f '' C).Infinite := by
    intro hfinite
    apply hxinf
    apply Set.Finite.of_finite_fibers f hfinite
    intro z hz
    exact (finite_continuumCubeIndex_fiber hn hlocal z.1).subset fun u hu ↦ by
      change continuumCubeIndex n u.1 = z.1
      exact congrArg Subtype.val hu.2
  let xI : continuumOccupiedCubeSet P n :=
    ⟨continuumCubeIndex n x.1, continuumCubeIndex_mem_occupied hn x.2⟩
  refine ⟨xI, himage.mono ?_⟩
  rintro z ⟨y, hyC, rfl⟩
  obtain ⟨w⟩ := hyC
  exact continuumWalk_projects_to_reachable hn w

end Percolation
