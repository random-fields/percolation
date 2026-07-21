import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite frameworks and rigidity

This file formalizes the geometric definitions used in Grimmett, Chapter 12, §12.6.  A
framework is an injective placement of the vertices of a finite graph in Euclidean space.  A
motion is a differentiable one-parameter family of injective placements which contains the
given placement and preserves every graph-edge length.  A motion is rigid when it preserves
all pairwise distances.

The linearized edge constraints are also packaged as a genuine linear map.  They are the
rigidity matrix written without choosing enumerations of the vertices or edges.  Generic
rigidity and the percolative critical parameters are developed in later files.
-/

namespace Percolation

open Set SimpleGraph
open scoped BigOperators RealInnerProductSpace

/-- The Euclidean coordinate space used for a `d`-dimensional framework. -/
abbrev FrameworkPoint (d : ℕ) := Fin d → ℝ

/-- Squared Euclidean distance in the unbundled coordinate representation. -/
def frameworkSqDist {d : ℕ} (x y : FrameworkPoint d) : ℝ :=
  ∑ i, (x i - y i) ^ 2

/-- Euclidean distance in the coordinate representation. -/
noncomputable def frameworkDist {d : ℕ} (x y : FrameworkPoint d) : ℝ :=
  Real.sqrt (frameworkSqDist x y)

theorem frameworkSqDist_nonneg {d : ℕ} (x y : FrameworkPoint d) :
    0 ≤ frameworkSqDist x y :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

@[simp]
theorem frameworkSqDist_self {d : ℕ} (x : FrameworkPoint d) :
    frameworkSqDist x x = 0 := by
  simp [frameworkSqDist]

theorem frameworkSqDist_comm {d : ℕ} (x y : FrameworkPoint d) :
    frameworkSqDist x y = frameworkSqDist y x := by
  unfold frameworkSqDist
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem frameworkDist_comm {d : ℕ} (x y : FrameworkPoint d) :
    frameworkDist x y = frameworkDist y x := by
  rw [frameworkDist, frameworkDist, frameworkSqDist_comm]

@[simp]
theorem frameworkDist_self {d : ℕ} (x : FrameworkPoint d) :
    frameworkDist x x = 0 := by
  simp [frameworkDist]

theorem frameworkDist_eq_iff_sqDist_eq {d : ℕ}
    {x y z w : FrameworkPoint d} :
    frameworkDist x y = frameworkDist z w ↔
      frameworkSqDist x y = frameworkSqDist z w := by
  constructor
  · intro h
    calc
      frameworkSqDist x y = (Real.sqrt (frameworkSqDist x y)) ^ 2 :=
        (Real.sq_sqrt (frameworkSqDist_nonneg _ _)).symm
      _ = (Real.sqrt (frameworkSqDist z w)) ^ 2 := by
        rw [show Real.sqrt (frameworkSqDist x y) =
          Real.sqrt (frameworkSqDist z w) by simpa [frameworkDist] using h]
      _ = frameworkSqDist z w := Real.sq_sqrt (frameworkSqDist_nonneg _ _)
  · intro h
    simp only [frameworkDist]
    rw [h]

/-- An injective placement of a finite graph in `ℝ^d`. -/
structure Framework {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  position : V → FrameworkPoint d
  injective_position : Function.Injective position

namespace Framework

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ}

instance : CoeFun (Framework G d) fun _ ↦ V → FrameworkPoint d :=
  ⟨Framework.position⟩

/-- A differentiable family of embeddings containing `F`, with all graph-edge lengths fixed.

The parameter is defined on all of `ℝ` so Mathlib's ordinary differentiability API applies, but
the source interval and every geometric obligation are restricted to `[0,1]`.  `baseTime`
records Grimmett's phrase that the family contains the prescribed framework; it need not be
silently identified with time zero. -/
structure Motion (F : Framework G d) where
  path : ℝ → V → FrameworkPoint d
  differentiableOn_path : ∀ v, DifferentiableOn ℝ (fun t ↦ path t v) (Icc 0 1)
  injective_path : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (path t)
  baseTime : ℝ
  baseTime_mem : baseTime ∈ Icc (0 : ℝ) 1
  path_baseTime : path baseTime = F.position
  preserves_edge_dist : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ⦃u v⦄,
    G.Adj u v → frameworkDist (path t u) (path t v) =
      frameworkDist (F u) (F v)

namespace Motion

variable {F : Framework G d}

instance : CoeFun (Motion F) fun _ ↦ ℝ → V → FrameworkPoint d :=
  ⟨Motion.path⟩

/-- Equation (12.27): every motion preserves the length of each graph edge. -/
theorem edge_dist_eq (M : Motion F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {u v : V} (huv : G.Adj u v) :
    frameworkDist (M t u) (M t v) = frameworkDist (F u) (F v) :=
  M.preserves_edge_dist t ht huv

/-- A motion is rigid when it preserves every pairwise distance, not only edge lengths. -/
def IsRigid (M : Motion F) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v,
    frameworkDist (M t u) (M t v) = frameworkDist (F u) (F v)

/-- The constant family is always a motion. -/
noncomputable def constant (F : Framework G d) : Motion F where
  path := fun _ ↦ F.position
  differentiableOn_path := fun _ ↦ differentiableOn_const _
  injective_path := fun _ _ ↦ F.injective_position
  baseTime := 0
  baseTime_mem := by constructor <;> norm_num
  path_baseTime := rfl
  preserves_edge_dist := by simp

theorem constant_isRigid (F : Framework G d) : (constant F).IsRigid := by
  intro t ht u v
  rfl

end Motion

/-- A framework is rigid when all of its motions are rigid. -/
def IsRigid (F : Framework G d) : Prop :=
  ∀ M : Motion F, M.IsRigid

/-- A framework on a complete graph is rigid: every pair is already an edge (apart from the
trivial diagonal case). -/
theorem isRigid_of_top (F : Framework (⊤ : SimpleGraph V) d) : F.IsRigid := by
  intro M t ht u v
  by_cases huv : u = v
  · subst v
    simp
  · exact M.edge_dist_eq ht ((SimpleGraph.top_adj u v).2 huv)

/-! ### The coordinate-free rigidity matrix

The domain is a velocity vector at every vertex.  The row belonging to `{u,v}` is the linear
functional `Σ i, (F u i - F v i) * (X u i - X v i)`.  Using `Sym2.lift` makes the row independent
of the arbitrary ordering of the two endpoints.
-/

/-- Linearized length constraint associated with one unordered vertex pair. -/
def rigidityConstraint (F : Framework G d) (e : Sym2 V)
    (X : V → FrameworkPoint d) : ℝ :=
  Sym2.lift
    ⟨fun u v ↦ ∑ i, (F u i - F v i) * (X u i - X v i), by
      intro u v
      apply Finset.sum_congr rfl
      intro i _hi
      ring⟩ e

@[simp]
theorem rigidityConstraint_mk (F : Framework G d) (u v : V)
    (X : V → FrameworkPoint d) :
    rigidityConstraint F s(u, v) X =
      ∑ i, (F u i - F v i) * (X u i - X v i) := by
  simp [rigidityConstraint, Sym2.lift_mk]

theorem rigidityConstraint_add (F : Framework G d) (e : Sym2 V)
    (X Y : V → FrameworkPoint d) :
    rigidityConstraint F e (X + Y) =
      rigidityConstraint F e X + rigidityConstraint F e Y := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [rigidityConstraint_mk, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp
      ring

theorem rigidityConstraint_smul (F : Framework G d) (e : Sym2 V)
    (c : ℝ) (X : V → FrameworkPoint d) :
    rigidityConstraint F e (c • X) = c * rigidityConstraint F e X := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [rigidityConstraint_mk, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp
      ring

/-- The rigidity matrix as a linear map from vertex velocities to one scalar constraint per
graph edge. -/
def rigidityLinearMap (F : Framework G d) :
    (V → FrameworkPoint d) →ₗ[ℝ] (G.edgeSet → ℝ) where
  toFun := fun X e ↦ rigidityConstraint F e.1 X
  map_add' := by
    intro X Y
    funext e
    exact rigidityConstraint_add F e.1 X Y
  map_smul' := by
    intro c X
    funext e
    exact rigidityConstraint_smul F e.1 c X

@[simp]
theorem rigidityLinearMap_apply (F : Framework G d)
    (X : V → FrameworkPoint d) (e : G.edgeSet) :
    rigidityLinearMap F X e = rigidityConstraint F e.1 X := rfl

/-- Infinitesimal motions are exactly the kernel of the rigidity matrix. -/
def InfinitesimalMotion (F : Framework G d) : Submodule ℝ (V → FrameworkPoint d) :=
  LinearMap.ker (rigidityLinearMap F)

theorem mem_infinitesimalMotion_iff (F : Framework G d)
    (X : V → FrameworkPoint d) :
    X ∈ F.InfinitesimalMotion ↔
      ∀ e : G.edgeSet, rigidityConstraint F e.1 X = 0 := by
  rw [InfinitesimalMotion, LinearMap.mem_ker]
  constructor
  · intro h e
    exact congrFun h e
  · intro h
    funext e
    exact h e

end Framework

/-! ### Source-facing aliases and algebraic generic rigidity -/

/-- Source-facing name for a differentiable framework motion. -/
abbrev FrameworkMotion {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (F : Framework G d) :=
  Framework.Motion F

/-- Source-facing name for the rigidity matrix viewed as a linear map. -/
abbrev RigidityMatrix {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (F : Framework G d) :=
  Framework.rigidityLinearMap F

/-- Maxwell's full-rank value for a `d`-dimensional framework on `n` vertices.  The subtraction
is natural-number subtraction; source-facing uses require `d+1≤n`, so no junk underflow is
silently interpreted as a rigidity assertion. -/
def expectedRigidityRank (d n : ℕ) : ℕ :=
  d * n - d * (d + 1) / 2

/-- Algebraic generic rigidity of a finite graph.  Existence of one placement at the maximal
rank is the standard measure-free replacement for the book's unspecified "natural probability
measure" on embeddings.  The cardinality guard is explicit because Maxwell's rank formula is
only the intended one once there are at least `d+1` vertices. -/
def GenericallyRigid {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  G.Connected ∧ d + 1 ≤ Fintype.card V ∧
    ∃ F : Framework G d,
      expectedRigidityRank d (Fintype.card V) ≤
        Module.finrank ℝ (LinearMap.range (Framework.rigidityLinearMap F))

/-- Regard a placement for a graph as a placement for a supergraph on the same vertices. -/
def Framework.ofLE {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ} (_hGH : G ≤ H) (F : Framework G d) :
    Framework H d where
  position := F.position
  injective_position := F.injective_position

/-- Restriction of a row vector on the edges of a supergraph to the edges of a subgraph. -/
def rigidityEdgeRestriction {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) :
    (H.edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearMap.pi fun e ↦ LinearMap.proj
    (⟨e.1, SimpleGraph.edgeSet_mono hGH e.2⟩ : H.edgeSet)

@[simp]
theorem rigidityEdgeRestriction_apply {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) (X : H.edgeSet → ℝ) (e : G.edgeSet) :
    rigidityEdgeRestriction hGH X e =
      X ⟨e.1, SimpleGraph.edgeSet_mono hGH e.2⟩ := rfl

theorem rigidityLinearMap_ofLE {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ} (hGH : G ≤ H) (F : Framework G d) :
    Framework.rigidityLinearMap F =
      (rigidityEdgeRestriction hGH).comp
        (Framework.rigidityLinearMap (F.ofLE hGH)) := by
  ext X e
  rfl

/-- Adding edges cannot decrease the rank of the rigidity matrix. -/
theorem rigidityLinearMap_finrank_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ} (hGH : G ≤ H) (F : Framework G d) :
    Module.finrank ℝ (LinearMap.range (Framework.rigidityLinearMap F)) ≤
      Module.finrank ℝ
        (LinearMap.range (Framework.rigidityLinearMap (F.ofLE hGH))) := by
  rw [rigidityLinearMap_ofLE hGH F]
  exact Module.finrank_le_finrank_of_rank_le_rank
    (Cardinal.lift_le.2 (LinearMap.rank_comp_le_right
      (Framework.rigidityLinearMap (F.ofLE hGH)) (rigidityEdgeRestriction hGH)))
    (Module.rank_lt_aleph0 ℝ
      (LinearMap.range (Framework.rigidityLinearMap (F.ofLE hGH))))

/-- Generic rigidity is monotone under adding edges. -/
theorem GenericallyRigid.mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ} (hGH : G ≤ H)
    (hG : GenericallyRigid G d) : GenericallyRigid H d := by
  refine ⟨hG.1.mono hGH, hG.2.1, ?_⟩
  obtain ⟨F, hF⟩ := hG.2.2
  exact ⟨F.ofLE hGH, hF.trans (rigidityLinearMap_finrank_mono hGH F)⟩

/-- A finite vertex set supports the induced finite subframework of `G`. -/
def genericallyRigidInducedOn {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (W : Finset V) : Prop :=
  GenericallyRigid (G.induce (W : Set V)) d

/-- Source definition of rigidity for an infinite graph: every finite part is contained in a
finite induced generically rigid part.  Quantifying over finite vertex sets is equivalent to
quantifying over finite subgraphs because the containing graph is induced. -/
def InfinitelyGenericallyRigid {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ W : Finset V, ∃ U : Finset V, W ⊆ U ∧ genericallyRigidInducedOn G d U

theorem InfinitelyGenericallyRigid.mono {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ}
    (hmono : ∀ U : Finset V,
      genericallyRigidInducedOn G d U → genericallyRigidInducedOn H d U)
    (hG : InfinitelyGenericallyRigid G d) :
    InfinitelyGenericallyRigid H d := by
  intro W
  obtain ⟨U, hWU, hU⟩ := hG W
  exact ⟨U, hWU, hmono U hU⟩

end Percolation
