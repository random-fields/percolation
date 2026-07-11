import Percolation.Bernoulli.StochasticDomination
import Percolation.Critical.Regions
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Prod.Lex

/-!
# Finite-box clusters and static block events

This file gives the deterministic finite-graph vocabulary used in Grimmett's static
renormalization argument.  All component vertex sets are converted back to ambient cubic
vertices, so their diameter and face-crossing properties use the same geometry as Chapter 6.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The open graph induced on the translated coordinate box centered at `x`. -/
noncomputable def finiteBoxOpenGraph
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) :
    SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n} :=
  (cubicOpenGraph d ω).induce (cubicMetricBox d x n : Set (Cubic d))

/-- The induced open graph in a box is completely determined by the internal box edges. -/
theorem finiteBoxOpenGraph_eq_of_agree {d : ℕ} {ω η : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (hagree : ∀ e ∈ cubicBoxEdges d x n, (e ∈ ω ↔ e ∈ η)) :
    finiteBoxOpenGraph d ω x n = finiteBoxOpenGraph d η x n := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  change (cubicOpenGraph d ω).Adj u.1 v.1 ↔ (cubicOpenGraph d η).Adj u.1 v.1
  constructor
  · intro huv
    obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp huv
    let e : CubicEdge d :=
      ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr hadj⟩
    have hebox : e ∈ cubicBoxEdges d x n := by
      obtain ⟨a, ha⟩ := cubicGraph_adj_iff_exists_stepFrom u.1 v.1 |>.mp hadj
      have heq : e = cubicStepEdge u.1 a := by
        apply Subtype.ext
        simp [e, cubicStepEdge, ha]
      rw [heq]
      exact cubicStepEdge_mem_cubicBoxEdges u.2 (by simpa [ha] using v.2)
    exact cubicOpenGraph_adj.mpr ⟨hadj, (hagree e hebox).mp hopen⟩
  · intro huv
    obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp huv
    let e : CubicEdge d :=
      ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr hadj⟩
    have hebox : e ∈ cubicBoxEdges d x n := by
      obtain ⟨a, ha⟩ := cubicGraph_adj_iff_exists_stepFrom u.1 v.1 |>.mp hadj
      have heq : e = cubicStepEdge u.1 a := by
        apply Subtype.ext
        simp [e, cubicStepEdge, ha]
      rw [heq]
      exact cubicStepEdge_mem_cubicBoxEdges u.2 (by simpa [ha] using v.2)
    exact cubicOpenGraph_adj.mpr ⟨hadj, (hagree e hebox).mpr hopen⟩

/-! ### Graph-parametric component data

The following definitions depend on the configuration only through the finite induced graph.
This factoring is what makes static good-box events provably finite cylinders despite the
dependent type of connected components. -/

/-- Coordinates relative to the center of a translated box, with lexicographic order. -/
def boxRelativeVertex {d : ℕ} (x y : Cubic d) : Lex (Cubic d) :=
  toLex fun i ↦ y i - x i

/-- Ambient vertices in a component of an arbitrary graph on the fixed box subtype. -/
noncomputable def finiteBoxGraphComponentVertices {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBox d x n).filter fun y ↦ ∃ hy : y ∈ cubicMetricBox d x n,
    (⟨y, hy⟩ : {z : Cubic d // z ∈ cubicMetricBox d x n}) ∈ C.supp

noncomputable def finiteBoxGraphComponentCard {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : ℕ :=
  (finiteBoxGraphComponentVertices C).card

noncomputable def finiteBoxGraphComponentDiameter {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : ℕ :=
  (finiteBoxGraphComponentVertices C).sup fun u ↦
    (finiteBoxGraphComponentVertices C).sup fun v ↦ cubicLInfDist u v

def finiteBoxGraphComponentCrossesDirection {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) (i : Fin d) : Prop :=
  (∃ u ∈ finiteBoxGraphComponentVertices C, u ∈ cubicBoxFace d x n i false) ∧
    ∃ v ∈ finiteBoxGraphComponentVertices C, v ∈ cubicBoxFace d x n i true

def finiteBoxGraphComponentIsCrossing {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : Prop :=
  ∀ i : Fin d, finiteBoxGraphComponentCrossesDirection C i

noncomputable def finiteBoxGraphComponentAnchor {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : Lex (Cubic d) := by
  classical
  let s := (finiteBoxGraphComponentVertices C).image (boxRelativeVertex x)
  have hnonempty : (finiteBoxGraphComponentVertices C).Nonempty := by
    obtain ⟨y, hy⟩ := C.nonempty_supp
    exact ⟨y.1, by
      simp only [finiteBoxGraphComponentVertices, Finset.mem_filter]
      exact ⟨y.2, y.2, hy⟩⟩
  exact s.min' (hnonempty.image (boxRelativeVertex x))

noncomputable def finiteBoxGraphComponentKey {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) : ℕ ×ₗ OrderDual (Lex (Cubic d)) :=
  toLex (finiteBoxGraphComponentCard C,
    OrderDual.toDual (finiteBoxGraphComponentAnchor C))

private theorem finiteBoxGraphComponents_nonempty {d : ℕ} (x : Cubic d) (n : ℕ)
    (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}) :
    (Finset.univ : Finset G.ConnectedComponent).Nonempty := by
  let x' : {y : Cubic d // y ∈ cubicMetricBox d x n} :=
    ⟨x, by simp [mem_cubicMetricBox]⟩
  exact ⟨G.connectedComponentMk x', Finset.mem_univ _⟩

/-- Largest component selected by size and the translation-neutral anchor tie-break. -/
noncomputable def finiteBoxGraphLargestComponent {d : ℕ} (x : Cubic d) (n : ℕ)
    (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}) : G.ConnectedComponent :=
  Classical.choose <| Finset.exists_max_image (Finset.univ : Finset G.ConnectedComponent)
    finiteBoxGraphComponentKey (finiteBoxGraphComponents_nonempty x n G)

/-- Graph-parametric form of Grimmett's `ε`-good predicate. -/
def FiniteBoxGraph.IsEpsilonGood {d : ℕ} (p : I) (ε : ℝ) (x : Cubic d) (n : ℕ)
    (G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}) : Prop :=
  let M := finiteBoxGraphLargestComponent x n G
  finiteBoxGraphComponentIsCrossing M ∧
    (∀ C : G.ConnectedComponent,
      n ≤ finiteBoxGraphComponentDiameter C → C = M) ∧
    (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤
      finiteBoxGraphComponentCard M

/-- The finite set of connected components of the open graph in a box. -/
noncomputable def boxOpenComponents
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) :
    Finset (finiteBoxOpenGraph d ω x n).ConnectedComponent := by
  classical
  exact Finset.univ

/-- Ambient cubic vertices belonging to a finite-box component. -/
noncomputable def boxComponentVertices {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBox d x n).filter fun y ↦ ∃ hy : y ∈ cubicMetricBox d x n,
    (⟨y, hy⟩ : {z : Cubic d // z ∈ cubicMetricBox d x n}) ∈ C.supp

theorem mem_boxComponentVertices_iff {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    {C : (finiteBoxOpenGraph d ω x n).ConnectedComponent} {y : Cubic d} :
    y ∈ boxComponentVertices C ↔
      ∃ hy : y ∈ cubicMetricBox d x n,
        (⟨y, hy⟩ : {z : Cubic d // z ∈ cubicMetricBox d x n}) ∈ C.supp := by
  classical
  simp only [boxComponentVertices, Finset.mem_filter]
  constructor
  · rintro ⟨_ymem, h⟩
    exact h
  · intro h
    exact ⟨h.choose, h⟩

theorem boxComponentVertices_nonempty {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) :
    (boxComponentVertices C).Nonempty := by
  obtain ⟨y, hy⟩ := C.nonempty_supp
  exact ⟨y.1, mem_boxComponentVertices_iff.mpr ⟨y.2, hy⟩⟩

/-- Number of vertices in a finite-box component. -/
noncomputable def boxComponentCard {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) : ℕ :=
  (boxComponentVertices C).card

/-- Coordinate diameter of a finite-box component. -/
noncomputable def boxComponentDiameter {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) : ℕ :=
  (boxComponentVertices C).sup fun u ↦
    (boxComponentVertices C).sup fun v ↦ cubicLInfDist u v

theorem boxComponentDiameter_le_two_mul {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) :
    boxComponentDiameter C ≤ 2 * n := by
  rw [boxComponentDiameter]
  apply Finset.sup_le
  intro u hu
  apply Finset.sup_le
  intro v hv
  have hu' := mem_boxComponentVertices_iff.mp hu
  have hv' := mem_boxComponentVertices_iff.mp hv
  exact (cubicLInfDist_triangle u x v).trans <| by
    rw [cubicLInfDist_comm u x]
    have hux : cubicLInfDist x u ≤ n := mem_cubicMetricBox_iff_lInfDist_le.mp hu'.choose
    have hxv : cubicLInfDist x v ≤ n := mem_cubicMetricBox_iff_lInfDist_le.mp hv'.choose
    omega

/-- A component meets both signed faces perpendicular to coordinate `i`. -/
def boxComponentCrossesDirection {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) (i : Fin d) : Prop :=
  (∃ u ∈ boxComponentVertices C, u ∈ cubicBoxFace d x n i false) ∧
    ∃ v ∈ boxComponentVertices C, v ∈ cubicBoxFace d x n i true

/-- A crossing component meets both faces in every coordinate direction. -/
def boxComponentIsCrossing {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) : Prop :=
  ∀ i : Fin d, boxComponentCrossesDirection C i

theorem boxComponentDiameter_eq_two_mul_of_crosses {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ} (hd : 1 ≤ d)
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent)
    (hC : boxComponentIsCrossing C) : boxComponentDiameter C = 2 * n := by
  apply Nat.le_antisymm (boxComponentDiameter_le_two_mul C)
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨u, huC, huF⟩ := (hC i).1
  obtain ⟨v, hvC, hvF⟩ := (hC i).2
  have huv : cubicLInfDist u v = 2 * n := by
    apply Nat.le_antisymm
    · exact (cubicLInfDist_triangle u x v).trans <| by
        have hu := mem_cubicBoxFace.mp huF
        have hv := mem_cubicBoxFace.mp hvF
        have hux : cubicLInfDist x u ≤ n :=
          mem_cubicMetricBox_iff_lInfDist_le.mp
            (mem_boxComponentVertices_iff.mp huC).choose
        have hxv : cubicLInfDist x v ≤ n :=
          mem_cubicMetricBox_iff_lInfDist_le.mp
            (mem_boxComponentVertices_iff.mp hvC).choose
        rw [cubicLInfDist_comm x u] at hux
        omega
    · have hu := (mem_cubicBoxFace.mp huF).1
      have hv := (mem_cubicBoxFace.mp hvF).1
      have hcoord := cubicLInfDist_coord_le u v i
      simp [i] at hu hv
      have : (v i - u i).natAbs = 2 * n := by
        rw [hu, hv]
        have hz : x i + (n : ℤ) - (x i - (n : ℤ)) = 2 * (n : ℤ) := by omega
        rw [hz]
        apply Nat.cast_injective (R := ℤ)
        rw [Int.natCast_natAbs, abs_of_nonneg (by positivity)]
        norm_num
      omega
  rw [boxComponentDiameter]
  calc
    2 * n = cubicLInfDist u v := huv.symm
    _ ≤ (boxComponentVertices C).sup (fun z ↦
        (boxComponentVertices C).sup fun w ↦ cubicLInfDist z w) := by
      have hinner : cubicLInfDist u v ≤
          (boxComponentVertices C).sup (fun w ↦ cubicLInfDist u w) :=
        Finset.le_sup hvC
      have houter : (boxComponentVertices C).sup (fun w ↦ cubicLInfDist u w) ≤
          (boxComponentVertices C).sup (fun z ↦
            (boxComponentVertices C).sup fun w ↦ cubicLInfDist z w) :=
        Finset.le_sup (s := boxComponentVertices C)
          (f := fun z ↦ (boxComponentVertices C).sup fun w ↦ cubicLInfDist z w) huC
      exact hinner.trans houter

/-! ### Canonical largest component -/

/-- Lexicographically first relative vertex of a nonempty component. -/
noncomputable def boxComponentAnchor {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) : Lex (Cubic d) := by
  classical
  let s := (boxComponentVertices C).image (boxRelativeVertex x)
  exact s.min' ((boxComponentVertices_nonempty C).image (boxRelativeVertex x))

theorem exists_vertex_boxComponentAnchor {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) :
    ∃ y ∈ boxComponentVertices C, boxRelativeVertex x y = boxComponentAnchor C := by
  classical
  let s := (boxComponentVertices C).image (boxRelativeVertex x)
  have hmem : boxComponentAnchor C ∈ s := by
    simpa [boxComponentAnchor, s] using
      s.min'_mem ((boxComponentVertices_nonempty C).image (boxRelativeVertex x))
  simpa [s] using hmem

theorem boxRelativeVertex_injective {d : ℕ} (x : Cubic d) :
    Function.Injective (boxRelativeVertex x) := by
  intro y z h
  have h' := congrArg ofLex h
  change (fun i ↦ y i - x i) = (fun i ↦ z i - x i) at h'
  apply funext
  intro i
  have hi := congrFun h' i
  omega

theorem boxComponent_eq_of_anchor_eq {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    {C D : (finiteBoxOpenGraph d ω x n).ConnectedComponent}
    (h : boxComponentAnchor C = boxComponentAnchor D) : C = D := by
  obtain ⟨y, hyC, hyAnchor⟩ := exists_vertex_boxComponentAnchor C
  obtain ⟨z, hzD, hzAnchor⟩ := exists_vertex_boxComponentAnchor D
  have hyz : y = z := boxRelativeVertex_injective x (hyAnchor.trans (h.trans hzAnchor.symm))
  obtain ⟨hyBox, hySupp⟩ := mem_boxComponentVertices_iff.mp hyC
  obtain ⟨hzBox, hzSupp⟩ := mem_boxComponentVertices_iff.mp hzD
  subst z
  have hySuppD :
      (⟨y, hyBox⟩ : {q : Cubic d // q ∈ cubicMetricBox d x n}) ∈ D.supp := by
    simpa using hzSupp
  have hC := (C.mem_supp_iff (⟨y, hyBox⟩ :
    {q : Cubic d // q ∈ cubicMetricBox d x n})).mp hySupp
  have hD := (D.mem_supp_iff (⟨y, hyBox⟩ :
    {q : Cubic d // q ∈ cubicMetricBox d x n})).mp hySuppD
  exact hC.symm.trans hD

/-- Components are ordered first by cardinality and then by the reverse of their relative
anchor, so the maximum has largest size and a deterministic translation-neutral tie-break. -/
noncomputable def boxComponentKey {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ}
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) :
    ℕ ×ₗ OrderDual (Lex (Cubic d)) :=
  toLex (boxComponentCard C, OrderDual.toDual (boxComponentAnchor C))

theorem boxComponentKey_injective {d : ℕ} {ω : EdgeConfiguration d}
    {x : Cubic d} {n : ℕ} :
    Function.Injective (boxComponentKey (d := d) (ω := ω) (x := x) (n := n)) := by
  intro C D h
  have h' := congrArg ofLex h
  have hAnchor : boxComponentAnchor C = boxComponentAnchor D := by
    exact congrArg (fun q : ℕ × OrderDual (Lex (Cubic d)) ↦
      OrderDual.ofDual q.2) h'
  exact boxComponent_eq_of_anchor_eq hAnchor

private theorem boxOpenComponents_nonempty
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) :
    (boxOpenComponents d ω x n).Nonempty := by
  let x' : {y : Cubic d // y ∈ cubicMetricBox d x n} :=
    ⟨x, by simp [mem_cubicMetricBox]⟩
  exact ⟨(finiteBoxOpenGraph d ω x n).connectedComponentMk x', by simp [boxOpenComponents]⟩

/-- Canonical largest open component in a finite box. -/
noncomputable def boxLargestCluster
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) :
    (finiteBoxOpenGraph d ω x n).ConnectedComponent :=
  Classical.choose <|
    Finset.exists_max_image (boxOpenComponents d ω x n) boxComponentKey
      (boxOpenComponents_nonempty d ω x n)

theorem boxLargestCluster_mem_components
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ) :
    boxLargestCluster d ω x n ∈ boxOpenComponents d ω x n :=
  (Classical.choose_spec <|
    Finset.exists_max_image (boxOpenComponents d ω x n) boxComponentKey
      (boxOpenComponents_nonempty d ω x n)).1

theorem boxComponentCard_le_largest
    (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) (n : ℕ)
    (C : (finiteBoxOpenGraph d ω x n).ConnectedComponent) :
    boxComponentCard C ≤ boxComponentCard (boxLargestCluster d ω x n) := by
  have hkey := (Classical.choose_spec <|
    Finset.exists_max_image (boxOpenComponents d ω x n) boxComponentKey
      (boxOpenComponents_nonempty d ω x n)).2 C (by simp [boxOpenComponents])
  exact (Prod.Lex.toLex_le_toLex.mp hkey).elim (fun h ↦ h.le) (fun h ↦ h.1.le)

/-- Grimmett's event that the translated box is `ε`-good. -/
def epsilonGoodBoxEvent
    (d : ℕ) (p : I) (ε : ℝ) (x : Cubic d) (n : ℕ) : Set (EdgeConfiguration d) :=
  {ω | FiniteBoxGraph.IsEpsilonGood p ε x n (finiteBoxOpenGraph d ω x n)}

theorem dependsOn_epsilonGoodBoxEvent
    (d : ℕ) (p : I) (ε : ℝ) (x : Cubic d) (n : ℕ) :
    DependsOn (cubicBoxEdges d x n) (epsilonGoodBoxEvent d p ε x n) := by
  intro ω η hagree
  change FiniteBoxGraph.IsEpsilonGood p ε x n (finiteBoxOpenGraph d ω x n) ↔
    FiniteBoxGraph.IsEpsilonGood p ε x n (finiteBoxOpenGraph d η x n)
  rw [finiteBoxOpenGraph_eq_of_agree hagree]

theorem measurableSet_epsilonGoodBoxEvent
    (d : ℕ) (p : I) (ε : ℝ) (x : Cubic d) (n : ℕ) :
    MeasurableSet (epsilonGoodBoxEvent d p ε x n) :=
  (dependsOn_epsilonGoodBoxEvent d p ε x n).measurableSet

/-- The static good-block site field `X_{ε,x}(n)`. -/
def epsilonGoodBlockCenter {d : ℕ} (n : ℕ) (x : Cubic d) : Cubic d :=
  cubicScale (n : ℤ) x

/-- The static good-block site field `X_{ε,x}(n)`, indexed on the coarse lattice.  Scaling the
box centers is essential: without it the claimed finite-range dependence would be false. -/
def epsilonGoodBlockField
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (ω : EdgeConfiguration d) : Set (Cubic d) :=
  {x | ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n}

@[simp]
theorem epsilonGoodBlockCenter_zero {d : ℕ} (x : Cubic d) :
    epsilonGoodBlockCenter 0 x = cubicOrigin := by
  funext i
  simp [epsilonGoodBlockCenter, cubicScale, cubicOrigin]

/-- Edge supports of coarse blocks whose indices are more than `3d` apart are disjoint.  The
constant is deliberately the source's conservative `3d`; the coordinate estimate below is
slightly stronger. -/
theorem disjoint_cubicBoxEdges_epsilonGoodBlockCenter {d n : ℕ} (hn : 1 ≤ n)
    {u v : Cubic d} (hfar : 3 * d < cubicL1Dist u v) :
    Disjoint
      (cubicBoxEdges d (epsilonGoodBlockCenter n u) n)
      (cubicBoxEdges d (epsilonGoodBlockCenter n v) n) := by
  classical
  rw [Finset.disjoint_left]
  intro e heu hev
  let z : Cubic d := e.1.out.1
  have hzu : z ∈ cubicMetricBox d (epsilonGoodBlockCenter n u) n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heu (by
      change e.1.out.1 ∈ (e : Sym2 (Cubic d))
      exact Sym2.out_fst_mem (e : Sym2 (Cubic d)))
  have hzv : z ∈ cubicMetricBox d (epsilonGoodBlockCenter n v) n :=
    endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges hev (by
      change e.1.out.1 ∈ (e : Sym2 (Cubic d))
      exact Sym2.out_fst_mem (e : Sym2 (Cubic d)))
  have hcenter : cubicLInfDist (epsilonGoodBlockCenter n u)
      (epsilonGoodBlockCenter n v) ≤ 2 * n := by
    calc
      cubicLInfDist (epsilonGoodBlockCenter n u) (epsilonGoodBlockCenter n v) ≤
          cubicLInfDist (epsilonGoodBlockCenter n u) z +
            cubicLInfDist z (epsilonGoodBlockCenter n v) :=
        cubicLInfDist_triangle _ _ _
      _ ≤ n + n := Nat.add_le_add
        (mem_cubicMetricBox_iff_lInfDist_le.mp hzu)
        (by rw [cubicLInfDist_comm]; exact mem_cubicMetricBox_iff_lInfDist_le.mp hzv)
      _ = 2 * n := by omega
  have hcoord : ∀ i : Fin d, (v i - u i).natAbs ≤ 2 := by
    intro i
    have hi := (cubicLInfDist_coord_le
      (epsilonGoodBlockCenter n u) (epsilonGoodBlockCenter n v) i).trans hcenter
    have heq :
        (epsilonGoodBlockCenter n v i - epsilonGoodBlockCenter n u i).natAbs =
          n * (v i - u i).natAbs := by
      rw [show epsilonGoodBlockCenter n v i - epsilonGoodBlockCenter n u i =
          (n : ℤ) * (v i - u i) by
        simp [epsilonGoodBlockCenter, cubicScale]
        ring, Int.natAbs_mul]
      simp
    have hmul : n * (v i - u i).natAbs ≤ n * 2 := by
      rw [heq] at hi
      simpa [mul_comm] using hi
    exact Nat.le_of_mul_le_mul_left hmul hn
  have hl1 : cubicL1Dist u v ≤ 2 * d := by
    rw [cubicL1Dist]
    calc
      (∑ i : Fin d, (v i - u i).natAbs) ≤ ∑ _i : Fin d, 2 :=
        Finset.sum_le_sum fun i _hi ↦ hcoord i
      _ = 2 * d := by simp [mul_comm]
  omega

theorem measurable_epsilonGoodBlockField
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) :
    Measurable (epsilonGoodBlockField d p ε n) := by
  change Measurable (MeasurableEquiv.setOf ∘
    fun (ω : EdgeConfiguration d) (x : Cubic d) ↦
      (ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n : Prop))
  apply Measurable.comp (by fun_prop)
  apply measurable_pi_lambda
  intro x
  apply measurable_to_prop
  convert measurableSet_epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n using 1
  ext ω
  simp

/-- Law of the coarse good-block field under Bernoulli bond percolation. -/
noncomputable def epsilonGoodBlockLaw
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) : Measure (Set (Cubic d)) :=
  (bernoulliBondMeasure d p).map (epsilonGoodBlockField d p ε n)

instance epsilonGoodBlockLaw_isProbabilityMeasure
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) :
    IsProbabilityMeasure (epsilonGoodBlockLaw d p ε n) := by
  unfold epsilonGoodBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_epsilonGoodBlockField d p ε n).aemeasurable

theorem epsilonGoodBlockLaw_real_mem
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x : Cubic d) :
    (epsilonGoodBlockLaw d p ε n).real {η : Set (Cubic d) | x ∈ η} =
      (bernoulliBondMeasure d p).real
        (epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n) := by
  rw [epsilonGoodBlockLaw]
  exact MeasureTheory.map_measureReal_apply
    (measurable_epsilonGoodBlockField d p ε n) (measurableSet_mem x)

/-- Underlying bond coordinates queried by a family of coarse blocks. -/
def epsilonGoodBlockEdgeSupportSet
    (d n : ℕ) (A : Set (Cubic d)) : Set (CubicEdge d) :=
  ⋃ x : A, (cubicBoxEdges d (epsilonGoodBlockCenter n x.1) n : Set (CubicEdge d))

theorem disjoint_epsilonGoodBlockEdgeSupportSet {d n : ℕ} (hn : 1 ≤ n)
    {A B : Set (Cubic d)}
    (hsep : ∀ x ∈ A, ∀ y ∈ B, ((3 * d : ℕ) : ℕ∞) < (cubicGraph d).edist x y) :
    Disjoint (epsilonGoodBlockEdgeSupportSet d n A)
      (epsilonGoodBlockEdgeSupportSet d n B) := by
  rw [Set.disjoint_left]
  intro e heA heB
  obtain ⟨x, hex⟩ := Set.mem_iUnion.mp heA
  obtain ⟨y, hey⟩ := Set.mem_iUnion.mp heB
  have hfarE := hsep x.1 x.2 y.1 y.2
  obtain ⟨w⟩ := nonempty_cubicWalk d x.1 y.1
  have hreach : (cubicGraph d).Reachable x.1 y.1 := ⟨w⟩
  have hfar : 3 * d < cubicL1Dist x.1 y.1 := by
    rw [← hreach.coe_dist_eq_edist, cubicGraph_dist_eq_l1Dist] at hfarE
    exact_mod_cast hfarE
  exact Finset.disjoint_left.mp
    (disjoint_cubicBoxEdges_epsilonGoodBlockCenter hn hfar) hex hey

theorem comap_epsilonGoodBlockField_siteCoordinate_le
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (A : Set (Cubic d)) :
    MeasurableSpace.comap (epsilonGoodBlockField d p ε n)
        (siteCoordinateMeasurableSpace (Cubic d) A) ≤
      MeasurableSpace.generateFrom
        (coordinateEvents (epsilonGoodBlockEdgeSupportSet d n A)) := by
  rw [siteCoordinateMeasurableSpace, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  intro t ht
  obtain ⟨s, hs, rfl⟩ := ht
  obtain ⟨x, hx, rfl⟩ := hs
  change MeasurableSet[MeasurableSpace.generateFrom
      (coordinateEvents (epsilonGoodBlockEdgeSupportSet d n A))]
    (epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n)
  apply (dependsOn_epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n).measurableSet_generateFrom_coordinateEvents
  intro e he
  apply Set.mem_iUnion.mpr
  exact ⟨⟨x, hx⟩, he⟩

theorem epsilonGoodBlockLaw_kDependent
    (d : ℕ) (p : I) (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    KDependent (cubicGraph d) (3 * d) (epsilonGoodBlockLaw d p ε n) := by
  intro A B hsep
  have hsupports : Disjoint (epsilonGoodBlockEdgeSupportSet d n A)
      (epsilonGoodBlockEdgeSupportSet d n B) :=
    disjoint_epsilonGoodBlockEdgeSupportSet hn hsep
  have hbase := indep_generateFrom_coordinateEvents p hsupports
  have hcomap : Indep
      (MeasurableSpace.comap (epsilonGoodBlockField d p ε n)
        (siteCoordinateMeasurableSpace (Cubic d) A))
      (MeasurableSpace.comap (epsilonGoodBlockField d p ε n)
        (siteCoordinateMeasurableSpace (Cubic d) B))
      (bernoulliBondMeasure d p) := by
    apply indep_of_indep_of_le hbase
    · exact comap_epsilonGoodBlockField_siteCoordinate_le d p ε n A
    · exact comap_epsilonGoodBlockField_siteCoordinate_le d p ε n B
  unfold epsilonGoodBlockLaw
  exact Indep.map_measure (measurable_epsilonGoodBlockField d p ε n)
    (siteCoordinateMeasurableSpace_le (Cubic d) A)
    (siteCoordinateMeasurableSpace_le (Cubic d) B) hcomap

/-- There is a crossing component containing at least `q` vertices. -/
def largeCrossingClusterEvent (d q n : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | ∃ C : (finiteBoxOpenGraph d ω x n).ConnectedComponent,
    boxComponentIsCrossing C ∧ q ≤ boxComponentCard C}

/-- The box contains a crossing component and a distinct component of diameter at least `m`.
This is Grimmett's event `T_{m,n}` before Lemma 7.104. -/
def secondMacroscopicClusterEvent (d m n : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  {ω | ∃ C D : (finiteBoxOpenGraph d ω x n).ConnectedComponent,
    C ≠ D ∧ boxComponentIsCrossing C ∧ m ≤ boxComponentDiameter D}

@[simp]
theorem secondMacroscopicClusterEvent_eq_empty_of_two_mul_lt {d m n : ℕ}
    (x : Cubic d) (hm : 2 * n < m) :
    secondMacroscopicClusterEvent d m n x = ∅ := by
  ext ω
  simp only [secondMacroscopicClusterEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨C, D, _hne, _hcross, hmD⟩
  exact (not_le_of_gt hm) (hmD.trans (boxComponentDiameter_le_two_mul D))

/-! ### Two-arm separation events -/

/-- Connection from `x` to the surface of the origin-centered box of radius `N`, constrained to
that box. -/
def connectionToBoxSurfaceEvent (d N : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  ⋃ y ∈ cubicBoxSurface d cubicOrigin N,
    connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y

theorem measurableSet_connectionToBoxSurfaceEvent (d N : ℕ) (x : Cubic d) :
    MeasurableSet (connectionToBoxSurfaceEvent d N x) := by
  apply (cubicBoxSurface d cubicOrigin N).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y).measurableSet

/-- Both `x` and `y` reach the outer box surface but are not connected inside that box. -/
def twoArmSeparationEvent (d n N : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  if x ∈ cubicMetricBox d cubicOrigin n ∧ y ∈ cubicMetricBox d cubicOrigin n then
    connectionToBoxSurfaceEvent d N x ∩ connectionToBoxSurfaceEvent d N y ∩
      (connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y)ᶜ
  else ∅

theorem measurableSet_twoArmSeparationEvent (d n N : ℕ) (x y : Cubic d) :
    MeasurableSet (twoArmSeparationEvent d n N x y) := by
  unfold twoArmSeparationEvent
  split_ifs
  · exact ((measurableSet_connectionToBoxSurfaceEvent d N x).inter
      (measurableSet_connectionToBoxSurfaceEvent d N y)).inter
        (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin N) x y).measurableSet.compl
  · exact MeasurableSet.empty

@[simp]
theorem twoArmSeparationEvent_self (d n N : ℕ) (x : Cubic d) :
    twoArmSeparationEvent d n N x x = ∅ := by
  unfold twoArmSeparationEvent
  split_ifs with h
  · ext ω
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hω
    exact hω.2 ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by
      intro e he
      simp [walkEdgeFinset, walkEdgeList] at he⟩
  · rfl

/-- Integer outer radius used for the source notation `B(an)`. -/
noncomputable def scaledBoxRadius (a : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (a * n)

end Percolation
