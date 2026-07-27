import Percolation.Critical.Regions
import Percolation.Bernoulli.Inhomogeneous

/-!
# Periodic lattices, mixed percolation, and AB percolation

This file formalizes the model definitions at the start of Grimmett, *Percolation* (2nd ed.),
Chapter 12.  The periodic-lattice structure records the graph-theoretic content actually used
later: a connected locally finite graph, a free `ℤ^d` action by graph automorphisms, and a finite
fundamental domain.  Mixed percolation keeps vertex and edge coordinates separate, while AB
percolation retains precisely the edges whose endpoint labels differ.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval

/-- A graph-theoretic `d`-dimensional periodic lattice with a chosen finite fundamental domain. -/
structure PeriodicLattice (V : Type*) (d : ℕ) where
  graph : SimpleGraph V
  connected : graph.Connected
  neighborSet_finite : ∀ v, (graph.neighborSet v).Finite
  translate : (Fin d → ℤ) → graph ≃g graph
  translate_zero : translate 0 = SimpleGraph.Iso.refl
  translate_add : ∀ a b, translate (a + b) = (translate a).trans (translate b)
  free : ∀ a v, translate a v = v → a = 0
  fundamentalDomain : Finset V
  covers : ∀ v, ∃ a u, u ∈ fundamentalDomain ∧ translate a u = v

/-- A sufficient discrete encoding of Kesten's geometric definition of a periodic lattice.

The chosen placement is equivariant for integer translations.  Properness is stated on integer
coordinate boxes; together with the uniform coordinate-span bound on edges and local finiteness
of the underlying periodic graph, this implies that every compact subset of `ℝ^d` meets only
finitely many embedded straight edges.  Recording these two checkable conditions avoids putting
topological line-segment intersection data into every later percolation theorem. -/
structure GeometricPeriodicLattice (V : Type*) (d : ℕ)
    extends PeriodicLattice V d where
  position : V → Fin d → ℝ
  injective_position : Function.Injective position
  position_translate : ∀ (a : Fin d → ℤ) (v : V) (i : Fin d),
    position (translate a v) i = position v i + a i
  proper_integer_boxes : ∀ n : ℕ,
    {v | ∀ i : Fin d, -(n : ℝ) ≤ position v i ∧ position v i ≤ n}.Finite
  edge_coordinate_span_bounded : ∃ R : ℝ, 0 ≤ R ∧
    ∀ {x y : V}, graph.Adj x y → ∀ i : Fin d,
      |position x i - position y i| ≤ R

namespace PeriodicLattice

variable {V : Type*} {d : ℕ} (L : PeriodicLattice V d)

@[simp]
theorem translate_zero_apply (v : V) : L.translate 0 v = v := by
  rw [L.translate_zero]
  rfl

theorem translate_add_apply (a b : Fin d → ℤ) (v : V) :
    L.translate (a + b) v = L.translate b (L.translate a v) := by
  rw [L.translate_add]
  rfl

theorem fundamentalDomain_nonempty [Nonempty V] : L.fundamentalDomain.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨a, u, hu, _⟩ := L.covers v
  exact ⟨u, hu⟩

end PeriodicLattice

namespace GeometricPeriodicLattice

variable {V : Type*} {d : ℕ} (L : GeometricPeriodicLattice V d)

theorem position_injective : Function.Injective L.position :=
  L.injective_position

theorem vertices_in_integer_box_finite (n : ℕ) :
    {v | ∀ i : Fin d, -(n : ℝ) ≤ L.position v i ∧ L.position v i ≤ n}.Finite :=
  L.proper_integer_boxes n

end GeometricPeriodicLattice

/-- Site and bond coordinates for mixed percolation on `G`. -/
abbrev MixedConfiguration {V : Type*} (G : SimpleGraph V) :=
  Set V × Set G.edgeSet

/-- The mixed open graph: both endpoints must be open sites and their bond must be open. -/
def mixedOpenGraph {V : Type*} (G : SimpleGraph V) (ω : MixedConfiguration G) :
    SimpleGraph V where
  Adj x y := ∃ h : G.Adj x y,
    x ∈ ω.1 ∧ y ∈ ω.1 ∧
      (⟨s(x, y), (SimpleGraph.mem_edgeSet G).2 h⟩ : G.edgeSet) ∈ ω.2
  symm := by
    rintro x y ⟨h, hx, hy, he⟩
    refine ⟨h.symm, hy, hx, ?_⟩
    simpa only [Sym2.eq_swap] using he
  loopless := ⟨by
    intro x
    rintro ⟨h, _⟩
    exact G.loopless.irrefl x h⟩

theorem mixedOpenGraph_le {V : Type*} (G : SimpleGraph V)
    (ω : MixedConfiguration G) : mixedOpenGraph G ω ≤ G := by
  intro x y hxy
  exact hxy.1

/-- Independent site/bond law for mixed percolation. -/
noncomputable def mixedPercolationMeasure {V : Type*} [Countable V]
    (G : SimpleGraph V) (siteDensity bondDensity : I) :
    Measure (MixedConfiguration G) :=
  (setBernoulli (Set.univ : Set V) siteDensity).prod
    (setBernoulli (Set.univ : Set G.edgeSet) bondDensity)

noncomputable instance mixedPercolationMeasure.isProbabilityMeasure
    {V : Type*} [Countable V] (G : SimpleGraph V) (siteDensity bondDensity : I) :
    IsProbabilityMeasure (mixedPercolationMeasure G siteDensity bondDensity) := by
  rw [mixedPercolationMeasure]
  infer_instance

/-- Root cluster for mixed percolation. -/
def mixedOpenCluster {V : Type*} (G : SimpleGraph V)
    (ω : MixedConfiguration G) (root : V) : Set V :=
  {v | (mixedOpenGraph G ω).Reachable root v}

/-- Rooted mixed-percolation probability.  The event is exposed separately so its cylinder
approximations can be audited without hiding measurability in the definition. -/
noncomputable def mixedTheta {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) (siteDensity bondDensity : I) : ℝ :=
  (mixedPercolationMeasure G siteDensity bondDensity).real
    {ω | (mixedOpenCluster G ω root).Infinite}

/-- The AB graph retains an ambient edge precisely when its endpoint labels differ. -/
def abOpenGraph {V : Type*} (G : SimpleGraph V) (labels : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ labels ↔ y ∉ labels)
  symm := by
    rintro x y ⟨hxy, hlabel⟩
    refine ⟨hxy.symm, ?_⟩
    tauto
  loopless := ⟨by
    intro x
    rintro ⟨hxx, _⟩
    exact G.loopless.irrefl x hxx⟩

theorem abOpenGraph_le {V : Type*} (G : SimpleGraph V) (labels : Set V) :
    abOpenGraph G labels ≤ G := by
  intro x y hxy
  exact hxy.1

theorem abOpenGraph_compl_labels {V : Type*} (G : SimpleGraph V) (labels : Set V) :
    abOpenGraph G labelsᶜ = abOpenGraph G labels := by
  ext x y
  simp only [abOpenGraph, Set.mem_compl_iff]
  constructor <;> rintro ⟨hxy, h⟩ <;> refine ⟨hxy, ?_⟩ <;> tauto

/-- The AB cluster of `root`. -/
def abOpenCluster {V : Type*} (G : SimpleGraph V) (labels : Set V) (root : V) : Set V :=
  {v | (abOpenGraph G labels).Reachable root v}

/-- AB percolation probability under iid Bernoulli vertex labels. -/
noncomputable def abTheta {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) (p : I) : ℝ :=
  (setBernoulli (Set.univ : Set V) p).real
    {labels | (abOpenCluster G labels root).Infinite}

@[simp]
theorem abOpenGraph_empty {V : Type*} (G : SimpleGraph V) :
    abOpenGraph G (∅ : Set V) = ⊥ := by
  ext x y
  simp [abOpenGraph]

@[simp]
theorem abOpenGraph_univ {V : Type*} (G : SimpleGraph V) :
    abOpenGraph G (Set.univ : Set V) = ⊥ := by
  ext x y
  simp [abOpenGraph]

end Percolation
