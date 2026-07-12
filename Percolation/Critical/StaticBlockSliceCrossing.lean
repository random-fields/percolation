import Percolation.Critical.LSSGoodBlocks
import Percolation.Critical.StaticBlockPath
import Percolation.Planar.Crossings

/-!
# Planar slice crossings of the static good-block field

For `d ≥ 2`, the first-coordinate embedding identifies a copy of the square lattice inside
the coarse cubic lattice.  Pulling the finite site-crossing event back along this embedding gives
an increasing finite-cylinder event to which the proved LSS good-block comparison applies.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Restrict a site configuration on `ℤ^d` to the embedded first two coordinates. -/
def cubicFirstTwoSiteRestriction {d : ℕ} (_hd : 2 ≤ d)
    (η : Set (Cubic d)) : Set SquareVertex :=
  (cubicEmbed 2 d) ⁻¹' η

theorem measurable_cubicFirstTwoSiteRestriction {d : ℕ} (hd : 2 ≤ d) :
    Measurable (cubicFirstTwoSiteRestriction hd :
      Set (Cubic d) → Set SquareVertex) := by
  change Measurable
    ((fun P : SquareVertex → Prop ↦ {x | P x}) ∘
      fun (η : Set (Cubic d)) (x : SquareVertex) ↦
        ((cubicEmbed 2 d x ∈ η) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun x ↦ (measurableSet_mem (cubicEmbed 2 d x)).mem

/-- A left-right site crossing in the embedded planar slice of the coarse lattice. -/
def epsilonGoodBlockSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) : Set (Set (Cubic d)) :=
  cubicFirstTwoSiteRestriction hd ⁻¹' siteSquareRectangleCrossingEvent m n

/-- Embedded support of the planar rectangle. -/
noncomputable def epsilonGoodBlockSliceCrossingSupport
    (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) : Finset (Cubic d) :=
  (squareRectangleVertices m n).map
    ⟨cubicEmbed 2 d, cubicEmbed_injective hd⟩

theorem dependsOn_epsilonGoodBlockSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) :
    DependsOn (epsilonGoodBlockSliceCrossingSupport d hd m n)
      (epsilonGoodBlockSliceCrossingEvent d hd m n) := by
  intro η ξ hagree
  apply (dependsOn_siteSquareRectangleCrossingEvent m n)
  intro x hx
  apply hagree
  rw [epsilonGoodBlockSliceCrossingSupport, Finset.mem_map]
  exact ⟨x, hx, rfl⟩

theorem measurableSet_epsilonGoodBlockSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) :
    MeasurableSet (epsilonGoodBlockSliceCrossingEvent d hd m n) :=
  (dependsOn_epsilonGoodBlockSliceCrossingEvent d hd m n).measurableSet

theorem isIncreasingEvent_epsilonGoodBlockSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) :
    IsIncreasingEvent (epsilonGoodBlockSliceCrossingEvent d hd m n) := by
  intro η ξ hηξ hη
  exact isIncreasingEvent_siteSquareRectangleCrossingEvent m n
    (fun x hx ↦ hηξ hx) hη

/-- Iid sites have exactly the same crossing probability on the embedded planar slice. -/
theorem setBernoulli_real_epsilonGoodBlockSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (q : I) (m n : ℕ) :
    setBer((Set.univ : Set (Cubic d)), q).real
        (epsilonGoodBlockSliceCrossingEvent d hd m n) =
      setBer((Set.univ : Set SquareVertex), q).real
        (siteSquareRectangleCrossingEvent m n) := by
  let f : SquareVertex ↪ Cubic d :=
    ⟨cubicEmbed 2 d, cubicEmbed_injective hd⟩
  have hmap := setBernoulli_map_preimage_univ f q
  have hfun : (fun s : Set (Cubic d) ↦ f ⁻¹' s) =
      cubicFirstTwoSiteRestriction hd := rfl
  rw [hfun] at hmap
  rw [epsilonGoodBlockSliceCrossingEvent, ← hmap, map_measureReal_apply
    (measurable_cubicFirstTwoSiteRestriction hd)
    (measurableSet_siteSquareRectangleCrossingEvent m n)]

/-- LSS comparison for a finite planar crossing of the `ε`-good block field. -/
theorem siteCrossingProbability_le_epsilonGoodBlockSliceCrossing
    (d : ℕ) (hd : 2 ≤ d) (p q : I) (ε : ℝ)
    (blockScale m n : ℕ) (hblockScale : 1 ≤ blockScale)
    (hq : (q : ℝ) < 1)
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε blockScale).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    setBer((Set.univ : Set SquareVertex), q).real
        (siteSquareRectangleCrossingEvent m n) ≤
      (epsilonGoodBlockLaw d p ε blockScale).real
        (epsilonGoodBlockSliceCrossingEvent d hd m n) := by
  rw [← setBernoulli_real_epsilonGoodBlockSliceCrossingEvent d hd]
  exact epsilonGoodBlockLaw_lss_finiteCylinder_measureReal_le
    d (lt_of_lt_of_le (by omega) hd) p q ε blockScale hblockScale hq hmarginal
    (dependsOn_epsilonGoodBlockSliceCrossingEvent d hd m n)
    (isIncreasingEvent_epsilonGoodBlockSliceCrossingEvent d hd m n)

/-- A crossing of good coarse sites in the embedded planar slice lifts to an open bond
connection between the corresponding endpoint-block faces. -/
theorem exists_connectionEvent_between_faces_of_mem_goodBlockSliceCrossing
    {d : ℕ} (hd : 2 ≤ d) (p : I) (ε : ℝ)
    (blockScale m n : ℕ) (omega : EdgeConfiguration d)
    (hcross : epsilonGoodBlockField d p ε blockScale omega ∈
      epsilonGoodBlockSliceCrossingEvent d hd m n) :
    ∃ x ∈ squareRectangleLeft m n, ∃ y ∈ squareRectangleRight m n,
      ∃ u ∈ cubicBoxFace d
          (epsilonGoodBlockCenter blockScale (cubicEmbed 2 d x)) blockScale
          (Fin.castLE hd 0) false,
        ∃ v ∈ cubicBoxFace d
          (epsilonGoodBlockCenter blockScale (cubicEmbed 2 d y)) blockScale
          (Fin.castLE hd 0) true,
          omega ∈ connectionEvent d u v := by
  change cubicFirstTwoSiteRestriction hd
      (epsilonGoodBlockField d p ε blockScale omega) ∈
        siteSquareRectangleCrossingEvent m n at hcross
  simp only [siteSquareRectangleCrossingEvent, Set.mem_iUnion] at hcross
  obtain ⟨x, hx, y, hy, w, _hwRectangle, hwGood⟩ := hcross
  let wd : (cubicGraph d).Walk (cubicEmbed 2 d x) (cubicEmbed 2 d y) :=
    w.map (cubicEmbedHom hd)
  have hgood : ∀ z ∈ wd.support,
      omega ∈ epsilonGoodBoxEvent d p ε
        (epsilonGoodBlockCenter blockScale z) blockScale := by
    intro z hz
    change z ∈ (w.map (cubicEmbedHom hd)).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact hwGood z' hz'
  obtain ⟨u, huFace, v, hvFace, huv⟩ :=
    exists_connectionEvent_between_faces_of_good_walk
      p ε omega wd hgood (Fin.castLE hd 0)
  exact ⟨x, hx, y, hy, u, huFace, v, hvFace, huv⟩

end Percolation
