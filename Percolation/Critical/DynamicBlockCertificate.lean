import Percolation.Critical.AdaptiveExploration

/-!
# From an infinite block exploration to bond percolation

The final step of Grimmett's construction is deterministic: infinitely many successful coarse
blocks carry distinct seed anchors, and every anchor is joined to the root anchor by an open path
inside the thickened region.  This file isolates that certificate so the probability argument
cannot silently replace an infinite connected block set by an infinite bond cluster.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Distinct anchors for an infinite index set, all joined to one root anchor inside `A`, force
an infinite open cluster in `A`. -/
theorem hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
    {V : Type*} {d : ℕ} {A : Set (Cubic d)} {omega : EdgeConfiguration d}
    {S : Set V} (hS : S.Infinite) (anchor : V → Cubic d)
    (hinj : Set.InjOn anchor S) {root : V} (hroot : root ∈ S)
    (hA : ∀ v ∈ S, anchor v ∈ A)
    (hconn : ∀ v ∈ S,
      omega ∈ connectionEventWithinVertices d A (anchor root) (anchor v)) :
    hasInfiniteOpenClusterInVertices d A omega := by
  refine ⟨anchor root, hA root hroot, ?_⟩
  have himage : (anchor '' S).Infinite := Set.Infinite.image hinj hS
  exact himage.mono fun z hz ↦ by
    rcases hz with ⟨v, hv, rfl⟩
    exact ⟨hA v hv, hconn v hv⟩

/-- Injectivity is stronger than the block construction needs.  If every physical anchor has
only finitely many coarse preimages, then an infinite accepted coarse set still supplies
infinitely many distinct vertices in the open cluster.  This form is useful for selected seeds:
their exact locations are random, but geometric containment in uniformly finite coarse boxes
makes every fiber finite. -/
theorem hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections_finiteFibers
    {V : Type*} {d : ℕ} {A : Set (Cubic d)} {omega : EdgeConfiguration d}
    {S : Set V} (hS : S.Infinite) (anchor : V → Cubic d)
    (hfinite : ∀ z, (anchor ⁻¹' {z}).Finite) {root : V} (hroot : root ∈ S)
    (hA : ∀ v ∈ S, anchor v ∈ A)
    (hconn : ∀ v ∈ S,
      omega ∈ connectionEventWithinVertices d A (anchor root) (anchor v)) :
    hasInfiniteOpenClusterInVertices d A omega := by
  refine ⟨anchor root, hA root hroot, ?_⟩
  have himage : (anchor '' S).Infinite := by
    intro himageFinite
    apply hS
    apply himageFinite.of_finite_fibers anchor
    intro z _hz
    exact (hfinite z).subset Set.inter_subset_right
  exact himage.mono fun z hz ↦ by
    rcases hz with ⟨v, hv, rfl⟩
    exact ⟨hA v hv, hconn v hv⟩

namespace AdaptiveSiteExploration

variable {V Omega : Type*} [Countable V] [DecidableEq V] [LinearOrder V]
  [MeasurableSpace Omega]

/-- Probability-level composition of adaptive Lemma 7.24 with the distinct-seed/open-connection
certificate.  The concrete Theorem 7.2 construction must instantiate `answer`, `anchor`, and
`bondConfiguration` from the common uniform labels and verify the displayed geometric facts. -/
theorem bondInfiniteCluster_probability_pos_of_prefixLowerBound
    (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : MeasurableAnswer answer)
    (e : ℕ ≃ V) (q : I) (hq : 0 < (q : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n (E.occupiedLimitLaw mu answer)) (q : ℝ))
    (d : ℕ) (A : Set (Cubic d))
    (bondConfiguration : Omega → EdgeConfiguration d)
    (anchor : Omega → V → Cubic d)
    (hroot : ∀ omega, root ∈ E.occupiedLimit (answer omega))
    (hinj : ∀ omega, Set.InjOn (anchor omega) (E.occupiedLimit (answer omega)))
    (hA : ∀ omega v, v ∈ E.occupiedLimit (answer omega) → anchor omega v ∈ A)
    (hconn : ∀ omega v, v ∈ E.occupiedLimit (answer omega) →
      bondConfiguration omega ∈ connectionEventWithinVertices d A
        (anchor omega root) (anchor omega v)) :
    0 < mu.real {omega |
      hasInfiniteOpenClusterInVertices d A (bondConfiguration omega)} := by
  have hsite := E.infiniteCluster_probability_pos_of_prefixLowerBound
    mu answer hanswer e q hq root hinitial hseq
  exact hsite.trans_le <| measureReal_mono fun omega homega ↦
    hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections
      (Set.Infinite.of_hasInfiniteSiteCluster homega) (anchor omega)
      (hinj omega) (hroot omega) (hA omega) (hconn omega)

/-- Finite-fiber version of the probability-level block certificate. -/
theorem bondInfiniteCluster_probability_pos_of_prefixLowerBound_finiteFibers
    (E : AdaptiveSiteExploration V)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (answer : Omega → List (V × Bool) → V → Bool)
    (hanswer : MeasurableAnswer answer)
    (e : ℕ ≃ V) (q : I) (hq : 0 < (q : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n (E.occupiedLimitLaw mu answer)) (q : ℝ))
    (d : ℕ) (A : Set (Cubic d))
    (bondConfiguration : Omega → EdgeConfiguration d)
    (anchor : Omega → V → Cubic d)
    (hroot : ∀ omega, root ∈ E.occupiedLimit (answer omega))
    (hfinite : ∀ omega z, ((anchor omega) ⁻¹' {z}).Finite)
    (hA : ∀ omega v, v ∈ E.occupiedLimit (answer omega) → anchor omega v ∈ A)
    (hconn : ∀ omega v, v ∈ E.occupiedLimit (answer omega) →
      bondConfiguration omega ∈ connectionEventWithinVertices d A
        (anchor omega root) (anchor omega v)) :
    0 < mu.real {omega |
      hasInfiniteOpenClusterInVertices d A (bondConfiguration omega)} := by
  have hsite := E.infiniteCluster_probability_pos_of_prefixLowerBound
    mu answer hanswer e q hq root hinitial hseq
  exact hsite.trans_le <| measureReal_mono fun omega homega ↦
    hasInfiniteOpenClusterInVertices_of_infinite_anchor_connections_finiteFibers
      (Set.Infinite.of_hasInfiniteSiteCluster homega) (anchor omega)
      (hfinite omega) (hroot omega) (hA omega) (hconn omega)

end AdaptiveSiteExploration

end Percolation
