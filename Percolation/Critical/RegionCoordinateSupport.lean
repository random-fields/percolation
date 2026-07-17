import Percolation.Bernoulli.CoordinateIndependence
import Percolation.Critical.Regions

/-!
# Infinite coordinate supports for induced-region events

An event constrained to a possibly infinite vertex region is determined by the bonds whose two
endpoints lie in that region.  This is the locality input needed to make consecutive infinite
strips fresh in the proof of Grimmett's Theorem 8.21.
-/

namespace Percolation

/-- All cubic bonds with both endpoints in `A`. -/
def cubicInternalEdgeSet (d : ℕ) (A : Set (Cubic d)) : Set (CubicEdge d) :=
  {e | e.1.out.1 ∈ A ∧ e.1.out.2 ∈ A}

@[simp]
theorem mem_cubicInternalEdgeSet {d : ℕ} {A : Set (Cubic d)} {e : CubicEdge d} :
    e ∈ cubicInternalEdgeSet d A ↔ e.1.out.1 ∈ A ∧ e.1.out.2 ∈ A :=
  Iff.rfl

/-- Openness of a walk supported in `A` only uses edges internal to `A`. -/
theorem walkIsOpen_congr_of_agree_cubicInternalEdgeSet
    {d : ℕ} {A : Set (Cubic d)} {ω η : EdgeConfiguration d}
    {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hwA : ∀ z ∈ w.support, z ∈ A)
    (hagree : ∀ e ∈ cubicInternalEdgeSet d A, (e ∈ ω ↔ e ∈ η)) :
    walkIsOpen ω w ↔ walkIsOpen η w := by
  constructor <;> intro hopen e he
  · apply (hagree ⟨e, w.edges_subset_edgeSet he⟩ ?_).mp (hopen e he)
    exact ⟨hwA e.out.1 (w.mem_support_of_mem_edges he (Sym2.out_fst_mem e)),
      hwA e.out.2 (w.mem_support_of_mem_edges he (Sym2.out_snd_mem e))⟩
  · apply (hagree ⟨e, w.edges_subset_edgeSet he⟩ ?_).mpr (hopen e he)
    exact ⟨hwA e.out.1 (w.mem_support_of_mem_edges he (Sym2.out_fst_mem e)),
      hwA e.out.2 (w.mem_support_of_mem_edges he (Sym2.out_snd_mem e))⟩

theorem connectionEventWithinVertices_congr_of_agree_cubicInternalEdgeSet
    {d : ℕ} {A : Set (Cubic d)} {ω η : EdgeConfiguration d}
    {x y : Cubic d}
    (hagree : ∀ e ∈ cubicInternalEdgeSet d A, (e ∈ ω ↔ e ∈ η)) :
    ω ∈ connectionEventWithinVertices d A x y ↔
      η ∈ connectionEventWithinVertices d A x y := by
  constructor <;> rintro ⟨w, hopen, hwA⟩
  · exact ⟨w,
      (walkIsOpen_congr_of_agree_cubicInternalEdgeSet w hwA hagree).mp hopen, hwA⟩
  · exact ⟨w,
      (walkIsOpen_congr_of_agree_cubicInternalEdgeSet w hwA hagree).mpr hopen, hwA⟩

theorem dependsOnCoordinates_connectionEventWithinVertices
    (d : ℕ) (A : Set (Cubic d)) (x y : Cubic d) :
    DependsOnCoordinates (cubicInternalEdgeSet d A)
      (connectionEventWithinVertices d A x y) :=
  fun _ω _η hagree ↦
    connectionEventWithinVertices_congr_of_agree_cubicInternalEdgeSet hagree

theorem cubicOpenClusterWithinVertices_eq_of_agree_cubicInternalEdgeSet
    {d : ℕ} {A : Set (Cubic d)} {ω η : EdgeConfiguration d} {x : Cubic d}
    (hagree : ∀ e ∈ cubicInternalEdgeSet d A, (e ∈ ω ↔ e ∈ η)) :
    cubicOpenClusterWithinVertices d A ω x =
      cubicOpenClusterWithinVertices d A η x := by
  ext y
  exact and_congr_right fun _hyA ↦
    connectionEventWithinVertices_congr_of_agree_cubicInternalEdgeSet hagree

theorem dependsOnCoordinates_cubicOpenClusterWithinVertices_infinite
    (d : ℕ) (A : Set (Cubic d)) (x : Cubic d) :
    DependsOnCoordinates (cubicInternalEdgeSet d A)
      {ω | (cubicOpenClusterWithinVertices d A ω x).Infinite} := by
  intro ω η hagree
  change (cubicOpenClusterWithinVertices d A ω x).Infinite ↔
    (cubicOpenClusterWithinVertices d A η x).Infinite
  rw [cubicOpenClusterWithinVertices_eq_of_agree_cubicInternalEdgeSet hagree]

theorem dependsOnCoordinates_hasInfiniteOpenClusterInVertices
    (d : ℕ) (A : Set (Cubic d)) :
    DependsOnCoordinates (cubicInternalEdgeSet d A)
      {ω | hasInfiniteOpenClusterInVertices d A ω} := by
  intro ω η hagree
  simp only [hasInfiniteOpenClusterInVertices]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _hx
  rw [cubicOpenClusterWithinVertices_eq_of_agree_cubicInternalEdgeSet hagree]

end Percolation
