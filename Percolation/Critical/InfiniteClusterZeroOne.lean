import Percolation.Bernoulli.TailZeroOne
import Percolation.Critical.BoxRadius
import Percolation.Critical.Regions

/-!
# Zero--one infrastructure for existence of a global infinite cluster

The first step supplies a denumeration of cubic edges in every positive dimension.  The
finite-closing invariance of the global infinite-cluster event is developed below this
enumeration and then fed to the generic Bernoulli tail theorem.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

section DeleteOneEdge

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- Deleting one edge from a connected graph leaves every vertex connected to at least one of
the two endpoints. -/
theorem SimpleGraph.Connected.reachable_deleteEdges_endpoint_cover
    (hG : G.Connected) (huv : G.Adj u v) (w : V) :
    (G.deleteEdges {s(u, v)}).Reachable u w ∨
      (G.deleteEdges {s(u, v)}).Reachable v w := by
  classical
  obtain ⟨P, hP⟩ := hG.exists_isPath w u
  by_cases heP : s(u, v) ∈ P.edges
  · have hvP : v ∈ P.support := P.snd_mem_support_of_mem_edges heP
    let Q := P.takeUntil v hvP
    have huNotQ : u ∉ Q.support := by
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hP hvP huv.ne
    have heNotQ : s(u, v) ∉ Q.edges := by
      intro heQ
      exact huNotQ (Q.fst_mem_support_of_mem_edges heQ)
    right
    exact (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨Q, heNotQ⟩).symm
  · left
    exact (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨P, heP⟩).symm

/-- A connected infinite graph still has an infinite component after one edge is deleted. -/
theorem SimpleGraph.Connected.exists_infinite_reachable_deleteEdges_singleton
    [Infinite V] (hG : G.Connected) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ x : V, {y | (G.deleteEdges {e}).Reachable x y}.Infinite := by
  induction e using Sym2.ind with
  | _ u v =>
      have huv : G.Adj u v := by simpa [SimpleGraph.mem_edgeSet] using he
      let U : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable u y}
      let W : Set V := {y | (G.deleteEdges {s(u, v)}).Reachable v y}
      by_cases hU : U.Infinite
      · exact ⟨u, hU⟩
      · have hUfin : U.Finite := Set.not_infinite.mp hU
        have hcover : Set.univ ⊆ U ∪ W := by
          intro y _hy
          exact reachable_deleteEdges_endpoint_cover hG huv y
        have hW : W.Infinite := by
          intro hWfin
          have huniv : (Set.univ : Set V).Finite :=
            (hUfin.union hWfin).subset hcover
          exact Set.infinite_univ huniv
        exact ⟨v, hW⟩

end DeleteOneEdge

/-- Pairwise separated positive first-axis edges. -/
def separatedAxisEdge {d : ℕ} (hd : 0 < d) (n : ℕ) : CubicEdge d :=
  cubicStepEdge (cubicAxisVertex d (2 * n)) ((⟨0, hd⟩ : Fin d), true)

theorem separatedAxisEdge_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (separatedAxisEdge hd) := by
  intro m n hmn
  have hmem : cubicAxisVertex d (2 * m) ∈ (separatedAxisEdge hd n).1 := by
    rw [← hmn]
    simp [separatedAxisEdge, cubicStepEdge]
  rw [separatedAxisEdge, cubicStepEdge, Sym2.mem_iff] at hmem
  rcases hmem with hleft | hright
  · have hcoord := congrFun hleft (⟨0, hd⟩ : Fin d)
    simp [cubicAxisVertex] at hcoord
    omega
  · have hcoord := congrFun hright (⟨0, hd⟩ : Fin d)
    simp [cubicAxisVertex, cubicStepFrom, cubicDirectionIncrement] at hcoord
    omega

noncomputable instance cubicEdgeInfinite {d : ℕ} [NeZero d] : Infinite (CubicEdge d) :=
  Infinite.of_injective (separatedAxisEdge (Nat.pos_of_ne_zero NeZero.out))
    (separatedAxisEdge_injective (Nat.pos_of_ne_zero NeZero.out))

noncomputable instance cubicEdgeDenumerable {d : ℕ} [NeZero d] :
    Denumerable (CubicEdge d) := by
  letI := Encodable.ofCountable (CubicEdge d)
  exact Denumerable.ofEncodableOfInfinite (CubicEdge d)

end Percolation
