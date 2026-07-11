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
