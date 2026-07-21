import Percolation.Extensions.RigidityEvents
import Percolation.Critical.Basic
import Percolation.Bernoulli.Coupling

/-!
# Infinite rigid subgraphs in cubic percolation

This file encodes Grimmett's source event before attaching a probability to it.  A witness is an
infinite vertex set containing the origin whose induced open graph is rigid in the source's
finite-exhaustion sense.  Taking the induced graph loses no generality because finite generic
rigidity is monotone under adding edges.
-/

namespace Percolation

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The origin belongs to an infinite open rigid graph. -/
def HasInfiniteOpenRigidGraph (d : ℕ) (omega : EdgeConfiguration d) : Prop :=
  ∃ V : Set (Cubic d), cubicOrigin ∈ V ∧ V.Infinite ∧
    InfinitelyGenericallyRigid ((cubicOpenGraph d omega).induce V) d

/-- Source event `R` from §12.6. -/
def hasInfiniteOpenRigidGraphEvent (d : ℕ) : Set (EdgeConfiguration d) :=
  {omega | HasInfiniteOpenRigidGraph d omega}

theorem HasInfiniteOpenRigidGraph.mono_configuration {d : ℕ}
    {omega eta : EdgeConfiguration d} (hmono : omega ⊆ eta)
    (h : HasInfiniteOpenRigidGraph d omega) :
    HasInfiniteOpenRigidGraph d eta := by
  obtain ⟨V, h0, hV, hrigid⟩ := h
  refine ⟨V, h0, hV, ?_⟩
  apply hrigid.mono
  intro U hU
  apply hU.mono
  intro x y hxy
  rw [SimpleGraph.induce_adj] at hxy ⊢
  rw [SimpleGraph.induce_adj] at hxy ⊢
  obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp hxy
  exact cubicOpenGraph_adj.mpr ⟨hadj, hmono hopen⟩

theorem isIncreasingEvent_hasInfiniteOpenRigidGraph (d : ℕ) :
    IsIncreasingEvent (hasInfiniteOpenRigidGraphEvent d) := by
  intro omega eta hmono h
  exact h.mono_configuration hmono

/-- Every vertex of an infinite rigid witness is ordinarily open-connected to the origin. -/
theorem HasInfiniteOpenRigidGraph.vertices_subset_openCluster {d : ℕ}
    {omega : EdgeConfiguration d} {V : Set (Cubic d)}
    (h0 : cubicOrigin ∈ V)
    (hrigid : InfinitelyGenericallyRigid ((cubicOpenGraph d omega).induce V) d) :
    V ⊆ cubicOpenCluster d omega := by
  intro y hy
  let oV : V := ⟨cubicOrigin, h0⟩
  let yV : V := ⟨y, hy⟩
  let W : Finset V := {oV, yV}
  obtain ⟨U, hWU, hUrigid⟩ := hrigid W
  have hoU : oV ∈ U := hWU (by simp [W])
  have hyU : yV ∈ U := hWU (by simp [W])
  let oU : (U : Set V) := ⟨oV, hoU⟩
  let yU : (U : Set V) := ⟨yV, hyU⟩
  obtain ⟨w, _hwpath⟩ := hUrigid.1.exists_isPath oU yU
  let f :
      (((cubicOpenGraph d omega).induce V).induce (U : Set V)) →g
        cubicOpenGraph d omega :=
    { toFun := fun z ↦ z.1.1
      map_rel' := by
        intro a b hab
        exact (SimpleGraph.induce_adj.mp (SimpleGraph.induce_adj.mp hab)) }
  let q : (cubicOpenGraph d omega).Walk cubicOrigin y :=
    (w.map f).copy (by rfl) (by rfl)
  let ambient : (cubicGraph d).Walk cubicOrigin y := q.map (cubicOpenGraphHom d omega)
  exact ⟨ambient, by
    simpa only [ambient] using walkIsOpen_map_cubicOpenGraphHom q⟩

/-- A rigid infinite open graph is in particular an ordinary infinite open cluster. -/
theorem HasInfiniteOpenRigidGraph.hasInfiniteOpenCluster {d : ℕ}
    {omega : EdgeConfiguration d} (h : HasInfiniteOpenRigidGraph d omega) :
    hasInfiniteOpenCluster d omega := by
  obtain ⟨V, h0, hV, hrigid⟩ := h
  exact hV.mono (HasInfiniteOpenRigidGraph.vertices_subset_openCluster h0 hrigid)

theorem hasInfiniteOpenRigidGraphEvent_subset_hasInfiniteOpenCluster (d : ℕ) :
    hasInfiniteOpenRigidGraphEvent d ⊆
      {omega : EdgeConfiguration d | hasInfiniteOpenCluster d omega} := by
  intro omega h
  exact h.hasInfiniteOpenCluster

/-! ### Probability and critical parameter -/

/-- Probability that the origin belongs to an infinite open rigid graph. -/
noncomputable def rigidityTheta (d : ℕ) (p : I) : ℝ :=
  (bernoulliBondMeasure d p).real (hasInfiniteOpenRigidGraphEvent d)

/-- Rigid percolation is contained in ordinary percolation. -/
theorem rigidityTheta_le_theta (d : ℕ) (p : I) :
    rigidityTheta d p ≤ theta d p := by
  letI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  unfold rigidityTheta theta
  exact measureReal_mono
    (hasInfiniteOpenRigidGraphEvent_subset_hasInfiniteOpenCluster d)
    (measure_ne_top _ _)

theorem rigidityTheta_zero (d : ℕ) : rigidityTheta d (0 : I) = 0 := by
  apply le_antisymm
  · exact (rigidityTheta_le_theta d (0 : I)).trans_eq
      (theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one d (0 : I) (by simp))
  · exact measureReal_nonneg

/-- The generic-rigidity percolation threshold from Grimmett, §12.6. -/
noncomputable def rigidityCriticalProbability (d : ℕ) : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | rigidityTheta d p = 0}) : Set ℝ)

theorem rigidityCriticalProbability_nonneg (d : ℕ) :
    0 ≤ rigidityCriticalProbability d := by
  rw [rigidityCriticalProbability]
  apply le_csSup
  · exact ⟨1, by
      rintro q ⟨p, hp, rfl⟩
      exact p.2.2⟩
  · exact ⟨(0 : I), rigidityTheta_zero d, rfl⟩

theorem rigidityCriticalProbability_le_one (d : ℕ) :
    rigidityCriticalProbability d ≤ 1 := by
  rw [rigidityCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I), rigidityTheta_zero d, rfl⟩⟩
  · rintro q ⟨p, hp, rfl⟩
    exact p.2.2

/-- The non-strict elementary half of Theorem 12.28(a). -/
theorem cubicCriticalProbability_le_rigidityCriticalProbability (d : ℕ) :
    cubicCriticalProbability d ≤ rigidityCriticalProbability d := by
  rw [cubicCriticalProbability, rigidityCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I),
      theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one d (0 : I) (by simp), rfl⟩⟩
  · rintro q ⟨p, hp, rfl⟩
    apply le_csSup
    · exact ⟨1, by
        rintro q ⟨r, hr, rfl⟩
        exact r.2.2⟩
    · refine ⟨p, ?_, rfl⟩
      exact le_antisymm ((rigidityTheta_le_theta d p).trans_eq hp) measureReal_nonneg

end Percolation
