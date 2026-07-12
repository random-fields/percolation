import Percolation.Critical.AdaptiveTargetExhaustion

/-!
# Finite cubic-region shells for adaptive exploration

The target exhaustion in Grimmett Lemma 7.24 is supplied by ambient Manhattan spheres intersected
with the region.  Rooted connected explored sets that reach a farther sphere must cross every
nearer sphere, while a set meeting all spheres is infinite.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical

/-- A cubic walk whose endpoint is at Manhattan distance at least `n` has a vertex at distance
exactly `n`. -/
theorem exists_getVert_cubicL1Dist_eq
    {d n : ℕ} {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hy : n ≤ cubicL1Dist x y) :
    ∃ k, k ≤ w.length ∧ cubicL1Dist x (w.getVert k) = n := by
  classical
  have hexit : ∃ k : ℕ,
      k ≤ w.length ∧ n ≤ cubicL1Dist x (w.getVert k) :=
    ⟨w.length, le_rfl, by simpa using hy⟩
  let k := Nat.find hexit
  have hk : k ≤ w.length ∧ n ≤ cubicL1Dist x (w.getVert k) := Nat.find_spec hexit
  refine ⟨k, hk.1, ?_⟩
  by_cases hkzero : k = 0
  · have hn : n = 0 := by
      simpa [hkzero] using hk.2
    simp [hkzero, hn]
  · let j := k - 1
    have hksucc : k = j + 1 := by omega
    have hjfind : j < Nat.find hexit := by
      change j < k
      omega
    have hjlt : cubicL1Dist x (w.getVert j) < n := by
      apply lt_of_not_ge
      intro hj
      exact Nat.find_min hexit hjfind ⟨by omega, hj⟩
    have hjlen : j < w.length := by omega
    have hadj := w.adj_getVert_succ hjlen
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
    have hupper : cubicL1Dist x (w.getVert (j + 1)) ≤ n := by
      calc
        cubicL1Dist x (w.getVert (j + 1)) ≤
            cubicL1Dist x (w.getVert j) +
              cubicL1Dist (w.getVert j) (w.getVert (j + 1)) :=
          cubicL1Dist_triangle _ _ _
        _ = cubicL1Dist x (w.getVert j) + 1 := by
          rw [ha, cubicL1Dist_stepFrom]
        _ ≤ n := by omega
    rw [hksucc]
    exact le_antisymm hupper (by simpa [hksucc] using hk.2)

/-- Finite ambient Manhattan sphere restricted to a cubic region. -/
noncomputable def cubicRegionMetricSphere
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) : Finset F :=
  (cubicMetricSphere d root n).subtype F

/-- Finite ambient Manhattan ball restricted to a cubic region. -/
noncomputable def cubicRegionMetricBall
    (d : ℕ) (F : Set (Cubic d)) (root : F) (n : ℕ) : Finset F :=
  (cubicMetricBall d root n).subtype F

@[simp]
theorem mem_cubicRegionMetricBall_iff
    {d : ℕ} {F : Set (Cubic d)} {root z : F} {n : ℕ} :
    z ∈ cubicRegionMetricBall d F root n ↔
      cubicL1Dist (root : Cubic d) (z : Cubic d) ≤ n := by
  classical
  rw [cubicRegionMetricBall]
  exact (Finset.mem_subtype (p := F) (s := cubicMetricBall d root n) (a := z)).trans
    mem_cubicMetricBall_iff_l1Dist_le

@[simp]
theorem mem_cubicRegionMetricSphere_iff
    {d : ℕ} {F : Set (Cubic d)} {root z : F} {n : ℕ} :
    z ∈ cubicRegionMetricSphere d F root n ↔
      cubicL1Dist (root : Cubic d) (z : Cubic d) = n := by
  classical
  rw [cubicRegionMetricSphere]
  exact (Finset.mem_subtype (p := F) (s := cubicMetricSphere d root n) (a := z)).trans
    mem_cubicMetricSphere_iff_l1Dist_eq

/-- Discrete intermediate value along a walk in an induced cubic region. -/
theorem exists_mem_walk_support_cubicRegionMetricSphere
    {d n : ℕ} {F : Set (Cubic d)} {root y : F}
    (w : (cubicRegionGraph d F).Walk root y)
    (hy : n ≤ cubicL1Dist (root : Cubic d) (y : Cubic d)) :
    ∃ z ∈ w.support, z ∈ cubicRegionMetricSphere d F root n := by
  let emb := SimpleGraph.Embedding.induce (G := cubicGraph d) F
  let ambientWalk := w.map emb.toHom
  have hy' : n ≤ cubicL1Dist (root : Cubic d) (y : Cubic d) := hy
  obtain ⟨k, hk, hkdist⟩ := exists_getVert_cubicL1Dist_eq ambientWalk hy'
  refine ⟨w.getVert k, w.getVert_mem_support k, ?_⟩
  rw [mem_cubicRegionMetricSphere_iff]
  simpa [ambientWalk, SimpleGraph.Walk.getVert_map] using hkdist

/-- First-hit prefix of a walk in a cubic region.  The returned walk ends on the prescribed
Manhattan sphere, stays in the corresponding ball, and uses only vertices of the original
walk. -/
theorem exists_cubicRegionWalk_prefix_to_metricSphere
    {d n : ℕ} {F : Set (Cubic d)} {root u y : F}
    (w : (cubicRegionGraph d F).Walk u y)
    (hu : cubicL1Dist (root : Cubic d) (u : Cubic d) ≤ n)
    (hy : n ≤ cubicL1Dist (root : Cubic d) (y : Cubic d)) :
    ∃ z : F, ∃ q : (cubicRegionGraph d F).Walk u z,
      z ∈ cubicRegionMetricSphere d F root n ∧
        (∀ v ∈ q.support, v ∈ cubicRegionMetricBall d F root n) ∧
        ∀ v ∈ q.support, v ∈ w.support := by
  induction w with
  | @nil u₀ =>
      have hdist : cubicL1Dist (root : Cubic d) (u₀ : Cubic d) = n :=
        le_antisymm hu hy
      refine ⟨u₀, .nil, ?_, ?_, ?_⟩
      · exact mem_cubicRegionMetricSphere_iff.mpr hdist
      · intro v hv
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
        subst v
        exact mem_cubicRegionMetricBall_iff.mpr hdist.le
      · simp
  | @cons u₀ u₁ y₀ hu₀u₁ tail ih =>
      by_cases hlevel : cubicL1Dist (root : Cubic d) (u₀ : Cubic d) = n
      · refine ⟨u₀, .nil, mem_cubicRegionMetricSphere_iff.mpr hlevel, ?_, ?_⟩
        · intro v hv
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
          subst v
          exact mem_cubicRegionMetricBall_iff.mpr hlevel.le
        · simp
      · have hu₀lt : cubicL1Dist (root : Cubic d) (u₀ : Cubic d) < n :=
          lt_of_le_of_ne hu hlevel
        have hadj : (cubicGraph d).Adj (u₀ : Cubic d) (u₁ : Cubic d) := by
          exact SimpleGraph.induce_adj.mp hu₀u₁
        obtain ⟨a, ha⟩ := (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj
        have hu₁le : cubicL1Dist (root : Cubic d) (u₁ : Cubic d) ≤ n := by
          calc
            cubicL1Dist (root : Cubic d) (u₁ : Cubic d) ≤
                cubicL1Dist (root : Cubic d) (u₀ : Cubic d) +
                  cubicL1Dist (u₀ : Cubic d) (u₁ : Cubic d) :=
              cubicL1Dist_triangle _ _ _
            _ = cubicL1Dist (root : Cubic d) (u₀ : Cubic d) + 1 := by
              rw [ha, cubicL1Dist_stepFrom]
            _ ≤ n := by omega
        obtain ⟨z, q, hzSphere, hqBall, hqSupport⟩ := ih hu₁le hy
        refine ⟨z, q.cons hu₀u₁, hzSphere, ?_, ?_⟩
        · intro v hv
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact mem_cubicRegionMetricBall_iff.mpr hu
          · exact hqBall v hv
        · intro v hv
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv ⊢
          rcases hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (hqSupport v hv)

namespace SiteExploration

/-- For the actual adaptive exploration of a cubic region, hitting an outer Manhattan sphere in
the occupied limit forces a hit on every inner sphere. -/
theorem antitone_cubicRegion_adaptiveLimitSphereHitEvent
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    {Omega : Type*}
    (answer : Omega → List (F × Bool) → F → Bool) :
    Antitone fun n ↦
      (cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n) := by
  intro m n hmn omega homega
  rcases homega with ⟨z, hzSphere, hzOccupied⟩
  have hzdist : cubicL1Dist (root : Cubic d) (z : Cubic d) = n :=
    mem_cubicRegionMetricSphere_iff.mp hzSphere
  let E := (cubicRegionSiteExploration d F root).toAdaptive
  have hinitial : E.OpenRootedAt root E.initial := by
    simpa [E, SiteExploration.toAdaptive, AdaptiveSiteExploration.OpenRootedAt,
      SiteExploration.OpenRootedAt] using
        cubicRegionSiteExploration_initial_openRootedAt d F root
  obtain ⟨w, hw⟩ := E.exists_open_walk_of_mem_occupiedLimit
    (answer omega) root hinitial hzOccupied
  obtain ⟨v, hvSupport, hvSphere⟩ :=
    exists_mem_walk_support_cubicRegionMetricSphere w (hmn.trans_eq hzdist.symm)
  exact ⟨v, hvSphere, hw v hvSupport⟩

/-- Meeting every ambient Manhattan sphere forces the actual occupied limit in the region to be
infinite. -/
theorem iInter_cubicRegion_adaptiveLimitSphereHitEvent_subset_infinite
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    {Omega : Type*}
    (answer : Omega → List (F × Bool) → F → Bool) :
    (⋂ n,
      (cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
        answer (cubicRegionMetricSphere d F root n)) ⊆
      {omega |
        ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (answer omega)).Infinite} := by
  intro omega homega
  simp only [Set.mem_iInter] at homega
  change ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
    (answer omega)).Infinite
  rw [← Set.not_finite]
  intro hfinite
  let S : Set F :=
    (cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit (answer omega)
  have hSfinite : S.Finite := by simpa [S] using hfinite
  letI : Fintype S := hSfinite.fintype
  let radius : S → ℕ := fun z ↦
    cubicL1Dist (root : Cubic d) ((z : F) : Cubic d)
  have hradius : Function.Surjective radius := by
    intro n
    obtain ⟨z, hzSphere, hzOccupied⟩ := homega n
    refine ⟨⟨z, hzOccupied⟩, ?_⟩
    exact mem_cubicRegionMetricSphere_iff.mp hzSphere
  exact Finite.false (α := ℕ) (Finite.of_surjective radius hradius)

/-- Region-specific exhaustion theorem: a uniform lower bound for hitting every finite Manhattan
sphere passes to the probability that the actual adaptive occupied limit is infinite. -/
theorem cubicRegion_occupiedLimit_infinite_probability_ge_of_sphere_lowerBounds
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (F × Bool) → F → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (c : ℝ)
    (hlower : ∀ n,
      c ≤ mu.real
        ((cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
          answer (cubicRegionMetricSphere d F root n))) :
    c ≤ mu.real {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (answer omega)).Infinite} := by
  let A : ℕ → Set Omega := fun n ↦
    (cubicRegionSiteExploration d F root).adaptiveLimitTargetHitEvent
      answer (cubicRegionMetricSphere d F root n)
  apply measureReal_limitEvent_ge_of_antitone_exhaustion mu A
    {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (answer omega)).Infinite} c
  · intro n
    exact measurableSet_adaptiveLimitTargetHitEvent
      (cubicRegionSiteExploration d F root) hanswer _
  · exact antitone_cubicRegion_adaptiveLimitSphereHitEvent d F root answer
  · exact iInter_cubicRegion_adaptiveLimitSphereHitEvent_subset_infinite d F root answer
  · exact hlower

end SiteExploration

end Percolation
