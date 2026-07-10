import Percolation.Critical.TorusDifferential
import Percolation.Bernoulli.BK

/-!
# Joint finite edge/green cube on the periodic lattice

The Aizenman--Barsky inequalities use BK on edge and green coordinates simultaneously.  This
file packages the two finite cubes as one inhomogeneous Bernoulli cube and proves the exact
Fubini bridge back to the nested polynomial used elsewhere in the development.
-/

namespace Percolation

open Set
open scoped BigOperators unitInterval

noncomputable section

theorem finiteBernoulliWeightFamily_disjSum_mixed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {E : Finset ι} {F : Finset κ} (q : ι → ℝ) (r : κ → ℝ)
    {w : Finset (ι ⊕ κ)} (hw : w ⊆ E.disjSum F) :
    finiteBernoulliWeightFamily (E.disjSum F) (Sum.elim q r) w =
      finiteBernoulliWeightFamily E q w.toLeft *
        finiteBernoulliWeightFamily F r w.toRight := by
  unfold finiteBernoulliWeightFamily
  obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp hw
  rw [show w = w.toLeft.disjSum w.toRight by
    exact (@Finset.toLeft_disjSum_toRight _ _ w).symm]
  have hsdiff : E.disjSum F \ (w.toLeft.disjSum w.toRight) =
      (E \ w.toLeft).disjSum (F \ w.toRight) := by
    ext (a | a) <;> simp
  rw [hsdiff]
  simp
  ring

theorem finiteBernoulliExpectationFamily_disjSum_mixed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (E : Finset ι) (F : Finset κ) (q : ι → ℝ) (r : κ → ℝ)
    (X : Finset (ι ⊕ κ) → ℝ) :
    finiteBernoulliExpectationFamily (E.disjSum F) (Sum.elim q r) X =
      finiteBernoulliExpectationFamily E q fun s ↦
        finiteBernoulliExpectationFamily F r fun t ↦ X (s.disjSum t) := by
  unfold finiteBernoulliExpectationFamily
  simp only [Finset.mul_sum, mul_assoc]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun w ↦ (w.toLeft, w.toRight))
    (fun x ↦ x.1.disjSum x.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hw)
    rw [Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr hL, Finset.mem_powerset.mpr hR⟩
  · intro x hx
    rw [Finset.mem_product] at hx
    exact Finset.mem_powerset.mpr
      (Finset.disjSum_mono (Finset.mem_powerset.mp hx.1)
        (Finset.mem_powerset.mp hx.2))
  · intro w hw
    exact Finset.toLeft_disjSum_toRight
  · intro x hx
    simp
  · intro w hw
    rw [finiteBernoulliWeightFamily_disjSum_mixed q r
      (Finset.mem_powerset.mp hw)]
    rw [Finset.toLeft_disjSum_toRight]
    ring

theorem finiteBernoulliProbabilityFamily_disjSum_mixed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (E : Finset ι) (F : Finset κ) (q : ι → ℝ) (r : κ → ℝ)
    (T : Set (Finset ι)) (U : Set (Finset κ)) :
    finiteBernoulliProbabilityFamily (E.disjSum F) (Sum.elim q r)
        {w : Finset (ι ⊕ κ) | w.toLeft ∈ T ∧ w.toRight ∈ U} =
      finiteBernoulliProbabilityFamily E q T *
        finiteBernoulliProbabilityFamily F r U := by
  rw [finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_nbij' (fun w ↦ (w.toLeft, w.toRight))
    (fun x ↦ x.1.disjSum x.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hw)
    rw [Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr hL, Finset.mem_powerset.mpr hR⟩
  · intro x hx
    rw [Finset.mem_product] at hx
    exact Finset.mem_powerset.mpr
      (Finset.disjSum_mono (Finset.mem_powerset.mp hx.1)
        (Finset.mem_powerset.mp hx.2))
  · intro w hw
    exact Finset.toLeft_disjSum_toRight
  · intro x hx
    simp
  · intro w hw
    rw [finiteBernoulliWeightFamily_disjSum_mixed q r
      (Finset.mem_powerset.mp hw)]
    by_cases h1 : w.toLeft ∈ T
    · by_cases h2 : w.toRight ∈ U
      · have hmem : w ∈ {w : Finset (ι ⊕ κ) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
          ⟨h1, h2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1,
          Set.indicator_of_mem h2]
        ring
      · have hmem : w ∉ {w : Finset (ι ⊕ κ) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
          fun hc ↦ h2 hc.2
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h2]
        ring
    · have hmem : w ∉ {w : Finset (ι ⊕ κ) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
        fun hc ↦ h1 hc.1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]
      ring

theorem finiteBernoulliProbabilityFamily_map_equiv
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (q : ι → ℝ) (f : ι ≃ ι)
    (hE : E.map f.toEmbedding = E) (hq : ∀ a, q (f a) = q a)
    (T : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily E q {s | s.map f.toEmbedding ∈ T} =
      finiteBernoulliProbabilityFamily E q T := by
  rw [finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator]
  refine Finset.sum_nbij' (fun s ↦ s.map f.toEmbedding)
    (fun s ↦ s.map f.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs ⊢
    rw [← hE]
    exact Finset.map_subset_map.mpr hs
  · intro s hs
    rw [Finset.mem_powerset] at hs ⊢
    have hEinv : E.map f.symm.toEmbedding = E := by
      ext x
      have hx := congrArg (fun S : Finset ι ↦ f x ∈ S) hE
      simpa using hx.symm
    rw [← hEinv]
    exact Finset.map_subset_map.mpr hs
  · intro s hs
    ext x
    simp
  · intro s hs
    ext x
    simp
  · intro s hs
    rw [finiteBernoulliWeightFamily_map_equiv E q f hE hq s]
    rfl

abbrev TorusGhostCoordinate (d N : ℕ) :=
  CubicTorusEdge d N ⊕ CubicTorus d N

noncomputable def torusGhostCoordinateFinset (d N : ℕ) (hN : 2 ≤ N) :
    Finset (TorusGhostCoordinate d N) :=
  (cubicTorusEdgeFinset d N hN).disjSum (cubicTorusVertexFinset d N hN)

def torusGhostCoordinateDensity (p γ : ℝ) : TorusGhostCoordinate d N → ℝ :=
  Sum.elim (fun _ ↦ p) (fun _ ↦ γ)

def torusGhostHitJointTrace (d N : ℕ) : Set (Finset (TorusGhostCoordinate d N)) :=
  {s | ∃ y ∈ s.toRight,
    y ∈ cubicTorusOpenCluster d N (s.toLeft : Set (CubicTorusEdge d N))}

def torusGhostReachJointTrace (d N : ℕ) (x : CubicTorus d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  {s | ∃ y ∈ s.toRight,
    y ∈ cubicTorusOpenClusterFrom d N
      (s.toLeft : Set (CubicTorusEdge d N)) x}

theorem torusGhostHitJointTrace_eq_reach_origin (d N : ℕ) :
    torusGhostHitJointTrace d N =
      torusGhostReachJointTrace d N (cubicTorusOrigin d N) := rfl

theorem isIncreasingTrace_torusGhostHitJointTrace (d N : ℕ) :
    IsIncreasingTrace (torusGhostHitJointTrace d N) := by
  intro s t hst
  rintro ⟨y, hyG, hyC⟩
  refine ⟨y, Finset.toRight_subset_toRight hst hyG, ?_⟩
  exact cubicTorusOpenCluster_mono (Finset.coe_subset.mpr
    (Finset.toLeft_subset_toLeft hst)) hyC

theorem isIncreasingTrace_torusGhostReachJointTrace
    (d N : ℕ) (x : CubicTorus d N) :
    IsIncreasingTrace (torusGhostReachJointTrace d N x) := by
  intro s t hst
  rintro ⟨y, hyG, w, hw⟩
  refine ⟨y, Finset.toRight_subset_toRight hst hyG, w, ?_⟩
  exact torusWalkIsOpen_mono (Finset.coe_subset.mpr
    (Finset.toLeft_subset_toLeft hst)) hw

noncomputable def torusGhostTranslationEquiv (hN : 2 ≤ N)
    (z : CubicTorus d N) : TorusGhostCoordinate d N ≃ TorusGhostCoordinate d N :=
  Equiv.sumCongr (cubicTorusTranslationIso hN z).mapEdgeSet
    (cubicTorusTranslationIso hN z).toEquiv

@[simp]
theorem torusGhostTranslationEquiv_inl (hN : 2 ≤ N) (z : CubicTorus d N)
    (e : CubicTorusEdge d N) :
    torusGhostTranslationEquiv hN z (Sum.inl e) =
      Sum.inl ((cubicTorusTranslationIso hN z).mapEdgeSet e) := rfl

@[simp]
theorem torusGhostTranslationEquiv_inr (hN : 2 ≤ N) (z : CubicTorus d N)
    (x : CubicTorus d N) :
    torusGhostTranslationEquiv hN z (Sum.inr x) =
      Sum.inr (cubicTorusTranslate z x) := rfl

theorem torusGhostCoordinateFinset_map_translation (hN : 2 ≤ N)
    (z : CubicTorus d N) :
    (torusGhostCoordinateFinset d N hN).map
        (torusGhostTranslationEquiv hN z).toEmbedding =
      torusGhostCoordinateFinset d N hN := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rcases a with e | x
    · exact Finset.inl_mem_disjSum.mpr (mem_cubicTorusEdgeFinset hN e)
    · exact Finset.inr_mem_disjSum.mpr (mem_cubicTorusVertexFinset hN x)
  · intro ha
    rcases a with e | x
    · let f := (cubicTorusTranslationIso hN z).mapEdgeSet.symm e
      apply Finset.mem_map.mpr
      refine ⟨Sum.inl f, Finset.inl_mem_disjSum.mpr
        (mem_cubicTorusEdgeFinset hN f), ?_⟩
      exact congrArg Sum.inl
        ((cubicTorusTranslationIso hN z).mapEdgeSet.apply_symm_apply e)
    · let y := (cubicTorusTranslationIso hN z).toEquiv.symm x
      apply Finset.mem_map.mpr
      refine ⟨Sum.inr y, Finset.inr_mem_disjSum.mpr
        (mem_cubicTorusVertexFinset hN y), ?_⟩
      exact congrArg Sum.inr
        ((cubicTorusTranslationIso hN z).toEquiv.apply_symm_apply x)

theorem torusGhostCoordinateDensity_translation (hN : 2 ≤ N)
    (z : CubicTorus d N) (p γ : ℝ) (a : TorusGhostCoordinate d N) :
    torusGhostCoordinateDensity p γ (torusGhostTranslationEquiv hN z a) =
      torusGhostCoordinateDensity p γ a := by
  rcases a with a | a <;> rfl

@[simp]
theorem toLeft_map_torusGhostTranslation (hN : 2 ≤ N)
    (z : CubicTorus d N) (s : Finset (TorusGhostCoordinate d N)) :
    (s.map (torusGhostTranslationEquiv hN z).toEmbedding).toLeft =
      s.toLeft.map (cubicTorusTranslationIso hN z).mapEdgeSet.toEmbedding := by
  ext e
  simp [torusGhostTranslationEquiv]

@[simp]
theorem toRight_map_torusGhostTranslation (hN : 2 ≤ N)
    (z : CubicTorus d N) (s : Finset (TorusGhostCoordinate d N)) :
    (s.map (torusGhostTranslationEquiv hN z).toEmbedding).toRight =
      s.toRight.map (cubicTorusTranslationIso hN z).toEquiv.toEmbedding := by
  ext x
  simp [torusGhostTranslationEquiv]

theorem torusWalkIsOpen_map_iso
    (f : cubicTorusGraph d N ≃g cubicTorusGraph d N)
    (s : Finset (CubicTorusEdge d N)) {x y : CubicTorus d N}
    (w : (cubicTorusGraph d N).Walk x y)
    (hw : torusWalkIsOpen (s : Set (CubicTorusEdge d N)) w) :
    torusWalkIsOpen (s.map f.mapEdgeSet.toEmbedding : Set (CubicTorusEdge d N))
      (w.map f.toHom) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨g, hg, hge⟩ := List.mem_map.mp he
  let gE : CubicTorusEdge d N := ⟨g, w.edges_subset_edgeSet hg⟩
  apply Finset.mem_map.mpr
  refine ⟨gE, hw g hg, ?_⟩
  apply Subtype.ext
  exact hge

theorem torusGhostReachJointTrace_map_translation_iff
    (hN : 2 ≤ N) (z x : CubicTorus d N)
    (s : Finset (TorusGhostCoordinate d N)) :
    s.map (torusGhostTranslationEquiv hN z).toEmbedding ∈
        torusGhostReachJointTrace d N (cubicTorusTranslate z x) ↔
      s ∈ torusGhostReachJointTrace d N x := by
  let f := cubicTorusTranslationIso hN z
  constructor
  · rintro ⟨y, hyG, w, hw⟩
    rw [toRight_map_torusGhostTranslation] at hyG
    obtain ⟨y₀, hy₀G, hy₀⟩ := Finset.mem_map.mp hyG
    let w₀ := w.map f.symm.toHom
    have hw₀ : torusWalkIsOpen
        ((s.toLeft.map f.mapEdgeSet.toEmbedding).map
          f.symm.mapEdgeSet.toEmbedding : Set (CubicTorusEdge d N)) w₀ := by
      apply torusWalkIsOpen_map_iso f.symm
      simpa [f, toLeft_map_torusGhostTranslation] using hw
    have hedge : (s.toLeft.map f.mapEdgeSet.toEmbedding).map
        f.symm.mapEdgeSet.toEmbedding = s.toLeft := by
      ext e
      constructor
      · intro he
        obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hg
        have hback : f.symm.mapEdgeSet (f.mapEdgeSet k) = k :=
          f.mapEdgeSet.symm_apply_apply k
        change f.symm.mapEdgeSet (f.mapEdgeSet k) ∈ s.toLeft
        rw [hback]
        exact hk
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨f.mapEdgeSet e, Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
        exact f.mapEdgeSet.symm_apply_apply e
    let w₁ : (cubicTorusGraph d N).Walk x y₀ :=
      w₀.copy (f.symm_apply_apply x) (by
        change f.symm y = y₀
        rw [← hy₀]
        exact f.symm_apply_apply y₀)
    refine ⟨y₀, hy₀G, w₁, ?_⟩
    rw [hedge] at hw₀
    intro e he
    apply hw₀ e
    simpa [w₁, SimpleGraph.Walk.edges_copy] using he
  · rintro ⟨y, hyG, w, hw⟩
    refine ⟨cubicTorusTranslate z y, ?_, w.map f.toHom, ?_⟩
    · rw [toRight_map_torusGhostTranslation]
      exact Finset.mem_map.mpr ⟨y, hyG, rfl⟩
    · rw [toLeft_map_torusGhostTranslation]
      exact torusWalkIsOpen_map_iso f s.toLeft w hw

theorem finiteBernoulliProbabilityFamily_torusGhostHitJointTrace
    (d N : ℕ) (hN : 2 ≤ N) (p γ : ℝ) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ) (torusGhostHitJointTrace d N) =
      torusGhostThetaPolynomial d N hN p γ := by
  unfold finiteBernoulliProbabilityFamily
  unfold torusGhostCoordinateFinset torusGhostCoordinateDensity
  rw [finiteBernoulliExpectationFamily_disjSum_mixed]
  simp_rw [finiteBernoulliExpectationFamily_const]
  rw [finiteBernoulliExpectation_comm]
  unfold torusGhostThetaPolynomial finiteBernoulliProbability
  apply finiteBernoulliExpectation_congr
  intro G hG
  apply finiteBernoulliExpectation_congr
  intro ω hω
  have hmem : ω.disjSum G ∈ torusGhostHitJointTrace d N ↔
      ω ∈ torusHitEdgeTrace d N G := by
    simp [torusGhostHitJointTrace, torusHitEdgeTrace]
  by_cases h : ω.disjSum G ∈ torusGhostHitJointTrace d N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem fun h' ↦ h (hmem.mpr h')]

theorem finiteBernoulliProbabilityFamily_torusGhostReachJointTrace
    (d N : ℕ) (hN : 2 ≤ N) (p γ : ℝ) (x : CubicTorus d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ) (torusGhostReachJointTrace d N x) =
      torusGhostThetaPolynomial d N hN p γ := by
  have hx : cubicTorusTranslate x (cubicTorusOrigin d N) = x := by
    ext i
    simp [cubicTorusTranslate, cubicTorusOrigin]
  have hmap := finiteBernoulliProbabilityFamily_map_equiv
    (torusGhostCoordinateFinset d N hN) (torusGhostCoordinateDensity p γ)
    (torusGhostTranslationEquiv hN x)
    (torusGhostCoordinateFinset_map_translation hN x)
    (torusGhostCoordinateDensity_translation hN x p γ)
    (torusGhostReachJointTrace d N x)
  have hpre : {s : Finset (TorusGhostCoordinate d N) |
      s.map (torusGhostTranslationEquiv hN x).toEmbedding ∈
        torusGhostReachJointTrace d N x} =
      torusGhostHitJointTrace d N := by
    ext s
    change s.map (torusGhostTranslationEquiv hN x).toEmbedding ∈
        torusGhostReachJointTrace d N x ↔
      s ∈ torusGhostReachJointTrace d N (cubicTorusOrigin d N)
    have ht := torusGhostReachJointTrace_map_translation_iff hN x
      (cubicTorusOrigin d N) s
    rw [hx] at ht
    exact ht
  rw [hpre] at hmap
  rw [← hmap]
  exact finiteBernoulliProbabilityFamily_torusGhostHitJointTrace d N hN p γ

theorem torusGhostReach_disjointOccurrence_le_theta_sq
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) (x : CubicTorus d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (TraceDisjointOccurrence (torusGhostReachJointTrace d N x)
          (torusGhostReachJointTrace d N x)) ≤
      torusGhostThetaPolynomial d N hN p γ ^ 2 := by
  have hbk := finiteBernoulliProbabilityFamily_traceDisjointOccurrence_le_mul
    (E := torusGhostCoordinateFinset d N hN)
    (q := torusGhostCoordinateDensity (p : ℝ) (γ : ℝ))
    (fun a _ha ↦ by
      cases a <;> simp [torusGhostCoordinateDensity, p.2.1, γ.2.1])
    (fun a _ha ↦ by
      cases a <;> simp [torusGhostCoordinateDensity, p.2.2, γ.2.2])
    (isIncreasingTrace_torusGhostReachJointTrace d N x)
    (isIncreasingTrace_torusGhostReachJointTrace d N x)
  rw [finiteBernoulliProbabilityFamily_torusGhostReachJointTrace
    d N hN p γ x] at hbk
  simpa [pow_two] using hbk

end

end Percolation
