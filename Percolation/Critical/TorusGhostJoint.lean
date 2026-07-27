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
open scoped BigOperators unitInterval Classical

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
  simp only [Finset.mul_sum]
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

/-- Finite inhomogeneous Bernoulli probability is additive on disjoint trace events. -/
theorem finiteBernoulliProbabilityFamily_union_of_disjoint
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (q : ι → ℝ)
    {T U : Set (Finset ι)} (hTU : Disjoint T U) :
    finiteBernoulliProbabilityFamily E q (T ∪ U) =
      finiteBernoulliProbabilityFamily E q T +
        finiteBernoulliProbabilityFamily E q U := by
  rw [finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hT : s ∈ T
  · have hU : s ∉ U := fun hU ↦ Set.disjoint_left.mp hTU hT hU
    simp [hT, hU]
  · by_cases hU : s ∈ U <;> simp [hT, hU]

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

def finiteHitsTrace {ι : Type*} (S : Finset ι) : Set (Finset ι) :=
  {t | ∃ x ∈ S, x ∈ t}

def finiteAvoidsTrace {ι : Type*} (S : Finset ι) : Set (Finset ι) :=
  {t | Disjoint S t}

noncomputable def finiteExactlyOneTrace {ι : Type*}
    (S : Finset ι) : Set (Finset ι) := by
  classical
  exact {t | (S ∩ t).card = 1}

theorem finiteBernoulliProbability_avoids_finset
    {ι : Type*} [DecidableEq ι] {E S : Finset ι} (hSE : S ⊆ E) (p : I) :
    finiteBernoulliProbability E p (finiteAvoidsTrace S) =
      (1 - (p : ℝ)) ^ S.card := by
  have hpartition : finiteBernoulliProbability E p (finiteAvoidsTrace S) +
      finiteBernoulliProbability E p (finiteHitsTrace S) = 1 := by
    unfold finiteBernoulliProbability
    rw [← finiteBernoulliExpectation_add]
    calc
      finiteBernoulliExpectation E p
          (fun t ↦ (finiteAvoidsTrace S).indicator (fun _ ↦ (1 : ℝ)) t +
            (finiteHitsTrace S).indicator (fun _ ↦ (1 : ℝ)) t) =
          finiteBernoulliExpectation E p (fun _ ↦ (1 : ℝ)) := by
        apply finiteBernoulliExpectation_congr
        intro t ht
        by_cases h : Disjoint S t
        · have hn : t ∉ finiteHitsTrace S := by
            rintro ⟨x, hxS, hxt⟩
            exact Finset.disjoint_left.mp h hxS hxt
          have hav : t ∈ finiteAvoidsTrace S := h
          rw [Set.indicator_of_mem hav, Set.indicator_of_notMem hn]
          norm_num
        · have hh : t ∈ finiteHitsTrace S := by
            rw [Finset.not_disjoint_iff] at h
            obtain ⟨x, hxS, hxt⟩ := h
            exact ⟨x, hxS, hxt⟩
          simp [finiteAvoidsTrace, h, hh]
      _ = 1 := finiteBernoulliExpectation_one E p
  have hhit := finiteBernoulliProbability_hits_finset hSE p
  change finiteBernoulliProbability E p (finiteHitsTrace S) = _ at hhit
  linarith

theorem finiteBernoulliProbability_exactlyOne_finset
    {ι : Type*} [DecidableEq ι] {E S : Finset ι} (hSE : S ⊆ E) (p : I) :
    finiteBernoulliProbability E p (finiteExactlyOneTrace S) =
      (S.card : ℝ) * (p : ℝ) * (1 - (p : ℝ)) ^ (S.card - 1) := by
  letI : DecidableEq ι := Classical.decEq ι
  induction E using Finset.induction generalizing S with
  | empty =>
      have hS : S = ∅ := Finset.subset_empty.mp hSE
      subst S
      simp [finiteExactlyOneTrace, finiteBernoulliProbability,
        finiteBernoulliExpectation]
  | @insert a E ha ih =>
      by_cases haS : a ∈ S
      · let S₀ := S.erase a
        have hS : S = insert a S₀ := by
          simp [S₀, haS]
        have hS₀E : S₀ ⊆ E := by
          intro x hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          have hxIns := hSE hxS
          rw [Finset.mem_insert] at hxIns
          have hane : a ∉ S₀ := by simp [S₀]
          exact hxIns.resolve_left fun hxa ↦
            hane (hxa ▸ hx)
        unfold finiteBernoulliProbability
        conv_lhs =>
          rw [finiteBernoulliExpectation_insert (E := E) (a := a) ha]
        have hopen : finiteBernoulliExpectation E p
            (fun t ↦ (finiteExactlyOneTrace S).indicator (fun _ ↦ (1 : ℝ)) (insert a t)) =
            finiteBernoulliProbability E p (finiteAvoidsTrace S₀) := by
          unfold finiteBernoulliProbability
          apply finiteBernoulliExpectation_congr
          intro t ht
          have hat : a ∉ t := fun hat ↦ ha (Finset.mem_powerset.mp ht hat)
          have hinter : S ∩ insert a t = insert a (S₀ ∩ t) := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [haS, hat, S₀]
            · simp [hxa, S₀]
          have hiff : insert a t ∈ finiteExactlyOneTrace S ↔
              t ∈ finiteAvoidsTrace S₀ := by
            rw [finiteExactlyOneTrace, finiteAvoidsTrace, Set.mem_setOf_eq,
              Set.mem_setOf_eq, hinter, Finset.card_insert_of_notMem]
            · rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
              omega
            · simp [hat]
          by_cases h : insert a t ∈ finiteExactlyOneTrace S
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
          · rw [Set.indicator_of_notMem h,
              Set.indicator_of_notMem fun h' ↦ h (hiff.mpr h')]
        have hclosed : finiteBernoulliExpectation E p
            (fun t ↦ (finiteExactlyOneTrace S).indicator (fun _ ↦ (1 : ℝ)) t) =
            finiteBernoulliProbability E p (finiteExactlyOneTrace S₀) := by
          unfold finiteBernoulliProbability
          apply finiteBernoulliExpectation_congr
          intro t ht
          have hat : a ∉ t := fun hat ↦ ha (Finset.mem_powerset.mp ht hat)
          have hinter : S ∩ t = S₀ ∩ t := by ext x; simp [S₀, hat]
          by_cases h : t ∈ finiteExactlyOneTrace S
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
            simpa [finiteExactlyOneTrace, hinter] using h
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
            intro h'
            exact h (by simpa [finiteExactlyOneTrace, hinter] using h')
        rw [hopen, hclosed,
          finiteBernoulliProbability_avoids_finset hS₀E p, ih hS₀E]
        have hcard : S.card = S₀.card + 1 := by
          rw [hS, Finset.card_insert_of_notMem]
          simp [S₀]
        rw [hcard]
        simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
        cases hk : S₀.card with
        | zero => simp
        | succ k =>
            rw [Nat.succ_sub_one, pow_succ]
            ring
      · have hSE' : S ⊆ E := by
          intro x hx
          have hxIns := hSE hx
          rw [Finset.mem_insert] at hxIns
          exact hxIns.resolve_left fun hxa ↦ haS (hxa ▸ hx)
        unfold finiteBernoulliProbability
        conv_lhs =>
          rw [finiteBernoulliExpectation_insert (E := E) (a := a) ha]
        have hsameInsert : finiteBernoulliExpectation E p
            (fun t ↦ (finiteExactlyOneTrace S).indicator (fun _ ↦ (1 : ℝ)) (insert a t)) =
            finiteBernoulliProbability E p (finiteExactlyOneTrace S) := by
          unfold finiteBernoulliProbability
          apply finiteBernoulliExpectation_congr
          intro t ht
          have hinter : S ∩ insert a t = S ∩ t := by ext x; simp [haS]
          by_cases h : insert a t ∈ finiteExactlyOneTrace S
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
            simpa [finiteExactlyOneTrace, hinter] using h
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
            intro h'
            exact h (by simpa [finiteExactlyOneTrace, hinter] using h')
        have hsame : finiteBernoulliExpectation E p
            (fun t ↦ (finiteExactlyOneTrace S).indicator (fun _ ↦ (1 : ℝ)) t) =
            finiteBernoulliProbability E p (finiteExactlyOneTrace S) := rfl
        rw [hsameInsert, hsame, ih hSE']
        ring

def torusOriginGreenCount (d N : ℕ) (hN : 2 ≤ N)
    (s : Finset (TorusGhostCoordinate d N)) : ℕ :=
  ((cubicTorusOpenClusterFinset d N hN
    (s.toLeft : Set (CubicTorusEdge d N))) ∩ s.toRight).card

def torusExactlyOneGreenTrace (d N : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  {s | torusOriginGreenCount d N hN s = 1}

def torusAtLeastTwoGreenTrace (d N : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  {s | 2 ≤ torusOriginGreenCount d N hN s}

theorem finiteBernoulliProbabilityFamily_torusExactlyOneGreenTrace
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ) (torusExactlyOneGreenTrace d N hN) =
      (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ := by
  unfold finiteBernoulliProbabilityFamily
  unfold torusGhostCoordinateFinset torusGhostCoordinateDensity
  rw [finiteBernoulliExpectationFamily_disjSum_mixed]
  simp_rw [finiteBernoulliExpectationFamily_const]
  calc
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
        (fun ω ↦ finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
          (fun G ↦ (torusExactlyOneGreenTrace d N hN).indicator
            (fun _ ↦ (1 : ℝ)) (ω.disjSum G))) =
      finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p (fun ω ↦
        let S := cubicTorusOpenClusterFinset d N hN
          (ω : Set (CubicTorusEdge d N))
        (S.card : ℝ) * (γ : ℝ) * (1 - (γ : ℝ)) ^ (S.card - 1)) := by
      apply finiteBernoulliExpectation_congr
      intro ω hω
      let S := cubicTorusOpenClusterFinset d N hN
        (ω : Set (CubicTorusEdge d N))
      have hprob := finiteBernoulliProbability_exactlyOne_finset
        (E := cubicTorusVertexFinset d N hN) (S := S)
        (restrictTo_subset _ _) γ
      rw [finiteBernoulliProbability] at hprob
      change finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
          (fun G ↦ (torusExactlyOneGreenTrace d N hN).indicator
            (fun _ ↦ (1 : ℝ)) (ω.disjSum G)) =
        (S.card : ℝ) * (γ : ℝ) * (1 - (γ : ℝ)) ^ (S.card - 1)
      rw [← hprob]
      apply finiteBernoulliExpectation_congr
      intro G hG
      have hmem : ω.disjSum G ∈ torusExactlyOneGreenTrace d N hN ↔
          G ∈ finiteExactlyOneTrace S := by
        unfold torusExactlyOneGreenTrace torusOriginGreenCount finiteExactlyOneTrace
        simp only [Set.mem_setOf_eq, Finset.toLeft_disjSum, Finset.toRight_disjSum]
        constructor
        · intro h
          rw [Finset.card_eq_one] at h ⊢
          obtain ⟨x, hx⟩ := h
          refine ⟨x, Finset.ext fun y ↦ ?_⟩
          have hxy := Finset.ext_iff.mp hx y
          simpa [S] using hxy
        · intro h
          rw [Finset.card_eq_one] at h ⊢
          obtain ⟨x, hx⟩ := h
          refine ⟨x, Finset.ext fun y ↦ ?_⟩
          have hxy := Finset.ext_iff.mp hx y
          simpa [S] using hxy
      by_cases h : ω.disjSum G ∈ torusExactlyOneGreenTrace d N hN
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem fun h' ↦ h (hmem.mpr h')]
    _ = (γ : ℝ) * torusGhostThetaGammaDerivativeByCluster d N hN p γ := by
      unfold torusGhostThetaGammaDerivativeByCluster
      rw [← finiteBernoulliExpectation_const_mul]
      apply finiteBernoulliExpectation_congr
      intro ω hω
      ring
    _ = (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ := by
      rw [torusGhostThetaGammaDerivative_eq_byCluster d N hN p γ hγ0 hγ1]

/-- Two disjoint open witnesses from the origin to green vertices necessarily expose two
distinct green vertices in the origin cluster.  This is the deterministic inclusion used
before applying BK in Grimmett's equation (5.71). -/
theorem torusGhostReach_disjointOccurrence_subset_atLeastTwoGreenTrace
    (d N : ℕ) (hN : 2 ≤ N) :
    TraceDisjointOccurrence
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N)) ⊆
      torusAtLeastTwoGreenTrace d N hN := by
  rintro s ⟨H, K, hdisj, hHs, hKs, hH, hK⟩
  obtain ⟨y, hyH, hyC⟩ := hH
  obtain ⟨z, hzK, hzC⟩ := hK
  have hyG : y ∈ s.toRight := Finset.toRight_subset_toRight hHs hyH
  have hzG : z ∈ s.toRight := Finset.toRight_subset_toRight hKs hzK
  have hyCluster : y ∈ cubicTorusOpenCluster d N
      (s.toLeft : Set (CubicTorusEdge d N)) :=
    cubicTorusOpenCluster_mono
      (Finset.coe_subset.mpr (Finset.toLeft_subset_toLeft hHs)) hyC
  have hzCluster : z ∈ cubicTorusOpenCluster d N
      (s.toLeft : Set (CubicTorusEdge d N)) :=
    cubicTorusOpenCluster_mono
      (Finset.coe_subset.mpr (Finset.toLeft_subset_toLeft hKs)) hzC
  have hyMem : y ∈ cubicTorusOpenClusterFinset d N hN
      (s.toLeft : Set (CubicTorusEdge d N)) ∩ s.toRight :=
    Finset.mem_inter.mpr ⟨(mem_cubicTorusOpenClusterFinset hN).mpr hyCluster, hyG⟩
  have hzMem : z ∈ cubicTorusOpenClusterFinset d N hN
      (s.toLeft : Set (CubicTorusEdge d N)) ∩ s.toRight :=
    Finset.mem_inter.mpr ⟨(mem_cubicTorusOpenClusterFinset hN).mpr hzCluster, hzG⟩
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_toRight.mp hyH) (Finset.mem_toRight.mp hzK)
  unfold torusAtLeastTwoGreenTrace torusOriginGreenCount
  rw [Set.mem_setOf_eq, Nat.succ_le_iff, Finset.one_lt_card]
  exact ⟨y, hyMem, z, hzMem, hyz⟩

theorem mem_torusGhostHitJointTrace_iff_originGreenCount_pos
    (d N : ℕ) (hN : 2 ≤ N) (s : Finset (TorusGhostCoordinate d N)) :
    s ∈ torusGhostHitJointTrace d N ↔ 0 < torusOriginGreenCount d N hN s := by
  unfold torusGhostHitJointTrace torusOriginGreenCount
  rw [Set.mem_setOf_eq, Finset.card_pos]
  constructor
  · rintro ⟨y, hyG, hyC⟩
    exact ⟨y, Finset.mem_inter.mpr
      ⟨(mem_cubicTorusOpenClusterFinset hN).mpr hyC, hyG⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨hyC, hyG⟩ := Finset.mem_inter.mp hy
    exact ⟨y, hyG, (mem_cubicTorusOpenClusterFinset hN).mp hyC⟩

/-- Equation (5.68), at the event level: hitting the green set means that the origin
cluster contains exactly one green vertex or at least two. -/
theorem torusGhostHitJointTrace_eq_exactlyOne_union_atLeastTwo
    (d N : ℕ) (hN : 2 ≤ N) :
    torusGhostHitJointTrace d N =
      torusExactlyOneGreenTrace d N hN ∪ torusAtLeastTwoGreenTrace d N hN := by
  ext s
  rw [mem_torusGhostHitJointTrace_iff_originGreenCount_pos d N hN]
  unfold torusExactlyOneGreenTrace torusAtLeastTwoGreenTrace
  simp only [Set.mem_union, Set.mem_setOf_eq]
  omega

theorem disjoint_torusExactlyOneGreenTrace_torusAtLeastTwoGreenTrace
    (d N : ℕ) (hN : 2 ≤ N) :
    Disjoint (torusExactlyOneGreenTrace d N hN)
      (torusAtLeastTwoGreenTrace d N hN) := by
  rw [Set.disjoint_left]
  intro s hOne hTwo
  exact (by
    unfold torusExactlyOneGreenTrace at hOne
    unfold torusAtLeastTwoGreenTrace at hTwo
    simp only [Set.mem_setOf_eq] at hOne hTwo
    omega)

noncomputable def torusGhostExceptionalTrace (d N : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  torusAtLeastTwoGreenTrace d N hN \
    TraceDisjointOccurrence
      (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
      (torusGhostReachJointTrace d N (cubicTorusOrigin d N))

theorem torusAtLeastTwoGreenTrace_eq_disjointOccurrence_union_exceptional
    (d N : ℕ) (hN : 2 ≤ N) :
    torusAtLeastTwoGreenTrace d N hN =
      TraceDisjointOccurrence
          (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
          (torusGhostReachJointTrace d N (cubicTorusOrigin d N)) ∪
        torusGhostExceptionalTrace d N hN := by
  apply Set.Subset.antisymm
  · intro s hs
    by_cases hd : s ∈ TraceDisjointOccurrence
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
    · exact Or.inl hd
    · exact Or.inr ⟨hs, hd⟩
  · rintro s (hs | hs)
    · exact torusGhostReach_disjointOccurrence_subset_atLeastTwoGreenTrace d N hN hs
    · exact hs.1

theorem disjoint_torusGhostReach_disjointOccurrence_exceptional
    (d N : ℕ) (hN : 2 ≤ N) :
    Disjoint
      (TraceDisjointOccurrence
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
        (torusGhostReachJointTrace d N (cubicTorusOrigin d N)))
      (torusGhostExceptionalTrace d N hN) := by
  rw [Set.disjoint_left]
  intro s hs hse
  exact hse.2 hs

/-- The probability form of equations (5.68)--(5.70), before the exceptional event is
estimated by pivotal edges. -/
theorem torusGhostThetaPolynomial_eq_gamma_mul_gammaDerivative_add_atLeastTwo
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostThetaPolynomial d N hN p γ =
      (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusAtLeastTwoGreenTrace d N hN) := by
  rw [← finiteBernoulliProbabilityFamily_torusGhostHitJointTrace d N hN p γ,
    torusGhostHitJointTrace_eq_exactlyOne_union_atLeastTwo d N hN,
    finiteBernoulliProbabilityFamily_union_of_disjoint
      (torusGhostCoordinateFinset d N hN) (torusGhostCoordinateDensity p γ)
      (disjoint_torusExactlyOneGreenTrace_torusAtLeastTwoGreenTrace d N hN),
    finiteBernoulliProbabilityFamily_torusExactlyOneGreenTrace
      d N hN p γ hγ0 hγ1]

theorem finiteBernoulliProbabilityFamily_torusAtLeastTwoGreenTrace_eq
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusAtLeastTwoGreenTrace d N hN) =
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (TraceDisjointOccurrence
            (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
            (torusGhostReachJointTrace d N (cubicTorusOrigin d N))) +
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostExceptionalTrace d N hN) := by
  rw [torusAtLeastTwoGreenTrace_eq_disjointOccurrence_union_exceptional d N hN,
    finiteBernoulliProbabilityFamily_union_of_disjoint
      (torusGhostCoordinateFinset d N hN) (torusGhostCoordinateDensity p γ)
      (disjoint_torusGhostReach_disjointOccurrence_exceptional d N hN)]

/-- Finite-volume precursor to Lemma 5.53: after the exact one-green term and BK term,
only Grimmett's exceptional pivotal event remains to be bounded. -/
theorem torusGhostThetaPolynomial_le_gammaDerivative_add_sq_add_exceptional
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    torusGhostThetaPolynomial d N hN p γ ≤
      (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
        torusGhostThetaPolynomial d N hN p γ ^ 2 +
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostExceptionalTrace d N hN) := by
  have hbk := torusGhostReach_disjointOccurrence_le_theta_sq
    d N hN p γ (cubicTorusOrigin d N)
  calc
    torusGhostThetaPolynomial d N hN p γ =
        (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusAtLeastTwoGreenTrace d N hN) :=
      torusGhostThetaPolynomial_eq_gamma_mul_gammaDerivative_add_atLeastTwo
        d N hN p γ hγ0 hγ1
    _ = (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
          (finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (TraceDisjointOccurrence
                (torusGhostReachJointTrace d N (cubicTorusOrigin d N))
                (torusGhostReachJointTrace d N (cubicTorusOrigin d N))) +
            finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (torusGhostExceptionalTrace d N hN)) := by
      rw [finiteBernoulliProbabilityFamily_torusAtLeastTwoGreenTrace_eq]
    _ ≤ (γ : ℝ) * torusGhostThetaGammaDerivative d N hN p γ +
          torusGhostThetaPolynomial d N hN p γ ^ 2 +
            finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (torusGhostExceptionalTrace d N hN) := by
      linarith

end

end Percolation
