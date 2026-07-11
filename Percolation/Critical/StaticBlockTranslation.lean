import Percolation.Critical.StaticBlocks
import Percolation.Critical.Translation
import Percolation.Critical.BoxFaces

/-!
# Translation equivariance of static finite boxes

The canonical largest-cluster tie-break in Chapter 7 was designed using coordinates relative to
the box centre.  This file proves that design invariant: translating the configuration and box
transports every component key, hence transports the selected largest component and the complete
`ε`-good predicate.  It is the deterministic core of stationarity (7.60).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private theorem finset_min'_eq_of_eq {α : Type*} [LinearOrder α]
    {s t : Finset α} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst t
  rfl

theorem cubicTranslate_mem_metricBox_iff {d n : ℕ} (x y z : Cubic d) :
    cubicTranslate x y z ∈ cubicMetricBox d y n ↔ z ∈ cubicMetricBox d x n := by
  rw [mem_cubicMetricBox_iff_lInfDist_le, mem_cubicMetricBox_iff_lInfDist_le]
  have h := cubicLInfDist_translate x y x z
  have h' : cubicLInfDist y (cubicTranslate x y z) = cubicLInfDist x z := by
    simpa [cubicTranslate] using h
  rw [h']

/-- Translation between the vertex subtypes of equal-radius boxes. -/
def finiteBoxTranslationEquiv {d : ℕ} (x y : Cubic d) (n : ℕ) :
    {z : Cubic d // z ∈ cubicMetricBox d x n} ≃
      {z : Cubic d // z ∈ cubicMetricBox d y n} where
  toFun z := ⟨cubicTranslate x y z.1,
    (cubicTranslate_mem_metricBox_iff x y z.1).mpr z.2⟩
  invFun z := ⟨cubicTranslate y x z.1,
    (cubicTranslate_mem_metricBox_iff y x z.1).mpr z.2⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    simp [cubicTranslate]
    ring
  right_inv z := by
    apply Subtype.ext
    funext i
    simp [cubicTranslate]
    ring

@[simp]
theorem finiteBoxTranslationEquiv_apply {d : ℕ} (x y : Cubic d) (n : ℕ)
    (z : {q : Cubic d // q ∈ cubicMetricBox d x n}) :
    (finiteBoxTranslationEquiv x y n z).1 = cubicTranslate x y z.1 := rfl

/-- Translation is an isomorphism between the corresponding finite open box graphs. -/
def finiteBoxOpenGraphTranslationIso {d : ℕ} (x y : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) :
    finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n ≃g
      finiteBoxOpenGraph d ω y n where
  toEquiv := finiteBoxTranslationEquiv x y n
  map_rel_iff' := by
    intro u v
    change (cubicOpenGraph d ω).Adj (cubicTranslate x y u.1) (cubicTranslate x y v.1) ↔
      (cubicOpenGraph d (cubicTranslationConfigurationPullback x y ω)).Adj u.1 v.1
    rw [cubicOpenGraph_adj, cubicOpenGraph_adj]
    constructor
    · rintro ⟨huv, hopen⟩
      have huv' : (cubicGraph d).Adj u.1 v.1 :=
        (cubicTranslationIso x y).map_rel_iff.mp huv
      refine ⟨huv', ?_⟩
      let e : CubicEdge d := ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr huv'⟩
      let e' : CubicEdge d :=
        ⟨s(cubicTranslate x y u.1, cubicTranslate x y v.1),
          (cubicGraph d).mem_edgeSet.mpr huv⟩
      have hemap : (cubicTranslationIso x y).mapEdgeSet e = e' := by
        apply Subtype.ext
        simp [e, e', SimpleGraph.Iso.mapEdgeSet]
      change (cubicTranslationIso x y).mapEdgeSet e ∈ ω
      simpa [hemap] using hopen
    · rintro ⟨huv, hopen⟩
      have huv' : (cubicGraph d).Adj (cubicTranslate x y u.1)
          (cubicTranslate x y v.1) :=
        (cubicTranslationIso x y).map_rel_iff.mpr huv
      refine ⟨huv', ?_⟩
      let e : CubicEdge d := ⟨s(u.1, v.1), (cubicGraph d).mem_edgeSet.mpr huv⟩
      let e' : CubicEdge d :=
        ⟨s(cubicTranslate x y u.1, cubicTranslate x y v.1),
          (cubicGraph d).mem_edgeSet.mpr huv'⟩
      have hemap : (cubicTranslationIso x y).mapEdgeSet e = e' := by
        apply Subtype.ext
        simp [e, e', SimpleGraph.Iso.mapEdgeSet]
      change (cubicTranslationIso x y).mapEdgeSet e ∈ ω at hopen
      simpa [hemap] using hopen

@[simp]
theorem boxRelativeVertex_translate {d : ℕ} (x y z : Cubic d) :
    boxRelativeVertex y (cubicTranslate x y z) = boxRelativeVertex x z := by
  apply ofLex.injective
  funext i
  simp [boxRelativeVertex, cubicTranslate]
  ring

theorem finiteBoxGraphComponentVertices_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentVertices
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) =
      (finiteBoxGraphComponentVertices C).image (cubicTranslate x y) := by
  classical
  let φ := finiteBoxOpenGraphTranslationIso x y n ω
  have hsupp (u : {z : Cubic d // z ∈ cubicMetricBox d x n}) :
      φ u ∈ (φ.connectedComponentEquiv C).supp ↔ u ∈ C.supp := by
    rw [(φ.connectedComponentEquiv C).mem_supp_iff, C.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
  ext z
  constructor
  · intro hz
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter] at hz
    obtain ⟨hzBox, hzProof, hzSupp⟩ := hz
    let zT : {q : Cubic d // q ∈ cubicMetricBox d y n} := ⟨z, hzProof⟩
    let uT : {q : Cubic d // q ∈ cubicMetricBox d x n} := φ.symm zT
    have huSupp : uT ∈ C.supp := by
      apply (hsupp uT).mp
      simpa [uT, zT, φ] using hzSupp
    have huVertices : uT.1 ∈ finiteBoxGraphComponentVertices C := by
      rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
      exact ⟨uT.2, uT.2, huSupp⟩
    rw [Finset.mem_image]
    refine ⟨uT.1, huVertices, ?_⟩
    have happly : φ uT = zT := φ.apply_symm_apply zT
    exact congrArg Subtype.val happly
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨u, huVertices, huz⟩ := hz
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter] at huVertices
    obtain ⟨huBox, huProof, huSupp⟩ := huVertices
    let uT : {q : Cubic d // q ∈ cubicMetricBox d x n} := ⟨u, huProof⟩
    have hmapSupp : φ uT ∈ (φ.connectedComponentEquiv C).supp := (hsupp uT).mpr huSupp
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
    have hzBox : z ∈ cubicMetricBox d y n := by
      rw [← huz]
      exact (cubicTranslate_mem_metricBox_iff x y u).mpr huProof
    refine ⟨hzBox, hzBox, ?_⟩
    have hval : (φ uT).1 = z := by simpa [φ, uT] using huz
    have hzSub : (⟨z, hzBox⟩ : {q : Cubic d // q ∈ cubicMetricBox d y n}) = φ uT :=
      Subtype.ext hval.symm
    exact hzSub.symm ▸ hmapSupp

theorem finiteBoxGraphComponentCard_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentCard
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) =
      finiteBoxGraphComponentCard C := by
  rw [finiteBoxGraphComponentCard, finiteBoxGraphComponentCard,
    finiteBoxGraphComponentVertices_map_translation]
  exact Finset.card_image_of_injective _ (cubicTranslate_injective x y)

theorem finiteBoxGraphComponentDiameter_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentDiameter
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) =
      finiteBoxGraphComponentDiameter C := by
  let D := (finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C
  have hverts : finiteBoxGraphComponentVertices D =
      (finiteBoxGraphComponentVertices C).image (cubicTranslate x y) :=
    finiteBoxGraphComponentVertices_map_translation x y n ω C
  apply Nat.le_antisymm
  · rw [finiteBoxGraphComponentDiameter]
    apply Finset.sup_le
    intro u hu
    apply Finset.sup_le
    intro v hv
    rw [hverts] at hu hv
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hv
    rw [cubicLInfDist_translate]
    have hinner : cubicLInfDist u₀ v₀ ≤
        (finiteBoxGraphComponentVertices C).sup (fun w ↦ cubicLInfDist u₀ w) :=
      Finset.le_sup hv₀
    have houter : (finiteBoxGraphComponentVertices C).sup (fun w ↦ cubicLInfDist u₀ w) ≤
      (finiteBoxGraphComponentVertices C).sup (fun z ↦
          (finiteBoxGraphComponentVertices C).sup fun w ↦ cubicLInfDist z w) :=
      Finset.le_sup (f := fun z ↦
        (finiteBoxGraphComponentVertices C).sup fun w ↦ cubicLInfDist z w) hu₀
    exact hinner.trans houter
  · rw [finiteBoxGraphComponentDiameter]
    apply Finset.sup_le
    intro u hu
    apply Finset.sup_le
    intro v hv
    have htu : cubicTranslate x y u ∈ finiteBoxGraphComponentVertices D := by
      rw [hverts]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have htv : cubicTranslate x y v ∈ finiteBoxGraphComponentVertices D := by
      rw [hverts]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    rw [← cubicLInfDist_translate x y u v]
    have hinner : cubicLInfDist (cubicTranslate x y u) (cubicTranslate x y v) ≤
        (finiteBoxGraphComponentVertices D).sup
          (fun w ↦ cubicLInfDist (cubicTranslate x y u) w) := Finset.le_sup htv
    have houter : (finiteBoxGraphComponentVertices D).sup
          (fun w ↦ cubicLInfDist (cubicTranslate x y u) w) ≤
        (finiteBoxGraphComponentVertices D).sup (fun z ↦
          (finiteBoxGraphComponentVertices D).sup fun w ↦ cubicLInfDist z w) :=
      Finset.le_sup (f := fun z ↦
        (finiteBoxGraphComponentVertices D).sup fun w ↦ cubicLInfDist z w) htu
    exact hinner.trans houter

theorem finiteBoxGraphComponentCrossesDirection_map_translation_iff {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent)
    (i : Fin d) :
    finiteBoxGraphComponentCrossesDirection
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) i ↔
      finiteBoxGraphComponentCrossesDirection C i := by
  let D := (finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C
  have hverts : finiteBoxGraphComponentVertices D =
      (finiteBoxGraphComponentVertices C).image (cubicTranslate x y) :=
    finiteBoxGraphComponentVertices_map_translation x y n ω C
  constructor
  · rintro ⟨⟨u, huD, huF⟩, ⟨v, hvD, hvF⟩⟩
    rw [hverts] at huD hvD
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp huD
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hvD
    exact ⟨⟨u₀, hu₀, (cubicTranslate_mem_boxFace_iff x y u₀ i false).mp huF⟩,
      ⟨v₀, hv₀, (cubicTranslate_mem_boxFace_iff x y v₀ i true).mp hvF⟩⟩
  · rintro ⟨⟨u, huC, huF⟩, ⟨v, hvC, hvF⟩⟩
    refine ⟨⟨cubicTranslate x y u, ?_,
      (cubicTranslate_mem_boxFace_iff x y u i false).mpr huF⟩,
      ⟨cubicTranslate x y v, ?_,
        (cubicTranslate_mem_boxFace_iff x y v i true).mpr hvF⟩⟩
    · rw [hverts]
      exact Finset.mem_image.mpr ⟨u, huC, rfl⟩
    · rw [hverts]
      exact Finset.mem_image.mpr ⟨v, hvC, rfl⟩

theorem finiteBoxGraphComponentIsCrossing_map_translation_iff {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentIsCrossing
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) ↔
      finiteBoxGraphComponentIsCrossing C := by
  constructor <;> intro h i
  · exact (finiteBoxGraphComponentCrossesDirection_map_translation_iff x y n ω C i).mp (h i)
  · exact (finiteBoxGraphComponentCrossesDirection_map_translation_iff x y n ω C i).mpr (h i)

theorem finiteBoxGraphComponentAnchor_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentAnchor
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) =
      finiteBoxGraphComponentAnchor C := by
  let D := (finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C
  have hverts : finiteBoxGraphComponentVertices D =
      (finiteBoxGraphComponentVertices C).image (cubicTranslate x y) :=
    finiteBoxGraphComponentVertices_map_translation x y n ω C
  have himage : (finiteBoxGraphComponentVertices D).image (boxRelativeVertex y) =
      (finiteBoxGraphComponentVertices C).image (boxRelativeVertex x) := by
    rw [hverts, Finset.image_image]
    apply Finset.image_congr
    intro z hz
    exact boxRelativeVertex_translate x y z
  unfold finiteBoxGraphComponentAnchor
  dsimp only
  exact finset_min'_eq_of_eq himage _ _

theorem finiteBoxGraphComponentKey_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d)
    (C : (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n).ConnectedComponent) :
    finiteBoxGraphComponentKey
        ((finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv C) =
      finiteBoxGraphComponentKey C := by
  unfold finiteBoxGraphComponentKey
  rw [finiteBoxGraphComponentCard_map_translation,
    finiteBoxGraphComponentAnchor_map_translation]

/-- The canonical largest component commutes with translation. -/
theorem boxLargestCluster_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d) :
    (finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv
        (boxLargestCluster d (cubicTranslationConfigurationPullback x y ω) x n) =
      boxLargestCluster d ω y n := by
  let φ := finiteBoxOpenGraphTranslationIso x y n ω
  let M := boxLargestCluster d (cubicTranslationConfigurationPullback x y ω) x n
  let N := boxLargestCluster d ω y n
  let D := φ.connectedComponentEquiv M
  let C := φ.connectedComponentEquiv.symm N
  have hDkey : finiteBoxGraphComponentKey D = finiteBoxGraphComponentKey M := by
    exact finiteBoxGraphComponentKey_map_translation x y n ω M
  have hNkey : finiteBoxGraphComponentKey N = finiteBoxGraphComponentKey C := by
    have h := finiteBoxGraphComponentKey_map_translation x y n ω C
    simpa [φ, C] using h
  have hDN : finiteBoxGraphComponentKey D ≤ finiteBoxGraphComponentKey N :=
    boxComponentKey_le_largest d ω y n D
  have hNMsource : finiteBoxGraphComponentKey C ≤ finiteBoxGraphComponentKey M :=
    boxComponentKey_le_largest d
      (cubicTranslationConfigurationPullback x y ω) x n C
  have hND : finiteBoxGraphComponentKey N ≤ finiteBoxGraphComponentKey D := by
    rw [hNkey, hDkey]
    exact hNMsource
  have hkey : finiteBoxGraphComponentKey D = finiteBoxGraphComponentKey N :=
    le_antisymm hDN hND
  exact boxComponentKey_injective hkey

theorem finiteBoxGraphLargestComponent_map_translation {d : ℕ}
    (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d) :
    (finiteBoxOpenGraphTranslationIso x y n ω).connectedComponentEquiv
        (finiteBoxGraphLargestComponent x n
          (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n)) =
      finiteBoxGraphLargestComponent y n (finiteBoxOpenGraph d ω y n) := by
  let φ := finiteBoxOpenGraphTranslationIso x y n ω
  let M := finiteBoxGraphLargestComponent x n
    (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n)
  let N := finiteBoxGraphLargestComponent y n (finiteBoxOpenGraph d ω y n)
  let D := φ.connectedComponentEquiv M
  let C := φ.connectedComponentEquiv.symm N
  have hDkey : finiteBoxGraphComponentKey D = finiteBoxGraphComponentKey M :=
    finiteBoxGraphComponentKey_map_translation x y n ω M
  have hNkey : finiteBoxGraphComponentKey N = finiteBoxGraphComponentKey C := by
    have h := finiteBoxGraphComponentKey_map_translation x y n ω C
    simpa [φ, C] using h
  have hDN : finiteBoxGraphComponentKey D ≤ finiteBoxGraphComponentKey N :=
    finiteBoxGraphComponentKey_le_largest y n (finiteBoxOpenGraph d ω y n) D
  have hCM : finiteBoxGraphComponentKey C ≤ finiteBoxGraphComponentKey M :=
    finiteBoxGraphComponentKey_le_largest x n
      (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n) C
  have hND : finiteBoxGraphComponentKey N ≤ finiteBoxGraphComponentKey D := by
    rw [hNkey, hDkey]
    exact hCM
  exact finiteBoxGraphComponentKey_injective (le_antisymm hDN hND)

set_option maxHeartbeats 800000 in
theorem finiteBoxGraph_isEpsilonGood_translation_iff {d : ℕ}
    (p : I) (ε : ℝ) (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d) :
    FiniteBoxGraph.IsEpsilonGood p ε x n
        (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n) ↔
      FiniteBoxGraph.IsEpsilonGood p ε y n (finiteBoxOpenGraph d ω y n) := by
  let φ := finiteBoxOpenGraphTranslationIso x y n ω
  let M := finiteBoxGraphLargestComponent x n
    (finiteBoxOpenGraph d (cubicTranslationConfigurationPullback x y ω) x n)
  let N := finiteBoxGraphLargestComponent y n (finiteBoxOpenGraph d ω y n)
  have hMN : φ.connectedComponentEquiv M = N :=
    finiteBoxGraphLargestComponent_map_translation x y n ω
  have hboxcard : (cubicMetricBox d x n).card = (cubicMetricBox d y n).card := by
    rw [cubicMetricBox_card, cubicMetricBox_card]
  constructor
  · rintro ⟨hcross, hunique, hsize⟩
    change finiteBoxGraphComponentIsCrossing M at hcross
    change (∀ C, n ≤ finiteBoxGraphComponentDiameter C → C = M) at hunique
    change (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤
      finiteBoxGraphComponentCard M at hsize
    change finiteBoxGraphComponentIsCrossing N ∧
      (∀ D, n ≤ finiteBoxGraphComponentDiameter D → D = N) ∧
      (1 - ε) * theta d p * (cubicMetricBox d y n).card ≤
        finiteBoxGraphComponentCard N
    refine ⟨?_, ?_, ?_⟩
    · have hmapCross :=
        (finiteBoxGraphComponentIsCrossing_map_translation_iff x y n ω M).mpr hcross
      rw [hMN] at hmapCross
      exact hmapCross
    · intro D hnD
      let C := φ.connectedComponentEquiv.symm D
      have hmap : φ.connectedComponentEquiv C = D :=
        φ.connectedComponentEquiv.apply_symm_apply D
      have hdiamEq := finiteBoxGraphComponentDiameter_map_translation x y n ω C
      rw [hmap] at hdiamEq
      have hdiam : n ≤ finiteBoxGraphComponentDiameter C := by
        rw [← hdiamEq]
        exact hnD
      have hCM : C = M := hunique C hdiam
      exact hmap.symm.trans ((congrArg φ.connectedComponentEquiv hCM).trans hMN)
    · have hcard := finiteBoxGraphComponentCard_map_translation x y n ω M
      rw [hMN] at hcard
      calc
        (1 - ε) * theta d p * (cubicMetricBox d y n).card =
            (1 - ε) * theta d p * (cubicMetricBox d x n).card := by rw [hboxcard]
        _ ≤ finiteBoxGraphComponentCard M := hsize
        _ = finiteBoxGraphComponentCard N := by exact_mod_cast hcard.symm
  · rintro ⟨hcross, hunique, hsize⟩
    change finiteBoxGraphComponentIsCrossing N at hcross
    change (∀ D, n ≤ finiteBoxGraphComponentDiameter D → D = N) at hunique
    change (1 - ε) * theta d p * (cubicMetricBox d y n).card ≤
      finiteBoxGraphComponentCard N at hsize
    change finiteBoxGraphComponentIsCrossing M ∧
      (∀ C, n ≤ finiteBoxGraphComponentDiameter C → C = M) ∧
      (1 - ε) * theta d p * (cubicMetricBox d x n).card ≤
        finiteBoxGraphComponentCard M
    refine ⟨?_, ?_, ?_⟩
    · apply (finiteBoxGraphComponentIsCrossing_map_translation_iff x y n ω M).mp
      rw [hMN]
      exact hcross
    · intro C hnC
      let D := φ.connectedComponentEquiv C
      have hdiamEq := finiteBoxGraphComponentDiameter_map_translation x y n ω C
      have hdiam : n ≤ finiteBoxGraphComponentDiameter D := by
        rw [hdiamEq]
        exact hnC
      have hDN : D = N := hunique D hdiam
      apply φ.connectedComponentEquiv.injective
      exact hDN.trans hMN.symm
    · have hcard := finiteBoxGraphComponentCard_map_translation x y n ω M
      rw [hMN] at hcard
      calc
        (1 - ε) * theta d p * (cubicMetricBox d x n).card =
            (1 - ε) * theta d p * (cubicMetricBox d y n).card := by rw [hboxcard]
        _ ≤ finiteBoxGraphComponentCard N := hsize
        _ = finiteBoxGraphComponentCard M := by exact_mod_cast hcard

theorem cubicTranslationConfigurationPullback_mem_epsilonGoodBoxEvent_iff
    {d : ℕ} (p : I) (ε : ℝ) (x y : Cubic d) (n : ℕ) (ω : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback x y ω ∈ epsilonGoodBoxEvent d p ε x n ↔
      ω ∈ epsilonGoodBoxEvent d p ε y n :=
  finiteBoxGraph_isEpsilonGood_translation_iff p ε x y n ω

/-- The probability that a box is `ε`-good is independent of its centre. -/
theorem bernoulliBondMeasure_real_epsilonGoodBoxEvent_eq {d : ℕ}
    (p : I) (ε : ℝ) (x y : Cubic d) (n : ℕ) :
    (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε x n) =
      (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε y n) := by
  let T := cubicTranslationConfigurationPullback x y
  have hpre : T ⁻¹' epsilonGoodBoxEvent d p ε x n =
      epsilonGoodBoxEvent d p ε y n := by
    ext ω
    exact cubicTranslationConfigurationPullback_mem_epsilonGoodBoxEvent_iff p ε x y n ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ.real (epsilonGoodBoxEvent d p ε x n))
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p x y)
  change (Measure.map (cubicTranslationConfigurationPullback x y)
      (bernoulliBondMeasure d p)).real (epsilonGoodBoxEvent d p ε x n) =
    (bernoulliBondMeasure d p).real (epsilonGoodBoxEvent d p ε x n) at hmap
  rw [MeasureTheory.map_measureReal_apply
    (measurable_cubicTranslationConfigurationPullback x y)
    (measurableSet_epsilonGoodBoxEvent d p ε x n), hpre] at hmap
  exact hmap.symm

theorem epsilonGoodBlockLaw_real_mem_eq_origin
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x : Cubic d) :
    (epsilonGoodBlockLaw d p ε n).real {η : Set (Cubic d) | x ∈ η} =
      (epsilonGoodBlockLaw d p ε n).real {η : Set (Cubic d) | cubicOrigin ∈ η} := by
  rw [epsilonGoodBlockLaw_real_mem, epsilonGoodBlockLaw_real_mem]
  exact bernoulliBondMeasure_real_epsilonGoodBoxEvent_eq p ε
    (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n cubicOrigin) n

/-- Pull a site configuration back along a cubic translation. -/
def cubicSiteTranslationPullback {d : ℕ} (x y : Cubic d) (η : Set (Cubic d)) :
    Set (Cubic d) :=
  (cubicTranslationEquiv x y).toEmbedding ⁻¹' η

theorem measurable_cubicSiteTranslationPullback {d : ℕ} (x y : Cubic d) :
    Measurable (cubicSiteTranslationPullback x y) :=
  measurable_preimage_embedding (cubicTranslationEquiv x y).toEmbedding

@[simp]
theorem mem_cubicSiteTranslationPullback {d : ℕ} (x y z : Cubic d)
    (η : Set (Cubic d)) :
    z ∈ cubicSiteTranslationPullback x y η ↔ cubicTranslate x y z ∈ η := Iff.rfl

theorem epsilonGoodBlockCenter_translate {d : ℕ} (n : ℕ) (x y z : Cubic d) :
    epsilonGoodBlockCenter n (cubicTranslate x y z) =
      cubicTranslate (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y)
        (epsilonGoodBlockCenter n z) := by
  funext i
  simp [epsilonGoodBlockCenter, cubicScale, cubicTranslate]
  ring

theorem cubicTranslationIso_epsilonGoodBlockCenter {d : ℕ}
    (n : ℕ) (x y z : Cubic d) :
    cubicTranslationIso (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y) =
      cubicTranslationIso (epsilonGoodBlockCenter n z)
        (epsilonGoodBlockCenter n (cubicTranslate x y z)) := by
  ext u i
  simp [cubicTranslationIso_apply, epsilonGoodBlockCenter_translate, cubicTranslate]

theorem cubicTranslationConfigurationPullback_epsilonGoodBlockCenter {d : ℕ}
    (n : ℕ) (x y z : Cubic d) (ω : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback
        (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y) ω =
      cubicTranslationConfigurationPullback
        (epsilonGoodBlockCenter n z)
          (epsilonGoodBlockCenter n (cubicTranslate x y z)) ω := by
  rw [cubicTranslationConfigurationPullback, cubicTranslationConfigurationPullback,
    cubicTranslationIso_epsilonGoodBlockCenter n x y z]

theorem epsilonGoodBlockField_translation_covariant
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x y : Cubic d)
    (ω : EdgeConfiguration d) :
    epsilonGoodBlockField d p ε n
        (cubicTranslationConfigurationPullback
          (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y) ω) =
      cubicSiteTranslationPullback x y (epsilonGoodBlockField d p ε n ω) := by
  ext z
  change cubicTranslationConfigurationPullback
      (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y) ω ∈
        epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n z) n ↔
    ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n (cubicTranslate x y z)) n
  rw [cubicTranslationConfigurationPullback_epsilonGoodBlockCenter n x y z]
  exact cubicTranslationConfigurationPullback_mem_epsilonGoodBoxEvent_iff p ε
    (epsilonGoodBlockCenter n z)
    (epsilonGoodBlockCenter n (cubicTranslate x y z)) n ω

/-- Full translation stationarity of the static good-block field, equation (7.60). -/
theorem epsilonGoodBlockLaw_map_cubicSiteTranslationPullback
    (d : ℕ) (p : I) (ε : ℝ) (n : ℕ) (x y : Cubic d) :
    (epsilonGoodBlockLaw d p ε n).map (cubicSiteTranslationPullback x y) =
      epsilonGoodBlockLaw d p ε n := by
  let Tbond := cubicTranslationConfigurationPullback
    (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y)
  let Tsite := cubicSiteTranslationPullback x y
  let X := epsilonGoodBlockField d p ε n
  have hcov : Tsite ∘ X = X ∘ Tbond := by
    funext ω
    exact (epsilonGoodBlockField_translation_covariant d p ε n x y ω).symm
  rw [epsilonGoodBlockLaw]
  calc
    Measure.map Tsite (Measure.map X (bernoulliBondMeasure d p)) =
        Measure.map (Tsite ∘ X) (bernoulliBondMeasure d p) :=
      Measure.map_map (measurable_cubicSiteTranslationPullback x y)
        (measurable_epsilonGoodBlockField d p ε n)
    _ = Measure.map (X ∘ Tbond) (bernoulliBondMeasure d p) :=
      congrArg (fun f ↦ Measure.map f (bernoulliBondMeasure d p)) hcov
    _ = Measure.map X (Measure.map Tbond (bernoulliBondMeasure d p)) :=
      (Measure.map_map (measurable_epsilonGoodBlockField d p ε n)
        (measurable_cubicTranslationConfigurationPullback
          (epsilonGoodBlockCenter n x) (epsilonGoodBlockCenter n y))).symm
    _ = Measure.map X (bernoulliBondMeasure d p) := by
      rw [bernoulliBondMeasure_map_cubicTranslationConfigurationPullback]

end Percolation
