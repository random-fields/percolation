import Percolation.Critical.LSSGoodBlocks
import Percolation.Critical.StaticBlockPath
import Percolation.Planar.SiteCrossingPeierls

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

/-! ### Translated planar slices

The source proof of (7.74) uses many parallel planar slices.  We retain the translation in the
definition, rather than identifying every slice with the origin slice: the translated supports
are later used to prove literal disjointness of the underlying bond coordinates.
-/

/-- The embedding of the first two coordinates through a prescribed coarse-lattice offset. -/
def cubicTranslatedFirstTwoEmbedding {d : ℕ} (hd : 2 ≤ d) (z : Cubic d) :
    SquareVertex ↪ Cubic d where
  toFun x := cubicTranslate cubicOrigin z (cubicEmbed 2 d x)
  inj' := (cubicTranslate_injective cubicOrigin z).comp (cubicEmbed_injective hd)

/-- The translated first-two-coordinate embedding as a graph homomorphism. -/
def cubicTranslatedFirstTwoHom {d : ℕ} (hd : 2 ≤ d) (z : Cubic d) :
    squareGraph →g cubicGraph d :=
  (cubicTranslationIso cubicOrigin z).toHom.comp (cubicEmbedHom hd)

@[simp]
theorem cubicTranslatedFirstTwoEmbedding_apply {d : ℕ} (hd : 2 ≤ d)
    (z : Cubic d) (x : SquareVertex) :
    cubicTranslatedFirstTwoEmbedding hd z x =
      cubicTranslate cubicOrigin z (cubicEmbed 2 d x) := rfl

@[simp]
theorem cubicTranslatedFirstTwoHom_apply {d : ℕ} (hd : 2 ≤ d)
    (z : Cubic d) (x : SquareVertex) :
    cubicTranslatedFirstTwoHom hd z x = cubicTranslatedFirstTwoEmbedding hd z x := rfl

/-- Restrict a coarse-site configuration to the planar slice translated by `z`. -/
def cubicTranslatedFirstTwoSiteRestriction {d : ℕ} (hd : 2 ≤ d) (z : Cubic d)
    (η : Set (Cubic d)) : Set SquareVertex :=
  (cubicTranslatedFirstTwoEmbedding hd z) ⁻¹' η

theorem measurable_cubicTranslatedFirstTwoSiteRestriction {d : ℕ} (hd : 2 ≤ d)
    (z : Cubic d) :
    Measurable (cubicTranslatedFirstTwoSiteRestriction hd z :
      Set (Cubic d) → Set SquareVertex) := by
  change Measurable
    ((fun P : SquareVertex → Prop ↦ {x | P x}) ∘
      fun (η : Set (Cubic d)) (x : SquareVertex) ↦
        ((cubicTranslatedFirstTwoEmbedding hd z x ∈ η) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun x ↦
    (measurableSet_mem (cubicTranslatedFirstTwoEmbedding hd z x)).mem

/-- A left-right site crossing in a translated copy of the planar coarse-lattice slice. -/
def epsilonGoodBlockTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (z : Cubic d) (m n : ℕ) : Set (Set (Cubic d)) :=
  cubicTranslatedFirstTwoSiteRestriction hd z ⁻¹' siteSquareRectangleCrossingEvent m n

/-- Coarse sites queried by a translated planar crossing. -/
noncomputable def epsilonGoodBlockTranslatedSliceCrossingSupport
    (d : ℕ) (hd : 2 ≤ d) (z : Cubic d) (m n : ℕ) : Finset (Cubic d) :=
  (squareRectangleVertices m n).map (cubicTranslatedFirstTwoEmbedding hd z)

theorem dependsOn_epsilonGoodBlockTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (z : Cubic d) (m n : ℕ) :
    DependsOn (epsilonGoodBlockTranslatedSliceCrossingSupport d hd z m n)
      (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n) := by
  intro η ξ hagree
  apply dependsOn_siteSquareRectangleCrossingEvent m n
  intro x hx
  apply hagree
  rw [epsilonGoodBlockTranslatedSliceCrossingSupport, Finset.mem_map]
  exact ⟨x, hx, rfl⟩

theorem measurableSet_epsilonGoodBlockTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (z : Cubic d) (m n : ℕ) :
    MeasurableSet (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n) :=
  (dependsOn_epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n).measurableSet

theorem isIncreasingEvent_epsilonGoodBlockTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (z : Cubic d) (m n : ℕ) :
    IsIncreasingEvent (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n) := by
  intro η ξ hηξ hη
  exact isIncreasingEvent_siteSquareRectangleCrossingEvent m n
    (fun x hx ↦ hηξ hx) hη

/-- The iid law sees every translated planar slice with the same crossing probability. -/
theorem setBernoulli_real_epsilonGoodBlockTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (q : I) (z : Cubic d) (m n : ℕ) :
    setBer((Set.univ : Set (Cubic d)), q).real
        (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n) =
      setBer((Set.univ : Set SquareVertex), q).real
        (siteSquareRectangleCrossingEvent m n) := by
  let f : SquareVertex ↪ Cubic d := cubicTranslatedFirstTwoEmbedding hd z
  have hmap := setBernoulli_map_preimage_univ f q
  have hfun : (fun s : Set (Cubic d) ↦ f ⁻¹' s) =
      cubicTranslatedFirstTwoSiteRestriction hd z := rfl
  rw [hfun] at hmap
  rw [epsilonGoodBlockTranslatedSliceCrossingEvent, ← hmap, map_measureReal_apply
    (measurable_cubicTranslatedFirstTwoSiteRestriction hd z)
    (measurableSet_siteSquareRectangleCrossingEvent m n)]

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

/-- Equation (7.73): once LSS supplies a dominating iid density above the planar Peierls
threshold, an `ε`-good coarse-site square crossing has exponentially small failure probability. -/
theorem epsilonGoodBlockSliceCrossing_probability_ge_one_sub_exp
    (d : ℕ) (hd : 2 ≤ d) (p q : I) (ε : ℝ)
    (blockScale K : ℕ) (hblockScale : 1 ≤ blockScale) (hK : 1 ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε blockScale).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    1 - Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) ≤
      (epsilonGoodBlockLaw d p ε blockScale).real
        (epsilonGoodBlockSliceCrossingEvent d hd (2 * K) K) := by
  calc
    1 - Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) ≤
        siteSquareRectangleCrossingProbability q (2 * K) K :=
      siteSquareCrossingProbability_ge_one_sub_exp q hqThreshold K hK
    _ ≤ (epsilonGoodBlockLaw d p ε blockScale).real
        (epsilonGoodBlockSliceCrossingEvent d hd (2 * K) K) :=
      siteCrossingProbability_le_epsilonGoodBlockSliceCrossing
        d hd p q ε blockScale (2 * K) K hblockScale hq hmarginal

/-! ### The translated events on the underlying bond space -/

/-- The underlying bond event that the translated coarse slice has a good-block crossing. -/
def epsilonGoodBondTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (p : I) (ε : ℝ) (blockScale : ℕ)
    (z : Cubic d) (m n : ℕ) : Set (EdgeConfiguration d) :=
  epsilonGoodBlockField d p ε blockScale ⁻¹'
    epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n

/-- Every bond coordinate queried by a translated coarse-slice crossing. -/
noncomputable def epsilonGoodBondTranslatedSliceCrossingSupport
    (d : ℕ) (hd : 2 ≤ d) (blockScale : ℕ)
    (z : Cubic d) (m n : ℕ) : Finset (CubicEdge d) :=
  (epsilonGoodBlockTranslatedSliceCrossingSupport d hd z m n).biUnion fun x ↦
    cubicBoxEdges d (epsilonGoodBlockCenter blockScale x) blockScale

theorem dependsOn_epsilonGoodBondTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (p : I) (ε : ℝ) (blockScale : ℕ)
    (z : Cubic d) (m n : ℕ) :
    DependsOn (epsilonGoodBondTranslatedSliceCrossingSupport
      d hd blockScale z m n)
      (epsilonGoodBondTranslatedSliceCrossingEvent
        d hd p ε blockScale z m n) := by
  intro ω η hagree
  apply dependsOn_epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n
  intro x hx
  apply dependsOn_epsilonGoodBoxEvent d p ε
    (epsilonGoodBlockCenter blockScale x) blockScale
  intro e he
  apply hagree e
  rw [epsilonGoodBondTranslatedSliceCrossingSupport, Finset.mem_biUnion]
  exact ⟨x, hx, he⟩

theorem measurableSet_epsilonGoodBondTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (p : I) (ε : ℝ) (blockScale : ℕ)
    (z : Cubic d) (m n : ℕ) :
    MeasurableSet (epsilonGoodBondTranslatedSliceCrossingEvent
      d hd p ε blockScale z m n) :=
  (dependsOn_epsilonGoodBondTranslatedSliceCrossingEvent
    d hd p ε blockScale z m n).measurableSet

/-- Events supported on pairwise-disjoint finite families of bond coordinates are mutually
independent under the Bernoulli bond law.  Unlike the special open-edge version used for seeds,
this applies to arbitrary finite-cylinder events and is the independence mechanism in (7.74). -/
theorem bernoulliBondMeasure_iIndepSet_of_pairwiseDisjoint_dependsOn
    {d : ℕ} {κ : Type*} [DecidableEq κ]
    (p : I) (support : κ → Finset (CubicEdge d))
    (A : κ → Set (EdgeConfiguration d))
    (hdep : ∀ k, DependsOn (support k) (A k))
    (hpair : Set.PairwiseDisjoint (Set.univ : Set κ) support) :
    iIndepSet A (bernoulliBondMeasure d p) := by
  classical
  apply (iIndepSet_iff_meas_biInter (fun k ↦ (hdep k).measurableSet)).2
  intro J
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      have hdisj : Disjoint (support a : Set (CubicEdge d))
          (J.biUnion support : Set (CubicEdge d)) := by
        rw [Set.disjoint_left]
        intro e hea heJ
        rw [Finset.coe_biUnion] at heJ
        obtain ⟨b, hbJ, heb⟩ := Set.mem_iUnion₂.mp heJ
        exact Finset.disjoint_left.mp
          (hpair (Set.mem_univ a) (Set.mem_univ b)
            (fun hab ↦ ha (hab ▸ hbJ))) hea heb
      have hind := indep_generateFrom_coordinateEvents p hdisj
      have hAa : MeasurableSet[
          MeasurableSpace.generateFrom (coordinateEvents (support a : Set (CubicEdge d)))]
          (A a) :=
        (hdep a).measurableSet_generateFrom_coordinateEvents (Set.Subset.rfl)
      have hAJ : MeasurableSet[
          MeasurableSpace.generateFrom
            (coordinateEvents (J.biUnion support : Set (CubicEdge d)))]
          (⋂ k ∈ J, A k) := by
        apply J.measurableSet_biInter
        intro k hk
        apply (hdep k).measurableSet_generateFrom_coordinateEvents
        intro e he
        rw [Finset.coe_biUnion]
        exact Set.mem_iUnion₂.mpr ⟨k, hk, he⟩
      have hprod :
          (bernoulliBondMeasure d p) (A a ∩ ⋂ k ∈ J, A k) =
            (bernoulliBondMeasure d p) (A a) *
              (bernoulliBondMeasure d p) (⋂ k ∈ J, A k) :=
        (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
          (hdep a).measurableSet
          (J.measurableSet_biInter fun k _hk ↦ (hdep k).measurableSet)
          (bernoulliBondMeasure d p)).mp
            (hind.indepSet_of_measurableSet hAa hAJ)
      simpa [ha, ih] using hprod

private theorem iIndepSet_compl_staticSlices
    {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : κ → Set Ω} (hA : iIndepSet A μ) :
    iIndepSet (fun k ↦ (A k)ᶜ) μ := by
  rw [iIndepSet_iff_iIndep] at hA ⊢
  have hgen : ∀ k,
      MeasurableSpace.generateFrom {(A k)ᶜ} =
        MeasurableSpace.generateFrom {A k} := by
    intro k
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      exact (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      have hc : MeasurableSet[MeasurableSpace.generateFrom {(A k)ᶜ}] ((A k)ᶜ) :=
        MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
      simpa only [compl_compl] using hc.compl
  convert hA using 1
  funext k
  exact hgen k

/-- The bond-space probability is exactly the pushforward good-block probability. -/
theorem bernoulliBondMeasure_real_epsilonGoodBondTranslatedSliceCrossingEvent
    (d : ℕ) (hd : 2 ≤ d) (p : I) (ε : ℝ) (blockScale : ℕ)
    (z : Cubic d) (m n : ℕ) :
    (bernoulliBondMeasure d p).real
        (epsilonGoodBondTranslatedSliceCrossingEvent
          d hd p ε blockScale z m n) =
      (epsilonGoodBlockLaw d p ε blockScale).real
        (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n) := by
  rw [epsilonGoodBlockLaw, map_measureReal_apply
    (measurable_epsilonGoodBlockField d p ε blockScale)
    (measurableSet_epsilonGoodBlockTranslatedSliceCrossingEvent d hd z m n)]
  rfl

/-- Translated form of (7.73), stated on the original bond configuration space. -/
theorem epsilonGoodBondTranslatedSliceCrossing_probability_ge_one_sub_exp
    (d : ℕ) (hd : 2 ≤ d) (p q : I) (ε : ℝ)
    (blockScale K : ℕ) (hblockScale : 1 ≤ blockScale) (hK : 1 ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε blockScale).real
          {η : Set (Cubic d) | cubicOrigin ∈ η})
    (z : Cubic d) :
    1 - Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) ≤
      (bernoulliBondMeasure d p).real
        (epsilonGoodBondTranslatedSliceCrossingEvent
          d hd p ε blockScale z (2 * K) K) := by
  rw [bernoulliBondMeasure_real_epsilonGoodBondTranslatedSliceCrossingEvent]
  calc
    1 - Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) ≤
        siteSquareRectangleCrossingProbability q (2 * K) K :=
      siteSquareCrossingProbability_ge_one_sub_exp q hqThreshold K hK
    _ = setBer((Set.univ : Set (Cubic d)), q).real
        (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z (2 * K) K) :=
      (setBernoulli_real_epsilonGoodBlockTranslatedSliceCrossingEvent
        d hd q z (2 * K) K).symm
    _ ≤ (epsilonGoodBlockLaw d p ε blockScale).real
        (epsilonGoodBlockTranslatedSliceCrossingEvent d hd z (2 * K) K) :=
      epsilonGoodBlockLaw_lss_finiteCylinder_measureReal_le
        d (lt_of_lt_of_le (by omega) hd) p q ε blockScale hblockScale hq hmarginal
        (dependsOn_epsilonGoodBlockTranslatedSliceCrossingEvent d hd z (2 * K) K)
        (isIncreasingEvent_epsilonGoodBlockTranslatedSliceCrossingEvent d hd z (2 * K) K)

/-! ### Disjoint translated slices -/

@[simp]
theorem cubicTranslatedFirstTwoEmbedding_apply_of_two_le
    {d : ℕ} (hd : 2 ≤ d) (z : Cubic d) (x : SquareVertex)
    (j : Fin d) (hj : 2 ≤ j.val) :
    cubicTranslatedFirstTwoEmbedding hd z x j = z j := by
  simp [cubicTranslatedFirstTwoEmbedding, cubicTranslate, cubicOrigin,
    cubicEmbed, not_lt_of_ge hj]

theorem coordinate_eq_of_mem_epsilonGoodBlockTranslatedSliceCrossingSupport
    {d : ℕ} (hd : 2 ≤ d) {z : Cubic d} {m n : ℕ} {x : Cubic d}
    (hx : x ∈ epsilonGoodBlockTranslatedSliceCrossingSupport d hd z m n)
    (j : Fin d) (hj : 2 ≤ j.val) :
    x j = z j := by
  rw [epsilonGoodBlockTranslatedSliceCrossingSupport, Finset.mem_map] at hx
  obtain ⟨u, _hu, rfl⟩ := hx
  exact cubicTranslatedFirstTwoEmbedding_apply_of_two_le hd z u j hj

/-- Two translated planar crossings query disjoint bond coordinates when their offsets differ by
at least three coarse sites in one transverse coordinate. -/
theorem disjoint_epsilonGoodBondTranslatedSliceCrossingSupport
    {d : ℕ} (hd : 2 ≤ d) {blockScale : ℕ} (hblockScale : 1 ≤ blockScale)
    {z w : Cubic d} (m n : ℕ) (j : Fin d) (hj : 2 ≤ j.val)
    (hsep : 2 < (w j - z j).natAbs) :
    Disjoint
      (epsilonGoodBondTranslatedSliceCrossingSupport d hd blockScale z m n)
      (epsilonGoodBondTranslatedSliceCrossingSupport d hd blockScale w m n) := by
  classical
  rw [Finset.disjoint_left]
  intro e hez hew
  rw [epsilonGoodBondTranslatedSliceCrossingSupport, Finset.mem_biUnion] at hez hew
  obtain ⟨x, hxSlice, hex⟩ := hez
  obtain ⟨y, hySlice, hey⟩ := hew
  have hxj : x j = z j :=
    coordinate_eq_of_mem_epsilonGoodBlockTranslatedSliceCrossingSupport hd hxSlice j hj
  have hyj : y j = w j :=
    coordinate_eq_of_mem_epsilonGoodBlockTranslatedSliceCrossingSupport hd hySlice j hj
  have hcoord :
      (epsilonGoodBlockCenter blockScale y j -
          epsilonGoodBlockCenter blockScale x j).natAbs =
        blockScale * (w j - z j).natAbs := by
    simp only [epsilonGoodBlockCenter, cubicScale]
    rw [hxj, hyj]
    rw [← mul_sub, Int.natAbs_mul]
    simp
  have hcenter :
      2 * blockScale <
        cubicLInfDist (epsilonGoodBlockCenter blockScale x)
          (epsilonGoodBlockCenter blockScale y) := by
    have hcoordLe := cubicLInfDist_coord_le
      (epsilonGoodBlockCenter blockScale x)
      (epsilonGoodBlockCenter blockScale y) j
    rw [hcoord] at hcoordLe
    simpa [mul_comm] using
      (Nat.mul_lt_mul_of_pos_left hsep hblockScale).trans_le hcoordLe
  exact Finset.disjoint_left.mp
    (disjoint_cubicBoxEdges_of_two_mul_lt_lInfDist hcenter) hex hey

/-- Pairwise separation of offsets in one transverse coordinate gives pairwise-disjoint bond
supports for the corresponding planar slice crossings. -/
theorem pairwiseDisjoint_epsilonGoodBondTranslatedSliceCrossingSupport
    {d : ℕ} (hd : 2 ≤ d) {κ : Type*} [DecidableEq κ]
    {blockScale : ℕ} (hblockScale : 1 ≤ blockScale)
    (J : Finset κ) (offset : κ → Cubic d) (m n : ℕ)
    (j : Fin d) (hj : 2 ≤ j.val)
    (hsep : ∀ a ∈ J, ∀ b ∈ J, a ≠ b →
      2 < (offset b j - offset a j).natAbs) :
    Set.PairwiseDisjoint (J : Set κ) fun a ↦
      epsilonGoodBondTranslatedSliceCrossingSupport
        d hd blockScale (offset a) m n := by
  intro a ha b hb hab
  exact disjoint_epsilonGoodBondTranslatedSliceCrossingSupport
    hd hblockScale m n j hj (hsep a ha b hb hab)

/-- Equation (7.74), before specializing the transverse index box: the probability that every
one of a finite pairwise-separated family of planar slices fails is exponentially small in the
product of the planar scale and the number of slices. -/
theorem epsilonGoodBondTranslatedSliceCrossing_all_fail_probability_le_exp
    {d : ℕ} (hd : 2 ≤ d) {κ : Type*} [DecidableEq κ]
    (p q : I) (ε : ℝ) (blockScale K : ℕ)
    (hblockScale : 1 ≤ blockScale) (hK : 1 ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε blockScale).real
          {η : Set (Cubic d) | cubicOrigin ∈ η})
    (J : Finset κ) (offset : κ → Cubic d)
    (hsupports : Set.PairwiseDisjoint (J : Set κ) fun a ↦
      epsilonGoodBondTranslatedSliceCrossingSupport
        d hd blockScale (offset a) (2 * K) K) :
    (bernoulliBondMeasure d p).real
        (⋂ k : {k : κ // k ∈ J},
          (epsilonGoodBondTranslatedSliceCrossingEvent
            d hd p ε blockScale (offset k.1) (2 * K) K)ᶜ) ≤
      Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) * (J.card : ℝ)) := by
  classical
  let success : {k : κ // k ∈ J} → Set (EdgeConfiguration d) := fun k ↦
    epsilonGoodBondTranslatedSliceCrossingEvent
      d hd p ε blockScale (offset k.1) (2 * K) K
  let support : {k : κ // k ∈ J} → Finset (CubicEdge d) := fun k ↦
    epsilonGoodBondTranslatedSliceCrossingSupport
      d hd blockScale (offset k.1) (2 * K) K
  have hpair : Set.PairwiseDisjoint
      (Set.univ : Set {k : κ // k ∈ J}) support := by
    intro a _ha b _hb hab
    exact hsupports a.2 b.2 (fun h ↦ hab (Subtype.ext h))
  have hiSuccess : iIndepSet success (bernoulliBondMeasure d p) := by
    apply bernoulliBondMeasure_iIndepSet_of_pairwiseDisjoint_dependsOn
      p support success
    · intro k
      exact dependsOn_epsilonGoodBondTranslatedSliceCrossingEvent
        d hd p ε blockScale (offset k.1) (2 * K) K
    · exact hpair
  have hiFail : iIndepSet (fun k ↦ (success k)ᶜ) (bernoulliBondMeasure d p) :=
    iIndepSet_compl_staticSlices hiSuccess
  have hmeasure := hiFail.meas_biInter
    (Finset.univ : Finset {k : κ // k ∈ J})
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_prod] at hreal
  have hfactor : ∀ k : {k : κ // k ∈ J},
      (bernoulliBondMeasure d p).real ((success k)ᶜ) ≤
        Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) := by
    intro k
    rw [probReal_compl_eq_one_sub
      (measurableSet_epsilonGoodBondTranslatedSliceCrossingEvent
        d hd p ε blockScale (offset k.1) (2 * K) K)]
    have hk := epsilonGoodBondTranslatedSliceCrossing_probability_ge_one_sub_exp
      d hd p q ε blockScale K hblockScale hK hq hqThreshold hmarginal (offset k.1)
    linarith
  calc
    (bernoulliBondMeasure d p).real
        (⋂ k : {k : κ // k ∈ J},
          (epsilonGoodBondTranslatedSliceCrossingEvent
            d hd p ε blockScale (offset k.1) (2 * K) K)ᶜ) =
        ∏ k : {k : κ // k ∈ J},
          (bernoulliBondMeasure d p).real ((success k)ᶜ) := by
      simpa [success] using hreal
    _ ≤ ∏ _k : {k : κ // k ∈ J},
        Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ)) := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun k _hk ↦ hfactor k)
    _ = Real.exp
        (-siteSquareCrossingPeierlsRate * (K : ℝ) * (J.card : ℝ)) := by
      rw [Finset.prod_const]
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [Finset.card_univ, Fintype.card_coe]
      ring

/-! ### The concrete transverse sublattice from (7.72)--(7.74) -/

/-- Multiples of three in `[-K,K]`, represented injectively by their quotient. -/
noncomputable def staticSeparatedCoordinate (K : ℕ) : Finset ℤ :=
  (Finset.Icc (-((K / 3 : ℕ) : ℤ)) ((K / 3 : ℕ) : ℤ)).image
    (fun a : ℤ ↦ 3 * a)

theorem staticSeparatedCoordinate_card (K : ℕ) :
    (staticSeparatedCoordinate K).card = 2 * (K / 3) + 1 := by
  rw [staticSeparatedCoordinate,
    Finset.card_image_of_injective _
      (mul_right_injective₀ (by norm_num : (3 : ℤ) ≠ 0)),
    Int.card_Icc]
  omega

/-- The separated transverse indices used for independent planar slices.  Requiring every
transverse coordinate to be a multiple of three is the condition that actually makes the
thickened regions pairwise disjoint. -/
noncomputable def staticTransverseSliceIndices (d K : ℕ) :
    Finset (Cubic (d - 2)) :=
  Fintype.piFinset fun _ : Fin (d - 2) ↦ staticSeparatedCoordinate K

theorem staticTransverseSliceIndices_card (d K : ℕ) :
    (staticTransverseSliceIndices d K).card =
      (2 * (K / 3) + 1) ^ (d - 2) := by
  rw [staticTransverseSliceIndices, Fintype.piFinset,
    Finset.card_map, Finset.card_pi]
  simp [staticSeparatedCoordinate_card]

/-- Insert a transverse `(d-2)`-tuple after the first two planar coordinates. -/
def cubicTransverseOffset (d : ℕ) (k : Cubic (d - 2)) : Cubic d :=
  fun i ↦ if hi : 2 ≤ i.val then k ⟨i.val - 2, by omega⟩ else 0

/-- Source-aligned offset for the coarse slice `[-K,K]² × {k}`.  The planar rectangle is
represented internally as `[0,2K] × [-K,K]`, so its first coordinate is translated by `-K`. -/
def staticTransverseSliceOffset (d K : ℕ) (k : Cubic (d - 2)) : Cubic d :=
  fun i ↦ if i.val = 0 then -(K : ℤ) else cubicTransverseOffset d k i

@[simp]
theorem staticTransverseSliceOffset_apply_zero {d K : ℕ} (hd : 1 ≤ d)
    (k : Cubic (d - 2)) :
    staticTransverseSliceOffset d K k (⟨0, hd⟩ : Fin d) = -(K : ℤ) := by
  simp [staticTransverseSliceOffset]

@[simp]
theorem staticTransverseSliceOffset_apply_one {d K : ℕ} (hd : 2 ≤ d)
    (k : Cubic (d - 2)) :
    staticTransverseSliceOffset d K k (⟨1, hd⟩ : Fin d) = 0 := by
  simp [staticTransverseSliceOffset, cubicTransverseOffset]

theorem staticTransverseSliceOffset_apply_of_two_le
    {d K : ℕ} (k : Cubic (d - 2)) (i : Fin d) (hi : 2 ≤ i.val) :
    staticTransverseSliceOffset d K k i = cubicTransverseOffset d k i := by
  have hi0 : i.val ≠ 0 := by omega
  simp [staticTransverseSliceOffset, hi0]

@[simp]
theorem cubicTransverseOffset_apply_add_two {d : ℕ} (hd : 2 ≤ d)
    (k : Cubic (d - 2)) (i : Fin (d - 2)) :
    cubicTransverseOffset d k ⟨i.val + 2, by omega⟩ = k i := by
  simp [cubicTransverseOffset]

theorem cubicTransverseOffset_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (cubicTransverseOffset d) := by
  intro k l hkl
  funext i
  have hi := congrFun hkl (⟨i.val + 2, by omega⟩ : Fin d)
  simpa using hi

theorem exists_transverse_coordinate_separated
    {d K : ℕ} (hd : 2 ≤ d) {a b : Cubic (d - 2)}
    (ha : a ∈ staticTransverseSliceIndices d K)
    (hb : b ∈ staticTransverseSliceIndices d K) (hab : a ≠ b) :
    ∃ j : Fin d, 2 ≤ j.val ∧
      2 < (cubicTransverseOffset d b j - cubicTransverseOffset d a j).natAbs := by
  have hcoord : ∃ i : Fin (d - 2), a i ≠ b i := by
    by_contra h
    push_neg at h
    exact hab (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hai := Fintype.mem_piFinset.mp ha i
  have hbi := Fintype.mem_piFinset.mp hb i
  rw [staticSeparatedCoordinate, Finset.mem_image] at hai hbi
  obtain ⟨u, _hu, hua⟩ := hai
  obtain ⟨v, _hv, hvb⟩ := hbi
  have huv : u ≠ v := by
    intro huv
    apply hi
    rw [← hua, ← hvb, huv]
  let j : Fin d := ⟨i.val + 2, by omega⟩
  refine ⟨j, by simp [j], ?_⟩
  have hoffA : cubicTransverseOffset d a j = a i := by
    simpa [j] using cubicTransverseOffset_apply_add_two hd a i
  have hoffB : cubicTransverseOffset d b j = b i := by
    simpa [j] using cubicTransverseOffset_apply_add_two hd b i
  rw [hoffA, hoffB, ← hua, ← hvb, ← mul_sub, Int.natAbs_mul]
  norm_num
  have hpos : 0 < (v - u).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr huv.symm)
  omega

theorem pairwiseDisjoint_staticTransverseSliceSupports
    {d K blockScale : ℕ} (hd : 2 ≤ d) (hblockScale : 1 ≤ blockScale) :
    Set.PairwiseDisjoint (staticTransverseSliceIndices d K : Set (Cubic (d - 2)))
      fun k ↦ epsilonGoodBondTranslatedSliceCrossingSupport
        d hd blockScale (staticTransverseSliceOffset d K k) (2 * K) K := by
  intro a ha b hb hab
  obtain ⟨j, hj, hsep⟩ := exists_transverse_coordinate_separated hd ha hb hab
  exact disjoint_epsilonGoodBondTranslatedSliceCrossingSupport
    hd hblockScale (2 * K) K j hj (by
      simpa [staticTransverseSliceOffset_apply_of_two_le a j hj,
        staticTransverseSliceOffset_apply_of_two_le b j hj] using hsep)

/-- Concrete form of (7.74) on the separated transverse sublattice. -/
theorem staticTransverseSlice_all_fail_probability_le_exp
    {d : ℕ} (hd : 3 ≤ d) (p q : I) (ε : ℝ)
    (blockScale K : ℕ) (hblockScale : 1 ≤ blockScale) (hK : 1 ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε blockScale).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    (bernoulliBondMeasure d p).real
        (⋂ k : {k : Cubic (d - 2) // k ∈ staticTransverseSliceIndices d K},
          (epsilonGoodBondTranslatedSliceCrossingEvent
            d (by omega) p ε blockScale
              (staticTransverseSliceOffset d K k.1) (2 * K) K)ᶜ) ≤
      Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) *
        ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by
  have h := epsilonGoodBondTranslatedSliceCrossing_all_fail_probability_le_exp
    (d := d) (κ := Cubic (d - 2)) (by omega) p q ε blockScale K
      hblockScale hK hq hqThreshold hmarginal
      (staticTransverseSliceIndices d K) (staticTransverseSliceOffset d K)
      (pairwiseDisjoint_staticTransverseSliceSupports (by omega) hblockScale)
  rw [staticTransverseSliceIndices_card] at h
  exact h

/-- The finite box support traversed by a mapped planar good-block walk is contained in the
predeclared bond support of that translated slice. -/
theorem epsilonGoodWalkEdgeSupport_map_cubicTranslatedFirstTwo_subset
    {d : ℕ} (hd : 2 ≤ d) {blockScale m n : ℕ} (z : Cubic d)
    {x y : SquareVertex} (w : squareGraph.Walk x y)
    (hwRectangle : ∀ u ∈ w.support, u ∈ squareRectangleVertices m n) :
    epsilonGoodWalkEdgeSupport (n := blockScale)
        (w.map (cubicTranslatedFirstTwoHom hd z)) ⊆
      epsilonGoodBondTranslatedSliceCrossingSupport
        d hd blockScale z m n := by
  classical
  intro e he
  rw [epsilonGoodWalkEdgeSupport, Finset.mem_biUnion] at he
  obtain ⟨u, hu, heu⟩ := he
  rw [epsilonGoodBondTranslatedSliceCrossingSupport, Finset.mem_biUnion]
  refine ⟨u, ?_, heu⟩
  rw [epsilonGoodBlockTranslatedSliceCrossingSupport, Finset.mem_map]
  simp only [SimpleGraph.Walk.support_map, List.mem_toFinset, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨v, hwRectangle v hv, by simp⟩

/-- A translated good-site crossing lifts to an open bond connection confined to the finite
bond support assigned to that slice.  This is the support-preserving deterministic bridge used
to turn different successful slices into edge-disjoint physical crossings. -/
theorem exists_connectionEventIn_between_faces_of_mem_goodBondTranslatedSliceCrossing
    {d : ℕ} (hd : 2 ≤ d) (p : I) (ε : ℝ)
    (blockScale m n : ℕ) (z : Cubic d) (omega : EdgeConfiguration d)
    (hcross : omega ∈ epsilonGoodBondTranslatedSliceCrossingEvent
      d hd p ε blockScale z m n) :
    ∃ x ∈ squareRectangleLeft m n, ∃ y ∈ squareRectangleRight m n,
      ∃ u ∈ cubicBoxFace d
          (epsilonGoodBlockCenter blockScale (cubicTranslatedFirstTwoEmbedding hd z x))
          blockScale (Fin.castLE hd 0) false,
        ∃ v ∈ cubicBoxFace d
          (epsilonGoodBlockCenter blockScale (cubicTranslatedFirstTwoEmbedding hd z y))
          blockScale (Fin.castLE hd 0) true,
          omega ∈ connectionEventIn d
            (epsilonGoodBondTranslatedSliceCrossingSupport
              d hd blockScale z m n) u v := by
  change cubicTranslatedFirstTwoSiteRestriction hd z
      (epsilonGoodBlockField d p ε blockScale omega) ∈
        siteSquareRectangleCrossingEvent m n at hcross
  simp only [siteSquareRectangleCrossingEvent, Set.mem_iUnion] at hcross
  obtain ⟨x, hx, y, hy, w, hwRectangle, hwGood⟩ := hcross
  let wd : (cubicGraph d).Walk
      (cubicTranslatedFirstTwoEmbedding hd z x)
      (cubicTranslatedFirstTwoEmbedding hd z y) :=
    w.map (cubicTranslatedFirstTwoHom hd z)
  have hgood : ∀ u ∈ wd.support,
      omega ∈ epsilonGoodBoxEvent d p ε
        (epsilonGoodBlockCenter blockScale u) blockScale := by
    intro u hu
    change u ∈ (w.map (cubicTranslatedFirstTwoHom hd z)).support at hu
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact hwGood v hv
  obtain ⟨u, huFace, v, hvFace, huv⟩ :=
    exists_connectionEventIn_between_faces_of_good_walk
      p ε omega wd hgood (Fin.castLE hd 0)
  have hsupport := epsilonGoodWalkEdgeSupport_map_cubicTranslatedFirstTwo_subset
    hd z w hwRectangle (blockScale := blockScale)
  exact ⟨x, hx, y, hy, u, huFace, v, hvFace,
    connectionEventIn_mono hsupport u v huv⟩

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
