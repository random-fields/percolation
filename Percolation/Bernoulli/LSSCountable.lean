import Percolation.Bernoulli.LSSInduction
import Percolation.Bernoulli.SequentialDominationCountable

/-!
# Countable finite-prefix transport for LSS domination

This file transports finite-range dependence to the finite laws of an enumeration.  The
ordinary induced prefix graph is not suitable: a short path may leave and re-enter the prefix.
Instead, two prefix coordinates are adjacent exactly when their original graph distance is at
most the dependence range.  Distance greater than one in this dependency graph therefore
certifies the separation needed by `KDependent`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Dependency-neighborhood graph induced by a map into the original vertex set. -/
def lssDependencyGraph {α V : Type*} (G : SimpleGraph V) (k : ℕ)
    (f : α → V) : SimpleGraph α where
  Adj x y := x ≠ y ∧ G.edist (f x) (f y) ≤ k
  symm x y h := ⟨h.1.symm, by simpa [G.edist_comm] using h.2⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

@[simp]
theorem lssDependencyGraph_adj {α V : Type*} (G : SimpleGraph V) (k : ℕ)
    (f : α → V) (x y : α) :
    (lssDependencyGraph G k f).Adj x y ↔
      x ≠ y ∧ G.edist (f x) (f y) ≤ k :=
  Iff.rfl

/-- The dependency graph converts separation beyond range one into separation beyond the
original dependence range. -/
theorem original_edist_gt_of_lssDependencyGraph_edist_gt_one
    {α V : Type*} (G : SimpleGraph V) (k : ℕ) (f : α → V)
    {x y : α} (hxy : (1 : ℕ∞) < (lssDependencyGraph G k f).edist x y) :
    (k : ℕ∞) < G.edist (f x) (f y) := by
  by_contra hfar
  have hclose : G.edist (f x) (f y) ≤ k := le_of_not_gt hfar
  have hne : x ≠ y := by
    intro h
    subst y
    simp at hxy
  have hadj : (lssDependencyGraph G k f).Adj x y := ⟨hne, hclose⟩
  have hone : (lssDependencyGraph G k f).edist x y ≤ 1 :=
    (SimpleGraph.edist_le_one_iff_adj_or_eq).mpr (Or.inl hadj)
  exact (not_lt_of_ge hone) hxy

/-- The dependency graph on the first `n` sites of an enumeration. -/
def enumerationPrefixDependencyGraph {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (e : ℕ ≃ V) (n : ℕ) : SimpleGraph (Fin n) :=
  lssDependencyGraph G k (enumerationPrefixEmbedding e n)

/-- A uniform finite cover of the original distance-`k` neighborhoods supplies the prefix
neighbor bound required by the finite LSS theorem. -/
theorem enumerationPrefixDependencyGraph_neighbor_card_le
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (neighborFinset : V → Finset V)
    (hcover : ∀ v w, G.edist v w ≤ k → w ∈ neighborFinset v)
    (hcard : ∀ v, (neighborFinset v).card ≤ B) :
    ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B := by
  intro n current
  let f := enumerationPrefixEmbedding e n
  let S := Finset.univ.filter fun x ↦
    (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1
  rw [← Finset.card_map f]
  apply (Finset.card_le_card ?_).trans (hcard (f current))
  intro v hv
  rw [Finset.mem_map] at hv
  obtain ⟨x, hxS, rfl⟩ := hv
  apply hcover
  have hxle := (SimpleGraph.edist_le_one_iff_adj_or_eq).mp
    (Finset.mem_filter.mp hxS).2
  rcases hxle with hadj | heq
  · exact hadj.2
  · subst x
    simp

/-- Pulling back a coordinate sigma-algebra along prefix restriction reads only the
corresponding original coordinates. -/
theorem comap_enumerationPrefixRestriction_siteCoordinate_le
    {V : Type*} (e : ℕ ≃ V) (n : ℕ) (A : Set (Fin n)) :
    MeasurableSpace.comap (enumerationPrefixRestriction e n)
        (siteCoordinateMeasurableSpace (Fin n) A) ≤
      siteCoordinateMeasurableSpace V (enumerationPrefixEmbedding e n '' A) := by
  rw [siteCoordinateMeasurableSpace, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  intro t ht
  rcases ht with ⟨s, hs, rfl⟩
  rcases hs with ⟨x, hx, rfl⟩
  change MeasurableSet[MeasurableSpace.generateFrom
    (coordinateEvents (enumerationPrefixEmbedding e n '' A))]
      {η : Set V | enumerationPrefixEmbedding e n x ∈ η}
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨enumerationPrefixEmbedding e n x, ⟨x, hx, rfl⟩, rfl⟩

/-- A `k`-dependent law restricts to a one-dependent law on every prefix dependency graph. -/
theorem enumerationPrefixLaw_kDependent
    {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (e : ℕ ≃ V) (n : ℕ)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu) :
    KDependent (enumerationPrefixDependencyGraph G k e n) 1
      (enumerationPrefixLaw e n mu) := by
  intro A B hsep
  let f := enumerationPrefixEmbedding e n
  have hsepOriginal : ∀ x ∈ f '' A, ∀ y ∈ f '' B,
      (k : ℕ∞) < G.edist x y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact original_edist_gt_of_lssDependencyGraph_edist_gt_one
      G k f (hsep x hx y hy)
  have hbase := hmu (f '' A) (f '' B) hsepOriginal
  have hcomap : Indep
      (MeasurableSpace.comap (enumerationPrefixRestriction e n)
        (siteCoordinateMeasurableSpace (Fin n) A))
      (MeasurableSpace.comap (enumerationPrefixRestriction e n)
        (siteCoordinateMeasurableSpace (Fin n) B)) mu := by
    apply indep_of_indep_of_le hbase
    · exact comap_enumerationPrefixRestriction_siteCoordinate_le e n A
    · exact comap_enumerationPrefixRestriction_siteCoordinate_le e n B
  unfold enumerationPrefixLaw
  exact Indep.map_measure (measurable_enumerationPrefixRestriction e n)
    (siteCoordinateMeasurableSpace_le (Fin n) A)
    (siteCoordinateMeasurableSpace_le (Fin n) B) hcomap

/-- Prefix restriction preserves the one-site marginal exactly. -/
theorem enumerationPrefixLaw_real_mem
    {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu] (x : Fin n) :
    (enumerationPrefixLaw e n mu).real {η : Set (Fin n) | x ∈ η} =
      mu.real {η : Set V | enumerationPrefixEmbedding e n x ∈ η} := by
  rw [enumerationPrefixLaw, map_measureReal_apply
    (measurable_enumerationPrefixRestriction e n) (measurableSet_mem x)]
  rfl

/-- Independent dilution commutes with restriction to an enumeration prefix. -/
theorem enumerationPrefixLaw_siteDilutionLaw
    {V : Type*} (e : ℕ ≃ V) (n : ℕ)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu] (p : I) :
    enumerationPrefixLaw e n (siteDilutionLaw mu p) =
      siteDilutionLaw (enumerationPrefixLaw e n mu) p := by
  let r := enumerationPrefixRestriction e n
  let nu := setBer((Set.univ : Set V), p)
  have hr : Measurable r := measurable_enumerationPrefixRestriction e n
  have hnu : Measure.map r nu =
      setBer((Set.univ : Set (Fin n)), p) := by
    exact setBernoulli_map_enumerationPrefixRestriction e n p
  unfold enumerationPrefixLaw siteDilutionLaw
  rw [Measure.map_map hr measurable_siteDilutionMap]
  rw [← hnu, Measure.map_prod_map mu nu hr hr]
  rw [Measure.map_map measurable_siteDilutionMap (hr.prodMap hr)]
  apply Measure.map_congr
  filter_upwards with yz
  ext x
  rfl

/-- Lowering the density preserves a ratio-free finite sequential lower bound. -/
theorem HasFiniteSequentialLowerBound.mono
    {n : ℕ} {mu : Measure (Set (Fin n))} {p q : ℝ}
    (h : HasFiniteSequentialLowerBound mu q) (hpq : p ≤ q) :
    HasFiniteSequentialLowerBound mu p := by
  intro i hi s
  have hmass : 0 ≤ boolPrefixMass (finiteSetBoolMass mu) hi.le s := by
    unfold boolPrefixMass
    apply Finset.sum_nonneg
    intro x _hx
    by_cases hx : boolPrefix hi.le x = s
    · simp [hx, finiteSetBoolMass, measureReal_nonneg]
    · simp [hx]
  exact (mul_le_mul_of_nonneg_right hpq hmass).trans (h i hi s)

/-- Unit-interval packaging of the auxiliary LSS retention density. -/
noncomputable def lssAuxiliaryDensityUnit (q : I) (hq : (q : ℝ) < 1) : I :=
  ⟨lssAuxiliaryDensity (q : ℝ),
    (lssAuxiliaryDensity_pos q.2.1).le,
    (lssAuxiliaryDensity_lt_one hq).le⟩

@[simp]
theorem lssAuxiliaryDensityUnit_coe (q : I) (hq : (q : ℝ) < 1) :
    (lssAuxiliaryDensityUnit q hq : ℝ) = lssAuxiliaryDensity (q : ℝ) :=
  rfl

/-- Every finite marginal of the countably diluted field satisfies the requested iid
prefix bound.  This is the projective finite-dimensional content of Theorem 7.65. -/
theorem enumerationPrefixLaw_siteDilution_hasFiniteSequentialLowerBound_lss
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (hmarginal : ∀ current : V,
      (lssMarginalThresholdUnit B q hq : ℝ) ≤
        mu.real {original : Set V | current ∈ original}) :
    ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n
        (siteDilutionLaw mu (lssAuxiliaryDensityUnit q hq))) (q : ℝ) := by
  intro n
  let H := enumerationPrefixDependencyGraph G k e n
  let a : ℝ := lssAuxiliaryDensity (q : ℝ)
  let delta : I := lssMarginalThresholdUnit B q hq
  let aI : I := lssAuxiliaryDensityUnit q hq
  obtain ⟨ha0, ha1, hqaa, _hdelta, hparameters⟩ :=
    lss_parameter_selection B q hq
  have hendpoint := hparameters delta (le_rfl)
  have hprefixMarginal : ∀ current : Fin n,
      (delta : ℝ) ≤ (enumerationPrefixLaw e n mu).real
        {original : Set (Fin n) | current ∈ original} := by
    intro current
    rw [enumerationPrefixLaw_real_mem]
    exact hmarginal (enumerationPrefixEmbedding e n current)
  have hseqAA := hasFiniteSequentialLowerBound_siteDilutionLaw_of_kDependent
    H 1 (enumerationPrefixLaw e n mu)
      (enumerationPrefixLaw_kDependent G k e n mu hmu)
      aI a (delta : ℝ) B ha0 ha0.le ha1.le
      hendpoint.1 hendpoint.2 hprefixMarginal (hneighbor n)
  have hcommute := enumerationPrefixLaw_siteDilutionLaw e n mu aI
  rw [hcommute]
  exact hseqAA.mono hqaa

/-- Countable LSS comparison for every increasing finite-cylinder event.  The full
expectation-form Theorem 7.65 additionally requires the monotone-class/regularity lift from
finite cylinders to arbitrary bounded increasing measurable observables. -/
theorem lss_finiteCylinder_measureReal_le
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (hmarginal : ∀ current : V,
      (lssMarginalThresholdUnit B q hq : ℝ) ≤
        mu.real {original : Set V | current ∈ original})
    {R : Finset V} {A : Set (Set V)}
    (hdep : DependsOn R A) (hinc : IsIncreasingEvent A) :
    setBer((Set.univ : Set V), q).real A ≤ mu.real A := by
  let aI := lssAuxiliaryDensityUnit q hq
  let diluted := siteDilutionLaw mu aI
  have hseq : ∀ n, HasFiniteSequentialLowerBound
      (enumerationPrefixLaw e n diluted) (q : ℝ) := by
    exact enumerationPrefixLaw_siteDilution_hasFiniteSequentialLowerBound_lss
      G k B e hneighbor q hq mu hmu hmarginal
  have hiidDiluted : setBer((Set.univ : Set V), q).real A ≤
      diluted.real A :=
    finiteCylinder_measureReal_le_of_prefixSequential
      e diluted q hseq hdep hinc
  have hDilutedOriginal : diluted.real A ≤ mu.real A := by
    exact (stochasticallyDominates_siteDilutionLaw mu aI).measureReal_le
      hdep.measurableSet hinc
  exact hiidDiluted.trans hDilutedOriginal

/-- Source-style threshold formulation of the countable finite-cylinder LSS theorem: for
every requested iid density below one, a uniform marginal threshold strictly below one
suffices. -/
theorem exists_lssFiniteCylinderDominationThreshold
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B)
    (q : I) (hq : (q : ℝ) < 1) :
    ∃ delta : I, (delta : ℝ) < 1 ∧
      ∀ (mu : Measure (Set V)), IsProbabilityMeasure mu →
        KDependent G k mu →
        (∀ current : V,
          (delta : ℝ) ≤ mu.real {original : Set V | current ∈ original}) →
        ∀ (R : Finset V) (A : Set (Set V)),
          DependsOn R A → IsIncreasingEvent A →
            setBer((Set.univ : Set V), q).real A ≤ mu.real A := by
  let delta := lssMarginalThresholdUnit B q hq
  refine ⟨delta, ?_, ?_⟩
  · exact lssMarginalThreshold_lt_one B q.2.1 hq
  · intro mu hprob hmu hmarginal R A hdep hinc
    letI : IsProbabilityMeasure mu := hprob
    exact lss_finiteCylinder_measureReal_le
      G k B e hneighbor q hq mu hmu hmarginal hdep hinc

end Percolation
