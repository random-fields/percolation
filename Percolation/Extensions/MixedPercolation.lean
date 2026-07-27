import Percolation.Extensions.PeriodicMixed

/-!
# Measurability and deterministic laws for mixed percolation

The model definition in §12.1 is completed here with explicit finite-walk certificates.  They
make rooted connection and infinite-cluster events measurable under the independent site/bond
product law.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped unitInterval

/-- An ambient walk is open in a mixed configuration when every traversed edge and both of its
endpoints are open.  The empty walk is allowed, matching graph reachability. -/
def MixedWalkOpen {V : Type*} {G : SimpleGraph V} (omega : MixedConfiguration G)
    {x y : V} (w : G.Walk x y) : Prop :=
  ∀ dart ∈ w.darts, dart.fst ∈ omega.1 ∧ dart.snd ∈ omega.1 ∧
    (⟨s(dart.fst, dart.snd),
      (SimpleGraph.mem_edgeSet G).2 dart.adj⟩ : G.edgeSet) ∈ omega.2

@[simp]
theorem mixedWalkOpen_nil {V : Type*} {G : SimpleGraph V}
    (omega : MixedConfiguration G) (x : V) :
    MixedWalkOpen omega (SimpleGraph.Walk.nil : G.Walk x x) := by
  simp [MixedWalkOpen]

theorem mixedWalkOpen_cons_iff {V : Type*} {G : SimpleGraph V}
    (omega : MixedConfiguration G) {x y z : V} (hxy : G.Adj x y) (w : G.Walk y z) :
    MixedWalkOpen omega (SimpleGraph.Walk.cons hxy w) ↔
      x ∈ omega.1 ∧ y ∈ omega.1 ∧
        (⟨s(x, y), (SimpleGraph.mem_edgeSet G).2 hxy⟩ : G.edgeSet) ∈ omega.2 ∧
          MixedWalkOpen omega w := by
  simp [MixedWalkOpen, SimpleGraph.Walk.darts_cons]
  tauto

/-- Reachability in the mixed open graph has a finite ambient-walk certificate. -/
theorem mixedOpenGraph_reachable_iff_exists_mixedWalkOpen
    {V : Type*} (G : SimpleGraph V) (omega : MixedConfiguration G) (x y : V) :
    (mixedOpenGraph G omega).Reachable x y ↔
      ∃ w : G.Walk x y, MixedWalkOpen omega w := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨SimpleGraph.Walk.nil, mixedWalkOpen_nil omega x⟩
    | @cons u v z huv w ih =>
        obtain ⟨q, hq⟩ := ih
        refine ⟨SimpleGraph.Walk.cons huv.1 q, ?_⟩
        exact (mixedWalkOpen_cons_iff omega huv.1 q).2
          ⟨huv.2.1, huv.2.2.1, huv.2.2.2, hq⟩
  · rintro ⟨w, hw⟩
    induction w with
    | nil => exact ⟨SimpleGraph.Walk.nil⟩
    | @cons u v z huv w ih =>
        have hopen := (mixedWalkOpen_cons_iff omega huv w).1 hw
        obtain ⟨q⟩ := ih hopen.2.2.2
        exact ⟨SimpleGraph.Walk.cons
          ⟨huv, hopen.1, hopen.2.1, hopen.2.2.1⟩ q⟩

/-- Fixed-endpoint connection event for mixed percolation. -/
def mixedConnectionEvent {V : Type*} (G : SimpleGraph V) (x y : V) :
    Set (MixedConfiguration G) :=
  {omega | (mixedOpenGraph G omega).Reachable x y}

private theorem measurableSet_mixedWalkOpen
    {V : Type*} {G : SimpleGraph V} {x y : V} (w : G.Walk x y) :
    MeasurableSet {omega : MixedConfiguration G | MixedWalkOpen omega w} := by
  induction w with
  | nil => simp [MixedWalkOpen]
  | @cons u v z huv w ih =>
      let e : G.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet G).2 huv⟩
      have hrepr :
          {omega : MixedConfiguration G |
            MixedWalkOpen omega (SimpleGraph.Walk.cons huv w)} =
            (Prod.fst ⁻¹' {sites : Set V | u ∈ sites}) ∩
              (Prod.fst ⁻¹' {sites : Set V | v ∈ sites}) ∩
                (Prod.snd ⁻¹' {bonds : Set G.edgeSet | e ∈ bonds}) ∩
                  {omega | MixedWalkOpen omega w} := by
        ext omega
        simp [mixedWalkOpen_cons_iff, e]
        tauto
      rw [hrepr]
      exact (((measurableSet_mem u).preimage measurable_fst).inter
        ((measurableSet_mem v).preimage measurable_fst)).inter
          ((measurableSet_mem e).preimage measurable_snd) |>.inter ih

theorem measurableSet_mixedConnectionEvent
    {V : Type*} [Countable V] (G : SimpleGraph V) (x y : V) :
    MeasurableSet (mixedConnectionEvent G x y) := by
  classical
  letI : Countable (G.Walk x y) :=
    (show Function.Injective (fun w : G.Walk x y ↦ w.support) from
      fun _ _ h ↦ SimpleGraph.Walk.ext_support h).countable
  have hrepr : mixedConnectionEvent G x y =
      ⋃ w : G.Walk x y, {omega | MixedWalkOpen omega w} := by
    ext omega
    simp only [mixedConnectionEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    exact mixedOpenGraph_reachable_iff_exists_mixedWalkOpen G omega x y
  rw [hrepr]
  exact MeasurableSet.iUnion measurableSet_mixedWalkOpen

/-- The rooted infinite mixed-cluster event is measurable. -/
theorem measurableSet_infinite_mixedOpenCluster
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) :
    MeasurableSet {omega : MixedConfiguration G |
      (mixedOpenCluster G omega root).Infinite} := by
  classical
  have hrepr :
      {omega : MixedConfiguration G | (mixedOpenCluster G omega root).Infinite} =
        ⋂ s : Finset V, ⋃ y : V, ⋃ (_hy : y ∉ s), mixedConnectionEvent G root y := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hinfinite s
      obtain ⟨y, hy, hys⟩ := hinfinite.exists_notMem_finset s
      exact ⟨y, hys, hy⟩
    · intro h
      rw [← Set.not_finite]
      intro hfinite
      obtain ⟨y, hys, hy⟩ := h hfinite.toFinset
      exact hys (hfinite.mem_toFinset.mpr hy)
  rw [hrepr]
  exact MeasurableSet.iInter fun s ↦ MeasurableSet.iUnion fun y ↦
    MeasurableSet.iUnion fun _hy ↦ measurableSet_mixedConnectionEvent G root y

@[simp]
theorem mixedTheta_site_zero {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) (bondDensity : I) :
    mixedTheta G root (0 : I) bondDensity = 0 := by
  let A : Set (MixedConfiguration G) :=
    {omega | (mixedOpenCluster G omega root).Infinite}
  have hA : MeasurableSet A := measurableSet_infinite_mixedOpenCluster G root
  have hpre : (Prod.mk (∅ : Set V)) ⁻¹' A = ∅ := by
    ext bonds
    simp only [Set.mem_preimage, A, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    have hcluster : mixedOpenCluster G (∅, bonds) root = {root} := by
      have hgraph : mixedOpenGraph G (∅, bonds) = ⊥ := by
        ext x y
        simp [mixedOpenGraph]
      ext y
      simp [mixedOpenCluster, hgraph, SimpleGraph.reachable_bot]
    constructor
    · intro hinfinite
      rw [hcluster] at hinfinite
      exact hinfinite (Set.finite_singleton root)
    · intro hfalse
      contradiction
  unfold mixedTheta mixedPercolationMeasure
  rw [setBernoulli_zero, Measure.dirac_prod]
  rw [Measure.real, Measure.map_apply (by fun_prop) hA, hpre]
  simp

@[simp]
theorem mixedTheta_bond_zero {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) (siteDensity : I) :
    mixedTheta G root siteDensity (0 : I) = 0 := by
  let A : Set (MixedConfiguration G) :=
    {omega | (mixedOpenCluster G omega root).Infinite}
  have hA : MeasurableSet A := measurableSet_infinite_mixedOpenCluster G root
  have hpre : (fun sites : Set V ↦ (sites, (∅ : Set G.edgeSet))) ⁻¹' A = ∅ := by
    ext sites
    simp only [Set.mem_preimage, A, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    have hcluster : mixedOpenCluster G (sites, ∅) root = {root} := by
      have hgraph : mixedOpenGraph G (sites, ∅) = ⊥ := by
        ext x y
        simp [mixedOpenGraph]
      ext y
      simp [mixedOpenCluster, hgraph, SimpleGraph.reachable_bot]
    constructor
    · intro hinfinite
      rw [hcluster] at hinfinite
      exact hinfinite (Set.finite_singleton root)
    · intro hfalse
      contradiction
  unfold mixedTheta mixedPercolationMeasure
  rw [setBernoulli_zero, Measure.prod_dirac]
  rw [Measure.real, Measure.map_apply (by fun_prop) hA, hpre]
  simp

theorem mixedOpenGraph_mono {V : Type*} {G : SimpleGraph V}
    {omega eta : MixedConfiguration G} (hsite : omega.1 ⊆ eta.1)
    (hbond : omega.2 ⊆ eta.2) :
    mixedOpenGraph G omega ≤ mixedOpenGraph G eta := by
  rintro x y ⟨hxy, hx, hy, he⟩
  exact ⟨hxy, hsite hx, hsite hy, hbond he⟩

theorem mixedOpenCluster_mono {V : Type*} {G : SimpleGraph V}
    {omega eta : MixedConfiguration G} (hsite : omega.1 ⊆ eta.1)
    (hbond : omega.2 ⊆ eta.2) (root : V) :
    mixedOpenCluster G omega root ⊆ mixedOpenCluster G eta root := by
  intro y hy
  exact hy.mono (mixedOpenGraph_mono hsite hbond)

/-! ### Simultaneous two-parameter coupling -/

/-- Independent uniform fields for sites and bonds. -/
noncomputable def mixedCouplingMeasure {V : Type*} (G : SimpleGraph V) :
    Measure ((V → ℝ) × (G.edgeSet → ℝ)) :=
  (couplingMeasure V).prod (couplingMeasure G.edgeSet)

noncomputable instance mixedCouplingMeasure.isProbabilityMeasure
    {V : Type*} (G : SimpleGraph V) :
    IsProbabilityMeasure (mixedCouplingMeasure G) := by
  unfold mixedCouplingMeasure
  infer_instance

/-- Threshold both uniform fields at their respective densities. -/
def mixedThresholdConfiguration {V : Type*} {G : SimpleGraph V}
    (siteDensity bondDensity : I) (X : (V → ℝ) × (G.edgeSet → ℝ)) :
    MixedConfiguration G :=
  (thresholdConfiguration siteDensity X.1,
    thresholdConfiguration bondDensity X.2)

theorem measurable_mixedThresholdConfiguration
    {V : Type*} {G : SimpleGraph V} (siteDensity bondDensity : I) :
    Measurable (mixedThresholdConfiguration (G := G) siteDensity bondDensity) := by
  exact ((measurable_thresholdConfiguration siteDensity).comp measurable_fst).prodMk
    ((measurable_thresholdConfiguration bondDensity).comp measurable_snd)

theorem mixedThresholdConfiguration_mono
    {V : Type*} {G : SimpleGraph V}
    {siteDensity siteDensity' bondDensity bondDensity' : I}
    (hsite : siteDensity ≤ siteDensity') (hbond : bondDensity ≤ bondDensity')
    (X : (V → ℝ) × (G.edgeSet → ℝ)) :
    (mixedThresholdConfiguration (G := G) siteDensity bondDensity X).1 ⊆
        (mixedThresholdConfiguration (G := G) siteDensity' bondDensity' X).1 ∧
      (mixedThresholdConfiguration (G := G) siteDensity bondDensity X).2 ⊆
        (mixedThresholdConfiguration (G := G) siteDensity' bondDensity' X).2 :=
  ⟨thresholdConfiguration_mono hsite X.1,
    thresholdConfiguration_mono hbond X.2⟩

/-- The simultaneous threshold construction has the required independent mixed Bernoulli law. -/
theorem mixedCouplingMeasure_map_thresholdConfiguration
    {V : Type*} [Countable V] (G : SimpleGraph V) (siteDensity bondDensity : I) :
    (mixedCouplingMeasure G).map
        (mixedThresholdConfiguration (G := G) siteDensity bondDensity) =
      mixedPercolationMeasure G siteDensity bondDensity := by
  rw [mixedPercolationMeasure, ← couplingMeasure_map_thresholdConfiguration siteDensity,
    ← couplingMeasure_map_thresholdConfiguration bondDensity]
  symm
  simpa [mixedCouplingMeasure, mixedThresholdConfiguration] using
    Measure.map_prod_map (couplingMeasure V) (couplingMeasure G.edgeSet)
      (measurable_thresholdConfiguration siteDensity)
      (measurable_thresholdConfiguration bondDensity)

/-- The rooted mixed percolation probability is nondecreasing in both parameters. -/
theorem mixedTheta_mono {V : Type*} [Countable V] (G : SimpleGraph V) (root : V)
    {siteDensity siteDensity' bondDensity bondDensity' : I}
    (hsite : siteDensity ≤ siteDensity') (hbond : bondDensity ≤ bondDensity') :
    mixedTheta G root siteDensity bondDensity ≤
      mixedTheta G root siteDensity' bondDensity' := by
  let A : Set (MixedConfiguration G) :=
    {omega | (mixedOpenCluster G omega root).Infinite}
  have hA : MeasurableSet A := measurableSet_infinite_mixedOpenCluster G root
  rw [mixedTheta, mixedTheta,
    ← mixedCouplingMeasure_map_thresholdConfiguration G siteDensity bondDensity,
    ← mixedCouplingMeasure_map_thresholdConfiguration G siteDensity' bondDensity',
    Measure.real, Measure.real,
    Measure.map_apply (measurable_mixedThresholdConfiguration siteDensity bondDensity) hA,
    Measure.map_apply
      (measurable_mixedThresholdConfiguration siteDensity' bondDensity') hA]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro X hX
  have hmono := mixedThresholdConfiguration_mono hsite hbond X
  exact hX.mono (mixedOpenCluster_mono hmono.1 hmono.2 root)

/-- The zero phase in the mixed site/bond parameter square. -/
def mixedCriticalSet {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) : Set (I × I) :=
  {p | mixedTheta G root p.1 p.2 = 0}

theorem mixedCriticalSet_lower
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V)
    {p q : I × I} (hqp : q.1 ≤ p.1) (hqb : q.2 ≤ p.2)
    (hp : p ∈ mixedCriticalSet G root) :
    q ∈ mixedCriticalSet G root := by
  apply le_antisymm
  · exact (mixedTheta_mono G root hqp hqb).trans_eq hp
  · exact measureReal_nonneg

theorem mixedCriticalSet_compl_upper
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V)
    {p q : I × I} (hpqSite : p.1 ≤ q.1) (hpqBond : p.2 ≤ q.2)
    (hp : p ∉ mixedCriticalSet G root) :
    q ∉ mixedCriticalSet G root := by
  intro hq
  apply hp
  apply le_antisymm
  · exact (mixedTheta_mono G root hpqSite hpqBond).trans_eq hq
  · exact measureReal_nonneg

@[simp]
theorem mixedCriticalSet_zero_site
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) (bondDensity : I) :
    ((0 : I), bondDensity) ∈ mixedCriticalSet G root := by
  exact mixedTheta_site_zero G root bondDensity

@[simp]
theorem mixedCriticalSet_zero_bond
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) (siteDensity : I) :
    (siteDensity, (0 : I)) ∈ mixedCriticalSet G root := by
  exact mixedTheta_bond_zero G root siteDensity

/-- With every bond open, mixed percolation is exactly ordinary site percolation. -/
@[simp]
theorem mixedOpenGraph_all_bonds {V : Type*} (G : SimpleGraph V) (sites : Set V) :
    mixedOpenGraph G (sites, Set.univ) = siteOpenGraph G sites := by
  ext x y
  simp [mixedOpenGraph, siteOpenGraph_adj]
  tauto

@[simp]
theorem mixedOpenGraph_no_sites {V : Type*} (G : SimpleGraph V) (bonds : Set G.edgeSet) :
    mixedOpenGraph G (∅, bonds) = ⊥ := by
  ext x y
  simp [mixedOpenGraph]

@[simp]
theorem mixedOpenGraph_no_bonds {V : Type*} (G : SimpleGraph V) (sites : Set V) :
    mixedOpenGraph G (sites, ∅) = ⊥ := by
  ext x y
  simp [mixedOpenGraph]

theorem mixedOpenCluster_all_bonds_eq_of_root_mem
    {V : Type*} (G : SimpleGraph V) (sites : Set V) {root : V}
    (hroot : root ∈ sites) :
    mixedOpenCluster G (sites, Set.univ) root = siteOpenCluster G sites root := by
  rw [siteOpenCluster_eq_reachable]
  ext y
  simp only [mixedOpenCluster, Set.mem_setOf_eq, hroot, true_and]
  rw [mixedOpenGraph_all_bonds]

theorem mixedOpenCluster_all_bonds_eq_singleton_of_root_not_mem
    {V : Type*} (G : SimpleGraph V) (sites : Set V) {root : V}
    (hroot : root ∉ sites) :
    mixedOpenCluster G (sites, Set.univ) root = {root} := by
  ext y
  simp only [mixedOpenCluster, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [mixedOpenGraph_all_bonds]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | @cons root z y hrootz w =>
        exact (hroot (siteOpenGraph_adj.mp hrootz).2.1).elim
  · rintro rfl
    exact SimpleGraph.Reachable.rfl

/-- With every bond open, an infinite mixed root cluster is exactly an infinite site-open root
cluster.  The closed-root case is made explicit: the mixed graph still contains the isolated
root as a vertex, whereas `siteOpenCluster` is empty, but both sets are finite. -/
theorem mixedOpenCluster_all_bonds_infinite_iff
    {V : Type*} (G : SimpleGraph V) (sites : Set V) (root : V) :
    (mixedOpenCluster G (sites, Set.univ) root).Infinite ↔
      (siteOpenCluster G sites root).Infinite := by
  by_cases hroot : root ∈ sites
  · rw [mixedOpenCluster_all_bonds_eq_of_root_mem G sites hroot]
  · rw [mixedOpenCluster_all_bonds_eq_singleton_of_root_not_mem G sites hroot]
    have hsite : siteOpenCluster G sites root = ∅ := by
      rw [siteOpenCluster_eq_reachable]
      ext y
      simp [hroot]
    rw [hsite]
    simp

/-- The bond-density-one boundary of mixed percolation is rooted site percolation. -/
theorem mixedTheta_bond_one
    {V : Type*} [Countable V] (G : SimpleGraph V) (root : V) (siteDensity : I) :
    mixedTheta G root siteDensity (1 : I) =
      (setBernoulli (Set.univ : Set V) siteDensity).real
        {sites | (siteOpenCluster G sites root).Infinite} := by
  let A : Set (MixedConfiguration G) :=
    {omega | (mixedOpenCluster G omega root).Infinite}
  have hA : MeasurableSet A := measurableSet_infinite_mixedOpenCluster G root
  have hpre :
      (fun sites : Set V ↦ (sites, (Set.univ : Set G.edgeSet))) ⁻¹' A =
        {sites | (siteOpenCluster G sites root).Infinite} := by
    ext sites
    exact mixedOpenCluster_all_bonds_infinite_iff G sites root
  unfold mixedTheta mixedPercolationMeasure
  rw [setBernoulli_one, Measure.prod_dirac]
  rw [Measure.real, Measure.map_apply (by fun_prop) hA, hpre]
  rfl

/-- With every cubic-lattice site open, the mixed graph is the ordinary bond-open graph. -/
theorem mixedOpenGraph_cubic_all_sites (d : ℕ) (bonds : EdgeConfiguration d) :
    mixedOpenGraph (cubicGraph d) (Set.univ, bonds) = cubicOpenGraph d bonds := by
  ext x y
  rw [cubicOpenGraph_adj]
  simp [mixedOpenGraph]

/-- The site-density-one mixed origin cluster is literally the ordinary cubic bond cluster. -/
theorem mixedOpenCluster_cubic_all_sites (d : ℕ) (bonds : EdgeConfiguration d) :
    mixedOpenCluster (cubicGraph d) (Set.univ, bonds) cubicOrigin =
      cubicOpenCluster d bonds := by
  ext y
  change (mixedOpenGraph (cubicGraph d) (Set.univ, bonds)).Reachable cubicOrigin y ↔
    ∃ w : (cubicGraph d).Walk cubicOrigin y, walkIsOpen bonds w
  rw [show mixedOpenGraph (cubicGraph d) (Set.univ, bonds) = cubicOpenGraph d bonds from
    mixedOpenGraph_cubic_all_sites d bonds]
  exact cubicOpenGraph_reachable_iff

/-- The site-density-one boundary of the cubic mixed model is ordinary bond percolation. -/
theorem mixedTheta_cubic_site_one (d : ℕ) (bondDensity : I) :
    mixedTheta (cubicGraph d) cubicOrigin (1 : I) bondDensity = theta d bondDensity := by
  let A : Set (MixedConfiguration (cubicGraph d)) :=
    {omega | (mixedOpenCluster (cubicGraph d) omega cubicOrigin).Infinite}
  have hA : MeasurableSet A :=
    measurableSet_infinite_mixedOpenCluster (cubicGraph d) cubicOrigin
  have hpre :
      (fun bonds : EdgeConfiguration d ↦
        ((Set.univ : Set (Cubic d)), bonds)) ⁻¹' A =
        {bonds | hasInfiniteOpenCluster d bonds} := by
    ext bonds
    simpa [A, hasInfiniteOpenCluster] using
      congrArg Set.Infinite (mixedOpenCluster_cubic_all_sites d bonds)
  unfold mixedTheta mixedPercolationMeasure theta bernoulliBondMeasure
  rw [setBernoulli_one, Measure.dirac_prod]
  rw [Measure.real, Measure.map_apply (by fun_prop) hA, hpre]
  rfl

@[simp]
theorem mem_mixedCriticalSet_cubic_site_one_iff (d : ℕ) (bondDensity : I) :
    ((1 : I), bondDensity) ∈ mixedCriticalSet (cubicGraph d) cubicOrigin ↔
      theta d bondDensity = 0 := by
  rw [mixedCriticalSet, Set.mem_setOf_eq, mixedTheta_cubic_site_one]

end Percolation
