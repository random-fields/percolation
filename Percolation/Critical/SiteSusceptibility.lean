import Percolation.Critical.SiteBranching
import Percolation.Critical.RootedSitePercolation
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Site susceptibility on a countable graph

This file supplies the mean-cluster interface used by the continuum comparison in
Grimmett (12.42)--(12.44).  Cluster size is extended-valued, so an infinite cluster is never
silently encoded as zero.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal unitInterval

/-- Extended cardinality of the site-open cluster rooted at `root`. -/
noncomputable def siteClusterSizeENNReal {V : Type*}
    (G : SimpleGraph V) (eta : Set V) (root : V) : ℝ≥0∞ :=
  by
    classical
    exact ∑' y : V, if eta ∈ siteConnectionEvent G root y then 1 else 0

theorem measurable_siteOpenCluster {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) :
    Measurable (fun eta : Set V ↦ siteOpenCluster G eta root) := by
  rw [measurable_set_iff]
  intro y
  exact (measurableSet_siteConnectionEvent G root y).mem

theorem measurable_siteClusterSizeENNReal {V : Type*} [Countable V]
    (G : SimpleGraph V) (root : V) :
    Measurable (fun eta : Set V ↦ siteClusterSizeENNReal G eta root) := by
  classical
  unfold siteClusterSizeENNReal
  apply Measurable.tsum
  intro y
  exact measurable_const.indicator
    (measurableSet_siteConnectionEvent G root y)

/-- Mean size of the rooted site-open cluster. -/
noncomputable def siteSusceptibility {V : Type*} [Countable V]
    (G : SimpleGraph V) (p : I) (root : V) : ℝ≥0∞ :=
  ∫⁻ eta, siteClusterSizeENNReal G eta root
    ∂setBer((Set.univ : Set V), p)

theorem siteClusterSizeENNReal_eq_encard {V : Type*} [Countable V]
    (G : SimpleGraph V) (eta : Set V) (root : V) :
    siteClusterSizeENNReal G eta root = (siteOpenCluster G eta root).encard := by
  classical
  unfold siteClusterSizeENNReal
  rw [← ENNReal.tsum_set_one]
  change (∑' y : V,
    (siteOpenCluster G eta root).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
      ∑' _ : siteOpenCluster G eta root, (1 : ℝ≥0∞)
  exact (tsum_subtype (siteOpenCluster G eta root)
    fun _ ↦ (1 : ℝ≥0∞)).symm

/-- The site susceptibility is the sum of all rooted two-point probabilities. -/
theorem siteSusceptibility_eq_tsum_connection {V : Type*} [Countable V]
    (G : SimpleGraph V) (p : I) (root : V) :
    siteSusceptibility G p root =
      ∑' y : V,
        setBer((Set.univ : Set V), p) (siteConnectionEvent G root y) := by
  classical
  unfold siteSusceptibility siteClusterSizeENNReal
  rw [lintegral_tsum]
  apply tsum_congr
  intro y
  rw [show (fun eta : Set V ↦
      if eta ∈ siteConnectionEvent G root y then (1 : ℝ≥0∞) else 0) =
      (siteConnectionEvent G root y).indicator (fun _ ↦ 1) by
    funext eta
    rfl]
  rw [lintegral_indicator (measurableSet_siteConnectionEvent G root y)]
  simp
  · intro y
    have hm : Measurable ((siteConnectionEvent G root y).indicator
        (fun _ : Set V ↦ (1 : ℝ≥0∞))) :=
      measurable_const.indicator (measurableSet_siteConnectionEvent G root y)
    simpa only [Set.indicator_apply] using hm.aemeasurable

/-- Finite mean site-cluster size rules out a rooted infinite cluster. -/
theorem rootedInfiniteSiteCluster_measure_eq_zero_of_siteSusceptibility_lt_top
    {V : Type*} [Countable V] (G : SimpleGraph V) (p : I) (root : V)
    (hfinite : siteSusceptibility G p root < ⊤) :
    setBer((Set.univ : Set V), p)
      (rootedInfiniteSiteClusterEvent G root) = 0 := by
  let mu := setBer((Set.univ : Set V), p)
  have hae : ∀ᵐ eta : Set V ∂mu, siteClusterSizeENNReal G eta root < ⊤ :=
    ae_lt_top (measurable_siteClusterSizeENNReal G root) hfinite.ne
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with eta heta
  intro hinf
  apply (ne_of_lt heta)
  rw [siteClusterSizeENNReal_eq_encard, ENat.toENNReal_eq_top,
    Set.encard_eq_top_iff]
  exact hinf

/-! ### A bounded-degree susceptibility estimate -/

/-- A self-avoiding rooted walk, bundled with its length. -/
abbrev SiteRootedPathCode {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (root : V) :=
  Σ n : ℕ, ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath)

/-- The graph walk carried by a rooted path code. -/
def siteRootedPathCodeWalk {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [G.LocallyFinite] {root : V}
    (q : SiteRootedPathCode G root) : G.Walk root q.2.1.1 :=
  q.2.1.2

/-- Set of self-avoiding path codes that are open in `eta`. -/
def siteOpenPathCodes {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (root : V) (eta : Set V) :
    Set (SiteRootedPathCode G root) :=
  {q | eta ∈ siteWalkOpenEvent (siteRootedPathCodeWalk q)}

/-- The number of open self-avoiding paths from `root`, with value `∞` when there are
infinitely many. -/
noncomputable def siteOpenPathWitnessMass {V : Type*} [Countable V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (root : V) (eta : Set V) : ℝ≥0∞ :=
  by
    classical
    exact ∑' q : SiteRootedPathCode G root,
      (siteOpenPathCodes G root eta).indicator (fun _ ↦ 1) q

theorem siteOpenPathWitnessMass_eq_encard {V : Type*} [Countable V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (root : V) (eta : Set V) :
    siteOpenPathWitnessMass G root eta =
      (siteOpenPathCodes G root eta).encard := by
  classical
  unfold siteOpenPathWitnessMass
  rw [← ENNReal.tsum_set_one]
  exact (tsum_subtype (siteOpenPathCodes G root eta)
    fun _ ↦ (1 : ℝ≥0∞)).symm

/-- Choose a self-avoiding open path from the root to a vertex of its site cluster. -/
noncomputable def siteClusterToOpenPathCode {V : Type*} [Countable V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (root : V) (eta : Set V) :
    siteOpenCluster G eta root → siteOpenPathCodes G root eta := by
  intro y
  let w : G.Walk root y.1 := Classical.choose y.2
  have hwOpen : ∀ z ∈ w.support, z ∈ eta := Classical.choose_spec y.2
  let q : G.Walk root y.1 := w.toPath.1
  have hqPath : q.IsPath := w.toPath.2
  have hqMem : (⟨y.1, q⟩ : Σ z, G.Walk root z) ∈
      (G.rootedWalks q.length root).filter fun r ↦ r.2.IsPath := by
    rw [Finset.mem_filter]
    exact ⟨(SimpleGraph.mem_rootedWalks_iff G).mpr rfl, hqPath⟩
  let code : SiteRootedPathCode G root :=
    ⟨q.length, ⟨⟨y.1, q⟩, hqMem⟩⟩
  refine ⟨code, ?_⟩
  intro z hz
  exact hwOpen z (w.support_toPath_subset hz)

theorem siteClusterToOpenPathCode_injective {V : Type*} [Countable V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (root : V) (eta : Set V) :
    Function.Injective (siteClusterToOpenPathCode G root eta) := by
  intro y z hyz
  apply Subtype.ext
  have hcode := congrArg (fun q : siteOpenPathCodes G root eta ↦ q.1.2.1.1) hyz
  exact hcode

/-- Every cluster vertex receives a distinct open self-avoiding path witness. -/
theorem siteClusterSizeENNReal_le_openPathWitnessMass
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (root : V) (eta : Set V) :
    siteClusterSizeENNReal G eta root ≤ siteOpenPathWitnessMass G root eta := by
  rw [siteClusterSizeENNReal_eq_encard, siteOpenPathWitnessMass_eq_encard]
  exact_mod_cast ENat.card_le_card_of_injective
    (siteClusterToOpenPathCode_injective G root eta)

/-- Weighted version of the open-path witness comparison.  It is useful when the contribution
of a cluster vertex is itself random (for example, the number of Poisson points in a cube).
The chosen self-avoiding path preserves its endpoint, so no bound on `weight` is needed. -/
theorem siteClusterWeightedMass_le_openPathWeightedMass
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (root : V) (eta : Set V)
    (weight : V → ℝ≥0∞) :
    (∑' x : V, (siteConnectionEvent G root x).indicator
        (fun _ ↦ weight x) eta) ≤
      ∑' q : SiteRootedPathCode G root,
        (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
          (fun _ ↦ weight q.2.1.1) eta := by
  classical
  let f : siteOpenCluster G eta root → SiteRootedPathCode G root :=
    fun x ↦ (siteClusterToOpenPathCode G root eta x).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (siteClusterToOpenPathCode_injective G root eta)
  let mass : SiteRootedPathCode G root → ℝ≥0∞ :=
    fun q ↦ (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
      (fun _ ↦ weight q.2.1.1) eta
  calc
    (∑' x : V, (siteConnectionEvent G root x).indicator
        (fun _ ↦ weight x) eta) =
        ∑' x : siteOpenCluster G eta root, weight x.1 := by
      change (∑' x : V,
        (siteOpenCluster G eta root).indicator weight x) = _
      exact (tsum_subtype (siteOpenCluster G eta root) weight).symm
    _ = ∑' x : siteOpenCluster G eta root, mass (f x) := by
      apply tsum_congr
      intro x
      have hopen : eta ∈ siteWalkOpenEvent
          (siteRootedPathCodeWalk (f x)) :=
        (siteClusterToOpenPathCode G root eta x).2
      simp only [mass, Set.indicator_of_mem hopen]
      rfl
    _ ≤ ∑' q : SiteRootedPathCode G root, mass q :=
      ENNReal.tsum_comp_le_tsum_of_injective hf mass
    _ = ∑' q : SiteRootedPathCode G root,
        (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
          (fun _ ↦ weight q.2.1.1) eta := rfl

theorem measurable_siteOpenPathWitnessMass
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (root : V) :
    Measurable (siteOpenPathWitnessMass G root) := by
  classical
  unfold siteOpenPathWitnessMass siteOpenPathCodes
  apply Measurable.tsum
  intro q
  exact measurable_const.indicator
    (measurableSet_siteWalkOpenEvent (siteRootedPathCodeWalk q))

theorem siteSusceptibility_le_lintegral_openPathWitnessMass
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (p : I) (root : V) :
    siteSusceptibility G p root ≤
      ∫⁻ eta, siteOpenPathWitnessMass G root eta
        ∂setBer((Set.univ : Set V), p) := by
  unfold siteSusceptibility
  exact lintegral_mono fun eta ↦
    siteClusterSizeENNReal_le_openPathWitnessMass G root eta

theorem lintegral_siteOpenPathWitnessMass_eq_tsum
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (p : I) (root : V) :
    (∫⁻ eta, siteOpenPathWitnessMass G root eta
        ∂setBer((Set.univ : Set V), p)) =
      ∑' q : SiteRootedPathCode G root,
        setBer((Set.univ : Set V), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk q)) := by
  classical
  unfold siteOpenPathWitnessMass siteOpenPathCodes
  rw [lintegral_tsum]
  · apply tsum_congr
    intro q
    change (∫⁻ eta : Set V,
      (siteWalkOpenEvent (siteRootedPathCodeWalk q)).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) eta
        ∂setBer((Set.univ : Set V), p)) = _
    rw [lintegral_indicator
      (measurableSet_siteWalkOpenEvent (siteRootedPathCodeWalk q))]
    simp
  · intro q
    exact (measurable_const.indicator
      (measurableSet_siteWalkOpenEvent
        (siteRootedPathCodeWalk q))).aemeasurable

/-- ENNReal form of the exact open-path probability. -/
theorem setBernoulli_siteWalkOpenEvent_of_isPath
    {V : Type*} [Countable V] [DecidableEq V]
    {G : SimpleGraph V} {x y : V} (w : G.Walk x y)
    (hw : w.IsPath) (p : I) :
    setBer((Set.univ : Set V), p) (siteWalkOpenEvent w) =
      ENNReal.ofReal ((p : ℝ) ^ (w.length + 1)) := by
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (pow_nonneg p.2.1 _)]
  simpa only [Measure.real] using
    setBernoulli_real_siteWalkOpenEvent_of_isPath w hw p

theorem measure_siteOpenPathCode
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (p : I) (root : V)
    (q : SiteRootedPathCode G root) :
    setBer((Set.univ : Set V), p)
        (siteWalkOpenEvent (siteRootedPathCodeWalk q)) =
      ENNReal.ofReal ((p : ℝ) ^ (q.1 + 1)) := by
  have hmem := Finset.mem_filter.mp q.2.2
  have hlen : (siteRootedPathCodeWalk q).length = q.1 :=
    (SimpleGraph.mem_rootedWalks_iff G).mp hmem.1
  rw [setBernoulli_siteWalkOpenEvent_of_isPath
    (siteRootedPathCodeWalk q) hmem.2 p, hlen]

theorem card_siteRootedPathCode_fiber_le
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (root : V) (n : ℕ) :
    Fintype.card ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath) ≤ D ^ n := by
  calc
    Fintype.card ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath) =
        ((G.rootedWalks n root).filter fun q ↦ q.2.IsPath).card := by simp
    _ ≤ (G.rootedWalks n root).card := Finset.card_filter_le _ _
    _ ≤ D ^ n := SimpleGraph.card_rootedWalks_le G hdegree n root

theorem tsum_measure_siteOpenPathCode_le_geometric
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (p : I) (root : V) :
    (∑' q : SiteRootedPathCode G root,
        setBer((Set.univ : Set V), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk q))) ≤
      ∑' n : ℕ, (D : ℝ≥0∞) ^ n *
        (ENNReal.ofReal (p : ℝ)) ^ (n + 1) := by
  change (∑' q : Σ n : ℕ,
      ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath),
        setBer((Set.univ : Set V), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk q))) ≤ _
  rw [ENNReal.tsum_sigma']
  apply ENNReal.tsum_le_tsum
  intro n
  rw [tsum_fintype]
  calc
    (∑ q : ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath),
        setBer((Set.univ : Set V), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk ⟨n, q⟩))) =
        ∑ _q : ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath),
          (ENNReal.ofReal (p : ℝ)) ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [measure_siteOpenPathCode G p root ⟨n, q⟩,
        ENNReal.ofReal_pow p.2.1]
    _ = (Fintype.card
          ↥((G.rootedWalks n root).filter fun q ↦ q.2.IsPath) : ℕ) *
          (ENNReal.ofReal (p : ℝ)) ^ (n + 1) := by simp
    _ ≤ (D ^ n : ℕ) * (ENNReal.ofReal (p : ℝ)) ^ (n + 1) := by
      exact mul_le_mul_right'
        (by exact_mod_cast card_siteRootedPathCode_fiber_le G hdegree root n) _
    _ = (D : ℝ≥0∞) ^ n * (ENNReal.ofReal (p : ℝ)) ^ (n + 1) := by
      norm_cast

/-- Bounded degree and `D p < 1` imply finite mean site-cluster size. -/
theorem siteSusceptibility_lt_top_of_degree_mul_lt_one
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    {D : ℕ} (hdegree : ∀ x, G.degree x ≤ D)
    (p : I) (hp : (D : ℝ) * (p : ℝ) < 1) (root : V) :
    siteSusceptibility G p root < ⊤ := by
  let pE : ℝ≥0∞ := ENNReal.ofReal (p : ℝ)
  let r : ℝ≥0∞ := (D : ℝ≥0∞) * pE
  have hr : r < 1 := by
    rw [show r = ENNReal.ofReal ((D : ℝ) * (p : ℝ)) by
      simp [r, pE, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ D)]]
    exact (ENNReal.ofReal_lt_one).2 hp
  have hgeom : (∑' n : ℕ,
      (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) < ⊤ := by
    have heq : (∑' n : ℕ,
        (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) =
        pE * (1 - r)⁻¹ := by
      calc
        (∑' n : ℕ, (D : ℝ≥0∞) ^ n * pE ^ (n + 1)) =
            ∑' n : ℕ, pE * r ^ n := by
          apply tsum_congr
          intro n
          simp only [r, pow_succ']
          ring
        _ = pE * ∑' n : ℕ, r ^ n := ENNReal.tsum_mul_left
        _ = pE * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric]
    rw [heq]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [ENNReal.inv_lt_top]
    exact tsub_pos_iff_lt.mpr hr
  calc
    siteSusceptibility G p root ≤
        ∫⁻ eta, siteOpenPathWitnessMass G root eta
          ∂setBer((Set.univ : Set V), p) :=
      siteSusceptibility_le_lintegral_openPathWitnessMass G p root
    _ = ∑' q : SiteRootedPathCode G root,
        setBer((Set.univ : Set V), p)
          (siteWalkOpenEvent (siteRootedPathCodeWalk q)) :=
      lintegral_siteOpenPathWitnessMass_eq_tsum G p root
    _ ≤ ∑' n : ℕ, (D : ℝ≥0∞) ^ n * pE ^ (n + 1) := by
      simpa [pE] using tsum_measure_siteOpenPathCode_le_geometric
        G hdegree p root
    _ < ⊤ := hgeom

end Percolation
