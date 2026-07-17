import Percolation.Critical.StaticCoalescence
import Percolation.Critical.GhostField

/-!
# The radius and diameter of a finite open cluster

This file introduces the finite-cluster events used in Grimmett Chapter 8, §§8.4--8.5.  The
diameter is encoded by countable intersections of two-point connection events.  This avoids a
junk-value convention for infinite clusters and makes measurability immediate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The event in (8.19): the origin reaches the coordinate-box surface at radius `n`, but its
open cluster is finite. -/
def finiteBoxRadiusEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  connectionToBoxSurfaceEvent d n cubicOrigin ∩ finiteClusterEvent d

theorem measurableSet_finiteBoxRadiusEvent (d n : ℕ) :
    MeasurableSet (finiteBoxRadiusEvent d n) :=
  (measurableSet_connectionToBoxSurfaceEvent d n cubicOrigin).inter
    (measurableSet_finiteClusterEvent d)

/-- Probability of the finite-radius event in (8.19). -/
noncomputable def finiteBoxRadiusProbability (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (finiteBoxRadiusEvent d n)

theorem finiteBoxRadiusProbability_nonneg (d : ℕ) (p : I) (n : ℕ) :
    0 ≤ finiteBoxRadiusProbability d p n := measureReal_nonneg

theorem finiteBoxRadiusProbability_le_one (d : ℕ) (p : I) (n : ℕ) :
    finiteBoxRadiusProbability d p n ≤ 1 := measureReal_le_one

/-- All pairs of vertices connected to the origin are at coordinate `L∞` distance at most
`n`.  This is the totalized event `diam(C) ≤ n`; no finiteness is built into it. -/
def clusterLInfDiameterAtMostEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  ⋂ x : Cubic d, ⋂ y : Cubic d,
    if n < cubicLInfDist x y then
      (connectionEvent d cubicOrigin x ∩ connectionEvent d cubicOrigin y)ᶜ
    else Set.univ

theorem measurableSet_clusterLInfDiameterAtMostEvent (d n : ℕ) :
    MeasurableSet (clusterLInfDiameterAtMostEvent d n) := by
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  split_ifs
  · exact ((measurableSet_connectionEvent d cubicOrigin x).inter
      (measurableSet_connectionEvent d cubicOrigin y)).compl
  · exact MeasurableSet.univ

theorem mem_clusterLInfDiameterAtMostEvent_iff
    {d n : ℕ} {omega : EdgeConfiguration d} :
    omega ∈ clusterLInfDiameterAtMostEvent d n ↔
      ∀ x ∈ cubicOpenCluster d omega, ∀ y ∈ cubicOpenCluster d omega,
        cubicLInfDist x y ≤ n := by
  simp only [clusterLInfDiameterAtMostEvent, Set.mem_iInter]
  constructor
  · intro h x hx y hy
    by_contra hdist
    have hnlt : n < cubicLInfDist x y := Nat.lt_of_not_ge hdist
    have hxy := h x y
    rw [if_pos hnlt, Set.mem_compl_iff, Set.mem_inter_iff] at hxy
    apply hxy
    simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq] using And.intro hx hy
  · intro h x y
    by_cases hdist : n < cubicLInfDist x y
    · rw [if_pos hdist, Set.mem_compl_iff, Set.mem_inter_iff]
      intro hconn
      have hx : x ∈ cubicOpenCluster d omega := by
        simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
          Set.mem_setOf_eq] using hconn.1
      have hy : y ∈ cubicOpenCluster d omega := by
        simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
          Set.mem_setOf_eq] using hconn.2
      exact (Nat.not_lt_of_ge (h x hx y hy)) hdist
    · rw [if_neg hdist]
      exact Set.mem_univ omega

/-- Totalized numerical diameter.  Infinite clusters are assigned zero; all source-facing uses
pair this function with `finiteClusterEvent`, so the fallback value is never observed. -/
noncomputable def clusterLInfDiameter (d : ℕ) (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact if h : (cubicOpenCluster d omega).Finite then
    h.toFinset.sup fun x ↦ h.toFinset.sup fun y ↦ cubicLInfDist x y
  else 0

theorem clusterLInfDiameter_eq_sup_of_finite
    {d : ℕ} {omega : EdgeConfiguration d}
    (h : (cubicOpenCluster d omega).Finite) :
    clusterLInfDiameter d omega =
      h.toFinset.sup fun x ↦ h.toFinset.sup fun y ↦ cubicLInfDist x y := by
  simp [clusterLInfDiameter, h]

theorem mem_clusterLInfDiameterAtMostEvent_iff_of_finite
    {d n : ℕ} {omega : EdgeConfiguration d}
    (hfinite : (cubicOpenCluster d omega).Finite) :
    omega ∈ clusterLInfDiameterAtMostEvent d n ↔
      clusterLInfDiameter d omega ≤ n := by
  rw [mem_clusterLInfDiameterAtMostEvent_iff,
    clusterLInfDiameter_eq_sup_of_finite hfinite]
  constructor
  · intro h
    apply Finset.sup_le
    intro x hx
    apply Finset.sup_le
    intro y hy
    exact h x (by simpa using hx) y (by simpa using hy)
  · intro h x hx y hy
    have hx' : x ∈ hfinite.toFinset := by simpa using hx
    have hy' : y ∈ hfinite.toFinset := by simpa using hy
    calc
      cubicLInfDist x y ≤ hfinite.toFinset.sup (fun z ↦ cubicLInfDist x z) :=
        Finset.le_sup hy'
      _ ≤ hfinite.toFinset.sup
          (fun z ↦ hfinite.toFinset.sup fun w ↦ cubicLInfDist z w) :=
        Finset.le_sup (s := hfinite.toFinset)
          (f := fun z ↦ hfinite.toFinset.sup fun w ↦ cubicLInfDist z w) hx'
      _ ≤ n := h

/-- Exact finite-cluster `L∞` diameter.  At diameter zero the predecessor exclusion is omitted. -/
def finiteClusterLInfDiameterEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  finiteClusterEvent d ∩ clusterLInfDiameterAtMostEvent d n ∩
    if n = 0 then Set.univ else (clusterLInfDiameterAtMostEvent d (n - 1))ᶜ

theorem measurableSet_finiteClusterLInfDiameterEvent (d n : ℕ) :
    MeasurableSet (finiteClusterLInfDiameterEvent d n) := by
  rw [finiteClusterLInfDiameterEvent]
  apply ((measurableSet_finiteClusterEvent d).inter
    (measurableSet_clusterLInfDiameterAtMostEvent d n)).inter
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_clusterLInfDiameterAtMostEvent d (n - 1)).compl

theorem mem_finiteClusterLInfDiameterEvent_iff_of_pos
    {d n : ℕ} (hn : 0 < n) {omega : EdgeConfiguration d} :
    omega ∈ finiteClusterLInfDiameterEvent d n ↔
      (cubicOpenCluster d omega).Finite ∧
      (∀ x ∈ cubicOpenCluster d omega, ∀ y ∈ cubicOpenCluster d omega,
        cubicLInfDist x y ≤ n) ∧
      ∃ x ∈ cubicOpenCluster d omega, ∃ y ∈ cubicOpenCluster d omega,
        cubicLInfDist x y = n := by
  simp only [finiteClusterLInfDiameterEvent, if_neg hn.ne', Set.mem_inter_iff,
    Set.mem_compl_iff]
  rw [mem_clusterLInfDiameterAtMostEvent_iff,
    mem_clusterLInfDiameterAtMostEvent_iff]
  constructor
  · rintro ⟨⟨hfinite, hle⟩, hnot⟩
    change (cubicOpenCluster d omega).Finite at hfinite
    simp only [not_forall, not_le] at hnot
    obtain ⟨x, hx, y, hy, hdist⟩ := hnot
    exact ⟨hfinite, hle, x, hx, y, hy,
      Nat.le_antisymm (hle x hx y hy) (by omega)⟩
  · rintro ⟨hfinite, hle, x, hx, y, hy, hdist⟩
    refine ⟨⟨hfinite, hle⟩, ?_⟩
    intro hpred
    have := hpred x hx y hy
    omega

theorem mem_finiteClusterLInfDiameterEvent_iff
    {d n : ℕ} {omega : EdgeConfiguration d} :
    omega ∈ finiteClusterLInfDiameterEvent d n ↔
      (cubicOpenCluster d omega).Finite ∧ clusterLInfDiameter d omega = n := by
  cases n with
  | zero =>
      change (((cubicOpenCluster d omega).Finite ∧
        omega ∈ clusterLInfDiameterAtMostEvent d 0) ∧ True) ↔
          (cubicOpenCluster d omega).Finite ∧ clusterLInfDiameter d omega = 0
      constructor
      · rintro ⟨⟨hfinite, hdiam⟩, _⟩
        exact ⟨hfinite, Nat.eq_zero_of_le_zero
          ((mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mp hdiam)⟩
      · rintro ⟨hfinite, hdiam⟩
        refine ⟨⟨hfinite,
          (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mpr ?_⟩, trivial⟩
        omega
  | succ n =>
      rw [mem_finiteClusterLInfDiameterEvent_iff_of_pos (Nat.succ_pos n)]
      constructor
      · rintro ⟨hfinite, _hle, x, hx, y, hy, hxy⟩
        have hAtMost : omega ∈ clusterLInfDiameterAtMostEvent d (n + 1) :=
          (mem_clusterLInfDiameterAtMostEvent_iff.mpr _hle)
        have hupper :=
          (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mp hAtMost
        have hlower : n + 1 ≤ clusterLInfDiameter d omega := by
          rw [clusterLInfDiameter_eq_sup_of_finite hfinite]
          have hx' : x ∈ hfinite.toFinset := by simpa using hx
          have hy' : y ∈ hfinite.toFinset := by simpa using hy
          calc
            n + 1 = cubicLInfDist x y := hxy.symm
            _ ≤ hfinite.toFinset.sup (fun z ↦ cubicLInfDist x z) :=
              Finset.le_sup hy'
            _ ≤ hfinite.toFinset.sup
                (fun z ↦ hfinite.toFinset.sup fun w ↦ cubicLInfDist z w) :=
              Finset.le_sup (s := hfinite.toFinset)
                (f := fun z ↦ hfinite.toFinset.sup fun w ↦ cubicLInfDist z w) hx'
        exact ⟨hfinite, Nat.le_antisymm hupper hlower⟩
      · rintro ⟨hfinite, hdiam⟩
        have hAtMost : omega ∈ clusterLInfDiameterAtMostEvent d (Nat.succ n) :=
          (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mpr hdiam.le
        have hle := mem_clusterLInfDiameterAtMostEvent_iff.mp hAtMost
        have hsNonempty : hfinite.toFinset.Nonempty := by
          refine ⟨cubicOrigin, ?_⟩
          simp only [Set.Finite.mem_toFinset]
          exact ⟨.nil, by simp [walkIsOpen]⟩
        obtain ⟨x, hx, hxSup⟩ := Finset.exists_mem_eq_sup hfinite.toFinset
          hsNonempty (fun z ↦ hfinite.toFinset.sup fun w ↦ cubicLInfDist z w)
        obtain ⟨y, hy, hySup⟩ := Finset.exists_mem_eq_sup hfinite.toFinset
          hsNonempty (fun w ↦ cubicLInfDist x w)
        have hdiamSup := clusterLInfDiameter_eq_sup_of_finite hfinite
        have hxy : cubicLInfDist x y = Nat.succ n := by
          rw [hdiamSup, hxSup, hySup] at hdiam
          exact hdiam
        exact ⟨hfinite, hle, x, (by simpa using hx), y, (by simpa using hy), hxy⟩

/-- Exact-diameter probability used in Lemma 8.27. -/
noncomputable def finiteClusterLInfDiameterProbability
    (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (finiteClusterLInfDiameterEvent d n)

theorem finiteClusterLInfDiameterProbability_nonneg (d : ℕ) (p : I) (n : ℕ) :
    0 ≤ finiteClusterLInfDiameterProbability d p n := measureReal_nonneg

/-- Tail of the exact finite-diameter distribution. -/
def finiteClusterLInfDiameterTailEvent (d n : ℕ) : Set (EdgeConfiguration d) :=
  ⋃ k : {k : ℕ // n ≤ k}, finiteClusterLInfDiameterEvent d k.1

theorem measurableSet_finiteClusterLInfDiameterTailEvent (d n : ℕ) :
    MeasurableSet (finiteClusterLInfDiameterTailEvent d n) :=
  MeasurableSet.iUnion fun k ↦ measurableSet_finiteClusterLInfDiameterEvent d k.1

noncomputable def finiteClusterLInfDiameterTailProbability
    (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (finiteClusterLInfDiameterTailEvent d n)

theorem finiteClusterLInfDiameterTailEvent_eq
    (d n : ℕ) :
    finiteClusterLInfDiameterTailEvent d n =
      finiteClusterEvent d ∩ (if n = 0 then Set.univ else
        (clusterLInfDiameterAtMostEvent d (n - 1))ᶜ) := by
  ext omega
  simp only [finiteClusterLInfDiameterTailEvent, Set.mem_iUnion,
    mem_finiteClusterLInfDiameterEvent_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨k, hfinite, hk⟩
    refine ⟨hfinite, ?_⟩
    split_ifs with hn
    · exact Set.mem_univ omega
    · rw [Set.mem_compl_iff]
      intro hpred
      have hle := (mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mp hpred
      omega
  · rintro ⟨hfinite, htail⟩
    let k := clusterLInfDiameter d omega
    have hnk : n ≤ k := by
      split_ifs at htail with hn
      · omega
      · rw [Set.mem_compl_iff] at htail
        by_contra hkn
        have hkpred : k ≤ n - 1 := by omega
        exact htail ((mem_clusterLInfDiameterAtMostEvent_iff_of_finite hfinite).mpr hkpred)
    exact ⟨⟨k, hnk⟩, hfinite, rfl⟩

/-- A source-oriented exact-diameter event: the origin is a leftmost vertex, the first
coordinate width is `n`, and the full `L∞` diameter is at most `n`. -/
def firstCoordinateAnchoredDiameterEvent
    (d : ℕ) (hd : 0 < d) (n : ℕ) : Set (EdgeConfiguration d) :=
  finiteClusterEvent d ∩ clusterLInfDiameterAtMostEvent d n ∩
    (⋂ x : Cubic d, if x ⟨0, hd⟩ < 0 ∨ n < x ⟨0, hd⟩ then
      (connectionEvent d cubicOrigin x)ᶜ else Set.univ) ∩
    (⋃ x : Cubic d, if x ⟨0, hd⟩ = n then
      connectionEvent d cubicOrigin x else ∅)

theorem measurableSet_firstCoordinateAnchoredDiameterEvent
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    MeasurableSet (firstCoordinateAnchoredDiameterEvent d hd n) := by
  rw [firstCoordinateAnchoredDiameterEvent]
  have hbounds : MeasurableSet
      (⋂ x : Cubic d, if x ⟨0, hd⟩ < 0 ∨ n < x ⟨0, hd⟩ then
        (connectionEvent d cubicOrigin x)ᶜ else Set.univ) := by
    apply MeasurableSet.iInter
    intro x
    split_ifs
    · exact (measurableSet_connectionEvent d cubicOrigin x).compl
    · exact MeasurableSet.univ
  have hreaches : MeasurableSet
      (⋃ x : Cubic d, if x ⟨0, hd⟩ = n then
        connectionEvent d cubicOrigin x else ∅) := by
    apply MeasurableSet.iUnion
    intro x
    split_ifs
    · exact measurableSet_connectionEvent d cubicOrigin x
    · exact MeasurableSet.empty
  exact (((measurableSet_finiteClusterEvent d).inter
    (measurableSet_clusterLInfDiameterAtMostEvent d n)).inter hbounds).inter hreaches

theorem firstCoordinateAnchoredDiameterEvent_subset_finiteBoxRadiusEvent
    {d n : ℕ} (hd : 0 < d) :
    firstCoordinateAnchoredDiameterEvent d hd n ⊆ finiteBoxRadiusEvent d n := by
  intro omega homega
  rcases homega with ⟨⟨⟨hfinite, hdiam⟩, hbounds⟩, hreaches⟩
  refine ⟨?_, hfinite⟩
  simp only [Set.mem_iUnion] at hreaches
  obtain ⟨x, hx⟩ := hreaches
  have hxn : x ⟨0, hd⟩ = (n : ℤ) := by
    by_contra hne
    rw [if_neg hne] at hx
    exact hx.elim
  rw [if_pos hxn] at hx
  have hxCluster : x ∈ cubicOpenCluster d omega := by
    simpa only [connectionEvent, cubicOpenCluster, cubicOpenClusterFrom,
      Set.mem_setOf_eq] using hx
  have hxBox : x ∈ cubicMetricBox d cubicOrigin n := by
    have hdist := (mem_clusterLInfDiameterAtMostEvent_iff.mp hdiam)
      cubicOrigin (by exact ⟨.nil, by simp [walkIsOpen]⟩) x hxCluster
    exact mem_cubicMetricBox_iff_lInfDist_le.mpr hdist
  have hxSurface : x ∈ cubicBoxSurface d cubicOrigin n := by
    apply mem_cubicBoxSurface.mpr
    apply le_antisymm
    · exact mem_cubicMetricBox_iff_lInfDist_le.mp hxBox
    · have hcoord := cubicLInfDist_coord_le cubicOrigin x ⟨0, hd⟩
      simpa [cubicOrigin, hxn] using hcoord
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion]
  refine ⟨x, hxSurface, ?_⟩
  obtain ⟨w, hwOpen⟩ := hxCluster
  refine ⟨w, hwOpen, ?_⟩
  intro e he
  apply walkEdgeFinset_subset_cubicBoxEdges_of_support w
  · intro z hz
    have hzCluster : z ∈ cubicOpenCluster d omega :=
      mem_cubicOpenClusterFrom_of_mem_support hwOpen hz
    exact mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_clusterLInfDiameterAtMostEvent_iff.mp hdiam)
        cubicOrigin (by exact ⟨.nil, by simp [walkIsOpen]⟩) z hzCluster)
  · exact he

/-- The lower deterministic comparison underlying (8.40). -/
theorem firstCoordinateAnchoredDiameter_probability_le_finiteBoxRadiusProbability
    {d n : ℕ} (hd : 0 < d) (p : I) :
    (bernoulliBondMeasure d p).real (firstCoordinateAnchoredDiameterEvent d hd n) ≤
      finiteBoxRadiusProbability d p n :=
  measureReal_mono (firstCoordinateAnchoredDiameterEvent_subset_finiteBoxRadiusEvent hd)

/-- The upper deterministic comparison in (8.39): reaching radius `n` with a finite cluster
forces that cluster to have diameter at least `n`. -/
theorem finiteBoxRadiusEvent_disjoint_diameterAtMost_pred
    {d n : ℕ} (hn : 0 < n) :
    Disjoint (finiteBoxRadiusEvent d n) (clusterLInfDiameterAtMostEvent d (n - 1)) := by
  rw [Set.disjoint_left]
  intro omega hradius hdiam
  obtain ⟨hsurface, _hfinite⟩ := hradius
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion] at hsurface
  obtain ⟨x, hxSurface, w, hwOpen, _hwBox⟩ := hsurface
  have hxCluster : x ∈ cubicOpenCluster d omega := ⟨w, hwOpen⟩
  have horigin : cubicOrigin ∈ cubicOpenCluster d omega :=
    ⟨.nil, by simp [walkIsOpen]⟩
  have hle := (mem_clusterLInfDiameterAtMostEvent_iff.mp hdiam)
    cubicOrigin horigin x hxCluster
  rw [mem_cubicBoxSurface] at hxSurface
  omega

theorem finiteBoxRadiusEvent_subset_finiteClusterLInfDiameterTailEvent
    (d n : ℕ) :
    finiteBoxRadiusEvent d n ⊆ finiteClusterLInfDiameterTailEvent d n := by
  rw [finiteClusterLInfDiameterTailEvent_eq]
  intro omega homega
  refine ⟨homega.2, ?_⟩
  by_cases hn : n = 0
  · rw [if_pos hn]
    exact Set.mem_univ omega
  · rw [if_neg hn, Set.mem_compl_iff]
    intro hdiam
    exact Set.disjoint_left.mp
      (finiteBoxRadiusEvent_disjoint_diameterAtMost_pred (Nat.pos_of_ne_zero hn))
        homega hdiam

/-- Probability form of the first inequality in (8.39). -/
theorem finiteBoxRadiusProbability_le_finiteClusterLInfDiameterTailProbability
    (d : ℕ) (p : I) (n : ℕ) :
    finiteBoxRadiusProbability d p n ≤
      finiteClusterLInfDiameterTailProbability d p n :=
  measureReal_mono (finiteBoxRadiusEvent_subset_finiteClusterLInfDiameterTailEvent d n)

end Percolation
