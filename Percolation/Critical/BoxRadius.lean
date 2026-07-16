import Percolation.Critical.RadiusBlock
import Percolation.Critical.SusceptibilityThreshold
import Percolation.Planar.Peierls

/-!
# Coordinate-box radius events

This file begins the formalization of Chapter 6 of Grimmett's *Percolation*.  Grimmett uses
coordinate boxes in Chapter 6, whereas Chapter 5 uses graph-metric (Manhattan) balls.  We keep
the two notions separate and record the norm comparison explicitly.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators ENNReal

/-! ### The coordinate `L∞` metric -/

/-- Coordinate `L∞` distance on the cubic lattice. -/
def cubicLInfDist {d : ℕ} (x y : Cubic d) : ℕ :=
  Finset.univ.sup fun i : Fin d ↦ (y i - x i).natAbs

@[simp]
theorem cubicLInfDist_self {d : ℕ} (x : Cubic d) : cubicLInfDist x x = 0 := by
  simp [cubicLInfDist]

theorem cubicLInfDist_comm {d : ℕ} (x y : Cubic d) :
    cubicLInfDist x y = cubicLInfDist y x := by
  unfold cubicLInfDist
  apply Finset.sup_congr rfl
  intro i _hi
  rw [show x i - y i = -(y i - x i) by omega, Int.natAbs_neg]

/-- Every coordinate displacement is bounded by the `L∞` distance. -/
theorem cubicLInfDist_coord_le {d : ℕ} (x y : Cubic d) (i : Fin d) :
    (y i - x i).natAbs ≤ cubicLInfDist x y := by
  exact Finset.le_sup (f := fun j : Fin d ↦ (y j - x j).natAbs) (Finset.mem_univ i)

/-- The coordinate `L∞` distance is at most the Manhattan distance. -/
theorem cubicLInfDist_le_l1Dist {d : ℕ} (x y : Cubic d) :
    cubicLInfDist x y ≤ cubicL1Dist x y := by
  rw [cubicLInfDist]
  apply Finset.sup_le
  intro i _hi
  exact cubicL1Dist_coord_le x y i

/-- Triangle inequality for coordinate `L∞` distance. -/
theorem cubicLInfDist_triangle {d : ℕ} (x y z : Cubic d) :
    cubicLInfDist x z ≤ cubicLInfDist x y + cubicLInfDist y z := by
  rw [cubicLInfDist]
  apply Finset.sup_le
  intro i _hi
  calc
    (z i - x i).natAbs ≤ (y i - x i).natAbs + (z i - y i).natAbs := by
      have h := Int.natAbs_add_le (y i - x i) (z i - y i)
      convert h using 1 <;> omega
    _ ≤ cubicLInfDist x y + cubicLInfDist y z :=
      Nat.add_le_add (cubicLInfDist_coord_le x y i) (cubicLInfDist_coord_le y z i)

/-- A nearest-neighbor step has coordinate `L∞` length at most one. -/
theorem cubicLInfDist_stepFrom_le_one {d : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicLInfDist x (cubicStepFrom x a) ≤ 1 := by
  rw [← cubicL1Dist_stepFrom x a]
  exact cubicLInfDist_le_l1Dist x (cubicStepFrom x a)

theorem cubicLInfDist_translate {d : ℕ} (x y u v : Cubic d) :
    cubicLInfDist (cubicTranslate x y u) (cubicTranslate x y v) = cubicLInfDist u v := by
  unfold cubicLInfDist cubicTranslate
  apply Finset.sup_congr rfl
  intro i _hi
  congr 1
  omega

/-- The Manhattan distance is at most `d` times the coordinate `L∞` distance. -/
theorem cubicL1Dist_le_card_mul_lInfDist {d : ℕ} (x y : Cubic d) :
    cubicL1Dist x y ≤ d * cubicLInfDist x y := by
  rw [cubicL1Dist]
  calc
    (∑ i : Fin d, (y i - x i).natAbs) ≤
        ∑ _i : Fin d, cubicLInfDist x y := by
      apply Finset.sum_le_sum
      intro i _hi
      exact cubicLInfDist_coord_le x y i
    _ = d * cubicLInfDist x y := by simp

/-- Membership in the existing coordinate box is exactly an `L∞`-distance bound. -/
theorem mem_cubicMetricBox_iff_lInfDist_le {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicMetricBox d x n ↔ cubicLInfDist x y ≤ n := by
  constructor
  · intro hy
    rw [cubicLInfDist]
    apply Finset.sup_le
    intro i _hi
    have hi := mem_cubicMetricBox.mp hy i
    by_cases hnonneg : 0 ≤ y i - x i
    · have hiz : ((y i - x i).natAbs : ℤ) ≤ (n : ℤ) := by
        rw [Int.natAbs_of_nonneg hnonneg]
        omega
      exact_mod_cast hiz
    · have hz' : 0 ≤ -(y i - x i) := by omega
      rw [← Int.natAbs_neg]
      have hiz : ((-(y i - x i)).natAbs : ℤ) ≤ (n : ℤ) := by
        rw [Int.natAbs_of_nonneg hz']
        omega
      exact_mod_cast hiz
  · intro hdist
    rw [mem_cubicMetricBox]
    intro i
    have hi := (cubicLInfDist_coord_le x y i).trans hdist
    by_cases hnonneg : 0 ≤ y i - x i
    · have hiz : y i - x i ≤ (n : ℤ) := by
        have hiz' : ((y i - x i).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
        rwa [Int.natAbs_of_nonneg hnonneg] at hiz'
      omega
    · have hz' : 0 ≤ -(y i - x i) := by omega
      have hiz : -(y i - x i) ≤ (n : ℤ) := by
        rw [← Int.natAbs_neg] at hi
        have hiz' : ((-(y i - x i)).natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
        rwa [Int.natAbs_of_nonneg hz'] at hiz'
      omega

/-! ### Coordinate-box surfaces and connection events -/

/-- The boundary of the coordinate box of radius `n` centered at `x`. -/
noncomputable def cubicBoxSurface (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d x n).filter fun y ↦ cubicLInfDist x y = n

@[simp]
theorem mem_cubicBoxSurface {d n : ℕ} {x y : Cubic d} :
    y ∈ cubicBoxSurface d x n ↔ cubicLInfDist x y = n := by
  rw [cubicBoxSurface, Finset.mem_filter, mem_cubicMetricBox_iff_lInfDist_le]
  exact and_iff_right_of_imp fun h ↦ h.le

theorem cubicTranslate_mem_boxSurface_iff {d n : ℕ} (x y u : Cubic d) :
    cubicTranslate x y u ∈ cubicBoxSurface d y n ↔ u ∈ cubicBoxSurface d x n := by
  rw [mem_cubicBoxSurface, mem_cubicBoxSurface]
  rw [show cubicLInfDist y (cubicTranslate x y u) = cubicLInfDist x u by
    simpa using cubicLInfDist_translate x y x u]

/-- One of the `2d` coordinate faces of a cubic box. -/
noncomputable def cubicBoxFace (d : ℕ) (x : Cubic d) (n : ℕ)
    (i : Fin d) (positive : Bool) : Finset (Cubic d) :=
  Fintype.piFinset fun j : Fin d ↦
    if j = i then
      {if positive then x j + n else x j - n}
    else
      Finset.Icc (x j - n) (x j + n)

@[simp]
theorem mem_cubicBoxFace {d n : ℕ} {x y : Cubic d} {i : Fin d} {positive : Bool} :
    y ∈ cubicBoxFace d x n i positive ↔
      y i = (if positive then x i + n else x i - n) ∧
        ∀ j, j ≠ i → x j - n ≤ y j ∧ y j ≤ x j + n := by
  classical
  simp only [cubicBoxFace, Fintype.mem_piFinset]
  constructor
  · intro h
    constructor
    · simpa using h i
    · intro j hji
      simpa [hji] using h j
  · rintro ⟨hi, hrest⟩ j
    by_cases hji : j = i
    · subst j
      simpa using hi
    · simpa [hji] using hrest j hji

/-- Each face contains exactly `(2n+1)^(d-1)` vertices. -/
theorem cubicBoxFace_card {d n : ℕ} (x : Cubic d) (i : Fin d) (positive : Bool) :
    (cubicBoxFace d x n i positive).card = (2 * n + 1) ^ (d - 1) := by
  classical
  rw [cubicBoxFace, Fintype.card_piFinset]
  have hterm : ∀ j : Fin d,
      (if j = i then
          ({if positive then x j + n else x j - n} : Finset ℤ)
        else Finset.Icc (x j - n) (x j + n)).card =
        if j = i then 1 else 2 * n + 1 := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, Int.card_Icc]
      omega
  simp_rw [hterm]
  rw [Finset.prod_ite]
  rw [Finset.filter_ne']
  simp

/-- The union of all positive and negative coordinate faces. -/
noncomputable def cubicBoxFaces (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (Cubic d) :=
  Finset.univ.biUnion fun i : Fin d ↦
    cubicBoxFace d x n i true ∪ cubicBoxFace d x n i false

theorem cubicBoxSurface_subset_faces {d n : ℕ} (hd : 0 < d) (x : Cubic d) :
    cubicBoxSurface d x n ⊆ cubicBoxFaces d x n := by
  intro y hy
  let i0 : Fin d := ⟨0, hd⟩
  obtain ⟨i, _hi, hisup⟩ := Finset.exists_mem_eq_sup Finset.univ
    ⟨i0, Finset.mem_univ i0⟩ (fun j : Fin d ↦ (y j - x j).natAbs)
  have hsurface : cubicLInfDist x y = n := mem_cubicBoxSurface.mp hy
  have hcoord : (y i - x i).natAbs = n := by
    rw [cubicLInfDist] at hsurface
    exact hisup.symm.trans hsurface
  have hbox : y ∈ cubicMetricBox d x n :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr hsurface.le
  rw [cubicBoxFaces, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  by_cases hnonneg : 0 ≤ y i - x i
  · apply Finset.mem_union_left
    rw [mem_cubicBoxFace]
    constructor
    · change y i = x i + n
      have hz : (y i - x i : ℤ) = n := by
        have hz' : ((y i - x i).natAbs : ℤ) = (n : ℤ) := by exact_mod_cast hcoord
        rwa [Int.natAbs_of_nonneg hnonneg] at hz'
      omega
    · intro j _hji
      exact mem_cubicMetricBox.mp hbox j
  · apply Finset.mem_union_right
    rw [mem_cubicBoxFace]
    constructor
    · change y i = x i - n
      have hznonneg : 0 ≤ -(y i - x i) := by omega
      have hz : (-(y i - x i) : ℤ) = n := by
        rw [← Int.natAbs_neg] at hcoord
        have hz' : ((-(y i - x i)).natAbs : ℤ) = (n : ℤ) := by exact_mod_cast hcoord
        rwa [Int.natAbs_of_nonneg hznonneg] at hz'
      omega
    · intro j _hji
      exact mem_cubicMetricBox.mp hbox j

/-- Grimmett's elementary surface estimate, equation (6.28). -/
theorem cubicBoxSurface_card_le {d n : ℕ} (hd : 0 < d) (x : Cubic d) :
    (cubicBoxSurface d x n).card ≤ 2 * d * (2 * n + 1) ^ (d - 1) := by
  classical
  calc
    (cubicBoxSurface d x n).card ≤ (cubicBoxFaces d x n).card :=
      Finset.card_le_card (cubicBoxSurface_subset_faces hd x)
    _ ≤ ∑ i : Fin d,
        (cubicBoxFace d x n i true ∪ cubicBoxFace d x n i false).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin d,
        ((cubicBoxFace d x n i true).card + (cubicBoxFace d x n i false).card) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.card_union_le (cubicBoxFace d x n i true)
        (cubicBoxFace d x n i false)
    _ = 2 * d * (2 * n + 1) ^ (d - 1) := by
      simp [cubicBoxFace_card]
      ring

@[simp]
theorem cubicBoxSurface_zero (d : ℕ) (x : Cubic d) :
    cubicBoxSurface d x 0 = {x} := by
  ext y
  rw [mem_cubicBoxSurface, Finset.mem_singleton]
  constructor
  · intro h
    apply funext
    intro i
    have hi := cubicLInfDist_coord_le x y i
    rw [h] at hi
    have hz : (y i - x i).natAbs = 0 := Nat.eq_zero_of_le_zero hi
    have hz' : y i - x i = 0 := Int.natAbs_eq_zero.mp hz
    omega
  · rintro rfl
    simp

/-- All cubic edges with both endpoints in the coordinate box.  This is the finite support
used by Chapter 6 box-radius events. -/
noncomputable def cubicBoxEdges (d : ℕ) (x : Cubic d) (n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBox d x n).biUnion fun y ↦
    ((Finset.univ.filter fun a : CubicDirection d ↦
        cubicStepFrom y a ∈ cubicMetricBox d x n).image fun a ↦ cubicStepEdge y a)

theorem cubicStepEdge_mem_cubicBoxEdges {d n : ℕ} {x y : Cubic d}
    {a : CubicDirection d} (hy : y ∈ cubicMetricBox d x n)
    (hya : cubicStepFrom y a ∈ cubicMetricBox d x n) :
    cubicStepEdge y a ∈ cubicBoxEdges d x n := by
  classical
  simp only [cubicBoxEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨y, hy, a, hya, rfl⟩

theorem endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges
    {d n : ℕ} {x z : Cubic d} {e : CubicEdge d}
    (he : e ∈ cubicBoxEdges d x n) (hz : z ∈ (e : Sym2 (Cubic d))) :
    z ∈ cubicMetricBox d x n := by
  classical
  simp only [cubicBoxEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at he
  obtain ⟨y, hy, a, hya, rfl⟩ := he
  rw [cubicStepEdge, Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hy
  · exact hya

/-- If every vertex of a walk lies in a coordinate box, every traversed edge belongs to the
finite edge set of that box. -/
theorem walkEdgeFinset_subset_cubicBoxEdges_of_support {d n : ℕ} {x u v : Cubic d}
    (w : (cubicGraph d).Walk u v)
    (hbox : ∀ z ∈ w.support, z ∈ cubicMetricBox d x n) :
    walkEdgeFinset w ⊆ cubicBoxEdges d x n := by
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  induction w with
  | nil => simp at he
  | @cons u v z huv q ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨a, ha⟩
        have hu : u ∈ cubicMetricBox d x n := hbox u (by simp)
        have hv : v ∈ cubicMetricBox d x n := hbox v (by simp)
        have hedge : e = cubicStepEdge u a := by
          apply Subtype.ext
          simpa [cubicStepEdge, ha] using he
        rw [hedge]
        exact cubicStepEdge_mem_cubicBoxEdges hu (by simpa [ha] using hv)
      · apply ih
        · intro q' hq'
          exact hbox q' (by simp [hq'])
        · exact he

/-- If a walk starts in a coordinate box and every traversed edge is an internal box edge, its
entire support lies in that box. -/
theorem walk_support_subset_cubicMetricBox_of_edges
    {d N : ℕ} {c u v : Cubic d}
    (hu : u ∈ cubicMetricBox d c N) (w : (cubicGraph d).Walk u v)
    (hw : walkEdgeFinset w ⊆ cubicBoxEdges d c N) :
    ∀ z ∈ w.support, z ∈ cubicMetricBox d c N := by
  induction w with
  | nil => simpa using hu
  | @cons u y v huy q ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · let e : CubicEdge d := ⟨s(u, y), by
          rw [SimpleGraph.mem_edgeSet]
          exact huy⟩
        have hew : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huy q) := by
          rw [mem_walkEdgeFinset_iff]
          simp [e]
        have hy : y ∈ cubicMetricBox d c N :=
          endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges (hw hew) (by simp [e])
        have hq : walkEdgeFinset q ⊆ cubicBoxEdges d c N := by
          intro f hf
          apply hw
          rw [mem_walkEdgeFinset_iff] at hf ⊢
          simp [hf]
        exact ih hy hq z hz

/-- First-hitting construction for coordinate boxes.  An open walk ending at `L∞` distance
at least `n` has an open prefix ending on the box surface, entirely supported in the box. -/
theorem exists_open_walk_to_cubicBoxSurface_in_box {d n : ℕ}
    {ω : EdgeConfiguration d} {x y : Cubic d} (w : (cubicGraph d).Walk x y)
    (hopen : walkIsOpen ω w) (hy : n ≤ cubicLInfDist x y) :
    ∃ z, z ∈ cubicBoxSurface d x n ∧
      ω ∈ connectionEventIn d (cubicBoxEdges d x n) x z := by
  classical
  have hexit : ∃ k : ℕ,
      k ≤ w.length ∧ n ≤ cubicLInfDist x (w.getVert k) := by
    exact ⟨w.length, le_rfl, by simpa using hy⟩
  let k := Nat.find hexit
  have hk : k ≤ w.length ∧ n ≤ cubicLInfDist x (w.getVert k) := Nat.find_spec hexit
  have hkdist : cubicLInfDist x (w.getVert k) = n := by
    by_cases hkzero : k = 0
    · have hn : n = 0 := by simpa [hkzero] using hk.2
      simp [hkzero, hn]
    · let j := k - 1
      have hksucc : k = j + 1 := by omega
      have hjfind : j < Nat.find hexit := by change j < k; omega
      have hjlt : cubicLInfDist x (w.getVert j) < n := by
        apply lt_of_not_ge
        intro hj
        exact Nat.find_min hexit hjfind ⟨by omega, hj⟩
      have hjlen : j < w.length := by omega
      have hadj := w.adj_getVert_succ hjlen
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
      have hupper : cubicLInfDist x (w.getVert (j + 1)) ≤ n := by
        calc
          cubicLInfDist x (w.getVert (j + 1)) ≤
              cubicLInfDist x (w.getVert j) +
                cubicLInfDist (w.getVert j) (w.getVert (j + 1)) :=
            cubicLInfDist_triangle _ _ _
          _ ≤ cubicLInfDist x (w.getVert j) + 1 := by
            gcongr
            rw [ha]
            exact cubicLInfDist_stepFrom_le_one _ _
          _ ≤ n := by omega
      rw [hksucc]
      exact le_antisymm hupper (by simpa [hksucc] using hk.2)
  let q := w.take k
  have hq_length : q.length = k := by simp [q, Nat.min_eq_left hk.1]
  have hq_support : ∀ z ∈ q.support, z ∈ cubicMetricBox d x n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
    rcases hz with ⟨m, hm, hmle⟩
    subst z
    have hmk : m ≤ k := by omega
    have hget : q.getVert m = w.getVert m := by simp [q, Nat.min_eq_right hmk]
    rw [hget, mem_cubicMetricBox_iff_lInfDist_le]
    by_cases hmk' : m = k
    · simpa [hmk'] using hkdist.le
    · have hmlt : m < k := lt_of_le_of_ne hmk hmk'
      apply le_of_lt
      apply lt_of_not_ge
      intro hmge
      exact Nat.find_min hexit hmlt ⟨(hmle.trans_eq hq_length).trans hk.1, hmge⟩
  have hqopen : walkIsOpen ω q := by
    intro e he
    apply hopen e
    have he' : e ∈ (w.take k).edges := by simpa [q] using he
    rw [SimpleGraph.Walk.edges_take] at he'
    exact List.Sublist.subset (List.take_sublist k w.edges) he'
  refine ⟨w.getVert k, ?_, q, hqopen, ?_⟩
  · rw [mem_cubicBoxSurface]
    exact hkdist
  · exact walkEdgeFinset_subset_cubicBoxEdges_of_support q hq_support

/-- There is an open connection from `x` to the boundary of its coordinate box, witnessed
inside the finite coordinate box. -/
def boxRadiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ y, y ∈ cubicBoxSurface d x n ∧
    ω ∈ connectionEventIn d (cubicBoxEdges d x n) x y}

/-- The finite-support box event is equivalent to ordinary connection to some surface
vertex. -/
theorem mem_boxRadiusConnectionEvent_iff_exists_connection {d n : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d} :
    ω ∈ boxRadiusConnectionEvent d x n ↔
      ∃ y, y ∈ cubicBoxSurface d x n ∧ ω ∈ connectionEvent d x y := by
  constructor
  · rintro ⟨y, hy, hconn⟩
    exact ⟨y, hy, connectionEventIn_subset d _ x y hconn⟩
  · rintro ⟨y, hy, w, hopen⟩
    exact exists_open_walk_to_cubicBoxSurface_in_box w hopen
      (mem_cubicBoxSurface.mp hy).ge

private theorem cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent
    {d n : ℕ} (x y : Cubic d) (ω : EdgeConfiguration d)
    (h : cubicTranslationConfigurationPullback x y ω ∈ boxRadiusConnectionEvent d x n) :
    ω ∈ boxRadiusConnectionEvent d y n := by
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at h ⊢
  rcases h with ⟨z, hz, w, hw⟩
  let w' := w.map (cubicTranslationIso x y).toHom
  let w'' : (cubicGraph d).Walk y (cubicTranslate x y z) :=
    w'.copy (by simp [cubicTranslationIso_apply]) rfl
  refine ⟨cubicTranslate x y z, (cubicTranslate_mem_boxSurface_iff x y z).2 hz, w'', ?_⟩
  exact (walkIsOpen_copy w' (by simp [cubicTranslationIso_apply]) rfl).mpr
    (walkIsOpen_map_cubicTranslation w hw)

theorem cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent_iff
    {d n : ℕ} (x y : Cubic d) (ω : EdgeConfiguration d) :
    cubicTranslationConfigurationPullback x y ω ∈ boxRadiusConnectionEvent d x n ↔
      ω ∈ boxRadiusConnectionEvent d y n := by
  constructor
  · exact cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent x y ω
  · intro hω
    have hback : cubicTranslationConfigurationPullback y x
        (cubicTranslationConfigurationPullback x y ω) ∈ boxRadiusConnectionEvent d y n := by
      simpa using hω
    exact cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent
      y x (cubicTranslationConfigurationPullback x y ω) hback

theorem dependsOn_boxRadiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    DependsOn (cubicBoxEdges d x n) (boxRadiusConnectionEvent d x n) := by
  intro ω η hagree
  constructor
  · rintro ⟨y, hy, hω⟩
    exact ⟨y, hy, (dependsOn_connectionEventIn d _ x y hagree).mp hω⟩
  · rintro ⟨y, hy, hη⟩
    exact ⟨y, hy, (dependsOn_connectionEventIn d _ x y hagree).mpr hη⟩

theorem measurableSet_boxRadiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    MeasurableSet (boxRadiusConnectionEvent d x n) :=
  (dependsOn_boxRadiusConnectionEvent d x n).measurableSet

theorem isIncreasingEvent_boxRadiusConnectionEvent (d : ℕ) (x : Cubic d) (n : ℕ) :
    IsIncreasingEvent (boxRadiusConnectionEvent d x n) := by
  rintro ω η hωη ⟨y, hy, hconn⟩
  exact ⟨y, hy, isIncreasingEvent_connectionEventIn d _ x y hωη hconn⟩

/-- Connections to coordinate-box surfaces are nested as the radius grows. -/
theorem boxRadiusConnectionEvent_antitone (d : ℕ) (x : Cubic d) :
    Antitone (boxRadiusConnectionEvent d x) := by
  intro m n hmn ω hω
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at hω ⊢
  rcases hω with ⟨y, hy, w, hopen⟩
  obtain ⟨z, hz, hzconn⟩ := exists_open_walk_to_cubicBoxSurface_in_box w hopen
    (hmn.trans_eq (mem_cubicBoxSurface.mp hy).symm)
  exact ⟨z, hz, connectionEventIn_subset d _ x z hzconn⟩

@[simp]
theorem boxRadiusConnectionEvent_zero (d : ℕ) (x : Cubic d) :
    boxRadiusConnectionEvent d x 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  refine ⟨x, by simp, ?_⟩
  refine ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], ?_⟩
  simp [walkEdgeFinset, walkEdgeList]

/-- Grimmett's Chapter 6 box-radius probability `βₚ(n)`. -/
noncomputable def boxRadiusTail (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (boxRadiusConnectionEvent d cubicOrigin n)

@[simp]
theorem boxRadiusTail_zero (d : ℕ) (p : I) : boxRadiusTail d p 0 = 1 := by
  simp [boxRadiusTail]

theorem boxRadiusTail_antitone (d : ℕ) (p : I) : Antitone (boxRadiusTail d p) := by
  intro m n hmn
  exact measureReal_mono (boxRadiusConnectionEvent_antitone d cubicOrigin hmn)

theorem boxRadiusTail_mono_density (d : ℕ) (n : ℕ) :
    Monotone fun p : I ↦ boxRadiusTail d p n := by
  intro p q hpq
  exact (isIncreasingEvent_boxRadiusConnectionEvent d cubicOrigin n).setBernoulli_real_mono
    (measurableSet_boxRadiusConnectionEvent d cubicOrigin n) hpq

/-- The point at distance `n` on the first coordinate axis.  In dimension zero the function is
the unique empty coordinate tuple. -/
def cubicAxisVertex (d n : ℕ) : Cubic d :=
  fun i ↦ if (i : ℕ) = 0 then n else 0

theorem cubicL1Dist_origin_axisVertex {d n : ℕ} (hd : 0 < d) :
    cubicL1Dist (cubicOrigin : Cubic d) (cubicAxisVertex d n) = n := by
  let i0 : Fin d := ⟨0, hd⟩
  rw [cubicL1Dist]
  calc
    (∑ i : Fin d, (cubicAxisVertex d n i - cubicOrigin i).natAbs) =
        (cubicAxisVertex d n i0 - cubicOrigin i0).natAbs := by
      apply Finset.sum_eq_single i0
      · intro j _hj hji
        have hj0 : (j : ℕ) ≠ 0 := by
          intro hj
          apply hji
          apply Fin.ext
          exact hj
        simp [cubicAxisVertex, cubicOrigin, hj0]
      · simp
    _ = n := by simp [cubicAxisVertex, cubicOrigin, i0]

theorem cubicAxisVertex_mem_boxSurface {d n : ℕ} (hd : 0 < d) :
    cubicAxisVertex d n ∈ cubicBoxSurface d cubicOrigin n := by
  rw [mem_cubicBoxSurface]
  apply le_antisymm
  · rw [cubicLInfDist]
    apply Finset.sup_le
    intro i _hi
    by_cases hi0 : (i : ℕ) = 0
    · simp [cubicAxisVertex, cubicOrigin, hi0]
    · simp [cubicAxisVertex, cubicOrigin, hi0]
  · let i0 : Fin d := ⟨0, hd⟩
    have hi := cubicLInfDist_coord_le cubicOrigin (cubicAxisVertex d n) i0
    simpa [cubicAxisVertex, cubicOrigin, i0] using hi

/-- A fixed straight connection gives the elementary lower bound `p^n ≤ βₚ(n)`. -/
theorem pow_le_boxRadiusTail {d n : ℕ} (hd : 0 < d) (p : I) :
    (p : ℝ) ^ n ≤ boxRadiusTail d p n := by
  let y := cubicAxisVertex d n
  obtain ⟨w, hwlen⟩ := exists_cubicWalk_length_eq_l1Dist d cubicOrigin y
  let q : (cubicGraph d).Walk cubicOrigin y := w.toPath
  have hqlen : q.length ≤ n := by
    calc
      q.length ≤ w.length := by
        simpa [q, SimpleGraph.Walk.toPath] using SimpleGraph.Walk.length_bypass_le w
      _ = n := by simpa [y] using hwlen.trans (cubicL1Dist_origin_axisVertex hd)
  have hpow : (p : ℝ) ^ n ≤ (p : ℝ) ^ q.length :=
    pow_le_pow_of_le_one p.property.1 p.property.2 hqlen
  have hsub : {ω : EdgeConfiguration d | walkIsOpen ω q} ⊆
      boxRadiusConnectionEvent d cubicOrigin n := by
    intro ω hω
    rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
    exact ⟨y, cubicAxisVertex_mem_boxSurface hd, q, hω⟩
  calc
    (p : ℝ) ^ n ≤ (p : ℝ) ^ q.length := hpow
    _ = (bernoulliBondMeasure d p).real {ω : EdgeConfiguration d | walkIsOpen ω q} :=
      (bernoulliBondMeasure_real_walkIsOpen p q w.toPath.2.isTrail).symm
    _ ≤ boxRadiusTail d p n := measureReal_mono hsub

theorem boxRadiusTail_pos_of_pos_density {d n : ℕ} (hd : 0 < d) {p : I}
    (hp : 0 < (p : ℝ)) :
    0 < boxRadiusTail d p n :=
  (pow_pos hp n).trans_le (pow_le_boxRadiusTail hd p)

/-- Box-radius probabilities do not depend on the centre. -/
theorem bernoulliBondMeasure_real_boxRadiusConnectionEvent_eq_boxRadiusTail
    {d n : ℕ} (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (boxRadiusConnectionEvent d x n) =
      boxRadiusTail d p n := by
  let T := cubicTranslationConfigurationPullback cubicOrigin x
  have hpre : T ⁻¹' boxRadiusConnectionEvent d cubicOrigin n =
      boxRadiusConnectionEvent d x n := by
    ext ω
    exact cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent_iff
      cubicOrigin x ω
  have hmap := congrArg
    (fun μ : Measure (EdgeConfiguration d) ↦ μ (boxRadiusConnectionEvent d cubicOrigin n))
    (bernoulliBondMeasure_map_cubicTranslationConfigurationPullback p cubicOrigin x)
  change (Measure.map (cubicTranslationConfigurationPullback cubicOrigin x)
      (bernoulliBondMeasure d p)) (boxRadiusConnectionEvent d cubicOrigin n) =
    (bernoulliBondMeasure d p) (boxRadiusConnectionEvent d cubicOrigin n) at hmap
  rw [Measure.map_apply
    (measurable_cubicTranslationConfigurationPullback cubicOrigin x)
    (measurableSet_boxRadiusConnectionEvent d cubicOrigin n), hpre] at hmap
  simpa [MeasureTheory.measureReal_def, boxRadiusTail] using congrArg ENNReal.toReal hmap

/-- Reaching the boundary of a coordinate box of radius `n` entails reaching Manhattan
radius `n`. -/
theorem boxRadiusConnectionEvent_subset_radiusConnectionEvent
    (d : ℕ) (x : Cubic d) (n : ℕ) :
    boxRadiusConnectionEvent d x n ⊆ radiusConnectionEvent d x n := by
  rintro ω ⟨y, hy, hconn⟩
  apply mem_radiusConnectionEvent_iff_exists_connection.mpr
  have hordinary := connectionEventIn_subset d _ x y hconn
  rcases hordinary with ⟨w, hw⟩
  obtain ⟨z, hz, hzconn⟩ := exists_open_walk_to_cubicMetricSphere_in_ball w hw
    ((mem_cubicBoxSurface.mp hy).ge.trans (cubicLInfDist_le_l1Dist x y))
  exact ⟨z, hz, connectionEventIn_subset d _ x z hzconn⟩

/-- A Manhattan-radius connection at radius `d * n` must leave the coordinate box of
radius `n`, giving the reverse comparison needed to identify the box-tail limit. -/
theorem radiusConnectionEvent_mul_dimension_subset_boxRadiusConnectionEvent
    {d : ℕ} (hd : 0 < d) (x : Cubic d) (n : ℕ) :
    radiusConnectionEvent d x (d * n) ⊆ boxRadiusConnectionEvent d x n := by
  intro ω hω
  rw [mem_radiusConnectionEvent_iff_exists_connection] at hω
  rcases hω with ⟨y, hy, w, hwopen⟩
  have hl1 : cubicL1Dist x y = d * n := mem_cubicMetricSphere_iff_l1Dist_eq.mp hy
  have hmul : d * n ≤ d * cubicLInfDist x y := by
    rw [← hl1]
    exact cubicL1Dist_le_card_mul_lInfDist x y
  have hlinf : n ≤ cubicLInfDist x y := le_of_mul_le_mul_left hmul hd
  exact exists_open_walk_to_cubicBoxSurface_in_box w hwopen hlinf

theorem boxRadiusTail_le_radiusTail (d : ℕ) (p : I) (n : ℕ) :
    boxRadiusTail d p n ≤ radiusTail d p n := by
  exact measureReal_mono (boxRadiusConnectionEvent_subset_radiusConnectionEvent d _ n)

theorem radiusTail_mul_dimension_le_boxRadiusTail
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    radiusTail d p (d * n) ≤ boxRadiusTail d p n := by
  exact measureReal_mono
    (radiusConnectionEvent_mul_dimension_subset_boxRadiusConnectionEvent hd cubicOrigin n)

/-- Coordinate-box radius probabilities decrease to the percolation probability. -/
theorem boxRadiusTail_tendsto_theta
    {d : ℕ} (hd : 0 < d) (p : I) :
    Filter.Tendsto (boxRadiusTail d p) Filter.atTop (nhds (theta d p)) := by
  have hsubseq : Filter.Tendsto (fun n : ℕ ↦ radiusTail d p (d * n)) Filter.atTop
      (nhds (theta d p)) := by
    apply (radiusTail_tendsto_theta d p).comp
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    exact hn.trans (by
      simpa using Nat.mul_le_mul_right n hd)
  exact hsubseq.squeeze (radiusTail_tendsto_theta d p)
    (fun n ↦ radiusTail_mul_dimension_le_boxRadiusTail hd p n)
    (fun n ↦ boxRadiusTail_le_radiusTail d p n)

/-- Reaching the coordinate-box surface of radius `n` produces an open self-avoiding path
of length at least `n` from the origin. -/
theorem boxRadiusConnectionEvent_subset_hasOpenPathOfLengthAtLeast
    (d n : ℕ) :
    boxRadiusConnectionEvent d cubicOrigin n ⊆
      {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} := by
  intro ω hω
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection] at hω
  rcases hω with ⟨y, hy, w, hwopen⟩
  let q : (cubicGraph d).Walk cubicOrigin y := w.toPath
  refine ⟨y, q, w.toPath.2, ?_, walkIsOpen_toPath w hwopen⟩
  calc
    n = cubicLInfDist cubicOrigin y := (mem_cubicBoxSurface.mp hy).symm
    _ ≤ cubicL1Dist cubicOrigin y := cubicLInfDist_le_l1Dist _ _
    _ ≤ q.length := cubicL1Dist_le_walk_length q

/-- The elementary path-counting upper bound for the coordinate-box radius event. -/
theorem boxRadiusTail_le_selfAvoidingWalkCount_mul_pow
    (d : ℕ) (p : I) (n : ℕ) :
    boxRadiusTail d p n ≤
      (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n := by
  calc
    boxRadiusTail d p n ≤
        (bernoulliBondMeasure d p).real
          {ω : EdgeConfiguration d | hasOpenPathOfLengthAtLeast d ω n} :=
      measureReal_mono (boxRadiusConnectionEvent_subset_hasOpenPathOfLengthAtLeast d n)
    _ ≤ (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
      bernoulliBondMeasure_real_hasOpenPathOfLengthAtLeast_le d n p

/-- Crude but uniform path-counting bound `βₚ(n) ≤ ((2d)p)ⁿ`. -/
theorem boxRadiusTail_le_direction_count_mul_density_pow
    (d : ℕ) (p : I) (n : ℕ) :
    boxRadiusTail d p n ≤ (((2 * d : ℕ) : ℝ) * (p : ℝ)) ^ n := by
  calc
    boxRadiusTail d p n ≤
        (selfAvoidingWalkCount d n : ℝ) * (p : ℝ) ^ n :=
      boxRadiusTail_le_selfAvoidingWalkCount_mul_pow d p n
    _ ≤ (((2 * d : ℕ) : ℝ) ^ n) * (p : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg p.property.1 n)
      exact_mod_cast selfAvoidingWalkCount_le_directionWords d n
    _ = (((2 * d : ℕ) : ℝ) * (p : ℝ)) ^ n := (mul_pow _ _ _).symm

/-! ### Grimmett, Theorem 6.1 -/

/-- **Grimmett, Theorem 6.1.** If the susceptibility is finite, connection from the origin
to the boundary of a coordinate box decays exponentially. -/
theorem boxRadiusTail_exponential_decay_of_susceptibility_lt_top_of_density_lt_one
    {d : ℕ} {p : I} (hp1 : (p : ℝ) < 1)
    (hchi : susceptibility d p < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      boxRadiusTail d p n ≤ Real.exp (-c * n) := by
  obtain ⟨c, hc, hbound⟩ :=
    radiusTail_exponential_decay_of_susceptibility_lt_top hp1 hchi
  exact ⟨c, hc, fun n ↦ (boxRadiusTail_le_radiusTail d p n).trans (hbound n)⟩

/-- **Grimmett, Theorem 6.1.** In the chapter's range `d ≥ 2`, finite susceptibility alone
implies exponential decay of the coordinate-box connection probability. -/
theorem boxRadiusTail_exponential_decay_of_susceptibility_lt_top
    (d : ℕ) (hd : 2 ≤ d) (p : I) (hchi : susceptibility d p < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      boxRadiusTail d p n ≤ Real.exp (-c * n) := by
  have hp_le_pc : (p : ℝ) ≤ cubicCriticalProbability d :=
    density_le_criticalProbability_of_susceptibility_lt_top hchi
  have hp1 : (p : ℝ) < 1 :=
    hp_le_pc.trans_lt (cubicCriticalProbability_pos_lt_one hd).2
  exact boxRadiusTail_exponential_decay_of_susceptibility_lt_top_of_density_lt_one hp1 hchi

#print axioms boxRadiusTail_exponential_decay_of_susceptibility_lt_top

end Percolation
