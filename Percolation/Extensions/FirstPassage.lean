import Percolation.Critical.BoxRadius
import Percolation.Critical.Translation
import Mathlib.Data.ENNReal.Operations

/-!
# First-passage percolation on the cubic lattice

This file introduces the deterministic metric layer used in Grimmett, Chapter 12, §12.9.
Passage times take values in `ℝ≥0∞`; this records infinite edge times without a sentinel and
makes the infimum over all lattice walks endpoint-safe.
-/

namespace Percolation

open Set
open scoped ENNReal

/-- A first-passage environment assigns a nonnegative extended passage time to every cubic
edge. -/
abbrev FirstPassageConfiguration (d : ℕ) := CubicEdge d → ℝ≥0∞

/-- Totalized edge weight on unordered vertex pairs.  The off-graph value is irrelevant for
walks in `cubicGraph`, but permits direct use of `SimpleGraph.Walk.edges`. -/
noncomputable def firstPassageEdgeWeight {d : ℕ} (t : FirstPassageConfiguration d)
    (e : Sym2 (Cubic d)) : ℝ≥0∞ := by
  classical
  exact if h : e ∈ (cubicGraph d).edgeSet then t ⟨e, h⟩ else 0

@[simp]
theorem firstPassageEdgeWeight_coe {d : ℕ} (t : FirstPassageConfiguration d)
    (e : CubicEdge d) :
    firstPassageEdgeWeight t e.1 = t e := by
  simp [firstPassageEdgeWeight, e.2]

/-- Passage time accumulated by a finite nearest-neighbour walk. -/
noncomputable def firstPassagePathTime {d : ℕ} (t : FirstPassageConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) : ℝ≥0∞ :=
  (w.edges.map (firstPassageEdgeWeight t)).sum

@[simp]
theorem firstPassagePathTime_nil {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) :
    firstPassagePathTime t (SimpleGraph.Walk.nil : (cubicGraph d).Walk x x) = 0 := by
  simp [firstPassagePathTime]

@[simp]
theorem firstPassagePathTime_append {d : ℕ} (t : FirstPassageConfiguration d)
    {x y z : Cubic d} (w : (cubicGraph d).Walk x y)
    (q : (cubicGraph d).Walk y z) :
    firstPassagePathTime t (w.append q) =
      firstPassagePathTime t w + firstPassagePathTime t q := by
  simp [firstPassagePathTime, SimpleGraph.Walk.edges_append]

@[simp]
theorem firstPassagePathTime_reverse {d : ℕ} (t : FirstPassageConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) :
    firstPassagePathTime t w.reverse = firstPassagePathTime t w := by
  simp [firstPassagePathTime, SimpleGraph.Walk.edges_reverse]

/-- First-passage time between two vertices, as the infimum over all lattice walks. -/
noncomputable def firstPassageTime {d : ℕ} (t : FirstPassageConfiguration d)
    (x y : Cubic d) : ℝ≥0∞ :=
  ⨅ w : (cubicGraph d).Walk x y, firstPassagePathTime t w

theorem firstPassageTime_le_pathTime {d : ℕ} (t : FirstPassageConfiguration d)
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) :
    firstPassageTime t x y ≤ firstPassagePathTime t w :=
  iInf_le _ w

@[simp]
theorem firstPassageTime_self {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) : firstPassageTime t x x = 0 := by
  apply le_antisymm
  · exact (firstPassageTime_le_pathTime t
      (SimpleGraph.Walk.nil : (cubicGraph d).Walk x x)).trans_eq
      (firstPassagePathTime_nil t x)
  · exact bot_le

theorem firstPassageTime_comm {d : ℕ} (t : FirstPassageConfiguration d)
    (x y : Cubic d) : firstPassageTime t x y = firstPassageTime t y x := by
  apply le_antisymm
  · refine le_iInf fun w ↦ ?_
    exact (firstPassageTime_le_pathTime t w.reverse).trans_eq
      (firstPassagePathTime_reverse t w)
  · refine le_iInf fun w ↦ ?_
    exact (firstPassageTime_le_pathTime t w.reverse).trans_eq
      (firstPassagePathTime_reverse t w)

/-- The deterministic triangle inequality.  This is the subadditive input behind the axial
time-constant theorem. -/
theorem firstPassageTime_triangle {d : ℕ} (t : FirstPassageConfiguration d)
    (x y z : Cubic d) :
    firstPassageTime t x z ≤ firstPassageTime t x y + firstPassageTime t y z := by
  apply ENNReal.le_iInf_add_iInf
  intro w q
  exact iInf_le_of_le (w.append q) (firstPassagePathTime_append t w q).le

theorem firstPassageTime_mono {d : ℕ}
    {s t : FirstPassageConfiguration d} (hst : s ≤ t) (x y : Cubic d) :
    firstPassageTime s x y ≤ firstPassageTime t x y := by
  refine le_iInf fun w ↦ ?_
  refine (firstPassageTime_le_pathTime s w).trans ?_
  unfold firstPassagePathTime
  apply List.sum_le_sum
  intro e he
  unfold firstPassageEdgeWeight
  split_ifs with he'
  · exact hst ⟨e, he'⟩
  · exact le_rfl

/-- Vertices reached by time `a` from a specified source. -/
noncomputable def firstPassageWetVertices {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) (a : ℝ≥0∞) : Set (Cubic d) :=
  {y | firstPassageTime t x y ≤ a}

@[simp]
theorem mem_firstPassageWetVertices {d : ℕ} (t : FirstPassageConfiguration d)
    (x y : Cubic d) (a : ℝ≥0∞) :
    y ∈ firstPassageWetVertices t x a ↔ firstPassageTime t x y ≤ a := Iff.rfl

theorem firstPassageWetVertices_mono_time {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) : Monotone (firstPassageWetVertices t x) := by
  intro a b hab y hy
  exact hy.trans hab

theorem firstPassageWetVertices_antitone_configuration {d : ℕ}
    {s t : FirstPassageConfiguration d} (hst : s ≤ t) (x : Cubic d) (a : ℝ≥0∞) :
    firstPassageWetVertices t x a ⊆ firstPassageWetVertices s x a := by
  intro y hy
  exact (firstPassageTime_mono hst x y).trans hy

/-- The closed unit cube centred at a lattice vertex. -/
def firstPassageUnitCube {d : ℕ} (y : Cubic d) : Set (Fin d → ℝ) :=
  {z | ∀ i, (y i : ℝ) - 1 / 2 ≤ z i ∧ z i ≤ (y i : ℝ) + 1 / 2}

@[simp]
theorem mem_firstPassageUnitCube {d : ℕ} (y : Cubic d) (z : Fin d → ℝ) :
    z ∈ firstPassageUnitCube y ↔
      ∀ i, (y i : ℝ) - 1 / 2 ≤ z i ∧ z i ≤ (y i : ℝ) + 1 / 2 :=
  Iff.rfl

/-- Grimmett's filled wet region: the union of closed unit cubes centred at vertices reached by
time `a`. -/
noncomputable def firstPassageWetRegion {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) (a : ℝ≥0∞) : Set (Fin d → ℝ) :=
  ⋃ y ∈ firstPassageWetVertices t x a, firstPassageUnitCube y

theorem mem_firstPassageWetRegion {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) (a : ℝ≥0∞) (z : Fin d → ℝ) :
    z ∈ firstPassageWetRegion t x a ↔
      ∃ y : Cubic d, firstPassageTime t x y ≤ a ∧ z ∈ firstPassageUnitCube y := by
  simp [firstPassageWetRegion]

theorem firstPassageWetRegion_mono_time {d : ℕ} (t : FirstPassageConfiguration d)
    (x : Cubic d) : Monotone (firstPassageWetRegion t x) := by
  intro a b hab z hz
  rw [mem_firstPassageWetRegion] at hz ⊢
  obtain ⟨y, hya, hzy⟩ := hz
  exact ⟨y, hya.trans hab, hzy⟩

theorem firstPassageWetRegion_antitone_configuration {d : ℕ}
    {s t : FirstPassageConfiguration d} (hst : s ≤ t) (x : Cubic d) (a : ℝ≥0∞) :
    firstPassageWetRegion t x a ⊆ firstPassageWetRegion s x a := by
  intro z hz
  rw [mem_firstPassageWetRegion] at hz ⊢
  obtain ⟨y, hty, hzy⟩ := hz
  exact ⟨y, (firstPassageTime_mono hst x y).trans hty, hzy⟩

/-- A reached lattice vertex, viewed in Euclidean coordinates, lies in the filled wet region. -/
theorem cubicVertex_mem_firstPassageWetRegion {d : ℕ}
    (t : FirstPassageConfiguration d) (x y : Cubic d) (a : ℝ≥0∞)
    (hy : firstPassageTime t x y ≤ a) :
    (fun i ↦ (y i : ℝ)) ∈ firstPassageWetRegion t x a := by
  rw [mem_firstPassageWetRegion]
  refine ⟨y, hy, ?_⟩
  intro i
  constructor <;> norm_num

/-- Pull an edge-time environment back along the translation taking `x` to `y`. -/
def firstPassageTranslationPullback {d : ℕ} (x y : Cubic d)
    (t : FirstPassageConfiguration d) : FirstPassageConfiguration d :=
  fun e ↦ t ((cubicTranslationIso x y).mapEdgeSet e)

theorem firstPassagePathTime_map_translation {d : ℕ} (x y : Cubic d)
    (t : FirstPassageConfiguration d) {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    firstPassagePathTime t (w.map (cubicTranslationIso x y).toHom) =
      firstPassagePathTime (firstPassageTranslationPullback x y t) w := by
  unfold firstPassagePathTime
  rw [SimpleGraph.Walk.edges_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  have hedge : e ∈ (cubicGraph d).edgeSet := w.edges_subset_edgeSet he
  have hmapped : Sym2.map (cubicTranslationIso x y).toHom e ∈
      (cubicGraph d).edgeSet := by
    exact ((cubicTranslationIso x y).mapEdgeSet ⟨e, hedge⟩).2
  simp only [Function.comp_apply]
  unfold firstPassageEdgeWeight firstPassageTranslationPullback
  rw [dif_pos hmapped, dif_pos hedge]
  rfl

@[simp]
theorem firstPassageTranslationPullback_inverse {d : ℕ} (x y : Cubic d)
    (t : FirstPassageConfiguration d) :
    firstPassageTranslationPullback y x
      (firstPassageTranslationPullback x y t) = t := by
  funext e
  unfold firstPassageTranslationPullback
  have hsymm : cubicTranslationIso y x = (cubicTranslationIso x y).symm := by
    ext z
    rfl
  rw [hsymm]
  exact congrArg t ((cubicTranslationIso x y).mapEdgeSet.apply_symm_apply e)

theorem firstPassageTime_translation_le {d : ℕ} (x y u v : Cubic d)
    (t : FirstPassageConfiguration d) :
    firstPassageTime t (cubicTranslate x y u) (cubicTranslate x y v) ≤
      firstPassageTime (firstPassageTranslationPullback x y t) u v := by
  refine le_iInf fun w ↦ ?_
  have htime := firstPassagePathTime_map_translation x y t w
  exact (firstPassageTime_le_pathTime t
    (w.map (cubicTranslationIso x y).toHom)).trans_eq htime

theorem firstPassageTime_translation {d : ℕ} (x y u v : Cubic d)
    (t : FirstPassageConfiguration d) :
    firstPassageTime t (cubicTranslate x y u) (cubicTranslate x y v) =
      firstPassageTime (firstPassageTranslationPullback x y t) u v := by
  let F := cubicTranslationIso x y
  apply le_antisymm
  · exact firstPassageTime_translation_le x y u v t
  · have h := firstPassageTime_translation_le y x
      (cubicTranslate x y u) (cubicTranslate x y v)
      (firstPassageTranslationPullback x y t)
    have hu : cubicTranslate y x (cubicTranslate x y u) = u := by
      ext i
      simp [cubicTranslate]
      omega
    have hv : cubicTranslate y x (cubicTranslate x y v) = v := by
      ext i
      simp [cubicTranslate]
      omega
    simpa [hu, hv] using h

/-- The two-parameter axial passage-time process. -/
noncomputable def axialPassageTime {d : ℕ} (t : FirstPassageConfiguration d)
    (m n : ℕ) : ℝ≥0∞ :=
  firstPassageTime t (cubicAxisVertex d m) (cubicAxisVertex d n)

/-- Grimmett's displayed subadditivity `aₘₙ ≤ aₘᵣ + aᵣₙ`. -/
theorem axialPassageTime_subadditive {d : ℕ} (t : FirstPassageConfiguration d)
    (m r n : ℕ) :
    axialPassageTime t m n ≤
      axialPassageTime t m r + axialPassageTime t r n :=
  firstPassageTime_triangle t _ _ _

theorem cubicTranslate_axisVertex_add {d k n : ℕ} :
    cubicTranslate cubicOrigin (cubicAxisVertex d k) (cubicAxisVertex d n) =
      cubicAxisVertex d (k + n) := by
  ext i
  by_cases hi : (i : ℕ) = 0
  · simp [cubicTranslate, cubicOrigin, cubicAxisVertex, hi]
    ring
  · simp [cubicTranslate, cubicOrigin, cubicAxisVertex, hi]

/-- Translating the environment shifts both indices of the axial process. -/
theorem axialPassageTime_shift {d : ℕ} (t : FirstPassageConfiguration d)
    (k m n : ℕ) :
    axialPassageTime t (k + m) (k + n) =
      axialPassageTime
        (firstPassageTranslationPullback cubicOrigin (cubicAxisVertex d k) t) m n := by
  rw [axialPassageTime, axialPassageTime,
    ← cubicTranslate_axisVertex_add (d := d) (k := k) (n := m),
    ← cubicTranslate_axisVertex_add (d := d) (k := k) (n := n)]
  exact firstPassageTime_translation _ _ _ _ _

/-- Passage time from the origin to the first-coordinate axis point `n e₁`. -/
noncomputable def axialFirstPassageTime {d : ℕ} (t : FirstPassageConfiguration d)
    (n : ℕ) : ℝ≥0∞ :=
  firstPassageTime t cubicOrigin (cubicAxisVertex d n)

@[simp]
theorem axialFirstPassageTime_zero {d : ℕ} (t : FirstPassageConfiguration d) :
    axialFirstPassageTime t 0 = 0 := by
  unfold axialFirstPassageTime
  rw [show cubicAxisVertex d 0 = (cubicOrigin : Cubic d) by
    ext i
    simp [cubicAxisVertex, cubicOrigin]]
  exact firstPassageTime_self t cubicOrigin

end Percolation
