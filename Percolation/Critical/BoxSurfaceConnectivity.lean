import Percolation.Critical.BoxRadius
import Percolation.Critical.Regions

/-!
# Connectivity of coordinate-box surfaces

For dimension at least two, the vertex boundary of a coordinate box is connected by
nearest-neighbor walks which remain on that boundary.  This elementary geometry is the
surface-joining input in Grimmett's proof of Lemma 8.72.
-/

namespace Percolation

/-- The vertex having prescribed signed boundary coordinates in directions `i` and `j`, and
the center coordinate elsewhere.  It is used only when `i ≠ j`. -/
def cubicBoxFaceIntersectionVertex {d : ℕ} (center : Cubic d) (n : ℕ)
    (i : Fin d) (positiveI : Bool) (j : Fin d) (positiveJ : Bool) : Cubic d :=
  Function.update (Function.update center i
    (if positiveI then center i + n else center i - n)) j
      (if positiveJ then center j + n else center j - n)

theorem cubicBoxFaceIntersectionVertex_mem_firstFace
    {d n : ℕ} {center : Cubic d} {i j : Fin d} (hij : i ≠ j)
    (positiveI positiveJ : Bool) :
    cubicBoxFaceIntersectionVertex center n i positiveI j positiveJ ∈
      cubicBoxFace d center n i positiveI := by
  rw [mem_cubicBoxFace]
  constructor
  · simp [cubicBoxFaceIntersectionVertex, hij]
  · intro k hki
    by_cases hkj : k = j
    · subst k
      cases positiveJ <;> simp [cubicBoxFaceIntersectionVertex] <;> omega
    · simp [cubicBoxFaceIntersectionVertex, hki, hkj]

theorem cubicBoxFaceIntersectionVertex_mem_secondFace
    {d n : ℕ} {center : Cubic d} {i j : Fin d} (hij : i ≠ j)
    (positiveI positiveJ : Bool) :
    cubicBoxFaceIntersectionVertex center n i positiveI j positiveJ ∈
      cubicBoxFace d center n j positiveJ := by
  rw [mem_cubicBoxFace]
  constructor
  · simp [cubicBoxFaceIntersectionVertex]
  · intro k hkj
    by_cases hki : k = i
    · subst k
      cases positiveI <;> simp [cubicBoxFaceIntersectionVertex, hij] <;> omega
    · simp [cubicBoxFaceIntersectionVertex, hki, hkj]

/-- Two vertices on one face can be joined by a cubic walk which remains on that face. -/
theorem exists_cubicWalk_support_in_boxFace
    {d n : ℕ} {center x y : Cubic d} {i : Fin d} {positive : Bool}
    (hx : x ∈ cubicBoxFace d center n i positive)
    (hy : y ∈ cubicBoxFace d center n i positive) :
    ∃ w : (cubicGraph d).Walk x y,
      ∀ z ∈ w.support, z ∈ cubicBoxFace d center n i positive := by
  obtain ⟨w, hwBetween⟩ := exists_cubicWalk_support_between d x y
  refine ⟨w, fun z hz ↦ ?_⟩
  rw [mem_cubicBoxFace] at hx hy ⊢
  constructor
  · rcases hwBetween z hz i with hi | hi <;> omega
  · intro j hji
    rcases hwBetween z hz j with hj | hj
    · exact ⟨(hx.2 j hji).1.trans hj.1, hj.2.trans (hy.2 j hji).2⟩
    · exact ⟨(hy.2 j hji).1.trans hj.1, hj.2.trans (hx.2 j hji).2⟩

theorem exists_boxFace_of_mem_cubicBoxSurface
    {d n : ℕ} (hd : 0 < d) {center x : Cubic d}
    (hx : x ∈ cubicBoxSurface d center n) :
    ∃ i : Fin d, ∃ positive : Bool, x ∈ cubicBoxFace d center n i positive := by
  have hfaces := cubicBoxSurface_subset_faces hd center hx
  rw [cubicBoxFaces, Finset.mem_biUnion] at hfaces
  obtain ⟨i, hi, hface⟩ := hfaces
  rw [Finset.mem_union] at hface
  exact hface.elim (fun h ↦ ⟨i, true, h⟩) (fun h ↦ ⟨i, false, h⟩)

theorem cubicBoxFace_subset_surface_local
    {d n : ℕ} {center : Cubic d} (i : Fin d) (positive : Bool) :
    (cubicBoxFace d center n i positive : Set (Cubic d)) ⊆
      cubicBoxSurface d center n := by
  intro z hz
  change z ∈ cubicBoxFace d center n i positive at hz
  change z ∈ cubicBoxSurface d center n
  rw [mem_cubicBoxFace] at hz
  rw [mem_cubicBoxSurface]
  have hbox : z ∈ cubicMetricBox d center n := by
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      cases positive <;> simp_all <;> omega
    · exact hz.2 j hji
  have hle : cubicLInfDist center z ≤ n :=
    mem_cubicMetricBox_iff_lInfDist_le.mp hbox
  have hcoord : (z i - center i).natAbs = n := by
    cases positive <;> simp_all
  exact le_antisymm hle (hcoord ▸ cubicLInfDist_coord_le center z i)

/-- In dimension at least two, any two vertices of the coordinate-box surface are joined by a
walk whose entire support remains on that surface. -/
theorem exists_cubicWalk_support_in_boxSurface
    {d n : ℕ} (hd : 2 ≤ d) {center x y : Cubic d}
    (hx : x ∈ cubicBoxSurface d center n)
    (hy : y ∈ cubicBoxSurface d center n) :
    ∃ w : (cubicGraph d).Walk x y,
      ∀ z ∈ w.support, z ∈ cubicBoxSurface d center n := by
  obtain ⟨i, positiveI, hxFace⟩ :=
    exists_boxFace_of_mem_cubicBoxSurface (by omega) hx
  obtain ⟨j, positiveJ, hyFace⟩ :=
    exists_boxFace_of_mem_cubicBoxSurface (by omega) hy
  have face_subset_surface (k : Fin d) (positive : Bool) :
      (cubicBoxFace d center n k positive : Set (Cubic d)) ⊆
        cubicBoxSurface d center n := by
    intro z hz
    exact cubicBoxFace_subset_surface_local k positive hz
  by_cases hij : i = j
  · subst j
    by_cases hsign : positiveI = positiveJ
    · subst positiveJ
      obtain ⟨w, hw⟩ := exists_cubicWalk_support_in_boxFace hxFace hyFace
      exact ⟨w, fun z hz ↦ face_subset_surface i positiveI (hw z hz)⟩
    · obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card
        (show 1 < Fintype.card (Fin d) by simpa using hd) i
      let u := cubicBoxFaceIntersectionVertex center n i positiveI k true
      let v := cubicBoxFaceIntersectionVertex center n i positiveJ k true
      have huI : u ∈ cubicBoxFace d center n i positiveI :=
        cubicBoxFaceIntersectionVertex_mem_firstFace hki.symm positiveI true
      have huK : u ∈ cubicBoxFace d center n k true :=
        cubicBoxFaceIntersectionVertex_mem_secondFace hki.symm positiveI true
      have hvI : v ∈ cubicBoxFace d center n i positiveJ :=
        cubicBoxFaceIntersectionVertex_mem_firstFace hki.symm positiveJ true
      have hvK : v ∈ cubicBoxFace d center n k true :=
        cubicBoxFaceIntersectionVertex_mem_secondFace hki.symm positiveJ true
      obtain ⟨w₁, hw₁⟩ := exists_cubicWalk_support_in_boxFace hxFace huI
      obtain ⟨w₂, hw₂⟩ := exists_cubicWalk_support_in_boxFace huK hvK
      obtain ⟨w₃, hw₃⟩ := exists_cubicWalk_support_in_boxFace hvI hyFace
      refine ⟨w₁.append (w₂.append w₃), ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rw [List.mem_append] at hz
      rcases hz with hz | hz
      · exact face_subset_surface i positiveI (hw₁ z hz)
      · have hz' : z ∈ (w₂.append w₃).support := List.mem_of_mem_tail hz
        simp only [SimpleGraph.Walk.support_append, List.mem_append] at hz'
        rcases hz' with hz' | hz'
        · exact face_subset_surface k true (hw₂ z hz')
        · exact face_subset_surface i positiveJ (hw₃ z (List.mem_of_mem_tail hz'))
  · let u := cubicBoxFaceIntersectionVertex center n i positiveI j positiveJ
    have huI : u ∈ cubicBoxFace d center n i positiveI :=
      cubicBoxFaceIntersectionVertex_mem_firstFace hij positiveI positiveJ
    have huJ : u ∈ cubicBoxFace d center n j positiveJ :=
      cubicBoxFaceIntersectionVertex_mem_secondFace hij positiveI positiveJ
    obtain ⟨w₁, hw₁⟩ := exists_cubicWalk_support_in_boxFace hxFace huI
    obtain ⟨w₂, hw₂⟩ := exists_cubicWalk_support_in_boxFace huJ hyFace
    refine ⟨w₁.append w₂, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rw [List.mem_append] at hz
    exact hz.elim
      (fun h ↦ face_subset_surface i positiveI (hw₁ z h))
      (fun h ↦ face_subset_surface j positiveJ (hw₂ z (List.mem_of_mem_tail h)))

/-- Edge version: the joining walk between surface vertices uses only edges incident to the
surface. -/
theorem exists_cubicWalk_edgeFinset_subset_surfaceIncidentEdges
    {d n : ℕ} (hd : 2 ≤ d) {center x y : Cubic d}
    (hx : x ∈ cubicBoxSurface d center n)
    (hy : y ∈ cubicBoxSurface d center n) :
    ∃ w : (cubicGraph d).Walk x y,
      walkEdgeFinset w ⊆ cubicIncidentEdges d (cubicBoxSurface d center n) := by
  obtain ⟨w, hwSurface⟩ := exists_cubicWalk_support_in_boxSurface hd hx hy
  refine ⟨w, ?_⟩
  rintro ⟨e, heGraph⟩ heWalk
  rw [mem_walkEdgeFinset_iff] at heWalk
  induction e using Sym2.ind with
  | _ a b =>
      have haSupport : a ∈ w.support := w.fst_mem_support_of_mem_edges heWalk
      exact mem_cubicIncidentEdges_of_endpoint (hwSurface a haSupport) (by simp)

end Percolation
