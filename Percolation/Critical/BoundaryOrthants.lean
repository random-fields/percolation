import Percolation.Critical.BoundaryContacts
import Percolation.Critical.BoxFaces

/-!
# Signed boundary orthants for Grimmett equation (7.14)

In dimension three the boundary of `B(n)` is covered by 24 signed face quadrants.  The uniform
definition below has `d * 2^d` cells and records the source's overlaps along coordinate
hyperplanes rather than imposing an arbitrary disjoint tie-break.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

/-- A choice of normal coordinate and one sign for every coordinate.  The normal-coordinate
sign chooses the face; all other signs choose its orthant. -/
structure BoxSurfaceOrthantIndex (d : ℕ) where
  normal : Fin d
  signs : Fin d → Bool
deriving DecidableEq, Fintype

def boxSurfaceOrthantIndexEquiv (d : ℕ) :
    BoxSurfaceOrthantIndex d ≃ Fin d × (Fin d → Bool) where
  toFun a := (a.normal, a.signs)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_boxSurfaceOrthantIndex (d : ℕ) :
    Fintype.card (BoxSurfaceOrthantIndex d) = d * 2 ^ d := by
  rw [Fintype.card_congr (boxSurfaceOrthantIndexEquiv d)]
  simp [Fintype.card_prod]

/-- A signed orthant of one signed face of the origin-centered box. -/
noncomputable def boxSurfaceOrthant
    (d n : ℕ) (a : BoxSurfaceOrthantIndex d) : Finset (Cubic d) :=
  (cubicBoxFace d cubicOrigin n a.normal (a.signs a.normal)).filter fun x =>
    ∀ j : Fin d, j ≠ a.normal →
      if a.signs j then 0 ≤ x j else x j ≤ 0

@[simp]
theorem mem_boxSurfaceOrthant_iff
    {d n : ℕ} {a : BoxSurfaceOrthantIndex d} {x : Cubic d} :
    x ∈ boxSurfaceOrthant d n a ↔
      x ∈ cubicBoxFace d cubicOrigin n a.normal (a.signs a.normal) ∧
        ∀ j : Fin d, j ≠ a.normal →
          if a.signs j then 0 ≤ x j else x j ≤ 0 := by
  classical
  simp [boxSurfaceOrthant]

theorem boxSurfaceOrthant_subset_surface
    (d n : ℕ) (a : BoxSurfaceOrthantIndex d) :
    boxSurfaceOrthant d n a ⊆ cubicBoxSurface d cubicOrigin n := by
  intro x hx
  exact cubicBoxFace_subset_surface cubicOrigin a.normal (a.signs a.normal)
    (mem_boxSurfaceOrthant_iff.mp hx).1

/-- The all-positive orthant on face `i`; this is Grimmett's `T(n)`. -/
def allPositiveBoxSurfaceOrthantIndex {d : ℕ} (i : Fin d) :
    BoxSurfaceOrthantIndex d :=
  ⟨i, fun _ => true⟩

theorem boxSurfaceOrthant_allPositive_eq_seededBoundaryQuadrant
    {d n : ℕ} (i : Fin d) :
    boxSurfaceOrthant d n (allPositiveBoxSurfaceOrthantIndex i) =
      seededBoundaryQuadrant d i n := by
  classical
  ext x
  simp [boxSurfaceOrthant, allPositiveBoxSurfaceOrthantIndex,
    seededBoundaryQuadrant]

/-- Every surface point lies in at least one signed face orthant. -/
theorem cubicBoxSurface_subset_iUnion_boxSurfaceOrthant
    {d n : ℕ} (hd : 0 < d) :
    (cubicBoxSurface d cubicOrigin n : Set (Cubic d)) ⊆
      ⋃ a : BoxSurfaceOrthantIndex d, (boxSurfaceOrthant d n a : Set (Cubic d)) := by
  intro x hx
  have hxFaces := cubicBoxSurface_subset_faces (x := cubicOrigin) hd hx
  rw [cubicBoxFaces, Finset.mem_biUnion] at hxFaces
  obtain ⟨i, _hi, hface⟩ := hxFaces
  rw [Finset.mem_union] at hface
  obtain ⟨positive, hxFace⟩ :
      ∃ positive : Bool, x ∈ cubicBoxFace d cubicOrigin n i positive := by
    rcases hface with hpos | hneg
    · exact ⟨true, hpos⟩
    · exact ⟨false, hneg⟩
  let signs : Fin d → Bool := fun j => if j = i then positive else decide (0 ≤ x j)
  let a : BoxSurfaceOrthantIndex d := ⟨i, signs⟩
  apply Set.mem_iUnion.mpr
  refine ⟨a, Finset.mem_coe.mpr (mem_boxSurfaceOrthant_iff.mpr ⟨?_, ?_⟩)⟩
  · simpa [a, signs] using hxFace
  · intro j _hji
    by_cases hj : 0 ≤ x j
    · simp [a, signs, _hji, hj]
    · simp [a, signs, _hji, hj]
      omega

/-- Contacts falling in a specified signed boundary orthant. -/
noncomputable def orthantBoundaryContacts
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (omega : EdgeConfiguration d) :
    Finset (Cubic d) :=
  (boxBoundaryContacts d m n omega).filter fun x => x ∈ boxSurfaceOrthant d n a

@[simp]
theorem mem_orthantBoundaryContacts_iff
    {d m n : ℕ} {a : BoxSurfaceOrthantIndex d} {omega : EdgeConfiguration d}
    {x : Cubic d} :
    x ∈ orthantBoundaryContacts d m n a omega ↔
      x ∈ boxBoundaryContacts d m n omega ∧ x ∈ boxSurfaceOrthant d n a := by
  classical
  simp [orthantBoundaryContacts]

theorem boxBoundaryContacts_subset_iUnion_orthantBoundaryContacts
    {d m n : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d) :
    (boxBoundaryContacts d m n omega : Set (Cubic d)) ⊆
      ⋃ a : BoxSurfaceOrthantIndex d,
        (orthantBoundaryContacts d m n a omega : Set (Cubic d)) := by
  intro x hx
  have hxSurface := (mem_boxBoundaryContacts_iff.mp hx).1
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp
    (cubicBoxSurface_subset_iUnion_boxSurfaceOrthant hd hxSurface)
  exact Set.mem_iUnion.mpr ⟨a, Finset.mem_coe.mpr
    (mem_orthantBoundaryContacts_iff.mpr ⟨hx, Finset.mem_coe.mp hxa⟩)⟩

theorem boxBoundaryContacts_card_le_sum_orthantBoundaryContacts
    {d m n : ℕ} (hd : 0 < d) (omega : EdgeConfiguration d) :
    (boxBoundaryContacts d m n omega).card ≤
      ∑ a : BoxSurfaceOrthantIndex d,
        (orthantBoundaryContacts d m n a omega).card := by
  have hcover := boxBoundaryContacts_subset_iUnion_orthantBoundaryContacts
    (m := m) (n := n) hd omega
  calc
    (boxBoundaryContacts d m n omega).card ≤
        (Finset.univ.biUnion fun a : BoxSurfaceOrthantIndex d =>
          orthantBoundaryContacts d m n a omega).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_biUnion]
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (hcover (Finset.mem_coe.mpr hx))
      exact ⟨a, Finset.mem_univ a, Finset.mem_coe.mp hxa⟩
    _ ≤ ∑ a : BoxSurfaceOrthantIndex d,
        (orthantBoundaryContacts d m n a omega).card := by
      exact Finset.card_biUnion_le

/-- The decreasing event that one signed boundary orthant contains fewer than `ell` contacts. -/
def orthantBoundaryContactCardLtEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    Set (EdgeConfiguration d) :=
  {omega | (orthantBoundaryContacts d m n a omega).card < ell}

theorem orthantBoundaryContacts_mono_configuration
    {d m n : ℕ} {a : BoxSurfaceOrthantIndex d}
    {omega eta : EdgeConfiguration d} (homegaeta : omega ⊆ eta) :
    orthantBoundaryContacts d m n a omega ⊆
      orthantBoundaryContacts d m n a eta := by
  intro x hx
  obtain ⟨hxContact, hxa⟩ := mem_orthantBoundaryContacts_iff.mp hx
  obtain ⟨hxSurface, y, hy, hconn⟩ := mem_boxBoundaryContacts_iff.mp hxContact
  have hxContactEta : x ∈ boxBoundaryContacts d m n eta :=
    mem_boxBoundaryContacts_iff.mpr ⟨hxSurface, y, hy,
      isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin n) y x
        homegaeta hconn⟩
  exact mem_orthantBoundaryContacts_iff.mpr ⟨hxContactEta, hxa⟩

theorem isDecreasingEvent_orthantBoundaryContactCardLtEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    IsDecreasingEvent (orthantBoundaryContactCardLtEvent d m n a ell) := by
  intro omega eta homegaeta heta
  change (orthantBoundaryContacts d m n a eta).card < ell at heta
  change (orthantBoundaryContacts d m n a omega).card < ell
  exact (Finset.card_le_card (orthantBoundaryContacts_mono_configuration homegaeta)).trans_lt heta

theorem dependsOn_orthantBoundaryContactCardLtEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    DependsOn (cubicBoxEdges d cubicOrigin n)
      (orthantBoundaryContactCardLtEvent d m n a ell) := by
  classical
  intro omega eta hagree
  have hcontacts : orthantBoundaryContacts d m n a omega =
      orthantBoundaryContacts d m n a eta := by
    ext x
    simp only [mem_orthantBoundaryContacts_iff, mem_boxBoundaryContacts_iff]
    apply and_congr
    · apply and_congr_right
      intro _hxSurface
      apply exists_congr
      intro y
      apply and_congr_right
      intro _hy
      exact dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) y x hagree
    · rfl
  simp [orthantBoundaryContactCardLtEvent, hcontacts]

theorem measurableSet_orthantBoundaryContactCardLtEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    MeasurableSet (orthantBoundaryContactCardLtEvent d m n a ell) :=
  (dependsOn_orthantBoundaryContactCardLtEvent d m n a ell).measurableSet

/-! ## Symmetry transport -/

theorem cubicGraphIsoConfigurationPullback_mem_boxBoundaryContacts_iff
    {d m n : ℕ} (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F x ∈ cubicMetricBox d cubicOrigin m)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F.symm x ∈ cubicMetricBox d cubicOrigin m)
    (hsurface : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F y ∈ cubicBoxSurface d cubicOrigin n)
    (hsurfaceBack : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F.symm y ∈ cubicBoxSurface d cubicOrigin n)
    (hedges : (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin n)
    (omega : EdgeConfiguration d) (y : Cubic d) :
    y ∈ boxBoundaryContacts d m n (cubicGraphIsoConfigurationPullback F omega) ↔
      F y ∈ boxBoundaryContacts d m n omega := by
  constructor
  · intro hy
    obtain ⟨hySurface, x, hx, hxy⟩ := mem_boxBoundaryContacts_iff.mp hy
    refine mem_boxBoundaryContacts_iff.mpr
      ⟨hsurface y hySurface, F x, hinner x hx, ?_⟩
    have hmap := (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      F (cubicBoxEdges d cubicOrigin n) omega x y).mp hxy
    simpa [hedges] using hmap
  · intro hy
    obtain ⟨hFySurface, z, hz, hzFy⟩ := mem_boxBoundaryContacts_iff.mp hy
    let x := F.symm z
    have hx : x ∈ cubicMetricBox d cubicOrigin m := hinnerBack z hz
    have hySurface : y ∈ cubicBoxSurface d cubicOrigin n := by
      simpa [x] using hsurfaceBack (F y) hFySurface
    refine mem_boxBoundaryContacts_iff.mpr ⟨hySurface, x, hx, ?_⟩
    apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff
      F (cubicBoxEdges d cubicOrigin n) omega x y).mpr
    simpa [x, hedges] using hzFy

theorem cubicGraphIsoConfigurationPullback_mem_orthantBoundaryContacts_iff
    {d m n : ℕ} {a b : BoxSurfaceOrthantIndex d}
    (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F x ∈ cubicMetricBox d cubicOrigin m)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F.symm x ∈ cubicMetricBox d cubicOrigin m)
    (hsurface : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F y ∈ cubicBoxSurface d cubicOrigin n)
    (hsurfaceBack : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F.symm y ∈ cubicBoxSurface d cubicOrigin n)
    (horthant : ∀ y, y ∈ boxSurfaceOrthant d n a → F y ∈ boxSurfaceOrthant d n b)
    (horthantBack : ∀ y, y ∈ boxSurfaceOrthant d n b →
      F.symm y ∈ boxSurfaceOrthant d n a)
    (hedges : (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin n)
    (omega : EdgeConfiguration d) (y : Cubic d) :
    y ∈ orthantBoundaryContacts d m n a (cubicGraphIsoConfigurationPullback F omega) ↔
      F y ∈ orthantBoundaryContacts d m n b omega := by
  rw [mem_orthantBoundaryContacts_iff, mem_orthantBoundaryContacts_iff,
    cubicGraphIsoConfigurationPullback_mem_boxBoundaryContacts_iff
      F hinner hinnerBack hsurface hsurfaceBack hedges]
  constructor
  · exact fun h => ⟨h.1, horthant y h.2⟩
  · intro h
    refine ⟨h.1, ?_⟩
    have := horthantBack (F y) h.2
    simpa using this

theorem cubicGraphIsoConfigurationPullback_orthantContact_card_eq
    {d m n : ℕ} {a b : BoxSurfaceOrthantIndex d}
    (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F x ∈ cubicMetricBox d cubicOrigin m)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F.symm x ∈ cubicMetricBox d cubicOrigin m)
    (hsurface : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F y ∈ cubicBoxSurface d cubicOrigin n)
    (hsurfaceBack : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F.symm y ∈ cubicBoxSurface d cubicOrigin n)
    (horthant : ∀ y, y ∈ boxSurfaceOrthant d n a → F y ∈ boxSurfaceOrthant d n b)
    (horthantBack : ∀ y, y ∈ boxSurfaceOrthant d n b →
      F.symm y ∈ boxSurfaceOrthant d n a)
    (hedges : (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin n)
    (omega : EdgeConfiguration d) :
    (orthantBoundaryContacts d m n a (cubicGraphIsoConfigurationPullback F omega)).card =
      (orthantBoundaryContacts d m n b omega).card := by
  classical
  let A := orthantBoundaryContacts d m n a (cubicGraphIsoConfigurationPullback F omega)
  let B := orthantBoundaryContacts d m n b omega
  have himage : A.image F = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (cubicGraphIsoConfigurationPullback_mem_orthantBoundaryContacts_iff
        F hinner hinnerBack hsurface hsurfaceBack horthant horthantBack hedges omega x).mp hx
    · intro hy
      refine Finset.mem_image.mpr ⟨F.symm y, ?_, by simp⟩
      apply (cubicGraphIsoConfigurationPullback_mem_orthantBoundaryContacts_iff
        F hinner hinnerBack hsurface hsurfaceBack horthant horthantBack hedges omega
          (F.symm y)).mpr
      change y ∈ orthantBoundaryContacts d m n b omega at hy
      simpa using hy
  change A.card = B.card
  rw [← himage, Finset.card_image_of_injective _ F.injective]

theorem orthantBoundaryContactProbability_eq_of_iso
    {d m n ell : ℕ} {a b : BoxSurfaceOrthantIndex d}
    (p : I) (F : cubicGraph d ≃g cubicGraph d)
    (hinner : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F x ∈ cubicMetricBox d cubicOrigin m)
    (hinnerBack : ∀ x, x ∈ cubicMetricBox d cubicOrigin m →
      F.symm x ∈ cubicMetricBox d cubicOrigin m)
    (hsurface : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F y ∈ cubicBoxSurface d cubicOrigin n)
    (hsurfaceBack : ∀ y, y ∈ cubicBoxSurface d cubicOrigin n →
      F.symm y ∈ cubicBoxSurface d cubicOrigin n)
    (horthant : ∀ y, y ∈ boxSurfaceOrthant d n a → F y ∈ boxSurfaceOrthant d n b)
    (horthantBack : ∀ y, y ∈ boxSurfaceOrthant d n b →
      F.symm y ∈ boxSurfaceOrthant d n a)
    (hedges : (cubicBoxEdges d cubicOrigin n).image F.mapEdgeSet =
      cubicBoxEdges d cubicOrigin n) :
    (bernoulliBondMeasure d p).real (orthantBoundaryContactCardLtEvent d m n a ell) =
      (bernoulliBondMeasure d p).real (orthantBoundaryContactCardLtEvent d m n b ell) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hpre : T ⁻¹' orthantBoundaryContactCardLtEvent d m n a ell =
      orthantBoundaryContactCardLtEvent d m n b ell := by
    ext omega
    change (orthantBoundaryContacts d m n a (T omega)).card < ell ↔
      (orthantBoundaryContacts d m n b omega).card < ell
    rw [cubicGraphIsoConfigurationPullback_orthantContact_card_eq F hinner hinnerBack
      hsurface hsurfaceBack horthant horthantBack hedges]
  have hmap := congrArg
    (fun mu : Measure (EdgeConfiguration d) =>
      mu.real (orthantBoundaryContactCardLtEvent d m n a ell))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p)).real
      (orthantBoundaryContactCardLtEvent d m n a ell) =
    (bernoulliBondMeasure d p).real
      (orthantBoundaryContactCardLtEvent d m n a ell) at hmap
  rw [map_measureReal_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_orthantBoundaryContactCardLtEvent d m n a ell), hpre] at hmap
  exact hmap.symm

/-- If every signed orthant has fewer than `ell` contacts, the whole surface has fewer than
`(d*2^d)*ell` contacts. -/
theorem iInter_orthantContactLt_subset_fullContactLt
    {d m n ell : ℕ} (hd : 0 < d) :
    (⋂ a : BoxSurfaceOrthantIndex d,
        orthantBoundaryContactCardLtEvent d m n a ell) ⊆
      boundaryContactCardLtEvent d m n ((d * 2 ^ d) * ell) := by
  intro omega homega
  letI : Nonempty (BoxSurfaceOrthantIndex d) :=
    ⟨⟨⟨0, hd⟩, fun _ => true⟩⟩
  have ha : ∀ a : BoxSurfaceOrthantIndex d,
      (orthantBoundaryContacts d m n a omega).card < ell := by
    intro a
    exact Set.mem_iInter.mp homega a
  change (boxBoundaryContacts d m n omega).card < (d * 2 ^ d) * ell
  refine (boxBoundaryContacts_card_le_sum_orthantBoundaryContacts hd omega).trans_lt ?_
  calc
    ∑ a : BoxSurfaceOrthantIndex d,
        (orthantBoundaryContacts d m n a omega).card <
      ∑ _a : BoxSurfaceOrthantIndex d, ell := by
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ha => ha a)
    _ = (d * 2 ^ d) * ell := by
      simp [card_boxSurfaceOrthantIndex]

/-- Iterated decreasing FKG for all signed boundary orthants. -/
theorem prod_orthantContactLt_probability_le_fullContactLt
    {d m n ell : ℕ} (hd : 0 < d) (p : I) :
    (∏ a : BoxSurfaceOrthantIndex d,
        (bernoulliBondMeasure d p).real
          (orthantBoundaryContactCardLtEvent d m n a ell)) ≤
      (bernoulliBondMeasure d p).real
        (boundaryContactCardLtEvent d m n ((d * 2 ^ d) * ell)) := by
  calc
    (∏ a : BoxSurfaceOrthantIndex d,
        (bernoulliBondMeasure d p).real
          (orthantBoundaryContactCardLtEvent d m n a ell)) ≤
      (bernoulliBondMeasure d p).real
        (⋂ a : BoxSurfaceOrthantIndex d,
          orthantBoundaryContactCardLtEvent d m n a ell) := by
        simpa using bernoulliBondMeasure_prod_le_real_biInter_fkg_of_decreasing
          p (J := Finset.univ)
          (fun a _ha => isDecreasingEvent_orthantBoundaryContactCardLtEvent d m n a ell)
          (fun a _ha => measurableSet_orthantBoundaryContactCardLtEvent d m n a ell)
    _ ≤ (bernoulliBondMeasure d p).real
        (boundaryContactCardLtEvent d m n ((d * 2 ^ d) * ell)) :=
      measureReal_mono (iInter_orthantContactLt_subset_fullContactLt hd) (measure_ne_top _ _)

end Percolation
