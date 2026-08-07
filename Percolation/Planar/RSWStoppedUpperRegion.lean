import Percolation.Planar.RSWStoppedTail

/-!
# The finite region on the exterior side of a stopped RSW interface

Grimmett's proof of Lemma 11.73 uses the finite region `U(π)` above the doubled stopped tail.
After the quarter-turn used by the BR exploration, this is the region on the right of a
bottom--top barrier in `[0, 2n] × [0, 2n]`.  This file translates that barrier back to the
centered square, closes it along the deterministic left exterior, and records its mod-two
exterior index.  The construction contains no probabilistic assumption.
-/

namespace Percolation

open SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Translate the stopped square `[0,2n] × [0,2n]` back to the centered square
`[0,2n] × [-n,n]`. -/
def rswStoppedSquareNormalizeIso (n : ℕ) : squareGraph ≃g squareGraph :=
  cubicTranslationIso (squareVertex 0 (n : ℤ)) cubicOrigin

@[simp]
theorem rswStoppedSquareNormalizeIso_zero (n : ℕ) (x : SquareVertex) :
    rswStoppedSquareNormalizeIso n x 0 = x 0 := by
  simp [rswStoppedSquareNormalizeIso, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin]

@[simp]
theorem rswStoppedSquareNormalizeIso_one (n : ℕ) (x : SquareVertex) :
    rswStoppedSquareNormalizeIso n x 1 = x 1 - (n : ℤ) := by
  simp [rswStoppedSquareNormalizeIso, cubicTranslationIso_apply,
    cubicTranslate, squareVertex, cubicOrigin, sub_eq_add_neg]

theorem rswStoppedSquareNormalizeIso_topReflection
    (n : ℕ) (x : SquareVertex) :
    rswStoppedSquareNormalizeIso n (brPrimalTopReflectionIso n x) =
      brHorizontalAxisReflectionIso (rswStoppedSquareNormalizeIso n x) := by
  ext i
  fin_cases i
  · change rswStoppedSquareNormalizeIso n
      (brPrimalTopReflectionIso n x) 0 =
        brHorizontalAxisReflectionIso
          (rswStoppedSquareNormalizeIso n x) 0
    simp
  · change rswStoppedSquareNormalizeIso n
      (brPrimalTopReflectionIso n x) 1 =
        brHorizontalAxisReflectionIso
          (rswStoppedSquareNormalizeIso n x) 1
    simp
    omega

/-- Natural-number coordinate of the lower endpoint of the stopped barrier. -/
def brFilledHullStoppedBarrierEndpointNat
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : ℕ :=
  Int.toNat (brFilledHullLastMidlineVertex hn hR 0)

theorem brFilledHullStoppedBarrierEndpointNat_cast
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) =
      brFilledHullLastMidlineVertex hn hR 0 := by
  exact Int.toNat_of_nonneg (brFilledHullLastMidlineVertex_coordinates hn hR).1

/-- The stopped endpoint remains on the horizontal span of the square. -/
theorem brFilledHullStoppedBarrierEndpointNat_le
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brFilledHullStoppedBarrierEndpointNat hn hR ≤ 2 * n := by
  have hcoord := (brFilledHullLastMidlineVertex_coordinates hn hR).2
  have hcast := brFilledHullStoppedBarrierEndpointNat_cast hn hR
  omega

/-- The stopped barrier translated to the centered square and with explicit endpoints. -/
def brFilledHullStoppedBarrierNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (squareVertex (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) (-(n : ℤ)))
      (squareVertex (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) (n : ℤ)) :=
  ((brFilledHullStoppedBarrier hn hR).map
      (rswStoppedSquareNormalizeIso n).toHom).copy
    (by
      ext i
      fin_cases i
      · change rswStoppedSquareNormalizeIso n
          (brFilledHullLastMidlineVertex hn hR) 0 =
            (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ)
        rw [rswStoppedSquareNormalizeIso_zero]
        exact (brFilledHullStoppedBarrierEndpointNat_cast hn hR).symm
      · change rswStoppedSquareNormalizeIso n
          (brFilledHullLastMidlineVertex hn hR) 1 = -(n : ℤ)
        rw [rswStoppedSquareNormalizeIso_one,
          brFilledHullLastMidlineVertex_one]
        omega)
    (by
      ext i
      fin_cases i
      · change rswStoppedSquareNormalizeIso n
          (brPrimalTopReflectionIso n
            (brFilledHullLastMidlineVertex hn hR)) 0 =
              (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ)
        rw [rswStoppedSquareNormalizeIso_zero,
          brPrimalTopReflectionIso_zero]
        exact (brFilledHullStoppedBarrierEndpointNat_cast hn hR).symm
      · change rswStoppedSquareNormalizeIso n
          (brPrimalTopReflectionIso n
            (brFilledHullLastMidlineVertex hn hR)) 1 = (n : ℤ)
        rw [rswStoppedSquareNormalizeIso_one,
          brPrimalTopReflectionIso_one,
          brFilledHullLastMidlineVertex_one]
        omega)

/-- Direction word which closes the normalized barrier one lattice layer outside the centered
square.  Unlike the usual boundary-free closure, its horizontal pieces lie at heights
`n + 1` and `-n - 1`; hence a path contained in the square can meet the closure only at the two
barrier endpoints. -/
def brStoppedBarrierExteriorClosureSteps (n a : ℕ) : List (CubicDirection 2) :=
  List.replicate 1 (⟨1, by decide⟩, true) ++
    (List.replicate (a + 1) (⟨0, by decide⟩, false) ++
      (List.replicate (2 * n + 2) (⟨1, by decide⟩, false) ++
        (List.replicate (a + 1) (⟨0, by decide⟩, true) ++
          List.replicate 1 (⟨1, by decide⟩, true))))

theorem cubicEndpointFrom_brStoppedBarrierExteriorClosureSteps (n a : ℕ) :
    cubicEndpointFrom (squareVertex (a : ℤ) (n : ℤ))
        (brStoppedBarrierExteriorClosureSteps n a) =
      squareVertex (a : ℤ) (-(n : ℤ)) := by
  simp only [brStoppedBarrierExteriorClosureSteps, cubicEndpointFrom_append,
    cubicEndpointFrom_replicate_pos, cubicEndpointFrom_replicate_neg]
  ext i
  fin_cases i <;> simp [squareVertex, Function.update] <;> omega

/-- The exterior closure from the top endpoint of the stopped barrier back to its bottom
endpoint. -/
def brStoppedBarrierExteriorClosureWalk (n a : ℕ) :
    squareGraph.Walk (squareVertex (a : ℤ) (n : ℤ))
      (squareVertex (a : ℤ) (-(n : ℤ))) :=
  (cubicWalkFrom (squareVertex (a : ℤ) (n : ℤ))
    (brStoppedBarrierExteriorClosureSteps n a)).copy rfl
      (cubicEndpointFrom_brStoppedBarrierExteriorClosureSteps n a)

/-- Every vertex of the artificial closure, apart from its endpoints, lies strictly outside the
centered square. -/
theorem mem_brStoppedBarrierExteriorClosureWalk_support
    {n a : ℕ} {z : SquareVertex}
    (hz : z ∈ (brStoppedBarrierExteriorClosureWalk n a).support) :
    z = squareVertex (a : ℤ) (n : ℤ) ∨
      z = squareVertex (a : ℤ) (-(n : ℤ)) ∨
      z 0 = -1 ∨
        (z 1 = (n : ℤ) + 1 ∧ z 0 ≤ (a : ℤ)) ∨
        (z 1 = -(n : ℤ) - 1 ∧ z 0 ≤ (a : ℤ)) := by
  simp only [brStoppedBarrierExteriorClosureWalk,
    SimpleGraph.Walk.support_copy] at hz
  let x0 := squareVertex (a : ℤ) (n : ℤ)
  let x1 := squareVertex (a : ℤ) ((n : ℤ) + 1)
  let x2 := squareVertex (-1) ((n : ℤ) + 1)
  let x3 := squareVertex (-1) (-(n : ℤ) - 1)
  let x4 := squareVertex (a : ℤ) (-(n : ℤ) - 1)
  let s0 : List (CubicDirection 2) :=
    List.replicate 1 (⟨1, by decide⟩, true)
  let s1 : List (CubicDirection 2) :=
    List.replicate (a + 1) (⟨0, by decide⟩, false)
  let s2 : List (CubicDirection 2) :=
    List.replicate (2 * n + 2) (⟨1, by decide⟩, false)
  let s3 : List (CubicDirection 2) :=
    List.replicate (a + 1) (⟨0, by decide⟩, true)
  let s4 : List (CubicDirection 2) :=
    List.replicate 1 (⟨1, by decide⟩, true)
  have he0 : cubicEndpointFrom x0 s0 = x1 := by
    ext i
    fin_cases i <;> simp [x0, x1, s0, squareVertex,
      cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement,
      Function.update]
  have he1 : cubicEndpointFrom x1 s1 = x2 := by
    ext i
    fin_cases i <;> simp [x1, x2, s1, squareVertex,
      cubicEndpointFrom_replicate_neg, Function.update]
  have he2 : cubicEndpointFrom x2 s2 = x3 := by
    ext i
    fin_cases i
    · simp [x2, x3, s2, squareVertex,
        cubicEndpointFrom_replicate_neg, Function.update]
    · simp [x2, x3, s2, squareVertex,
        cubicEndpointFrom_replicate_neg, Function.update]
      omega
  have he3 : cubicEndpointFrom x3 s3 = x4 := by
    ext i
    fin_cases i <;> simp [x3, x4, s3, squareVertex,
      cubicEndpointFrom_replicate_pos, Function.update]
  have hz' : z ∈ cubicVerticesFrom x0 (s0 ++ (s1 ++ (s2 ++ (s3 ++ s4)))) := by
    simpa [x0, s0, s1, s2, s3, s4,
      brStoppedBarrierExteriorClosureSteps] using hz
  rw [mem_cubicVerticesFrom_append_iff] at hz'
  rcases hz' with hz0 | hz'
  · have hz0' := cubicVerticesFrom_replicate_pos_coord_between
      x0 (1 : Fin 2) 1 hz0
    have hz1' := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      x0 (1 : Fin 2) (0 : Fin 2) 1 (by decide) hz0
    simp [x0] at hz0' hz1'
    by_cases hztop : z 1 = n
    · left
      ext i
      fin_cases i <;> simp [squareVertex, hztop, hz1']
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  · rw [he0, mem_cubicVerticesFrom_append_iff] at hz'
    rcases hz' with hz1 | hz'
    · have hy := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
        x1 (0 : Fin 2) (1 : Fin 2) (a + 1) (by decide) hz1
      have hx := cubicVerticesFrom_replicate_neg_coord_between
        x1 (0 : Fin 2) (a + 1) hz1
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by simpa [x1] using hy, by simpa [x1] using hx.2⟩)))
    · rw [he1, mem_cubicVerticesFrom_append_iff] at hz'
      rcases hz' with hz2 | hz'
      · have hx := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
          x2 (1 : Fin 2) (0 : Fin 2) (2 * n + 2) (by decide) hz2
        exact Or.inr (Or.inr (Or.inl (by simpa [x2] using hx)))
      · rw [he2, mem_cubicVerticesFrom_append_iff] at hz'
        rcases hz' with hz3 | hz4
        · have hy := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
            x3 (0 : Fin 2) (1 : Fin 2) (a + 1) (by decide) hz3
          have hx := cubicVerticesFrom_replicate_pos_coord_between
            x3 (0 : Fin 2) (a + 1) hz3
          exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by simpa [x3] using hy, by simpa [x3] using hx.2⟩)))
        · rw [he3] at hz4
          have hz0' := cubicVerticesFrom_replicate_pos_coord_between
            x4 (1 : Fin 2) 1 hz4
          have hz1' := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
            x4 (1 : Fin 2) (0 : Fin 2) 1 (by decide) hz4
          simp [x4] at hz0' hz1'
          by_cases hzbottom : z 1 = -(n : ℤ)
          · right; left
            ext i
            fin_cases i <;> simp [squareVertex, hzbottom, hz1']
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

/-- Close the normalized stopped barrier through the one-layer exterior walk. -/
def brFilledHullStoppedBarrierClosedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareGraph.Walk
      (squareVertex (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) (-(n : ℤ)))
      (squareVertex (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) (-(n : ℤ))) :=
  (brFilledHullStoppedBarrierNormalized hn hR).append
    (brStoppedBarrierExteriorClosureWalk n
      (brFilledHullStoppedBarrierEndpointNat hn hR))

theorem brFilledHullStoppedBarrierNormalized_support_coordinates
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hz : z ∈ (brFilledHullStoppedBarrierNormalized hn hR).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  simp only [brFilledHullStoppedBarrierNormalized, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx' := brFilledHullStoppedBarrier_support_coordinates hn hR hx
  change 0 ≤ rswStoppedSquareNormalizeIso n x 0 ∧
    rswStoppedSquareNormalizeIso n x 0 ≤ 2 * (n : ℤ) ∧
    -(n : ℤ) ≤ rswStoppedSquareNormalizeIso n x 1 ∧
    rswStoppedSquareNormalizeIso n x 1 ≤ (n : ℤ)
  simp only [rswStoppedSquareNormalizeIso_zero,
    rswStoppedSquareNormalizeIso_one]
  omega

@[simp]
theorem rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    rswStoppedSquareNormalizeIso n z ∈
        (brFilledHullStoppedBarrierNormalized hn hR).support ↔
      z ∈ (brFilledHullStoppedBarrier hn hR).support := by
  simp only [brFilledHullStoppedBarrierNormalized,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨x, hx, hzx⟩
    exact (rswStoppedSquareNormalizeIso n).injective hzx ▸ hx
  · intro hz
    exact ⟨z, hz, rfl⟩

@[simp]
theorem brPrimalTopReflectionIso_mem_stoppedBarrier_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    brPrimalTopReflectionIso n z ∈
        (brFilledHullStoppedBarrier hn hR).support ↔
      z ∈ (brFilledHullStoppedBarrier hn hR).support := by
  rw [mem_brFilledHullStoppedBarrier_support_iff hn hR,
    mem_brFilledHullStoppedBarrier_support_iff hn hR]
  constructor
  · rintro (hzLower | hzUpper)
    · exact Or.inr
        ((mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).2 hzLower)
    · exact Or.inl
        (by simpa only [brPrimalTopReflectionIso_involutive] using
          (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).1 hzUpper)
  · rintro (hzLower | hzUpper)
    · exact Or.inr
        ((mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).2
          (by simpa only [brPrimalTopReflectionIso_involutive] using hzLower))
    · exact Or.inl
        ((mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).1 hzUpper)

/-- A stopped-square vertex which is not on the stopped barrier also avoids the artificial
closed walk after normalization. -/
theorem rswStoppedSquareNormalizeIso_not_mem_stoppedBarrierClosedWalk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hzBox : 0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
      0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ))
    (hzBarrier : z ∉ (brFilledHullStoppedBarrier hn hR).support) :
    rswStoppedSquareNormalizeIso n z ∉
      (brFilledHullStoppedBarrierClosedWalk hn hR).support := by
  intro hzClosed
  rw [brFilledHullStoppedBarrierClosedWalk,
    SimpleGraph.Walk.mem_support_append_iff] at hzClosed
  rcases hzClosed with hzStopped | hzClosure
  · exact hzBarrier
      ((rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mp hzStopped)
  · rcases mem_brStoppedBarrierExteriorClosureWalk_support hzClosure with
      hzTop | hzBottom | hzLeft | hzAbove | hzBelow
    · apply hzBarrier
      apply (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mp
      rw [hzTop]
      exact (brFilledHullStoppedBarrierNormalized hn hR).end_mem_support
    · apply hzBarrier
      apply (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mp
      rw [hzBottom]
      exact (brFilledHullStoppedBarrierNormalized hn hR).start_mem_support
    · rw [rswStoppedSquareNormalizeIso_zero] at hzLeft
      omega
    · rw [rswStoppedSquareNormalizeIso_one] at hzAbove
      omega
    · rw [rswStoppedSquareNormalizeIso_one] at hzBelow
      omega

private theorem closedSquareWalkFaceParity_eq_start_of_mem_path_ne_end
    {o r z : SquareVertex} (c : squareGraph.Walk o o)
    (p : squareGraph.Walk r z) (hp : p.IsPath)
    (havoid : ∀ t ∈ p.support, t ≠ z → t ∉ c.support) :
    ∀ t ∈ p.support, t ≠ z →
      closedSquareWalkFaceParity c t = closedSquareWalkFaceParity c r := by
  induction p with
  | nil =>
      intro t ht htz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
      exact (htz ht).elim
  | @cons u v z huv q ih =>
      intro t ht htz
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · rfl
      · have hqPath : q.IsPath := hp.of_cons
        have huNotQ : u ∉ q.support :=
          (SimpleGraph.Walk.cons_isPath_iff huv q).mp hp |>.2
        have huz : u ≠ z := by
          intro huz
          apply huNotQ
          rw [huz]
          exact q.end_mem_support
        by_cases hvz : v = z
        · subst v
          have hqNil : q = .nil := q.isPath_iff_eq_nil.mp hqPath
          subst q
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
          exact (htz ht).elim
        · have huClosed := havoid u (by simp) huz
          have hvClosed := havoid v (by simp) hvz
          have htailAvoid : ∀ x ∈ q.support, x ≠ z → x ∉ c.support := by
            intro x hx hxz
            exact havoid x (by simp [hx]) hxz
          exact (ih hqPath htailAvoid t ht htz).trans
            (closedSquareWalkFaceParity_eq_of_adj_of_not_mem
              c huv huClosed hvClosed).symm

private theorem walk_horizontalRayCount_eq_zero_of_support_left
    {u v : SquareVertex} (p : squareGraph.Walk u v)
    (f : DualSquareVertex)
    (hleft : ∀ z ∈ p.support, z 0 ≤ f 0) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hleft x (p.fst_mem_support_of_mem_edges he)
      have hy := hleft y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay]
      omega

/-- Every coordinate weakly to the right of the stopped square has exterior parity zero. -/
theorem brFilledHullStoppedBarrierClosedWalk_parity_eq_zero_of_right
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (f : DualSquareVertex) (hf : 2 * (n : ℤ) ≤ f 0) :
    closedSquareWalkFaceParity (brFilledHullStoppedBarrierClosedWalk hn hR) f = 0 := by
  have hbarrier : (brFilledHullStoppedBarrierNormalized hn hR).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
    apply walk_horizontalRayCount_eq_zero_of_support_left _ f
    intro z hz
    have hz' := brFilledHullStoppedBarrierNormalized_support_coordinates hn hR hz
    omega
  have hclosure :
      (brStoppedBarrierExteriorClosureWalk n
        (brFilledHullStoppedBarrierEndpointNat hn hR)).edges.countP
          (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
    apply walk_horizontalRayCount_eq_zero_of_support_left _ f
    intro z hz
    rcases mem_brStoppedBarrierExteriorClosureWalk_support hz with
      rfl | rfl | hzLeft | hzTop | hzBottom
    · simp only [squareVertex]
      rw [brFilledHullStoppedBarrierEndpointNat_cast hn hR]
      have hc := brFilledHullLastMidlineVertex_coordinates hn hR
      omega
    · simp only [squareVertex]
      rw [brFilledHullStoppedBarrierEndpointNat_cast hn hR]
      have hc := brFilledHullLastMidlineVertex_coordinates hn hR
      omega
    · omega
    · have ha :
          (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) ≤
            2 * (n : ℤ) := by
        rw [brFilledHullStoppedBarrierEndpointNat_cast hn hR]
        exact (brFilledHullLastMidlineVertex_coordinates hn hR).2.1
      omega
    · have ha :
          (brFilledHullStoppedBarrierEndpointNat hn hR : ℤ) ≤
            2 * (n : ℤ) := by
        rw [brFilledHullStoppedBarrierEndpointNat_cast hn hR]
        exact (brFilledHullLastMidlineVertex_coordinates hn hR).2.1
      omega
  unfold closedSquareWalkFaceParity brFilledHullStoppedBarrierClosedWalk
  simp only [SimpleGraph.Walk.edges_append, List.countP_append]
  rw [hbarrier, hclosure]

/-- The source-faithful exterior region `U(π)`, expressed in centered-square coordinates.
A vertex belongs to the strict exterior when it is not on the normalized stopped barrier and
has the same (zero) mod-two index as the right side of the square. -/
def brFilledHullStoppedStrictUpperRegionNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : Finset SquareVertex := by
  classical
  exact (squareRectangleVertices (2 * n) n).filter fun z ↦
    z ∉ (brFilledHullStoppedBarrierNormalized hn hR).support ∧
      closedSquareWalkFaceParity (brFilledHullStoppedBarrierClosedWalk hn hR) z = 0 ∧
      closedSquareWalkFaceParity (brFilledHullStoppedBarrierClosedWalk hn hR)
        (brHorizontalAxisReflectionIso z) = 0

/-- Barrier vertices together with the strict exterior vertices. -/
def brFilledHullStoppedUpperRegionVerticesNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : Finset SquareVertex :=
  brFilledHullStoppedStrictUpperRegionNormalized hn hR ∪
    (brFilledHullStoppedBarrierNormalized hn hR).support.toFinset

theorem brFilledHullStoppedBarrierNormalized_support_mem_rectangle
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex}
    (hz : z ∈ (brFilledHullStoppedBarrierNormalized hn hR).support) :
    z ∈ squareRectangleVertices (2 * n) n := by
  rw [mem_squareRectangleVertices_iff]
  exact brFilledHullStoppedBarrierNormalized_support_coordinates hn hR hz

@[simp]
theorem mem_brFilledHullStoppedUpperRegionVerticesNormalized_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    z ∈ brFilledHullStoppedUpperRegionVerticesNormalized hn hR ↔
      z ∈ squareRectangleVertices (2 * n) n ∧
        (z ∈ (brFilledHullStoppedBarrierNormalized hn hR).support ∨
          (closedSquareWalkFaceParity
              (brFilledHullStoppedBarrierClosedWalk hn hR) z = 0 ∧
            closedSquareWalkFaceParity
              (brFilledHullStoppedBarrierClosedWalk hn hR)
                (brHorizontalAxisReflectionIso z) = 0)) := by
  classical
  simp only [brFilledHullStoppedUpperRegionVerticesNormalized,
    brFilledHullStoppedStrictUpperRegionNormalized, Finset.mem_union,
    Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro (⟨hzRect, _hzNot, hzParity, hzReflectParity⟩ | hzBarrier)
    · exact ⟨hzRect, Or.inr ⟨hzParity, hzReflectParity⟩⟩
    · exact ⟨brFilledHullStoppedBarrierNormalized_support_mem_rectangle
        hn hR hzBarrier, Or.inl hzBarrier⟩
  · rintro ⟨hzRect, hzBarrier | ⟨hzParity, hzReflectParity⟩⟩
    · exact Or.inr hzBarrier
    · by_cases hzBarrier : z ∈
          (brFilledHullStoppedBarrierNormalized hn hR).support
      · exact Or.inr hzBarrier
      · exact Or.inl ⟨hzRect, hzBarrier, hzParity, hzReflectParity⟩

/-- Bonds of the source region `U(π)`: both endpoints lie on or strictly outside the stopped
barrier, at least one endpoint is strict, and the bond is an allowed boundary-free square bond.
The last condition exactly removes bonds lying wholly in the barrier. -/
def brFilledHullStoppedUpperRegionEdgesNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : Finset SquareEdge := by
  classical
  exact (squareBoundaryFreeRectangleEdges (2 * n) n).filter fun e ↦
    e.1.out.1 ∈ brFilledHullStoppedUpperRegionVerticesNormalized hn hR ∧
      e.1.out.2 ∈ brFilledHullStoppedUpperRegionVerticesNormalized hn hR ∧
      (e.1.out.1 ∈ brFilledHullStoppedStrictUpperRegionNormalized hn hR ∨
        e.1.out.2 ∈ brFilledHullStoppedStrictUpperRegionNormalized hn hR)

theorem brFilledHullStoppedUpperRegionEdgesNormalized_subset_boundaryFree
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brFilledHullStoppedUpperRegionEdgesNormalized hn hR ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
  exact Finset.filter_subset _ _

/-- Every vertex on the right side of the centered square belongs to the closed exterior
region. -/
theorem squareRectangleRight_subset_stoppedUpperRegionVerticesNormalized
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    squareRectangleRight (2 * n) n ⊆
      brFilledHullStoppedUpperRegionVerticesNormalized hn hR := by
  intro z hz
  rw [mem_brFilledHullStoppedUpperRegionVerticesNormalized_iff hn hR]
  have hz' := mem_squareRectangleRight_iff.mp hz
  refine ⟨(Finset.mem_filter.mp hz).1, Or.inr ⟨?_, ?_⟩⟩
  · apply brFilledHullStoppedBarrierClosedWalk_parity_eq_zero_of_right hn hR
    omega
  · apply brFilledHullStoppedBarrierClosedWalk_parity_eq_zero_of_right hn hR
    simp only [brHorizontalAxisReflectionIso_zero]
    omega

@[simp]
theorem brHorizontalAxisReflectionIso_mem_stoppedBarrierNormalized_support_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    brHorizontalAxisReflectionIso z ∈
        (brFilledHullStoppedBarrierNormalized hn hR).support ↔
      z ∈ (brFilledHullStoppedBarrierNormalized hn hR).support := by
  let F := rswStoppedSquareNormalizeIso n
  let s := F.symm z
  have hs : F s = z := F.apply_symm_apply z
  have hs' : rswStoppedSquareNormalizeIso n s = z := by
    simpa only [F] using hs
  constructor
  · intro hz
    have htopNorm : F (brPrimalTopReflectionIso n s) ∈
        (brFilledHullStoppedBarrierNormalized hn hR).support := by
      rw [rswStoppedSquareNormalizeIso_topReflection]
      simpa only [hs'] using hz
    have htop : brPrimalTopReflectionIso n s ∈
        (brFilledHullStoppedBarrier hn hR).support :=
      (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mp htopNorm
    have hsBarrier : s ∈ (brFilledHullStoppedBarrier hn hR).support :=
      (brPrimalTopReflectionIso_mem_stoppedBarrier_support_iff hn hR).mp htop
    have hsNorm :=
      (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mpr hsBarrier
    simpa only [hs'] using hsNorm
  · intro hz
    have hsNorm : rswStoppedSquareNormalizeIso n s ∈
        (brFilledHullStoppedBarrierNormalized hn hR).support := by
      rw [hs']
      exact hz
    have hsBarrier : s ∈ (brFilledHullStoppedBarrier hn hR).support :=
      (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mp hsNorm
    have htop : brPrimalTopReflectionIso n s ∈
        (brFilledHullStoppedBarrier hn hR).support :=
      (brPrimalTopReflectionIso_mem_stoppedBarrier_support_iff hn hR).mpr hsBarrier
    have htopNorm :=
      (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
        hn hR).mpr htop
    rw [rswStoppedSquareNormalizeIso_topReflection] at htopNorm
    simpa only [hs'] using htopNorm

@[simp]
theorem brHorizontalAxisReflectionIso_mem_stoppedStrictUpperRegionNormalized_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    brHorizontalAxisReflectionIso z ∈
        brFilledHullStoppedStrictUpperRegionNormalized hn hR ↔
      z ∈ brFilledHullStoppedStrictUpperRegionNormalized hn hR := by
  classical
  simp only [brFilledHullStoppedStrictUpperRegionNormalized,
    Finset.mem_filter]
  rw [brHorizontalAxisReflectionIso_mem_rectangle_iff,
    brHorizontalAxisReflectionIso_mem_stoppedBarrierNormalized_support_iff hn hR]
  simp only [brHorizontalAxisReflectionIso_involutive]
  tauto

@[simp]
theorem brHorizontalAxisReflectionIso_mem_stoppedUpperRegionVerticesNormalized_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {z : SquareVertex} :
    brHorizontalAxisReflectionIso z ∈
        brFilledHullStoppedUpperRegionVerticesNormalized hn hR ↔
      z ∈ brFilledHullStoppedUpperRegionVerticesNormalized hn hR := by
  rw [mem_brFilledHullStoppedUpperRegionVerticesNormalized_iff hn hR,
    mem_brFilledHullStoppedUpperRegionVerticesNormalized_iff hn hR,
    brHorizontalAxisReflectionIso_mem_rectangle_iff,
    brHorizontalAxisReflectionIso_mem_stoppedBarrierNormalized_support_iff hn hR]
  simp only [brHorizontalAxisReflectionIso_involutive]
  tauto

/-! ### The source region and contact events in stopped-square coordinates -/

/-- The bonds of `U(π)` transported back to the stopped square `[0,2n] × [0,2n]`.  The
definition is written as a filter of the already verified stopped-square support so later
conditioning lemmas can read it directly. -/
def brFilledHullStoppedUpperRegionEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) : Finset SquareEdge := by
  classical
  exact (rswStoppedSquareEdges n).filter fun e ↦
    (∀ z ∈ (e : Sym2 SquareVertex),
      rswStoppedSquareNormalizeIso n z ∈
        brFilledHullStoppedUpperRegionVerticesNormalized hn hR) ∧
    ∃ z ∈ (e : Sym2 SquareVertex),
      rswStoppedSquareNormalizeIso n z ∈
        brFilledHullStoppedStrictUpperRegionNormalized hn hR

theorem brFilledHullStoppedUpperRegionEdges_subset_stoppedSquare
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brFilledHullStoppedUpperRegionEdges hn hR ⊆ rswStoppedSquareEdges n := by
  classical
  exact Finset.filter_subset _ _

@[simp]
theorem brPrimalTopReflectionIso_mapEdgeSet_mem_stoppedUpperRegionEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    (e : SquareEdge) :
    (brPrimalTopReflectionIso n).mapEdgeSet e ∈
        brFilledHullStoppedUpperRegionEdges hn hR ↔
      e ∈ brFilledHullStoppedUpperRegionEdges hn hR := by
  classical
  let T := brPrimalTopReflectionIso n
  have hstoppedForward : ∀ f : SquareEdge, f ∈ rswStoppedSquareEdges n →
      T.mapEdgeSet f ∈ rswStoppedSquareEdges n := by
    intro f hf
    have himage : T.mapEdgeSet f ∈
        (rswStoppedSquareEdges n).image T.mapEdgeSet :=
      Finset.mem_image.mpr ⟨f, hf, rfl⟩
    rw [show (rswStoppedSquareEdges n).image T.mapEdgeSet =
        rswStoppedSquareEdges n by
      simpa only [T] using brPrimalTopReflectionIso_image_rswStoppedSquareEdges n] at himage
    exact himage
  have hstopped : T.mapEdgeSet e ∈ rswStoppedSquareEdges n ↔
      e ∈ rswStoppedSquareEdges n := by
    constructor
    · intro he
      have hdouble := hstoppedForward (T.mapEdgeSet e) he
      simpa only [T, brPrimalTopReflectionIso_mapEdgeSet_involutive] using hdouble
    · exact hstoppedForward e
  simp only [brFilledHullStoppedUpperRegionEdges, Finset.mem_filter]
  rw [hstopped]
  constructor
  · rintro ⟨heStopped, hall, z, hz, hzStrict⟩
    refine ⟨heStopped, ?_, ?_⟩
    · intro x hx
      have hxMapped : T x ∈ (T.mapEdgeSet e : Sym2 SquareVertex) := by
        change T x ∈ Sym2.map T (e : Sym2 SquareVertex)
        exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
      have h := hall (T x) hxMapped
      have hnormalize : rswStoppedSquareNormalizeIso n (T x) =
          brHorizontalAxisReflectionIso (rswStoppedSquareNormalizeIso n x) := by
        simpa only [T] using rswStoppedSquareNormalizeIso_topReflection n x
      rw [hnormalize,
        brHorizontalAxisReflectionIso_mem_stoppedUpperRegionVerticesNormalized_iff hn hR] at h
      exact h
    · change z ∈ Sym2.map T (e : Sym2 SquareVertex) at hz
      rw [Sym2.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨y, hy, ?_⟩
      have hnormalize : rswStoppedSquareNormalizeIso n (T y) =
          brHorizontalAxisReflectionIso (rswStoppedSquareNormalizeIso n y) := by
        simpa only [T] using rswStoppedSquareNormalizeIso_topReflection n y
      rw [hnormalize,
        brHorizontalAxisReflectionIso_mem_stoppedStrictUpperRegionNormalized_iff hn hR] at hzStrict
      exact hzStrict
  · rintro ⟨heStopped, hall, z, hz, hzStrict⟩
    refine ⟨heStopped, ?_, ?_⟩
    · intro x hx
      change x ∈ Sym2.map T (e : Sym2 SquareVertex) at hx
      rw [Sym2.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hnormalize : rswStoppedSquareNormalizeIso n (T y) =
          brHorizontalAxisReflectionIso (rswStoppedSquareNormalizeIso n y) := by
        simpa only [T] using rswStoppedSquareNormalizeIso_topReflection n y
      rw [hnormalize,
        brHorizontalAxisReflectionIso_mem_stoppedUpperRegionVerticesNormalized_iff hn hR]
      exact hall y hy
    · refine ⟨T z, ?_, ?_⟩
      · change T z ∈ Sym2.map T (e : Sym2 SquareVertex)
        exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
      · rw [show rswStoppedSquareNormalizeIso n (T z) =
            brHorizontalAxisReflectionIso (rswStoppedSquareNormalizeIso n z) by
          simpa only [T] using rswStoppedSquareNormalizeIso_topReflection n z,
          brHorizontalAxisReflectionIso_mem_stoppedStrictUpperRegionNormalized_iff hn hR]
        exact hzStrict

theorem brPrimalTopReflectionIso_image_stoppedUpperRegionEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (brFilledHullStoppedUpperRegionEdges hn hR).image
        (brPrimalTopReflectionIso n).mapEdgeSet =
      brFilledHullStoppedUpperRegionEdges hn hR := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact (brPrimalTopReflectionIso_mapEdgeSet_mem_stoppedUpperRegionEdges_iff
      hn hR f).mpr hf
  · rw [Finset.card_image_of_injective _
      (brPrimalTopReflectionIso n).mapEdgeSet.injective]

@[simp]
theorem brPrimalTopReflectionIso_mem_stoppedSquareRightSide_iff
    (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n x ∈ rswStoppedSquareRightSide n ↔
      x ∈ rswStoppedSquareRightSide n := by
  rw [mem_rswStoppedSquareRightSide_iff,
    mem_rswStoppedSquareRightSide_iff]
  simp only [brPrimalTopReflectionIso_zero,
    brPrimalTopReflectionIso_one]
  omega

/-- Grimmett's event `M⁻_π`: the stopped lower tail is joined to the right side using only
bonds of the finite source region `U(π)`. -/
def brStoppedLowerUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (brFilledHullStoppedUpperRegionEdges hn hR) z r

/-- The reflected event `M⁺_π`. -/
def brStoppedUpperUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brPrimalTopReflectionIso n)
    (brStoppedLowerUpperRegionTailContactEvent R hn hR)

/-- The literal upper-tail version of `M⁺_π`, before identifying it with the reflected lower
event. -/
def brStoppedExplicitUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Set (EdgeConfiguration 2) :=
  ⋃ z ∈ (brReflectedFilledHullSelectedUpperTailPath hn hR).support.toFinset,
    ⋃ r ∈ rswStoppedSquareRightSide n,
      connectionEventIn 2 (brFilledHullStoppedUpperRegionEdges hn hR) z r

theorem measurableSet_brStoppedLowerUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedLowerUpperRegionTailContactEvent R hn hR) := by
  apply (brFilledHullSelectedUpperTailPath hn hR).support.toFinset.measurableSet_biUnion
  intro z _hz
  apply (rswStoppedSquareRightSide n).measurableSet_biUnion
  intro r _hr
  exact (dependsOn_connectionEventIn 2
    (brFilledHullStoppedUpperRegionEdges hn hR) z r).measurableSet

theorem isIncreasingEvent_brStoppedLowerUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedLowerUpperRegionTailContactEvent R hn hR) := by
  intro omega eta hmono
  simp only [brStoppedLowerUpperRegionTailContactEvent, Set.mem_iUnion]
  rintro ⟨z, hz, r, hr, hzr⟩
  exact ⟨z, hz, r, hr,
    isIncreasingEvent_connectionEventIn 2 _ z r hmono hzr⟩

theorem measurableSet_brStoppedUpperUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    MeasurableSet (brStoppedUpperUpperRegionTailContactEvent R hn hR) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_brStoppedLowerUpperRegionTailContactEvent R hn hR)

theorem isIncreasingEvent_brStoppedUpperUpperRegionTailContactEvent
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    IsIncreasingEvent (brStoppedUpperUpperRegionTailContactEvent R hn hR) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_brStoppedLowerUpperRegionTailContactEvent R hn hR)

/-- Reflection exchanges the lower source-region contact event with its literal upper-tail
counterpart. -/
theorem cubicGraphIsoEvent_brStoppedLowerUpperRegionTailContactEvent_eq_explicitUpper
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    cubicGraphIsoEvent (brPrimalTopReflectionIso n)
        (brStoppedLowerUpperRegionTailContactEvent R hn hR) =
      brStoppedExplicitUpperRegionTailContactEvent R hn hR := by
  let F := brPrimalTopReflectionIso n
  ext omega
  change cubicGraphIsoConfigurationPullback F omega ∈
      brStoppedLowerUpperRegionTailContactEvent R hn hR ↔
    omega ∈ brStoppedExplicitUpperRegionTailContactEvent R hn hR
  simp only [brStoppedLowerUpperRegionTailContactEvent,
    brStoppedExplicitUpperRegionTailContactEvent,
    Set.mem_iUnion, List.mem_toFinset]
  constructor
  · rintro ⟨z, hz, r, hr, hzr⟩
    have hzr' :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (brFilledHullStoppedUpperRegionEdges hn hR) omega z r).mp hzr
    rw [show (brFilledHullStoppedUpperRegionEdges hn hR).image F.mapEdgeSet =
        brFilledHullStoppedUpperRegionEdges hn hR by
      simpa only [F] using
        brPrimalTopReflectionIso_image_stoppedUpperRegionEdges hn hR] at hzr'
    refine ⟨F z, ?_, F r, ?_, hzr'⟩
    · rw [mem_brReflectedFilledHullSelectedUpperTailPath_support_iff]
      simpa only [F, brPrimalTopReflectionIso_involutive] using hz
    · exact (brPrimalTopReflectionIso_mem_stoppedSquareRightSide_iff n r).2 hr
  · rintro ⟨z, hz, r, hr, hzr⟩
    refine ⟨F z, ?_, F r, ?_, ?_⟩
    · exact (mem_brReflectedFilledHullSelectedUpperTailPath_support_iff hn hR).mp hz
    · apply (brPrimalTopReflectionIso_mem_stoppedSquareRightSide_iff n (F r)).1
      simpa only [F, brPrimalTopReflectionIso_involutive] using hr
    · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (brFilledHullStoppedUpperRegionEdges hn hR) omega (F z) (F r)).mpr
      rw [show (brFilledHullStoppedUpperRegionEdges hn hR).image F.mapEdgeSet =
          brFilledHullStoppedUpperRegionEdges hn hR by
        simpa only [F] using
          brPrimalTopReflectionIso_image_stoppedUpperRegionEdges hn hR]
      simpa only [F, brPrimalTopReflectionIso_involutive] using hzr

theorem bernoulliBondMeasure_real_brStoppedUpperUpperRegionTailContactEvent_eq_lower
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    (bernoulliBondMeasure 2 p).real
        (brStoppedUpperUpperRegionTailContactEvent R hn hR) =
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerUpperRegionTailContactEvent R hn hR) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_brStoppedLowerUpperRegionTailContactEvent R hn hR)

/-- A source-region contact is an ordinary stopped-tail contact. -/
theorem brStoppedLowerUpperRegionTailContactEvent_subset_tailContact
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brStoppedLowerUpperRegionTailContactEvent R hn hR ⊆
      brStoppedLowerTailContactEvent R hn hR := by
  intro omega homega
  simp only [brStoppedLowerUpperRegionTailContactEvent,
    brStoppedLowerTailContactEvent, Set.mem_iUnion] at homega ⊢
  obtain ⟨z, hz, r, hr, hzr⟩ := homega
  exact ⟨z, hz, r, hr, connectionEventIn_mono
    (brFilledHullStoppedUpperRegionEdges_subset_stoppedSquare hn hR) z r hzr⟩

/-- A square crossing, trimmed at its first visit to the doubled stopped tail, stays in the
finite source region `U(π)`.  Thus it reaches either the lower or the upper literal tail through
`U(π)`. -/
theorem rswStoppedSquareCrossingEvent_subset_upperRegionTailContact_union_explicit
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerUpperRegionTailContactEvent R hn hR ∪
        brStoppedExplicitUpperRegionTailContactEvent R hn hR := by
  classical
  intro omega homega
  obtain ⟨u, v, q, hu0, _hu1Lower, _hu1Upper, hv,
      hqOpen, hqEdges, hqSupport⟩ :=
    exists_rswStoppedSquareCrossingWalk_of_mem homega
  have hvCoords := mem_rswStoppedSquareRightSide_iff.mp hv
  obtain ⟨z0, hz0q, hz0Barrier⟩ :=
    squareWalk_support_inter_brFilledHullStoppedBarrier
      hn hR q hu0 hvCoords.1 hqSupport
  let barrier : Finset SquareVertex :=
    (brFilledHullStoppedBarrier hn hR).support.toFinset
  let war := q.reverse
  have hinter : {t ∈ barrier | t ∈ war.support}.Nonempty := by
    refine ⟨z0, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact List.mem_toFinset.mpr hz0Barrier
    · simpa [war] using hz0q
  obtain ⟨z, hzBarrierFinset, hzWar, hzFirst⟩ :=
    war.exists_mem_support_forall_mem_support_imp_eq barrier hinter
  have hzBarrier : z ∈ (brFilledHullStoppedBarrier hn hR).support :=
    List.mem_toFinset.mp hzBarrierFinset
  let arm : squareGraph.Walk v z := war.takeUntil z hzWar
  let path : squareGraph.Walk v z := arm.toPath
  have harmOpen : walkIsOpen omega arm :=
    walkIsOpen_of_edges_subset (walkIsOpen_reverse hqOpen)
      (war.edges_takeUntil_subset hzWar)
  have hpathOpen : walkIsOpen omega path := walkIsOpen_toPath arm harmOpen
  have hpathStopped : walkEdgeFinset path ⊆ rswStoppedSquareEdges n := by
    intro e he
    rw [mem_walkEdgeFinset_iff] at he
    have heArm : (e : Sym2 SquareVertex) ∈ arm.edges :=
      arm.edges_toPath_subset he
    have heWar : (e : Sym2 SquareVertex) ∈ war.edges :=
      war.edges_takeUntil_subset hzWar heArm
    simp only [war, SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heWar
    exact hqEdges ((mem_walkEdgeFinset_iff q e).mpr heWar)
  have hpathBox : ∀ t ∈ path.support,
      0 ≤ t 0 ∧ t 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ t 1 ∧ t 1 ≤ 2 * (n : ℤ) := by
    intro t ht
    have htArm : t ∈ arm.support := arm.support_toPath_subset ht
    have htWar : t ∈ war.support :=
      war.support_takeUntil_subset_support hzWar htArm
    have htQ : t ∈ q.support := by
      simpa only [war, SimpleGraph.Walk.support_reverse, List.mem_reverse] using htWar
    exact hqSupport t htQ
  have hfirstPath : ∀ t ∈ (brFilledHullStoppedBarrier hn hR).support,
      t ∈ path.support → t = z := by
    intro t htBarrier htPath
    apply hzFirst t (List.mem_toFinset.mpr htBarrier)
    exact arm.support_toPath_subset htPath
  let F := rswStoppedSquareNormalizeIso n
  let pathN : squareGraph.Walk (F v) (F z) := path.map F.toHom
  have hpathPath : path.IsPath := by
    simpa only [path] using arm.toPath.property
  have hpathNPath : pathN.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective F.injective hpathPath
  have hpathNAvoid : ∀ t ∈ pathN.support, t ≠ F z →
      t ∉ (brFilledHullStoppedBarrierClosedWalk hn hR).support := by
    intro t ht htEnd
    simp only [pathN, SimpleGraph.Walk.support_map, List.mem_map] at ht
    obtain ⟨s, hsPath, rfl⟩ := ht
    have hsz : s ≠ z := fun hsz ↦ htEnd (congrArg F hsz)
    apply rswStoppedSquareNormalizeIso_not_mem_stoppedBarrierClosedWalk
      hn hR (hpathBox s hsPath)
    intro hsBarrier
    exact hsz (hfirstPath s hsBarrier hsPath)
  have hvParity : closedSquareWalkFaceParity
      (brFilledHullStoppedBarrierClosedWalk hn hR) (F v) = 0 := by
    apply brFilledHullStoppedBarrierClosedWalk_parity_eq_zero_of_right hn hR
    simpa only [F, rswStoppedSquareNormalizeIso_zero] using hvCoords.1.ge
  have hpathParity : ∀ t ∈ path.support, t ≠ z →
      closedSquareWalkFaceParity
        (brFilledHullStoppedBarrierClosedWalk hn hR) (F t) = 0 := by
    intro t ht htz
    have htN : F t ∈ pathN.support := by
      simp only [pathN, SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨t, ht, rfl⟩
    have htNe : F t ≠ F z := F.injective.ne htz
    exact (closedSquareWalkFaceParity_eq_start_of_mem_path_ne_end
      (brFilledHullStoppedBarrierClosedWalk hn hR) pathN hpathNPath
      hpathNAvoid (F t) htN htNe).trans hvParity
  let T := brPrimalTopReflectionIso n
  let RF : squareGraph ≃g squareGraph := T.trans F
  let pathRN : squareGraph.Walk (RF v) (RF z) := path.map RF.toHom
  have hpathRNPath : pathRN.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective RF.injective hpathPath
  have hpathRNAvoid : ∀ t ∈ pathRN.support, t ≠ RF z →
      t ∉ (brFilledHullStoppedBarrierClosedWalk hn hR).support := by
    intro t ht htEnd
    simp only [pathRN, SimpleGraph.Walk.support_map, List.mem_map] at ht
    obtain ⟨s, hsPath, rfl⟩ := ht
    have hsz : s ≠ z := fun hsz ↦ htEnd (congrArg RF hsz)
    apply rswStoppedSquareNormalizeIso_not_mem_stoppedBarrierClosedWalk hn hR
    · have hsBox := hpathBox s hsPath
      change 0 ≤ T s 0 ∧ T s 0 ≤ 2 * (n : ℤ) ∧
        0 ≤ T s 1 ∧ T s 1 ≤ 2 * (n : ℤ)
      simp only [T, brPrimalTopReflectionIso_zero,
        brPrimalTopReflectionIso_one]
      omega
    · change brPrimalTopReflectionIso n s ∉
        (brFilledHullStoppedBarrier hn hR).support
      rw [brPrimalTopReflectionIso_mem_stoppedBarrier_support_iff hn hR]
      intro hsBarrier
      exact hsz (hfirstPath s hsBarrier hsPath)
  have hvRParity : closedSquareWalkFaceParity
      (brFilledHullStoppedBarrierClosedWalk hn hR) (RF v) = 0 := by
    apply brFilledHullStoppedBarrierClosedWalk_parity_eq_zero_of_right hn hR
    change 2 * (n : ℤ) ≤ F (T v) 0
    simp only [F, T, rswStoppedSquareNormalizeIso_zero,
      brPrimalTopReflectionIso_zero]
    omega
  have hpathReflectParity : ∀ t ∈ path.support, t ≠ z →
      closedSquareWalkFaceParity
        (brFilledHullStoppedBarrierClosedWalk hn hR)
          (brHorizontalAxisReflectionIso (F t)) = 0 := by
    intro t ht htz
    have htRN : RF t ∈ pathRN.support := by
      simp only [pathRN, SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨t, ht, rfl⟩
    have htNe : RF t ≠ RF z := RF.injective.ne htz
    have hparity := closedSquareWalkFaceParity_eq_start_of_mem_path_ne_end
      (brFilledHullStoppedBarrierClosedWalk hn hR) pathRN hpathRNPath
      hpathRNAvoid (RF t) htRN htNe
    have hRFt : RF t = brHorizontalAxisReflectionIso (F t) := by
      change F (T t) = brHorizontalAxisReflectionIso (F t)
      simpa only [F, T] using rswStoppedSquareNormalizeIso_topReflection n t
    rw [← hRFt]
    exact hparity.trans hvRParity
  have hstrict : ∀ t ∈ path.support, t ≠ z →
      F t ∈ brFilledHullStoppedStrictUpperRegionNormalized hn hR := by
    intro t ht htz
    rw [brFilledHullStoppedStrictUpperRegionNormalized, Finset.mem_filter]
    refine ⟨?_, ?_, hpathParity t ht htz, hpathReflectParity t ht htz⟩
    · rw [mem_squareRectangleVertices_iff]
      have htBox := hpathBox t ht
      simp only [F, rswStoppedSquareNormalizeIso_zero,
        rswStoppedSquareNormalizeIso_one]
      omega
    · intro htBarrierN
      have htBarrier :=
        (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
          hn hR).mp htBarrierN
      exact htz (hfirstPath t htBarrier ht)
  have hvertex : ∀ t ∈ path.support,
      F t ∈ brFilledHullStoppedUpperRegionVerticesNormalized hn hR := by
    intro t ht
    by_cases htz : t = z
    · subst t
      rw [mem_brFilledHullStoppedUpperRegionVerticesNormalized_iff hn hR]
      refine ⟨?_, Or.inl ?_⟩
      · rw [mem_squareRectangleVertices_iff]
        have hzBox := hpathBox z ht
        simp only [F, rswStoppedSquareNormalizeIso_zero,
          rswStoppedSquareNormalizeIso_one]
        omega
      · exact
          (rswStoppedSquareNormalizeIso_mem_stoppedBarrierNormalized_support_iff
            hn hR).mpr hzBarrier
    · rw [brFilledHullStoppedUpperRegionVerticesNormalized,
        Finset.mem_union]
      exact Or.inl (hstrict t ht htz)
  have hpathUpperRegion : walkEdgeFinset path ⊆
      brFilledHullStoppedUpperRegionEdges hn hR := by
    intro e he
    rw [brFilledHullStoppedUpperRegionEdges, Finset.mem_filter]
    have heRaw : (e : Sym2 SquareVertex) ∈ path.edges :=
      (mem_walkEdgeFinset_iff path e).mp he
    have hxPath : e.1.out.1 ∈ path.support :=
      path.mem_support_of_mem_edges heRaw (Sym2.out_fst_mem e.1)
    have hyPath : e.1.out.2 ∈ path.support :=
      path.mem_support_of_mem_edges heRaw (Sym2.out_snd_mem e.1)
    refine ⟨hpathStopped he, ?_, ?_⟩
    · intro t htEdge
      rw [← e.1.out_eq, Sym2.mem_iff] at htEdge
      rcases htEdge with rfl | rfl
      · exact hvertex _ hxPath
      · exact hvertex _ hyPath
    · by_cases hxz : e.1.out.1 = z
      · refine ⟨e.1.out.2, Sym2.out_snd_mem e.1, ?_⟩
        apply hstrict _ hyPath
        intro hyz
        have hadj : squareGraph.Adj e.1.out.1 e.1.out.2 := by
          apply squareGraph.mem_edgeSet.mp
          have hout : s(e.1.out.1, e.1.out.2) = (e.1 : Sym2 SquareVertex) :=
            e.1.out_eq
          rw [hout]
          exact e.2
        exact hadj.ne (hxz.trans hyz.symm)
      · exact ⟨e.1.out.1, Sym2.out_fst_mem e.1,
          hstrict _ hxPath hxz⟩
  have hreverseUpperRegion : walkEdgeFinset path.reverse ⊆
      brFilledHullStoppedUpperRegionEdges hn hR := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    exact hpathUpperRegion ((mem_walkEdgeFinset_iff path e).mpr he)
  have hzv : omega ∈ connectionEventIn 2
      (brFilledHullStoppedUpperRegionEdges hn hR) z v :=
    ⟨path.reverse, walkIsOpen_reverse hpathOpen, hreverseUpperRegion⟩
  rw [mem_brFilledHullStoppedBarrier_support_iff hn hR] at hzBarrier
  rcases hzBarrier with hzLower | hzUpper
  · left
    simp only [brStoppedLowerUpperRegionTailContactEvent,
      Set.mem_iUnion, List.mem_toFinset]
    exact ⟨z, hzLower, v, hv, hzv⟩
  · right
    simp only [brStoppedExplicitUpperRegionTailContactEvent,
      Set.mem_iUnion, List.mem_toFinset]
    exact ⟨z, hzUpper, v, hv, hzv⟩

/-- Source-faithful square-crossing cover by `M⁻_π ∪ M⁺_π`. -/
theorem rswStoppedSquareCrossingEvent_subset_upperRegionTailContact_union
    {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    rswStoppedSquareCrossingEvent n ⊆
      brStoppedLowerUpperRegionTailContactEvent R hn hR ∪
        brStoppedUpperUpperRegionTailContactEvent R hn hR := by
  rw [brStoppedUpperUpperRegionTailContactEvent,
    cubicGraphIsoEvent_brStoppedLowerUpperRegionTailContactEvent_eq_explicitUpper
      R hn hR]
  exact rswStoppedSquareCrossingEvent_subset_upperRegionTailContact_union_explicit
    R hn hR

/-- The lower source-region contact has the square-root probability bound, before conditioning
on the stopped exploration fiber. -/
theorem one_sub_sqrt_rswSquare_le_brStoppedLowerUpperRegionTailContactProbability
    (p : I) {n : ℕ} (R : Finset (BRLeftmostDualVertex n))
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    1 - Real.sqrt (1 - rswSquareCrossingProbability p n) ≤
      (bernoulliBondMeasure 2 p).real
        (brStoppedLowerUpperRegionTailContactEvent R hn hR) := by
  rw [← bernoulliBondMeasure_real_rswStoppedSquareCrossingEvent p n]
  exact one_sub_sqrt_one_sub_measureReal_le_of_subset_union_of_eq (d := 2) p
    (H := rswStoppedSquareCrossingEvent n)
    (L := brStoppedLowerUpperRegionTailContactEvent R hn hR)
    (U := brStoppedUpperUpperRegionTailContactEvent R hn hR)
    (rswStoppedSquareCrossingEvent_subset_upperRegionTailContact_union R hn hR)
    (bernoulliBondMeasure_real_brStoppedUpperUpperRegionTailContactEvent_eq_lower
      p R hn hR)
    (isIncreasingEvent_brStoppedLowerUpperRegionTailContactEvent R hn hR)
    (isIncreasingEvent_brStoppedUpperUpperRegionTailContactEvent R hn hR)
    (measurableSet_brStoppedLowerUpperRegionTailContactEvent R hn hR)
    (measurableSet_brStoppedUpperUpperRegionTailContactEvent R hn hR)

end

end Percolation
