import Percolation.Critical.CubicSymmetry
import Percolation.Planar.AlternatingPaths

/-!
# Arbitrary crossings of a square intersect

`AlternatingPaths` proves the corner-to-side form of the discrete Jordan-arc lemma.  This file
derives the form used by RSW: a walk joining the left and right sides of a square meets every walk
joining its bottom and top sides.  The proof embeds the square one lattice spacing inside a larger
square.  The four short outer-shell connectors cannot create a spurious intersection.
-/

namespace Percolation

/-- Translation by `(1,1)`, used to leave a one-edge shell around a square. -/
def squareShiftOneIso : squareGraph ≃g squareGraph :=
  cubicTranslationIso cubicOrigin (squareVertex 1 1)

@[simp]
theorem squareShiftOneIso_apply (x : SquareVertex) (i : Fin 2) :
    squareShiftOneIso x i = x i + 1 := by
  fin_cases i <;>
    simp [squareShiftOneIso, cubicTranslationIso_apply, cubicTranslate, cubicOrigin,
      squareVertex]

@[simp]
theorem squareShiftOneIso_toHom_apply (x : SquareVertex) (i : Fin 2) :
    squareShiftOneIso.toHom x i = x i + 1 :=
  squareShiftOneIso_apply x i

/-- The outer-shell connector from the lower-left corner to `(1,a+1)`. -/
def squareOuterLeftConnector (a : ℕ) :
    squareGraph.Walk (squareVertex 0 0) (squareVertex 1 (a + 1 : ℕ)) := by
  let steps : List (CubicDirection 2) :=
    List.replicate (a + 1) (⟨1, by decide⟩, true) ++ [(⟨0, by decide⟩, true)]
  exact (cubicWalkFrom (squareVertex 0 0) steps).copy rfl (by
    ext i
    fin_cases i <;>
      simp [steps, cubicEndpointFrom_append, cubicEndpointFrom_replicate_pos,
        cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, squareVertex, cubicOrigin])

/-- The one-edge connector from `(m+1,b+1)` to the right side of the enlarged square. -/
def squareOuterRightConnector (m b : ℕ) :
    squareGraph.Walk (squareVertex (m + 1 : ℕ) (b + 1 : ℕ))
      (squareVertex (m + 2 : ℕ) (b + 1 : ℕ)) :=
  (cubicWalkFrom (squareVertex (m + 1 : ℕ) (b + 1 : ℕ))
    [(⟨0, by decide⟩, true)]).copy rfl (by
      ext i
      fin_cases i <;>
        simp [cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, squareVertex] <;>
        omega)

/-- The outer-shell connector from the lower-right corner to `(c+1,1)`. -/
def squareOuterBottomConnector (m c : ℕ) (hc : c ≤ m) :
    squareGraph.Walk (squareVertex (m + 2 : ℕ) 0)
      (squareVertex (c + 1 : ℕ) 1) := by
  let steps : List (CubicDirection 2) :=
    List.replicate (m + 1 - c) (⟨0, by decide⟩, false) ++
      [(⟨1, by decide⟩, true)]
  exact (cubicWalkFrom (squareVertex (m + 2 : ℕ) 0) steps).copy rfl (by
    have hcm : c ≤ m + 1 := hc.trans (Nat.le_succ m)
    ext i
    fin_cases i <;>
      simp [steps, cubicEndpointFrom_append, cubicEndpointFrom_replicate_neg,
        cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, squareVertex,
        Nat.cast_sub hcm] <;>
      omega)

/-- The one-edge connector from `(d+1,m+1)` to the top side of the enlarged square. -/
def squareOuterTopConnector (m d : ℕ) :
    squareGraph.Walk (squareVertex (d + 1 : ℕ) (m + 1 : ℕ))
      (squareVertex (d + 1 : ℕ) (m + 2 : ℕ)) :=
  (cubicWalkFrom (squareVertex (d + 1 : ℕ) (m + 1 : ℕ))
    [(⟨1, by decide⟩, true)]).copy rfl (by
      ext i
      fin_cases i <;>
        simp [cubicEndpointFrom, cubicStepFrom, cubicDirectionIncrement, squareVertex] <;>
        omega)

private theorem squareOuterLeftConnector_support
    {a : ℕ} {z : SquareVertex} (hz : z ∈ (squareOuterLeftConnector a).support) :
    (z 0 = 0 ∧ 0 ≤ z 1 ∧ z 1 ≤ a + 1) ∨
      z = squareVertex 1 (a + 1 : ℕ) := by
  simp only [squareOuterLeftConnector, SimpleGraph.Walk.support_copy,
    cubicWalkFrom_support] at hz
  rw [mem_cubicVerticesFrom_append_iff] at hz
  rcases hz with hv | hv
  · left
    have h0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex 0 0) (⟨1, by decide⟩) (⟨0, by decide⟩) (a + 1) (by decide) hv
    have h1 := cubicVerticesFrom_replicate_pos_coord_between
      (squareVertex 0 0) (⟨1, by decide⟩) (a + 1) hv
    simp [squareVertex] at h0 h1 ⊢
    omega
  · simp only [cubicEndpointFrom_replicate_pos] at hv
    simp only [cubicVerticesFrom_cons, cubicVerticesFrom_nil, List.mem_cons,
      List.mem_singleton] at hv
    rcases hv with hv | hv
    · left
      subst z
      simp [squareVertex, cubicOrigin]
      positivity
    · rcases hv with hv | hv
      · right
        subst z
        ext i
        fin_cases i <;>
          simp [squareVertex, cubicStepFrom, cubicDirectionIncrement, cubicOrigin]
      · simpa using hv

private theorem squareOuterRightConnector_support
    {m b : ℕ} {z : SquareVertex} (hz : z ∈ (squareOuterRightConnector m b).support) :
    z = squareVertex (m + 1 : ℕ) (b + 1 : ℕ) ∨
      z = squareVertex (m + 2 : ℕ) (b + 1 : ℕ) := by
  simp only [squareOuterRightConnector, SimpleGraph.Walk.support_copy,
    cubicWalkFrom_support, cubicVerticesFrom_cons, cubicVerticesFrom_nil,
    List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | hz
  · exact Or.inl rfl
  · rcases hz with hz | hz
    · right
      subst z
      ext i
      fin_cases i <;>
        simp [cubicStepFrom, cubicDirectionIncrement, squareVertex] <;>
        omega
    · simpa using hz

private theorem squareOuterBottomConnector_support
    {m c : ℕ} (hc : c ≤ m) {z : SquareVertex}
    (hz : z ∈ (squareOuterBottomConnector m c hc).support) :
    (z 1 = 0 ∧ c + 1 ≤ z 0 ∧ z 0 ≤ m + 2) ∨
      z = squareVertex (c + 1 : ℕ) 1 := by
  simp only [squareOuterBottomConnector, SimpleGraph.Walk.support_copy,
    cubicWalkFrom_support] at hz
  rw [mem_cubicVerticesFrom_append_iff] at hz
  rcases hz with hv | hv
  · left
    have h0 := cubicVerticesFrom_replicate_neg_coord_between
      (squareVertex (m + 2 : ℕ) 0) (⟨0, by decide⟩) (m + 1 - c) hv
    have h1 := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
      (squareVertex (m + 2 : ℕ) 0) (⟨0, by decide⟩) (⟨1, by decide⟩)
        (m + 1 - c) (by decide) hv
    have hcm : c ≤ m + 1 := hc.trans (Nat.le_succ m)
    simp [squareVertex, Nat.cast_sub hcm] at h0 h1 ⊢
    omega
  · simp only [cubicEndpointFrom_replicate_neg] at hv
    simp only [cubicVerticesFrom_cons, cubicVerticesFrom_nil, List.mem_cons,
      List.mem_singleton] at hv
    rcases hv with hv | hv
    · left
      subst z
      have hcm : c ≤ m + 1 := hc.trans (Nat.le_succ m)
      simp [squareVertex, Nat.cast_sub hcm]
      omega
    · rcases hv with hv | hv
      · right
        subst z
        have hcm : c ≤ m + 1 := hc.trans (Nat.le_succ m)
        ext i
        fin_cases i <;>
          simp [squareVertex, cubicStepFrom, cubicDirectionIncrement, Nat.cast_sub hcm] <;>
          omega
      · simpa using hv

private theorem squareOuterTopConnector_support
    {m d : ℕ} {z : SquareVertex} (hz : z ∈ (squareOuterTopConnector m d).support) :
    z = squareVertex (d + 1 : ℕ) (m + 1 : ℕ) ∨
      z = squareVertex (d + 1 : ℕ) (m + 2 : ℕ) := by
  simp only [squareOuterTopConnector, SimpleGraph.Walk.support_copy,
    cubicWalkFrom_support, cubicVerticesFrom_cons, cubicVerticesFrom_nil,
    List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | hz
  · exact Or.inl rfl
  · rcases hz with hz | hz
    · right
      subst z
      ext i
      fin_cases i <;>
        simp [cubicStepFrom, cubicDirectionIncrement, squareVertex] <;>
        omega
    · simpa using hz

/-- Any left-right square-grid walk meets any bottom-top walk in the same square. -/
theorem squareWalk_support_inter_of_left_right_and_bottom_top
    {m a b c d : ℕ} (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) (hd : d ≤ m)
    (p : squareGraph.Walk (squareVertex 0 (a : ℤ))
      (squareVertex (m : ℤ) (b : ℤ)))
    (q : squareGraph.Walk (squareVertex (c : ℤ) 0)
      (squareVertex (d : ℤ) (m : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let ps : squareGraph.Walk (squareVertex 1 (a + 1 : ℕ))
      (squareVertex (m + 1 : ℕ) (b + 1 : ℕ)) :=
    (p.map squareShiftOneIso.toHom).copy (by
      ext i
      fin_cases i <;> simp [squareVertex]) (by
      ext i
      fin_cases i <;> simp [squareVertex])
  let qs : squareGraph.Walk (squareVertex (c + 1 : ℕ) 1)
      (squareVertex (d + 1 : ℕ) (m + 1 : ℕ)) :=
    (q.map squareShiftOneIso.toHom).copy (by
      ext i
      fin_cases i <;> simp [squareVertex]) (by
      ext i
      fin_cases i <;> simp [squareVertex])
  let P := (squareOuterLeftConnector a).append
    (ps.append (squareOuterRightConnector m b))
  let Q := (squareOuterBottomConnector m c hc).append
    (qs.append (squareOuterTopConnector m d))
  have hPbox : ∀ z ∈ P.support,
      0 ≤ z 0 ∧ z 0 ≤ m + 2 ∧ 0 ≤ z 1 ∧ z 1 ≤ m + 2 := by
    intro z hz
    simp only [P, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · rcases squareOuterLeftConnector_support hz with hz | rfl
      · omega
      · simp [squareVertex]; omega
    · simp only [ps, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hz
      rcases hz with ⟨x, hx, rfl⟩
      have h := hpbox x hx
      simp only [squareShiftOneIso_toHom_apply]
      omega
    · rcases squareOuterRightConnector_support hz with rfl | rfl <;>
        simp [squareVertex] <;> omega
  have hQbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ m + 2 ∧ 0 ≤ z 1 ∧ z 1 ≤ m + 2 := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · rcases squareOuterBottomConnector_support hc hz with hz | rfl
      · omega
      · simp [squareVertex]; omega
    · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hz
      rcases hz with ⟨x, hx, rfl⟩
      have h := hqbox x hx
      simp only [squareShiftOneIso_toHom_apply]
      omega
    · rcases squareOuterTopConnector_support hz with rfl | rfl <;>
        simp [squareVertex] <;> omega
  by_contra hno
  push_neg at hno
  obtain ⟨z, hzP, hzQ⟩ :=
    squareWalk_support_inter_of_bottomLeft_right_and_bottomRight_top
      (show b + 1 ≤ m + 2 by omega) (show d + 1 ≤ m + 2 by omega) P Q hPbox hQbox
  simp only [P, Q, SimpleGraph.Walk.mem_support_append_iff] at hzP hzQ
  rcases hzP with hzPL | hzPs | hzPR
  · rcases squareOuterLeftConnector_support hzPL with hzPL | hzPL
    · rcases hzQ with hzQB | hzQs | hzQT
      · rcases squareOuterBottomConnector_support hc hzQB with hzQB | hzQB
        · omega
        · have h0 := congrFun hzQB 0
          simp [squareVertex] at h0
          omega
      · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
          List.mem_map] at hzQs
        rcases hzQs with ⟨y, hy, hyz⟩
        have hybox := hqbox y hy
        have hy0 := congrFun hyz 0
        simp only [squareShiftOneIso_toHom_apply] at hy0
        omega
      · rcases squareOuterTopConnector_support hzQT with hzQT | hzQT
        · have h0 := congrFun hzQT 0
          simp [squareVertex] at h0
          omega
        · have h0 := congrFun hzQT 0
          simp [squareVertex] at h0
          omega
    · rcases hzQ with hzQB | hzQs | hzQT
      · rcases squareOuterBottomConnector_support hc hzQB with hzQB | hzQB
        · have h1 := congrFun hzPL 1
          simp [squareVertex] at h1
          omega
        · have hpq : squareVertex 0 (a : ℤ) = squareVertex (c : ℤ) 0 := by
            apply squareShiftOneIso.injective
            calc
              squareShiftOneIso (squareVertex 0 (a : ℤ)) =
                  squareVertex 1 (a + 1 : ℕ) := by ext i; fin_cases i <;> simp [squareVertex]
              _ = squareVertex (c + 1 : ℕ) 1 := hzPL.symm.trans hzQB
              _ = squareShiftOneIso (squareVertex (c : ℤ) 0) := by
                ext i; fin_cases i <;> simp [squareVertex]
          exact (hno _ p.start_mem_support) (hpq.symm ▸ q.start_mem_support)
      · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
          List.mem_map] at hzQs
        rcases hzQs with ⟨y, hy, hyz⟩
        have hpy : squareVertex 0 (a : ℤ) = y := by
          apply squareShiftOneIso.injective
          calc
            squareShiftOneIso (squareVertex 0 (a : ℤ)) =
                squareVertex 1 (a + 1 : ℕ) := by ext i; fin_cases i <;> simp [squareVertex]
            _ = squareShiftOneIso y := hzPL.symm.trans hyz.symm
        exact (hno _ p.start_mem_support) (hpy.symm ▸ hy)
      · rcases squareOuterTopConnector_support hzQT with hzQT | hzQT
        · have hpq : squareVertex 0 (a : ℤ) = squareVertex (d : ℤ) (m : ℤ) := by
            apply squareShiftOneIso.injective
            calc
              squareShiftOneIso (squareVertex 0 (a : ℤ)) =
                  squareVertex 1 (a + 1 : ℕ) := by ext i; fin_cases i <;> simp [squareVertex]
              _ = squareVertex (d + 1 : ℕ) (m + 1 : ℕ) := hzPL.symm.trans hzQT
              _ = squareShiftOneIso (squareVertex (d : ℤ) (m : ℤ)) := by
                ext i; fin_cases i <;> simp [squareVertex]
          exact (hno _ p.start_mem_support) (hpq.symm ▸ q.end_mem_support)
        · have h1 := congrFun (hzPL.symm.trans hzQT) 1
          simp [squareVertex] at h1
          omega
  · simp only [ps, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map] at hzPs
    rcases hzPs with ⟨x, hx, hxz⟩
    rcases hzQ with hzQB | hzQs | hzQT
    · rcases squareOuterBottomConnector_support hc hzQB with hzQB | hzQB
      · have hx1 := congrFun hxz 1
        simp only [squareShiftOneIso_toHom_apply] at hx1
        have hxbox := hpbox x hx
        omega
      · have hxEq : x = squareVertex (c : ℤ) 0 := by
          apply squareShiftOneIso.injective
          calc
            squareShiftOneIso x = z := hxz
            _ = squareVertex (c + 1 : ℕ) 1 := hzQB
            _ = squareShiftOneIso (squareVertex (c : ℤ) 0) := by
              ext i; fin_cases i <;> simp [squareVertex]
        exact (hno x hx) (hxEq.symm ▸ q.start_mem_support)
    · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
        List.mem_map] at hzQs
      rcases hzQs with ⟨y, hy, hyz⟩
      have hxy : x = y := by
        apply squareShiftOneIso.injective
        exact hxz.trans hyz.symm
      exact (hno x hx) (hxy.symm ▸ hy)
    · rcases squareOuterTopConnector_support hzQT with hEq | hEq
      · have hxEq : x = squareVertex (d : ℤ) (m : ℤ) := by
          apply squareShiftOneIso.injective
          calc
            squareShiftOneIso x = z := hxz
            _ = squareVertex (d + 1 : ℕ) (m + 1 : ℕ) := hEq
            _ = squareShiftOneIso (squareVertex (d : ℤ) (m : ℤ)) := by
              ext i; fin_cases i <;> simp [squareVertex]
        exact (hno x hx) (hxEq.symm ▸ q.end_mem_support)
      · have hx1 := congrFun hxz 1
        simp only [squareShiftOneIso_toHom_apply] at hx1
        have h1 := congrFun hEq 1
        have hxbox := hpbox x hx
        simp [squareVertex] at h1
        omega
  · rcases squareOuterRightConnector_support hzPR with hzPR | hzPR
    · rcases hzQ with hzQB | hzQs | hzQT
      · rcases squareOuterBottomConnector_support hc hzQB with hzQB | hEq
        · have h1 := congrFun hzPR 1
          simp [squareVertex] at h1
          have hz1 := hzQB.1
          omega
        · have hpq : squareVertex (m : ℤ) (b : ℤ) =
              squareVertex (c : ℤ) 0 := by
            apply squareShiftOneIso.injective
            calc
              squareShiftOneIso (squareVertex (m : ℤ) (b : ℤ)) =
                  squareVertex (m + 1 : ℕ) (b + 1 : ℕ) := by
                    ext i; fin_cases i <;> simp [squareVertex]
              _ = squareVertex (c + 1 : ℕ) 1 := hzPR.symm.trans hEq
              _ = squareShiftOneIso (squareVertex (c : ℤ) 0) := by
                ext i; fin_cases i <;> simp [squareVertex]
          exact (hno _ p.end_mem_support) (hpq.symm ▸ q.start_mem_support)
      · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
          List.mem_map] at hzQs
        rcases hzQs with ⟨y, hy, hyz⟩
        have hyEq : squareVertex (m : ℤ) (b : ℤ) = y := by
          apply squareShiftOneIso.injective
          calc
            squareShiftOneIso (squareVertex (m : ℤ) (b : ℤ)) =
                squareVertex (m + 1 : ℕ) (b + 1 : ℕ) := by
                  ext i; fin_cases i <;> simp [squareVertex]
            _ = squareShiftOneIso y := hzPR.symm.trans hyz.symm
        exact (hno _ p.end_mem_support) (hyEq.symm ▸ hy)
      · rcases squareOuterTopConnector_support hzQT with hEq | hEq
        · have hpq : squareVertex (m : ℤ) (b : ℤ) =
              squareVertex (d : ℤ) (m : ℤ) := by
            apply squareShiftOneIso.injective
            calc
              squareShiftOneIso (squareVertex (m : ℤ) (b : ℤ)) =
                  squareVertex (m + 1 : ℕ) (b + 1 : ℕ) := by
                    ext i; fin_cases i <;> simp [squareVertex]
              _ = squareVertex (d + 1 : ℕ) (m + 1 : ℕ) := hzPR.symm.trans hEq
              _ = squareShiftOneIso (squareVertex (d : ℤ) (m : ℤ)) := by
                ext i; fin_cases i <;> simp [squareVertex]
          exact (hno _ p.end_mem_support) (hpq.symm ▸ q.end_mem_support)
        · have h1 := congrFun (hzPR.symm.trans hEq) 1
          simp [squareVertex] at h1
          omega
    · rcases hzQ with hzQB | hzQs | hzQT
      · rcases squareOuterBottomConnector_support hc hzQB with hzQB | hEq
        · have h1 := congrFun hzPR 1
          simp [squareVertex] at h1
          have hz1 := hzQB.1
          omega
        · have h0 := congrFun (hzPR.symm.trans hEq) 0
          simp [squareVertex] at h0
          omega
      · simp only [qs, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
          List.mem_map] at hzQs
        rcases hzQs with ⟨y, hy, hyz⟩
        have hybox := hqbox y hy
        have h0 := congrFun (hzPR.symm.trans hyz.symm) 0
        simp only [squareShiftOneIso_toHom_apply] at h0
        simp [squareVertex] at h0
        omega
      · rcases squareOuterTopConnector_support hzQT with hEq | hEq
        · have h0 := congrFun (hzPR.symm.trans hEq) 0
          simp [squareVertex] at h0
          omega
        · have h0 := congrFun (hzPR.symm.trans hEq) 0
          simp [squareVertex] at h0
          omega

/-- A left-right walk in `[0,m] × [0,n]` meets a bottom-top walk when `n ≤ m`.
The shorter vertical walk is continued deterministically through the empty upper part of the
ambient square; any intersection there is forced to be its original endpoint. -/
theorem squareWalk_support_inter_of_left_right_and_bottom_top_of_le
    {m n : ℕ} (hnm : n ≤ m) {a b c d : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ m) (hd : d ≤ m)
    (p : squareGraph.Walk (squareVertex 0 (a : ℤ))
      (squareVertex (m : ℤ) (b : ℤ)))
    (q : squareGraph.Walk (squareVertex (c : ℤ) 0)
      (squareVertex (d : ℤ) (n : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let r : squareGraph.Walk (squareVertex (d : ℤ) (n : ℤ))
      (squareVertex (d : ℤ) (m : ℤ)) :=
    (cubicWalkFrom (squareVertex (d : ℤ) (n : ℤ))
      (List.replicate (m - n) (⟨1, by decide⟩, true))).copy rfl (by
        rw [cubicEndpointFrom_replicate_pos]
        ext i
        fin_cases i
        · simp [squareVertex]
        · simp [squareVertex, Nat.cast_sub hnm])
  let Q := q.append r
  have hQbox : ∀ z ∈ Q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ m := by
    intro z hz
    simp only [Q, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have h := hqbox z hz
      omega
    · have hz' : z ∈ cubicVerticesFrom (squareVertex (d : ℤ) (n : ℤ))
          (List.replicate (m - n) (⟨1, by decide⟩, true)) := by
        simpa [r] using hz
      have h0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
        (squareVertex (d : ℤ) (n : ℤ)) (⟨1, by decide⟩) (⟨0, by decide⟩)
          (m - n) (by decide) hz'
      have h1 := cubicVerticesFrom_replicate_pos_coord_between
        (squareVertex (d : ℤ) (n : ℤ)) (⟨1, by decide⟩) (m - n) hz'
      simp [squareVertex, Nat.cast_sub hnm] at h0 h1
      omega
  obtain ⟨z, hzp, hzQ⟩ := squareWalk_support_inter_of_left_right_and_bottom_top
    (ha.trans hnm) (hb.trans hnm) hc hd p Q
    (fun z hz ↦ by have h := hpbox z hz; omega) hQbox
  simp only [Q, SimpleGraph.Walk.mem_support_append_iff] at hzQ
  rcases hzQ with hzq | hzr
  · exact ⟨z, hzp, hzq⟩
  · have hzr' : z ∈ cubicVerticesFrom (squareVertex (d : ℤ) (n : ℤ))
        (List.replicate (m - n) (⟨1, by decide⟩, true)) := by
      simpa [r] using hzr
    have h0 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      (squareVertex (d : ℤ) (n : ℤ)) (⟨1, by decide⟩) (⟨0, by decide⟩)
        (m - n) (by decide) hzr'
    have h1 := cubicVerticesFrom_replicate_pos_coord_between
      (squareVertex (d : ℤ) (n : ℤ)) (⟨1, by decide⟩) (m - n) hzr'
    have hp := hpbox z hzp
    have hzeq : z = squareVertex (d : ℤ) (n : ℤ) := by
      ext i
      fin_cases i
      · simpa [squareVertex] using h0
      · simp [squareVertex] at h1 ⊢
        omega
    exact ⟨z, hzp, hzeq.symm ▸ q.end_mem_support⟩

/-- Integer-coordinate adapter for the rectangular intersection theorem. -/
theorem squareWalk_support_inter_of_left_right_and_bottom_top_of_le_int
    {m n : ℕ} (hnm : n ≤ m) {a b c d : ℤ}
    (ha0 : 0 ≤ a) (han : a ≤ n) (hb0 : 0 ≤ b) (hbn : b ≤ n)
    (hc0 : 0 ≤ c) (hcm : c ≤ m) (hd0 : 0 ≤ d) (hdm : d ≤ m)
    (p : squareGraph.Walk (squareVertex 0 a) (squareVertex (m : ℤ) b))
    (q : squareGraph.Walk (squareVertex c 0) (squareVertex d (n : ℤ)))
    (hpbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n)
    (hqbox : ∀ z ∈ q.support,
      0 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 ≤ n) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  have haCast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hbCast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
  have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc0
  have hdCast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd0
  have ha : a.toNat ≤ n := by
    rw [← Nat.cast_le (α := ℤ), haCast]
    exact han
  have hb : b.toNat ≤ n := by
    rw [← Nat.cast_le (α := ℤ), hbCast]
    exact hbn
  have hc : c.toNat ≤ m := by
    rw [← Nat.cast_le (α := ℤ), hcCast]
    exact hcm
  have hd : d.toNat ≤ m := by
    rw [← Nat.cast_le (α := ℤ), hdCast]
    exact hdm
  let p' : squareGraph.Walk (squareVertex 0 (a.toNat : ℤ))
      (squareVertex (m : ℤ) (b.toNat : ℤ)) := p.copy (by simp [haCast]) (by simp [hbCast])
  let q' : squareGraph.Walk (squareVertex (c.toNat : ℤ) 0)
      (squareVertex (d.toNat : ℤ) (n : ℤ)) := q.copy (by simp [hcCast]) (by simp [hdCast])
  obtain ⟨z, hzp, hzq⟩ := squareWalk_support_inter_of_left_right_and_bottom_top_of_le
    hnm ha hb hc hd p' q' (by simpa [p'] using hpbox) (by simpa [q'] using hqbox)
  exact ⟨z, by simpa [p'] using hzp, by simpa [q'] using hzq⟩

end Percolation
