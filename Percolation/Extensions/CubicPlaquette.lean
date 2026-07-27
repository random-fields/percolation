import Percolation.Extensions.PlaquetteSurface
import Percolation.Core.Cubic

/-!
# Cubic plaquettes in dimension three

The half-integer translation of the dual cubic lattice plays no combinatorial role, so a dual
vertex is stored by its integer cube anchor.  A positively oriented dual edge is its coordinate
axis together with its lower endpoint.  A plaquette is its normal axis together with the lower
corner of the unit square.  This gives exactly one plaquette crossing each positively oriented
primal edge.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The next coordinate axis in the cyclic order `0,1,2,0`. -/
def fin3Next (i : Fin 3) : Fin 3 := i + 1

/-- The previous coordinate axis in the cyclic order `0,2,1,0`. -/
def fin3Prev (i : Fin 3) : Fin 3 := i + 2

@[simp] theorem fin3Next_zero : fin3Next 0 = 1 := rfl
@[simp] theorem fin3Next_one : fin3Next 1 = 2 := rfl
@[simp] theorem fin3Next_two : fin3Next 2 = 0 := rfl
@[simp] theorem fin3Prev_zero : fin3Prev 0 = 2 := rfl
@[simp] theorem fin3Prev_one : fin3Prev 1 = 0 := rfl
@[simp] theorem fin3Prev_two : fin3Prev 2 = 1 := rfl

theorem fin3Next_ne (i : Fin 3) : fin3Next i ≠ i := by
  fin_cases i <;> decide

theorem fin3Prev_ne (i : Fin 3) : fin3Prev i ≠ i := by
  fin_cases i <;> decide

theorem fin3Next_ne_prev (i : Fin 3) : fin3Next i ≠ fin3Prev i := by
  fin_cases i <;> decide

/-- A positive coordinate edge in the half-translated dual lattice. -/
structure CubicDualEdge3 where
  axis : Fin 3
  anchor : Cubic 3
  deriving DecidableEq

instance : Countable CubicDualEdge3 :=
  (show Function.Injective (fun e : CubicDualEdge3 ↦ (e.axis, e.anchor)) from by
    intro a b h
    cases a
    cases b
    simp_all).countable

/-- A unit square in the half-translated dual lattice.  Its normal coordinate is also the
direction of the unique primal edge crossing its centre. -/
structure CubicPlaquette3 where
  normal : Fin 3
  anchor : Cubic 3
  deriving DecidableEq

instance : Countable CubicPlaquette3 :=
  (show Function.Injective (fun pi : CubicPlaquette3 ↦ (pi.normal, pi.anchor)) from by
    intro a b h
    cases a
    cases b
    simp_all).countable

theorem cubicPlaquette3_mk_eq_mk_iff (i j : Fin 3) (x y : Cubic 3) :
    CubicPlaquette3.mk i x = CubicPlaquette3.mk j y ↔
      i = j ∧ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · intro h
    have hn := congrArg CubicPlaquette3.normal h
    have ha := congrArg CubicPlaquette3.anchor h
    exact ⟨hn, congrFun ha 0, congrFun ha 1, congrFun ha 2⟩
  · rintro ⟨rfl, h0, h1, h2⟩
    congr 1
    funext a
    fin_cases a <;> assumption

theorem cubic3_eq_iff_coordinates (x y : Cubic 3) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨h0, h1, h2⟩
    funext a
    fin_cases a <;> assumption

/-- The primal positive edge crossed by a dual plaquette.  Integer anchors suppress the common
half-translation of the dual lattice. -/
def CubicPlaquette3.crossingEdge (pi : CubicPlaquette3) : Fin 3 × Cubic 3 :=
  (pi.normal, pi.anchor)

/-- Plaquettes and positive primal edges are in canonical bijection. -/
def cubicPlaquetteCrossingEdgeEquiv : CubicPlaquette3 ≃ Fin 3 × Cubic 3 where
  toFun := CubicPlaquette3.crossingEdge
  invFun := fun e ↦ ⟨e.1, e.2⟩
  left_inv := fun pi ↦ by cases pi; rfl
  right_inv := fun e ↦ by cases e; rfl

/-- The four dual edges bounding a unit plaquette. -/
def cubicPlaquetteBoundary (pi : CubicPlaquette3) : Finset CubicDualEdge3 :=
  { ⟨fin3Next pi.normal, pi.anchor⟩,
    ⟨fin3Next pi.normal,
      cubicStepFrom pi.anchor (fin3Prev pi.normal, true)⟩,
    ⟨fin3Prev pi.normal, pi.anchor⟩,
    ⟨fin3Prev pi.normal,
      cubicStepFrom pi.anchor (fin3Next pi.normal, true)⟩ }

/-- The concrete three-dimensional cubic plaquette boundary system. -/
def cubicPlaquetteBoundarySystem :
    PlaquetteBoundarySystem CubicPlaquette3 CubicDualEdge3 where
  boundary := cubicPlaquetteBoundary

/-- The four plaquettes incident to a dual edge. -/
def cubicPlaquettesIncidentTo (e : CubicDualEdge3) : Finset CubicPlaquette3 :=
  { ⟨fin3Next e.axis, e.anchor⟩,
    ⟨fin3Next e.axis,
      cubicStepFrom e.anchor (fin3Prev e.axis, false)⟩,
    ⟨fin3Prev e.axis, e.anchor⟩,
    ⟨fin3Prev e.axis,
      cubicStepFrom e.anchor (fin3Next e.axis, false)⟩ }

theorem cubicStepFrom_ne_self {d : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicStepFrom x a ≠ x := by
  exact (cubicGraph_adj_stepFrom x a).ne'

theorem eq_or_eq_cubicStepFrom_pos_iff {d : ℕ} (x y : Cubic d) (i : Fin d) :
    y = x ∨ y = cubicStepFrom x (i, true) ↔
      x = y ∨ x = cubicStepFrom y (i, false) := by
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (cubicStepFrom_pos_neg x i).symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (cubicStepFrom_neg_pos y i).symm

theorem cubicPlaquettesIncidentTo_card (e : CubicDualEdge3) :
    (cubicPlaquettesIncidentTo e).card = 4 := by
  rcases e with ⟨i, x⟩
  fin_cases i <;>
    simp [cubicPlaquettesIncidentTo, fin3Next, fin3Prev,
      cubicStepFrom_ne_self, Ne.symm (cubicStepFrom_ne_self _ _)]

/-- A dual edge bounds a plaquette exactly when that plaquette belongs to its four-element
incidence block. -/
theorem mem_cubicPlaquetteBoundary_iff (pi : CubicPlaquette3) (e : CubicDualEdge3) :
    e ∈ cubicPlaquetteBoundary pi ↔ pi ∈ cubicPlaquettesIncidentTo e := by
  rcases pi with ⟨i, x⟩
  rcases e with ⟨j, y⟩
  fin_cases i <;> fin_cases j <;>
    simp [cubicPlaquetteBoundary, cubicPlaquettesIncidentTo, fin3Next, fin3Prev,
      eq_or_eq_cubicStepFrom_pos_iff]

/-- Integer coordinates for a dual-lattice anchor. -/
def cubic3XYZ (x y z : ℤ) : Cubic 3 := ![x, y, z]

@[simp] theorem cubic3XYZ_apply_zero (x y z : ℤ) : cubic3XYZ x y z 0 = x := rfl
@[simp] theorem cubic3XYZ_apply_one (x y z : ℤ) : cubic3XYZ x y z 1 = y := rfl
@[simp] theorem cubic3XYZ_apply_two (x y z : ℤ) : cubic3XYZ x y z 2 = z := rfl

/-- The horizontal plaquette with lower-left corner `(i,j,0)` in the canonical square. -/
def canonicalSquarePlaquette {n : ℕ} (ij : Fin n × Fin n) : CubicPlaquette3 :=
  ⟨2, cubic3XYZ (ij.1 : ℤ) (ij.2 : ℤ) 0⟩

theorem canonicalSquarePlaquette_injective {n : ℕ} :
    Function.Injective (canonicalSquarePlaquette (n := n)) := by
  intro a b h
  have hanchor :
      cubic3XYZ (a.1 : ℤ) (a.2 : ℤ) 0 =
        cubic3XYZ (b.1 : ℤ) (b.2 : ℤ) 0 := by
    exact CubicPlaquette3.mk.inj h |>.2
  apply Prod.ext
  · apply Fin.ext
    have h0 : (a.1.val : ℤ) = b.1.val := by
      simpa using congrFun hanchor 0
    exact_mod_cast h0
  · apply Fin.ext
    have h1 : (a.2.val : ℤ) = b.2.val := by
      simpa using congrFun hanchor 1
    exact_mod_cast h1

/-- The `n²` horizontal plaquettes in the smallest surface spanning the square circuit. -/
def canonicalSquareSurface (n : ℕ) : Finset CubicPlaquette3 :=
  (Finset.univ : Finset (Fin n × Fin n)).image
    (canonicalSquarePlaquette (n := n))

theorem canonicalSquareSurface_card (n : ℕ) :
    (canonicalSquareSurface n).card = n ^ 2 := by
  rw [canonicalSquareSurface,
    Finset.card_image_of_injective _ canonicalSquarePlaquette_injective]
  simp [pow_two]

/-- Grimmett's square dual circuit `C_n`, defined as the mod-two boundary of the canonical
horizontal square.  The explicit side description is proved below and ensures this definition
does not hide a different boundary convention. -/
def canonicalSquareCircuit (n : ℕ) : Finset CubicDualEdge3 :=
  cubicPlaquetteBoundarySystem.surfaceBoundary (canonicalSquareSurface n)

/-- Exact source-facing lower bound (12.20). -/
theorem canonicalSquare_closedPlaquetteSurface_probability_ge (n : ℕ) (p : I) :
    (1 - (p : ℝ)) ^ (n ^ 2) ≤
      (setBernoulli (Set.univ : Set CubicPlaquette3) p).real
        (closedPlaquetteSurfaceEvent cubicPlaquetteBoundarySystem
          (canonicalSquareCircuit n)) := by
  simpa [canonicalSquareCircuit, canonicalSquareSurface_card] using
    (closedPlaquetteSurface_probability_ge cubicPlaquetteBoundarySystem
      (canonicalSquareCircuit n) (canonicalSquareSurface n) rfl p)

/-- If a dual edge belongs to the prescribed boundary, every closed spanning surface fails the
four-plaquette incidence block at that edge. -/
theorem closedPlaquetteSurface_subset_incidentBlockFailure
    (C : Finset CubicDualEdge3) (e : CubicDualEdge3) (he : e ∈ C) :
    closedPlaquetteSurfaceEvent cubicPlaquetteBoundarySystem C ⊆
      plaquetteBlockFailureEvent (cubicPlaquettesIncidentTo e) := by
  intro omega homega
  rcases homega with ⟨S, hboundary, hclosed⟩
  have heS : e ∈ cubicPlaquetteBoundarySystem.surfaceBoundary S := by
    rw [hboundary]
    exact he
  have hodd := (PlaquetteBoundarySystem.mem_surfaceBoundary_iff
    cubicPlaquetteBoundarySystem S e).mp heS
  obtain ⟨pi, hpi⟩ := Finset.card_pos.mp (Odd.pos hodd)
  have hpiS := (Finset.mem_filter.mp hpi).1
  have hepi := (Finset.mem_filter.mp hpi).2
  intro hallOpen
  have hpiBlock : pi ∈ cubicPlaquettesIncidentTo e :=
    (mem_cubicPlaquetteBoundary_iff pi e).mp hepi
  exact Set.disjoint_left.mp hclosed hpiS (hallOpen hpiBlock)

/-- Embed the index range `0,…,n-2` into `0,…,n-1`. -/
def predFinCast {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨k, by omega⟩

/-- Shift the index range `0,…,n-2` to `1,…,n-1`. -/
def predFinSucc {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨k + 1, by omega⟩

/-- The zero index, with non-emptiness certified by an index in `Fin (n-1)`. -/
def predFinZero {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨0, by
  have hk := k.isLt
  omega⟩

/-- The last index `n-1`, with non-emptiness certified by an index in `Fin (n-1)`. -/
def predFinLast {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨n - 1, by
  have hk := k.isLt
  omega⟩

/-- The selected boundary edges used in (12.21): on each side one corner edge is omitted, so
the four-plaquette incidence blocks are pairwise disjoint. -/
def canonicalSquareSelectedBoundaryEdge {n : ℕ}
    (s : Fin 4 × Fin (n - 1)) : CubicDualEdge3 :=
  ![
    ⟨0, cubic3XYZ (s.2 : ℤ) 0 0⟩,
    ⟨1, cubic3XYZ n (s.2 : ℤ) 0⟩,
    ⟨0, cubic3XYZ ((s.2 : ℤ) + 1) n 0⟩,
    ⟨1, cubic3XYZ 0 ((s.2 : ℤ) + 1) 0⟩
  ] s.1

theorem canonical_bottom_mem_boundary_iff {n : ℕ} (k : Fin (n - 1))
    (ij : Fin n × Fin n) :
    canonicalSquareSelectedBoundaryEdge (0, k) ∈
        cubicPlaquetteBoundary (canonicalSquarePlaquette ij) ↔
      ij = (predFinCast k, predFinZero k) := by
  rcases ij with ⟨i, j⟩
  simp only [canonicalSquareSelectedBoundaryEdge, Matrix.cons_val_zero,
    canonicalSquarePlaquette, cubicPlaquetteBoundary, fin3Next_two, fin3Prev_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · have ha := congrArg CubicDualEdge3.anchor h
      apply Prod.ext
      · apply Fin.ext
        have hx : (k.val : ℤ) = i.val := by simpa using congrFun ha 0
        exact (Int.ofNat_inj.mp hx).symm
      · apply Fin.ext
        have hy : (0 : ℤ) = j.val := by simpa using congrFun ha 1
        exact (Int.ofNat_inj.mp hy).symm
    · have ha := congrArg CubicDualEdge3.anchor h
      have hy := congrFun ha 1
      simp [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] at hy
      omega
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
  · intro h
    have hi : i = predFinCast k := congrArg Prod.fst h
    have hj : j = predFinZero k := congrArg Prod.snd h
    subst i
    subst j
    left
    simp [predFinCast, predFinZero]

theorem canonical_right_mem_boundary_iff {n : ℕ} (k : Fin (n - 1))
    (ij : Fin n × Fin n) :
    canonicalSquareSelectedBoundaryEdge (1, k) ∈
        cubicPlaquetteBoundary (canonicalSquarePlaquette ij) ↔
      ij = (predFinLast k, predFinCast k) := by
  rcases ij with ⟨i, j⟩
  simp only [canonicalSquareSelectedBoundaryEdge, Matrix.cons_val_one,
    canonicalSquarePlaquette, cubicPlaquetteBoundary, fin3Next_two, fin3Prev_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have ha := congrArg CubicDualEdge3.anchor h
      have hx := congrFun ha 0
      simp [cubic3XYZ] at hx
      have hi := i.isLt
      omega
    · have ha := congrArg CubicDualEdge3.anchor h
      have hx : (n : ℤ) = (i.val : ℤ) + 1 := by
        simpa [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] using congrFun ha 0
      have hy : (k.val : ℤ) = j.val := by
        simpa [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] using congrFun ha 1
      have hi : i = predFinLast k := by
        apply Fin.ext
        simp [predFinLast]
        omega
      have hj : j = predFinCast k := by
        apply Fin.ext
        simp [predFinCast]
        exact (Int.ofNat_inj.mp hy).symm
      exact Prod.ext hi hj
  · intro h
    have hi : i = predFinLast k := congrArg Prod.fst h
    have hj : j = predFinCast k := congrArg Prod.snd h
    subst i
    subst j
    right; right; right
    apply congrArg (fun x : Cubic 3 ↦ CubicDualEdge3.mk 1 x)
    have hk := k.isLt
    ext a
    fin_cases a <;>
      simp [predFinLast, predFinCast, cubicStepFrom, cubic3XYZ,
        cubicDirectionIncrement] <;> omega

theorem canonical_top_mem_boundary_iff {n : ℕ} (k : Fin (n - 1))
    (ij : Fin n × Fin n) :
    canonicalSquareSelectedBoundaryEdge (2, k) ∈
        cubicPlaquetteBoundary (canonicalSquarePlaquette ij) ↔
      ij = (predFinSucc k, predFinLast k) := by
  rcases ij with ⟨i, j⟩
  simp only [canonicalSquareSelectedBoundaryEdge, Matrix.cons_val_two,
    canonicalSquarePlaquette, cubicPlaquetteBoundary, fin3Next_two, fin3Prev_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · have ha := congrArg CubicDualEdge3.anchor h
      have hy := congrFun ha 1
      simp [cubic3XYZ] at hy
      have hj := j.isLt
      omega
    · have ha := congrArg CubicDualEdge3.anchor h
      have hx : (k.val : ℤ) + 1 = i.val := by
        simpa [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] using congrFun ha 0
      have hy : (n : ℤ) = (j.val : ℤ) + 1 := by
        simpa [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] using congrFun ha 1
      have hi : i = predFinSucc k := by
        apply Fin.ext
        simp [predFinSucc]
        omega
      have hj : j = predFinLast k := by
        apply Fin.ext
        simp [predFinLast]
        omega
      exact Prod.ext hi hj
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
  · intro h
    have hi : i = predFinSucc k := congrArg Prod.fst h
    have hj : j = predFinLast k := congrArg Prod.snd h
    subst i
    subst j
    right; left
    apply congrArg (fun x : Cubic 3 ↦ CubicDualEdge3.mk 0 x)
    have hk := k.isLt
    ext a
    fin_cases a <;>
      simp [predFinSucc, predFinLast, cubicStepFrom, cubic3XYZ,
        cubicDirectionIncrement] <;> omega

theorem canonical_left_mem_boundary_iff {n : ℕ} (k : Fin (n - 1))
    (ij : Fin n × Fin n) :
    canonicalSquareSelectedBoundaryEdge (3, k) ∈
        cubicPlaquetteBoundary (canonicalSquarePlaquette ij) ↔
      ij = (predFinZero k, predFinSucc k) := by
  rcases ij with ⟨i, j⟩
  simp only [canonicalSquareSelectedBoundaryEdge, Matrix.cons_val_three,
    canonicalSquarePlaquette, cubicPlaquetteBoundary, fin3Next_two, fin3Prev_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have haxis := congrArg CubicDualEdge3.axis h
      norm_num at haxis
    · have ha := congrArg CubicDualEdge3.anchor h
      have hx : (0 : ℤ) = i.val := by simpa using congrFun ha 0
      have hy : (k.val : ℤ) + 1 = j.val := by simpa using congrFun ha 1
      have hi : i = predFinZero k := by
        apply Fin.ext
        simp [predFinZero]
        exact (Int.ofNat_inj.mp hx).symm
      have hj : j = predFinSucc k := by
        apply Fin.ext
        simp [predFinSucc]
        omega
      exact Prod.ext hi hj
    · have ha := congrArg CubicDualEdge3.anchor h
      have hx := congrFun ha 0
      simp [cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] at hx
      omega
  · intro h
    have hi : i = predFinZero k := congrArg Prod.fst h
    have hj : j = predFinSucc k := congrArg Prod.snd h
    subst i
    subst j
    right; right; left
    simp [predFinZero, predFinSucc]

/-- The unique canonical horizontal plaquette incident to a selected boundary edge. -/
def canonicalSquareSelectedPlaquetteIndex {n : ℕ}
    (s : Fin 4 × Fin (n - 1)) : Fin n × Fin n :=
  ![
    (predFinCast s.2, predFinZero s.2),
    (predFinLast s.2, predFinCast s.2),
    (predFinSucc s.2, predFinLast s.2),
    (predFinZero s.2, predFinSucc s.2)
  ] s.1

theorem canonical_selected_mem_boundary_iff {n : ℕ}
    (s : Fin 4 × Fin (n - 1)) (ij : Fin n × Fin n) :
    canonicalSquareSelectedBoundaryEdge s ∈
        cubicPlaquetteBoundary (canonicalSquarePlaquette ij) ↔
      ij = canonicalSquareSelectedPlaquetteIndex s := by
  rcases s with ⟨side, k⟩
  fin_cases side
  · simpa [canonicalSquareSelectedPlaquetteIndex] using
      canonical_bottom_mem_boundary_iff k ij
  · simpa [canonicalSquareSelectedPlaquetteIndex] using
      canonical_right_mem_boundary_iff k ij
  · simpa [canonicalSquareSelectedPlaquetteIndex] using
      canonical_top_mem_boundary_iff k ij
  · simpa [canonicalSquareSelectedPlaquetteIndex] using
      canonical_left_mem_boundary_iff k ij

theorem canonical_selected_incidenceCount_eq_one {n : ℕ}
    (s : Fin 4 × Fin (n - 1)) :
    cubicPlaquetteBoundarySystem.incidenceCount (canonicalSquareSurface n)
        (canonicalSquareSelectedBoundaryEdge s) = 1 := by
  let witness := canonicalSquarePlaquette
    (canonicalSquareSelectedPlaquetteIndex s)
  have hfilter :
      (canonicalSquareSurface n).filter (fun pi ↦
        canonicalSquareSelectedBoundaryEdge s ∈ cubicPlaquetteBoundary pi) =
        {witness} := by
    ext pi
    constructor
    · intro hpi
      have hsurface := (Finset.mem_filter.mp hpi).1
      have hboundary := (Finset.mem_filter.mp hpi).2
      rw [canonicalSquareSurface] at hsurface
      rcases Finset.mem_image.mp hsurface with ⟨ij, _hij, rfl⟩
      have hij := (canonical_selected_mem_boundary_iff s ij).mp hboundary
      subst ij
      simp [witness]
    · intro hpi
      have hpiEq : pi = witness := Finset.mem_singleton.mp hpi
      subst pi
      apply Finset.mem_filter.mpr
      constructor
      · rw [canonicalSquareSurface]
        exact Finset.mem_image.mpr
          ⟨canonicalSquareSelectedPlaquetteIndex s, Finset.mem_univ _, rfl⟩
      · exact (canonical_selected_mem_boundary_iff s _).mpr rfl
  rw [PlaquetteBoundarySystem.incidenceCount]
  change ((canonicalSquareSurface n).filter (fun pi ↦
    canonicalSquareSelectedBoundaryEdge s ∈ cubicPlaquetteBoundary pi)).card = 1
  rw [hfilter]
  simp

theorem canonical_selected_mem_squareCircuit {n : ℕ}
    (s : Fin 4 × Fin (n - 1)) :
    canonicalSquareSelectedBoundaryEdge s ∈ canonicalSquareCircuit n := by
  rw [canonicalSquareCircuit,
    PlaquetteBoundarySystem.mem_surfaceBoundary_iff]
  rw [canonical_selected_incidenceCount_eq_one]
  simp

/-- The selected boundary edges have pairwise-disjoint four-plaquette incidence blocks. -/
theorem canonical_selected_incidentBlocks_pairwiseDisjoint (n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin 4 × Fin (n - 1)))
      (fun s ↦ cubicPlaquettesIncidentTo
        (canonicalSquareSelectedBoundaryEdge s)) := by
  intro a _ha b _hb hab
  change Disjoint
    (cubicPlaquettesIncidentTo (canonicalSquareSelectedBoundaryEdge a))
    (cubicPlaquettesIncidentTo (canonicalSquareSelectedBoundaryEdge b))
  rw [Finset.disjoint_left]
  intro pi hpa hpb
  rcases a with ⟨sa, ka⟩
  rcases b with ⟨sb, kb⟩
  have hka := ka.isLt
  have hkb := kb.isLt
  fin_cases sa <;> fin_cases sb <;>
    simp [cubicPlaquettesIncidentTo, canonicalSquareSelectedBoundaryEdge,
      fin3Next, fin3Prev, cubicStepFrom, cubic3XYZ, cubicDirectionIncrement] at hpa hpb hab
  all_goals
    rcases hpa with rfl | rfl | rfl | rfl <;>
      rcases hpb with h | h | h | h <;>
      simp [cubic3_eq_iff_coordinates, Function.update] at h hab <;>
      try omega

/-- Exact source-facing upper bound (12.21).  The selected family contains `4(n-1)` boundary
edges, each with a four-plaquette incidence block, and the preceding geometry proves that these
blocks are disjoint. -/
theorem closedPlaquetteSurface_probability_le (n : ℕ) (p : I) :
    (setBernoulli (Set.univ : Set CubicPlaquette3) p).real
        (closedPlaquetteSurfaceEvent cubicPlaquetteBoundarySystem
          (canonicalSquareCircuit n)) ≤
      (1 - (p : ℝ) ^ 4) ^ (4 * (n - 1)) := by
  let block : (Fin 4 × Fin (n - 1)) → Finset CubicPlaquette3 := fun s ↦
    cubicPlaquettesIncidentTo (canonicalSquareSelectedBoundaryEdge s)
  have hforce :
      closedPlaquetteSurfaceEvent cubicPlaquetteBoundarySystem
          (canonicalSquareCircuit n) ⊆
        ⋂ s : Fin 4 × Fin (n - 1), plaquetteBlockFailureEvent (block s) := by
    intro omega homega
    simp only [Set.mem_iInter]
    intro s
    exact closedPlaquetteSurface_subset_incidentBlockFailure
      (canonicalSquareCircuit n) (canonicalSquareSelectedBoundaryEdge s)
        (canonical_selected_mem_squareCircuit s) homega
  have h := closedPlaquetteSurface_probability_le_of_blocks
    cubicPlaquetteBoundarySystem (canonicalSquareCircuit n) block 4
      (fun s ↦ cubicPlaquettesIncidentTo_card
        (canonicalSquareSelectedBoundaryEdge s))
      (canonical_selected_incidentBlocks_pairwiseDisjoint n) hforce p
  simpa [block] using h

end Percolation
