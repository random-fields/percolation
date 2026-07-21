import Percolation.Extensions.CubicRigidityBoundary
import Percolation.Critical.StaticSecondCluster

/-!
# Non-rigidity of the cubic lattice

Every finite induced cubic graph spanning many parallel coordinate hyperplanes has many missing
directed edges.  The corresponding row deficit prevents its rigidity matrix from reaching the
Maxwell rank.  Applying the source's finite-exhaustion definition shows that no infinite rigid
subgraph of the cubic lattice exists, even when every bond is open.
-/

namespace Percolation

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A connected induced cubic graph spanning `N` coordinate units has at least `N+1` occupied
coordinate slices. -/
theorem missingDart_card_ge_of_connected_of_coord_span
    {d N : ℕ} (U : Finset (Cubic d))
    (hconn : ((cubicGraph d).induce (U : Set (Cubic d))).Connected)
    {x y : Cubic d} (hx : x ∈ U) (hy : y ∈ U) (i : Fin d)
    (hspan : N ≤ (y i - x i).natAbs) :
    (N + 1) * (d - 1) ≤ Fintype.card (CubicMissingDart U) := by
  let xU : (U : Set (Cubic d)) := ⟨x, hx⟩
  let yU : (U : Set (Cubic d)) := ⟨y, hy⟩
  obtain ⟨w, _hwPath⟩ := hconn.exists_isPath xU yU
  let emb := SimpleGraph.Embedding.induce (G := cubicGraph d) (U : Set (Cubic d))
  let ambient : (cubicGraph d).Walk x y := (w.map emb.toHom).copy (by rfl) (by rfl)
  by_cases hxy : x i ≤ y i
  · let level : Fin (N + 1) → ℤ := fun k ↦ x i + k
    have hlevel : Function.Injective level := by
      intro k l hkl
      apply Fin.ext
      dsimp [level] at hkl
      omega
    have hspan' : (N : ℤ) ≤ y i - x i := by
      calc
        (N : ℤ) ≤ ((y i - x i).natAbs : ℤ) := by exact_mod_cast hspan
        _ = y i - x i := Int.natAbs_of_nonneg (sub_nonneg.mpr hxy)
    have hslice : ∀ k, (cubicCoordinateSlice U i (level k)).Nonempty := by
      intro k
      have hxlevel : x i ≤ level k := by
        dsimp [level]
        omega
      have hlevely : level k ≤ y i := by
        dsimp [level]
        have hk : (k : ℕ) ≤ N := by omega
        have hkZ : (k : ℤ) ≤ N := by exact_mod_cast hk
        omega
      obtain ⟨z, q, hz, _hqside, hzambient⟩ :=
        exists_cubicWalk_prefix_to_level_of_le_end
          (G := cubicGraph d) (le_refl _) ambient i (level k) hxlevel hlevely
      have hzU : z ∈ U := by
        have hzambient' := hzambient z (by simp)
        have hzmap : z ∈ (w.map emb.toHom).support := by
          simpa [ambient, SimpleGraph.Walk.support_copy] using hzambient'
        rw [SimpleGraph.Walk.support_map] at hzmap
        obtain ⟨zU, hzUw, hzEq⟩ := List.mem_map.mp hzmap
        have hzEq' : zU.1 = z := by simpa [emb] using hzEq
        exact hzEq' ▸ zU.2
      exact ⟨z, mem_cubicCoordinateSlice.mpr ⟨hzU, hz⟩⟩
    simpa using card_mul_pred_le_missingDart_card U i level hlevel hslice
  · have hyx : y i ≤ x i := le_of_not_ge hxy
    let level : Fin (N + 1) → ℤ := fun k ↦ x i - k
    have hlevel : Function.Injective level := by
      intro k l hkl
      apply Fin.ext
      dsimp [level] at hkl
      omega
    have hspan' : (N : ℤ) ≤ x i - y i := by
      calc
        (N : ℤ) ≤ ((y i - x i).natAbs : ℤ) := by exact_mod_cast hspan
        _ = ((x i - y i).natAbs : ℤ) := by rw [show y i - x i = -(x i - y i) by ring,
          Int.natAbs_neg]
        _ = x i - y i := Int.natAbs_of_nonneg (sub_nonneg.mpr hyx)
    have hslice : ∀ k, (cubicCoordinateSlice U i (level k)).Nonempty := by
      intro k
      have hlevelx : level k ≤ x i := by
        dsimp [level]
        omega
      have hylevel : y i ≤ level k := by
        dsimp [level]
        have hk : (k : ℕ) ≤ N := by omega
        have hkZ : (k : ℤ) ≤ N := by exact_mod_cast hk
        omega
      obtain ⟨z, q, hz, _hqside, hzambient⟩ :=
        exists_cubicWalk_prefix_to_level_of_end_le
          (G := cubicGraph d) (le_refl _) ambient i (level k) hlevelx hylevel
      have hzU : z ∈ U := by
        have hzambient' := hzambient z (by simp)
        have hzmap : z ∈ (w.map emb.toHom).support := by
          simpa [ambient, SimpleGraph.Walk.support_copy] using hzambient'
        rw [SimpleGraph.Walk.support_map] at hzmap
        obtain ⟨zU, hzUw, hzEq⟩ := List.mem_map.mp hzmap
        have hzEq' : zU.1 = z := by simpa [emb] using hzEq
        exact hzEq' ▸ zU.2
      exact ⟨z, mem_cubicCoordinateSlice.mpr ⟨hzU, hz⟩⟩
    simpa using card_mul_pred_le_missingDart_card U i level hlevel hslice

/-- A convenient coordinate span large enough to exceed the constant-dimensional Maxwell
deficit. -/
def cubicRigidityObstructionSpan (d : ℕ) : ℕ := d * (d + 1) + 1

theorem cubicRigidityObstruction_missingDart_gt
    {d : ℕ} (hd : 2 ≤ d) (U : Finset (Cubic d))
    (hconn : ((cubicGraph d).induce (U : Set (Cubic d))).Connected)
    {x y : Cubic d} (hx : x ∈ U) (hy : y ∈ U) (i : Fin d)
    (hspan : cubicRigidityObstructionSpan d ≤ (y i - x i).natAbs) :
    d * (d + 1) < Fintype.card (CubicMissingDart U) := by
  have hlower := missingDart_card_ge_of_connected_of_coord_span U hconn hx hy i hspan
  unfold cubicRigidityObstructionSpan at hlower
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The boundary deficit makes the Maxwell rank strictly larger than the number of available
edge rows. -/
theorem expectedRigidityRank_not_le_cubic_edge_card_of_coord_span
    {d : ℕ} (hd : 2 ≤ d) (U : Finset (Cubic d))
    (hcard : d + 1 ≤ U.card)
    (hconn : ((cubicGraph d).induce (U : Set (Cubic d))).Connected)
    {x y : Cubic d} (hx : x ∈ U) (hy : y ∈ U) (i : Fin d)
    (hspan : cubicRigidityObstructionSpan d ≤ (y i - x i).natAbs) :
    ¬ expectedRigidityRank d U.card ≤
      Nat.card ((cubicGraph d).induce (U : Set (Cubic d))).edgeSet := by
  intro hrank
  have hmissing := cubicRigidityObstruction_missingDart_gt hd U hconn hx hy i hspan
  have hhandshake := twice_edge_card_add_missingDart_card U
  have htriangle : 2 * (d * (d + 1) / 2) = d * (d + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self d)
  have hdivle : d * (d + 1) / 2 ≤ d * U.card := by
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left d hcard)
  have hrhs : U.card * (2 * d) = 2 * (d * U.card) := by ring
  rw [hrhs] at hhandshake
  unfold expectedRigidityRank at hrank
  omega

/-- A finite induced cubic graph with a sufficiently large coordinate span is not generically
rigid. -/
theorem not_genericallyRigid_cubic_induce_of_coord_span
    {d : ℕ} (hd : 2 ≤ d) (U : Finset (Cubic d))
    {x y : Cubic d} (hx : x ∈ U) (hy : y ∈ U) (i : Fin d)
    (hspan : cubicRigidityObstructionSpan d ≤ (y i - x i).natAbs) :
    ¬GenericallyRigid ((cubicGraph d).induce (U : Set (Cubic d))) d := by
  intro hrigid
  apply expectedRigidityRank_not_le_cubic_edge_card_of_coord_span hd U
    (by simpa using hrigid.2.1) hrigid.1 hx hy i hspan
  have hcardU : Fintype.card (U : Set (Cubic d)) = U.card := by
    simpa only [Finset.coe_sort_coe] using Fintype.card_coe U
  simpa only [hcardU] using hrigid.expectedRank_le_edge_card

/-! ### Infinite consequence -/

/-- Ambient vertex set of a finite collection of vertices from a subtype. -/
noncomputable def finsetSubtypeVal
    {d : ℕ} {V : Set (Cubic d)} (U : Finset V) : Finset (Cubic d) :=
  U.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem mem_finsetSubtypeVal {d : ℕ} {V : Set (Cubic d)}
    {U : Finset V} {x : Cubic d} :
    x ∈ finsetSubtypeVal U ↔ ∃ z ∈ U, z.1 = x := by
  simp [finsetSubtypeVal]

theorem card_finsetSubtypeVal {d : ℕ} {V : Set (Cubic d)} (U : Finset V) :
    (finsetSubtypeVal U).card = U.card := by
  simp [finsetSubtypeVal]

/-- Forget the two induced-subtype layers and closed edges. -/
noncomputable def nestedOpenInducedToCubicInducedHom
    {d : ℕ} (omega : EdgeConfiguration d) (V : Set (Cubic d)) (U : Finset V) :
    (((cubicOpenGraph d omega).induce V).induce (U : Set V)) →g
      ((cubicGraph d).induce (finsetSubtypeVal U : Set (Cubic d))) where
  toFun z := ⟨z.1.1, by
    exact mem_finsetSubtypeVal.mpr ⟨z.1, z.2, rfl⟩⟩
  map_rel' := by
    intro a b hab
    rw [SimpleGraph.induce_adj]
    rw [SimpleGraph.induce_adj] at hab
    rw [SimpleGraph.induce_adj] at hab
    exact (cubicOpenGraph_adj.mp hab).choose

theorem nestedOpenInducedToCubicInducedHom_injective
    {d : ℕ} (omega : EdgeConfiguration d) (V : Set (Cubic d)) (U : Finset V) :
    Function.Injective (nestedOpenInducedToCubicInducedHom omega V U) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1) hab

theorem nestedOpenInducedToCubicInducedHom_surjective
    {d : ℕ} (omega : EdgeConfiguration d) (V : Set (Cubic d)) (U : Finset V) :
    Function.Surjective (nestedOpenInducedToCubicInducedHom omega V U) := by
  intro z
  have hz : z.1 ∈ finsetSubtypeVal U := z.2
  rw [mem_finsetSubtypeVal] at hz
  obtain ⟨u, hu, huEq⟩ := hz
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  exact huEq

theorem nestedOpenInduced_edge_card_le_cubicInduced
    {d : ℕ} (omega : EdgeConfiguration d) (V : Set (Cubic d)) (U : Finset V) :
    Nat.card ((((cubicOpenGraph d omega).induce V).induce (U : Set V)).edgeSet) ≤
      Nat.card (((cubicGraph d).induce
        (finsetSubtypeVal U : Set (Cubic d))).edgeSet) := by
  let f := nestedOpenInducedToCubicInducedHom omega V U
  exact Nat.card_le_card_of_injective f.mapEdgeSet
    (SimpleGraph.Hom.mapEdgeSet.injective f
      (nestedOpenInducedToCubicInducedHom_injective omega V U))

/-- No infinite vertex set in the cubic lattice is rigid in the finite-exhaustion sense, even
after retaining an arbitrary collection of open edges. -/
theorem not_infinitelyGenericallyRigid_cubicOpenGraph
    {d : ℕ} (hd : 2 ≤ d) (omega : EdgeConfiguration d)
    (V : Set (Cubic d)) (hV : V.Infinite) (h0 : cubicOrigin ∈ V) :
    ¬InfinitelyGenericallyRigid ((cubicOpenGraph d omega).induce V) d := by
  intro hrigid
  let N := cubicRigidityObstructionSpan d
  obtain ⟨y, hyV, hyout⟩ := hV.exists_notMem_finset (cubicMetricBox d cubicOrigin N)
  have hdist : N < cubicLInfDist cubicOrigin y := by
    exact lt_of_not_ge fun hle ↦ hyout (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
  obtain ⟨i, hi⟩ := exists_coord_natAbs_eq_cubicLInfDist (by omega) cubicOrigin y
  have hspan : N ≤ (y i - cubicOrigin i).natAbs := by
    rw [hi]
    exact hdist.le
  let oV : V := ⟨cubicOrigin, h0⟩
  let yV : V := ⟨y, hyV⟩
  let W : Finset V := {oV, yV}
  obtain ⟨U, hWU, hUrigid⟩ := hrigid W
  have hoU : oV ∈ U := hWU (by simp [W])
  have hyU : yV ∈ U := hWU (by simp [W])
  let A := finsetSubtypeVal U
  let f := nestedOpenInducedToCubicInducedHom omega V U
  have hfSurj : Function.Surjective f :=
    nestedOpenInducedToCubicInducedHom_surjective omega V U
  have hAconn : ((cubicGraph d).induce (A : Set (Cubic d))).Connected := by
    exact hUrigid.1.map f hfSurj
  have hAorigin : cubicOrigin ∈ A := by
    rw [mem_finsetSubtypeVal]
    exact ⟨oV, hoU, rfl⟩
  have hAy : y ∈ A := by
    rw [mem_finsetSubtypeVal]
    exact ⟨yV, hyU, rfl⟩
  have hUcard : Fintype.card (U : Set V) = U.card := by
    simpa only [Finset.coe_sort_coe] using Fintype.card_coe U
  have hAcard : A.card = U.card := card_finsetSubtypeVal U
  have hcard : d + 1 ≤ A.card := by
    rw [hAcard]
    simpa only [hUcard] using hUrigid.2.1
  have hrankSource := hUrigid.expectedRank_le_edge_card
  rw [hUcard, ← hAcard] at hrankSource
  have hrankTarget : expectedRigidityRank d A.card ≤
      Nat.card (((cubicGraph d).induce (A : Set (Cubic d))).edgeSet) :=
    hrankSource.trans (nestedOpenInduced_edge_card_le_cubicInduced omega V U)
  exact (expectedRigidityRank_not_le_cubic_edge_card_of_coord_span hd A hcard hAconn
    hAorigin hAy i hspan) hrankTarget

theorem not_hasInfiniteOpenRigidGraph_cubic
    {d : ℕ} (hd : 2 ≤ d) (omega : EdgeConfiguration d) :
    ¬HasInfiniteOpenRigidGraph d omega := by
  rintro ⟨V, h0, hV, hrigid⟩
  exact not_infinitelyGenericallyRigid_cubicOpenGraph hd omega V hV h0 hrigid

theorem hasInfiniteOpenRigidGraphEvent_eq_empty {d : ℕ} (hd : 2 ≤ d) :
    hasInfiniteOpenRigidGraphEvent d = ∅ := by
  ext omega
  simp only [hasInfiniteOpenRigidGraphEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact not_hasInfiniteOpenRigidGraph_cubic hd omega

theorem rigidityTheta_eq_zero {d : ℕ} (hd : 2 ≤ d) (p : I) :
    rigidityTheta d p = 0 := by
  simp [rigidityTheta, hasInfiniteOpenRigidGraphEvent_eq_empty hd]

/-- The cubic lattice is not rigid, so its rigidity threshold is one.  This is the explicit
cubic-lattice consequence stated immediately after Theorem 12.28(b). -/
theorem cubic_rigidityCriticalProbability_eq_one {d : ℕ} (hd : 2 ≤ d) :
    rigidityCriticalProbability d = 1 := by
  apply le_antisymm (rigidityCriticalProbability_le_one d)
  rw [rigidityCriticalProbability]
  apply le_csSup
  · exact ⟨1, by
      rintro q ⟨p, hp, rfl⟩
      exact p.2.2⟩
  · exact ⟨(1 : I), rigidityTheta_eq_zero hd 1, rfl⟩

/-- Theorem 12.28(a) for the cubic lattice. -/
theorem criticalProbability_lt_rigidityCriticalProbability
    {d : ℕ} (hd : 2 ≤ d) :
    cubicCriticalProbability d < rigidityCriticalProbability d := by
  rw [cubic_rigidityCriticalProbability_eq_one hd]
  exact (cubicCriticalProbability_pos_lt_one hd).2

end Percolation
