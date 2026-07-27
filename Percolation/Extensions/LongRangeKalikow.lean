import Percolation.Extensions.LongRangeConnectivity
import Percolation.Extensions.FiniteComponentDeletion

/-!
# Kalikow's finite component-count argument

Finite restrictions of the long-range graph and their component counts, corresponding to
Grimmett (12.10)--(12.19).  The interval indexed by `n` has vertices `0,...,n`.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory SimpleGraph
open scoped BigOperators unitInterval

/-- Embed the finite interval `0,...,n` in the integer line. -/
def longRangeIntervalVertexEmbedding (n : ℕ) : Fin (n + 1) ↪ ℤ where
  toFun i := i.val
  inj' := fun _ _ h ↦ Fin.ext (Int.ofNat_inj.mp h)

/-- Embed an unordered interval pair into the long-range edge coordinates. -/
def longRangeIntervalEdgeEmbedding (n : ℕ) : Sym2 (Fin (n + 1)) ↪ Sym2 ℤ :=
  (longRangeIntervalVertexEmbedding n).sym2Map

@[simp]
theorem longRangeIntervalEdgeEmbedding_mk (n : ℕ) (i j : Fin (n + 1)) :
    longRangeIntervalEdgeEmbedding n s(i, j) = s((i.val : ℤ), (j.val : ℤ)) := by
  rfl

/-- Restriction of a long-range configuration to the vertices `0,...,n`. -/
def longRangeIntervalOpenGraph (ω : LongRangeConfiguration) (n : ℕ) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromEdgeSet {e | longRangeIntervalEdgeEmbedding n e ∈ ω}

theorem longRangeIntervalOpenGraph_adj {ω : LongRangeConfiguration} {n : ℕ}
    {i j : Fin (n + 1)} :
    (longRangeIntervalOpenGraph ω n).Adj i j ↔
      s((i.val : ℤ), (j.val : ℤ)) ∈ ω ∧ i ≠ j := by
  simp [longRangeIntervalOpenGraph, SimpleGraph.fromEdgeSet_adj]

/-- Every edge coordinate inspected by the interval graph. -/
def longRangeIntervalEdgeSupport (n : ℕ) : Finset (Sym2 ℤ) :=
  (Finset.univ : Finset (Sym2 (Fin (n + 1)))).map
    (longRangeIntervalEdgeEmbedding n)

theorem dependsOnFun_longRangeIntervalOpenGraph (n : ℕ) :
    DependsOnFun (longRangeIntervalEdgeSupport n)
      (fun ω ↦ longRangeIntervalOpenGraph ω n) := by
  intro ω η h
  ext i j
  rw [longRangeIntervalOpenGraph_adj, longRangeIntervalOpenGraph_adj]
  apply and_congr
  · apply h
    exact Finset.mem_map.mpr ⟨s(i, j), Finset.mem_univ _, rfl⟩
  · rfl

/-- Number of connected components in the restriction to `0,...,n`. -/
noncomputable def longRangeIntervalComponentCount
    (ω : LongRangeConfiguration) (n : ℕ) : ℕ :=
  Nat.card (longRangeIntervalOpenGraph ω n).ConnectedComponent

theorem dependsOnFun_longRangeIntervalComponentCount (n : ℕ) :
    DependsOnFun (longRangeIntervalEdgeSupport n)
      (fun ω ↦ (longRangeIntervalComponentCount ω n : ℝ)) := by
  intro ω η h
  have hgraph := dependsOnFun_longRangeIntervalOpenGraph n h
  change longRangeIntervalOpenGraph ω n = longRangeIntervalOpenGraph η n at hgraph
  change (Nat.card (longRangeIntervalOpenGraph ω n).ConnectedComponent : ℝ) =
    Nat.card (longRangeIntervalOpenGraph η n).ConnectedComponent
  rw [hgraph]

theorem measurable_longRangeIntervalComponentCount (n : ℕ) :
    Measurable (fun ω ↦ (longRangeIntervalComponentCount ω n : ℝ)) :=
  (dependsOnFun_longRangeIntervalComponentCount n).measurable

theorem longRangeIntervalComponentCount_pos (ω : LongRangeConfiguration) (n : ℕ) :
    0 < longRangeIntervalComponentCount ω n := by
  have hne : Nonempty (longRangeIntervalOpenGraph ω n).ConnectedComponent :=
    ⟨(longRangeIntervalOpenGraph ω n).connectedComponentMk 0⟩
  letI := hne
  exact Nat.card_pos

theorem longRangeIntervalComponentCount_le (ω : LongRangeConfiguration) (n : ℕ) :
    longRangeIntervalComponentCount ω n ≤ n + 1 := by
  let G := longRangeIntervalOpenGraph ω n
  have hsurj : Function.Surjective G.connectedComponentMk := by
    intro C
    rcases C.exists_rep with ⟨x, hx⟩
    exact ⟨x, hx⟩
  simpa [longRangeIntervalComponentCount, G] using
    (Nat.card_le_card_of_surjective G.connectedComponentMk hsurj)

theorem integrable_longRangeIntervalComponentCount
    (p : LongRangeProfile) (n : ℕ) :
    Integrable (fun ω ↦ (longRangeIntervalComponentCount ω n : ℝ))
      (longRangeMeasure p) := by
  apply integrable_of_bounded_measurable
    (measurable_longRangeIntervalComponentCount n) (C := (n + 1 : ℝ))
  intro ω
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast longRangeIntervalComponentCount_le ω n

/-- `Fin n` is the complement of the last point in `Fin (n+1)`. -/
def finEquivDeleteLast (n : ℕ) :
    Fin n ≃ {x : Fin (n + 1) // x ∈ ({Fin.last n}ᶜ : Set (Fin (n + 1)))} where
  toFun i := ⟨i.castSucc, by
    simp⟩
  invFun x := ⟨x.val.val, by
    have hxlt := x.val.isLt
    have hxne : x.val ≠ Fin.last n := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
    have hxval : x.val.val ≠ n := fun h ↦ hxne (Fin.ext (by simpa using h))
    omega⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv x := by apply Subtype.ext; apply Fin.ext; rfl

/-- Deleting the newest vertex from the restriction on `0,...,n+1` recovers the preceding
restriction. -/
def longRangeIntervalDeleteLastIso (ω : LongRangeConfiguration) (n : ℕ) :
    longRangeIntervalOpenGraph ω n ≃g
      (longRangeIntervalOpenGraph ω (n + 1)).induce
        ({Fin.last (n + 1)}ᶜ : Set (Fin (n + 2))) where
  __ := finEquivDeleteLast (n + 1)
  map_rel_iff' := by
    intro i j
    rw [longRangeIntervalOpenGraph_adj]
    change (longRangeIntervalOpenGraph ω (n + 1)).Adj
      (finEquivDeleteLast (n + 1) i).1 (finEquivDeleteLast (n + 1) j).1 ↔ _
    rw [longRangeIntervalOpenGraph_adj]
    simp [finEquivDeleteLast]

theorem longRangeInterval_deleteLast_componentCount (ω : LongRangeConfiguration) (n : ℕ) :
    Nat.card ((longRangeIntervalOpenGraph ω (n + 1)).induce
        ({Fin.last (n + 1)}ᶜ : Set (Fin (n + 2)))).ConnectedComponent =
      longRangeIntervalComponentCount ω n := by
  rw [longRangeIntervalComponentCount]
  exact Nat.card_congr (longRangeIntervalDeleteLastIso ω n).connectedComponentEquiv.symm

/-- Adding the last vertex increases the component count by at most one. -/
theorem longRangeIntervalComponentCount_le_succ
    (ω : LongRangeConfiguration) (n : ℕ) :
    longRangeIntervalComponentCount ω (n + 1) ≤
      longRangeIntervalComponentCount ω n + 1 := by
  change Nat.card (longRangeIntervalOpenGraph ω (n + 1)).ConnectedComponent ≤
    Nat.card (longRangeIntervalOpenGraph ω n).ConnectedComponent + 1
  calc
    Nat.card (longRangeIntervalOpenGraph ω (n + 1)).ConnectedComponent ≤
        Nat.card ((longRangeIntervalOpenGraph ω (n + 1)).induce
          ({Fin.last (n + 1)}ᶜ : Set (Fin (n + 2)))).ConnectedComponent + 1 :=
      connectedComponent_card_le_deleteVertex_add_one
        (longRangeIntervalOpenGraph ω (n + 1)) (Fin.last (n + 1))
    _ = Nat.card (longRangeIntervalOpenGraph ω n).ConnectedComponent + 1 := by
      rw [longRangeInterval_deleteLast_componentCount]
      rfl

/-- If adding the last vertex creates an extra component, that vertex is isolated. -/
theorem longRangeInterval_last_isolated_of_componentCount_lt
    {ω : LongRangeConfiguration} {n : ℕ}
    (hcount : longRangeIntervalComponentCount ω n <
      longRangeIntervalComponentCount ω (n + 1)) :
    ∀ i : Fin (n + 2),
      ¬(longRangeIntervalOpenGraph ω (n + 1)).Adj (Fin.last (n + 1)) i := by
  apply no_adj_of_deleteVertex_card_lt
  rw [longRangeInterval_deleteLast_componentCount]
  exact hcount

/-- `Fin n` is also the complement of zero in `Fin (n+1)`, via the successor map. -/
def finEquivDeleteZero (n : ℕ) :
    Fin n ≃ {x : Fin (n + 1) // x ∈ ({0}ᶜ : Set (Fin (n + 1)))} where
  toFun i := ⟨i.succ, by simp⟩
  invFun x := ⟨x.val.val - 1, by
    have hxlt := x.val.isLt
    have hxpos : 0 < x.val.val := by
      have hxne : x.val ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
      have hxvalne : x.val.val ≠ 0 := by
        intro h
        apply hxne
        apply Fin.ext
        simpa using h
      omega
    omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have hxne : x.val ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
    have hxvalne : x.val.val ≠ 0 := by
      intro h
      apply hxne
      apply Fin.ext
      simpa using h
    have hxpos : 0 < x.val.val := by omega
    simp
    omega

/-- Removing zero from `[0,m+1]` and shifting left gives `[0,m]` in the translated
configuration. -/
def longRangeIntervalDeleteZeroIso (ω : LongRangeConfiguration) (m : ℕ) :
    longRangeIntervalOpenGraph (longRangeConfigurationPullback 1 ω) m ≃g
      (longRangeIntervalOpenGraph ω (m + 1)).induce
        ({0}ᶜ : Set (Fin (m + 2))) where
  __ := finEquivDeleteZero (m + 1)
  map_rel_iff' := by
    intro i j
    rw [longRangeIntervalOpenGraph_adj]
    change (longRangeIntervalOpenGraph ω (m + 1)).Adj
      (finEquivDeleteZero (m + 1) i).1 (finEquivDeleteZero (m + 1) j).1 ↔ _
    rw [longRangeIntervalOpenGraph_adj]
    simp [finEquivDeleteZero, longRangeConfigurationPullback,
      longRangeEdgeTranslateEmbedding_mk]

/-- Components of the graph on vertices `1,...,m+1`. -/
noncomputable def longRangeIntervalDeleteZeroComponentCount
    (ω : LongRangeConfiguration) (m : ℕ) : ℕ :=
  Nat.card ((longRangeIntervalOpenGraph ω (m + 1)).induce
    ({0}ᶜ : Set (Fin (m + 2)))).ConnectedComponent

theorem longRangeIntervalDeleteZeroComponentCount_eq
    (ω : LongRangeConfiguration) (m : ℕ) :
    longRangeIntervalDeleteZeroComponentCount ω m =
      longRangeIntervalComponentCount (longRangeConfigurationPullback 1 ω) m := by
  rw [longRangeIntervalDeleteZeroComponentCount, longRangeIntervalComponentCount]
  exact Nat.card_congr (longRangeIntervalDeleteZeroIso ω m).connectedComponentEquiv.symm

theorem measurable_longRangeIntervalDeleteZeroComponentCount (m : ℕ) :
    Measurable (fun ω ↦ (longRangeIntervalDeleteZeroComponentCount ω m : ℝ)) := by
  simp_rw [longRangeIntervalDeleteZeroComponentCount_eq]
  exact (measurable_longRangeIntervalComponentCount m).comp
    (measurable_longRangeConfigurationPullback 1)

theorem integrable_longRangeIntervalDeleteZeroComponentCount
    (p : LongRangeProfile) (m : ℕ) :
    Integrable (fun ω ↦ (longRangeIntervalDeleteZeroComponentCount ω m : ℝ))
      (longRangeMeasure p) := by
  apply integrable_of_bounded_measurable
    (measurable_longRangeIntervalDeleteZeroComponentCount m) (C := (m + 1 : ℝ))
  intro ω
  rw [abs_of_nonneg (Nat.cast_nonneg _),
    longRangeIntervalDeleteZeroComponentCount_eq]
  exact_mod_cast longRangeIntervalComponentCount_le
    (longRangeConfigurationPullback 1 ω) m

/-- Translation invariance identifies the expected component count on `1,...,m+1` with that
on `0,...,m`. -/
theorem integral_longRangeIntervalDeleteZeroComponentCount
    (p : LongRangeProfile) (m : ℕ) :
    ∫ ω, (longRangeIntervalDeleteZeroComponentCount ω m : ℝ)
        ∂longRangeMeasure p =
      ∫ ω, (longRangeIntervalComponentCount ω m : ℝ)
        ∂longRangeMeasure p := by
  simp_rw [longRangeIntervalDeleteZeroComponentCount_eq]
  have hmap := MeasureTheory.integral_map
    (μ := longRangeMeasure p) (measurable_longRangeConfigurationPullback 1).aemeasurable
    (measurable_longRangeIntervalComponentCount m).aestronglyMeasurable
  rw [← hmap, longRangeMeasure_map_configurationPullback]

/-- Adding zero to the shifted interval increases the component count by at most one. -/
theorem longRangeIntervalComponentCount_full_le_deleteZero_add_one
    (ω : LongRangeConfiguration) (m : ℕ) :
    longRangeIntervalComponentCount ω (m + 1) ≤
      longRangeIntervalDeleteZeroComponentCount ω m + 1 := by
  exact connectedComponent_card_le_deleteVertex_add_one
    (longRangeIntervalOpenGraph ω (m + 1)) 0

/-- If adding zero increases the component count, zero has no neighbour in the interval. -/
theorem longRangeInterval_zero_isolated_of_deleteZero_lt_full
    {ω : LongRangeConfiguration} {m : ℕ}
    (hcount : longRangeIntervalDeleteZeroComponentCount ω m <
      longRangeIntervalComponentCount ω (m + 1)) :
    ∀ i : Fin (m + 2), ¬(longRangeIntervalOpenGraph ω (m + 1)).Adj 0 i := by
  exact no_adj_of_deleteVertex_card_lt
    (longRangeIntervalOpenGraph ω (m + 1)) 0 hcount

/-! ### The finite insertion event -/

/-- The nearest-neighbour bond used for the insertion step. -/
def longRangeFirstEdge : Sym2 ℤ := s(0, 1)

/-- Force the nearest-neighbour bond closed. -/
def longRangeEraseFirstEdge (ω : LongRangeConfiguration) : LongRangeConfiguration :=
  ω \ {longRangeFirstEdge}

@[simp]
theorem mem_longRangeEraseFirstEdge_iff {e : Sym2 ℤ} {ω : LongRangeConfiguration} :
    e ∈ longRangeEraseFirstEdge ω ↔ e ∈ ω ∧ e ≠ longRangeFirstEdge := by
  simp [longRangeEraseFirstEdge]

/-- In the interval `0,...,m+1`, zero and one are disconnected after the bond `{0,1}` is
forced closed. -/
def longRangeIntervalFirstEdgeClosedDisconnectionEvent (m : ℕ) :
    Set LongRangeConfiguration :=
  {ω | ¬(longRangeIntervalOpenGraph (longRangeEraseFirstEdge ω) (m + 1)).Reachable 0 1}

/-- In the interval `0,...,m+1`, zero has an open edge to a vertex at least two. -/
def longRangeIntervalOriginLongEdgeEvent (m : ℕ) : Set LongRangeConfiguration :=
  {ω | ∃ i : Fin (m + 2), 2 ≤ i.val ∧
    (longRangeIntervalOpenGraph ω (m + 1)).Adj 0 i}

/-- Adding zero strictly merges components of the graph on `1,...,m+1`. -/
def longRangeIntervalMergeEvent (m : ℕ) : Set LongRangeConfiguration :=
  {ω | longRangeIntervalComponentCount ω (m + 1) <
    longRangeIntervalDeleteZeroComponentCount ω m}

/-- Zero is isolated inside the interval `0,...,m+1`. -/
def longRangeIntervalZeroIsolatedEvent (m : ℕ) : Set LongRangeConfiguration :=
  {ω | ∀ i : Fin (m + 2),
    ¬(longRangeIntervalOpenGraph ω (m + 1)).Adj 0 i}

theorem longRangeInterval_insertion_subset_merge (m : ℕ) :
    longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
        longRangeIntervalOriginLongEdgeEvent m ∩
        {ω | longRangeFirstEdge ∈ ω} ⊆
      longRangeIntervalMergeEvent m := by
  intro ω hω
  rcases hω with ⟨⟨hdis, i, hi, h0i⟩, h01open⟩
  let G := longRangeIntervalOpenGraph ω (m + 1)
  let H := G.induce ({0}ᶜ : Set (Fin (m + 2)))
  let oneH : {x : Fin (m + 2) // x ∈ ({0}ᶜ : Set (Fin (m + 2)))} :=
    ⟨1, by simp⟩
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    simp at hi
  let iH : {x : Fin (m + 2) // x ∈ ({0}ᶜ : Set (Fin (m + 2)))} :=
    ⟨i, by simpa using hi0⟩
  have h01 : G.Adj 0 1 := by
    rw [longRangeIntervalOpenGraph_adj]
    exact ⟨by simpa [longRangeFirstEdge] using h01open, by simp⟩
  have hnotreach : ¬H.Reachable oneH iH := by
    intro hreach
    let F : H →g longRangeIntervalOpenGraph
        (longRangeEraseFirstEdge ω) (m + 1) := {
      toFun := fun x : {x : Fin (m + 2) //
        x ∈ ({0}ᶜ : Set (Fin (m + 2)))} ↦ x.1
      map_rel' := by
        intro x y hxy
        change (longRangeIntervalOpenGraph ω (m + 1)).Adj x.1 y.1 at hxy
        rw [longRangeIntervalOpenGraph_adj] at hxy
        rw [longRangeIntervalOpenGraph_adj]
        refine ⟨?_, hxy.2⟩
        rw [mem_longRangeEraseFirstEdge_iff]
        refine ⟨hxy.1, ?_⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with heq | heq
        · exact x.property (by simpa [longRangeFirstEdge] using heq.1)
        · exact y.property (by simpa [longRangeFirstEdge] using heq.2)
    }
    have h1i := hreach.map F
    have h0iClosed : (longRangeIntervalOpenGraph
        (longRangeEraseFirstEdge ω) (m + 1)).Adj 0 i := by
      rw [longRangeIntervalOpenGraph_adj] at h0i ⊢
      refine ⟨?_, h0i.2⟩
      rw [mem_longRangeEraseFirstEdge_iff]
      refine ⟨h0i.1, ?_⟩
      intro heq
      rcases Sym2.eq_iff.mp heq with heq | heq
      · omega
      · omega
    change ¬(longRangeIntervalOpenGraph
      (longRangeEraseFirstEdge ω) (m + 1)).Reachable 0 1 at hdis
    exact hdis (h0iClosed.reachable.trans h1i.symm)
  change longRangeIntervalComponentCount ω (m + 1) <
    longRangeIntervalDeleteZeroComponentCount ω m
  exact connectedComponent_card_lt_deleteVertex_of_two_neighbors
    G 0 1 i h01 h0i hnotreach

theorem longRangeFirstEdge_mem_intervalSupport (m : ℕ) :
    longRangeFirstEdge ∈ longRangeIntervalEdgeSupport (m + 1) := by
  rw [longRangeIntervalEdgeSupport, Finset.mem_map]
  refine ⟨s((0 : Fin (m + 2)), (1 : Fin (m + 2))), Finset.mem_univ _, ?_⟩
  simp [longRangeFirstEdge]

theorem dependsOn_longRangeIntervalFirstEdgeClosedDisconnectionEvent (m : ℕ) :
    DependsOn ((longRangeIntervalEdgeSupport (m + 1)).erase longRangeFirstEdge)
      (longRangeIntervalFirstEdgeClosedDisconnectionEvent m) := by
  intro ω η h
  have hgraph : longRangeIntervalOpenGraph
      (longRangeEraseFirstEdge ω) (m + 1) =
      longRangeIntervalOpenGraph (longRangeEraseFirstEdge η) (m + 1) := by
    ext i j
    rw [longRangeIntervalOpenGraph_adj, longRangeIntervalOpenGraph_adj]
    apply and_congr
    · by_cases he : s((i.val : ℤ), (j.val : ℤ)) = longRangeFirstEdge
      · simp [mem_longRangeEraseFirstEdge_iff, he]
      · rw [mem_longRangeEraseFirstEdge_iff, mem_longRangeEraseFirstEdge_iff]
        exact and_congr
          (h _ (Finset.mem_erase.mpr ⟨he, Finset.mem_map.mpr
            ⟨s(i, j), Finset.mem_univ _, rfl⟩⟩)) (by simp [he])
    · rfl
  change (¬(longRangeIntervalOpenGraph
      (longRangeEraseFirstEdge ω) (m + 1)).Reachable 0 1) ↔
    ¬(longRangeIntervalOpenGraph
      (longRangeEraseFirstEdge η) (m + 1)).Reachable 0 1
  rw [hgraph]

theorem dependsOn_longRangeIntervalOriginLongEdgeEvent (m : ℕ) :
    DependsOn ((longRangeIntervalEdgeSupport (m + 1)).erase longRangeFirstEdge)
      (longRangeIntervalOriginLongEdgeEvent m) := by
  intro ω η h
  simp only [longRangeIntervalOriginLongEdgeEvent, Set.mem_setOf_eq]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [longRangeIntervalOpenGraph_adj, longRangeIntervalOpenGraph_adj]
  apply and_congr
  · apply h
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_map.mpr
      ⟨s((0 : Fin (m + 2)), i), Finset.mem_univ _, rfl⟩⟩
    intro he
    rcases Sym2.eq_iff.mp he with he | he <;>
      simp [longRangeFirstEdge] at he <;> omega
  · rfl

theorem dependsOn_longRangeIntervalMergeEvent (m : ℕ) :
    DependsOn (longRangeIntervalEdgeSupport (m + 1))
      (longRangeIntervalMergeEvent m) := by
  intro ω η h
  have hgraph := dependsOnFun_longRangeIntervalOpenGraph (m + 1) h
  change longRangeIntervalOpenGraph ω (m + 1) =
    longRangeIntervalOpenGraph η (m + 1) at hgraph
  simp only [longRangeIntervalMergeEvent, Set.mem_setOf_eq,
    longRangeIntervalComponentCount, longRangeIntervalDeleteZeroComponentCount]
  rw [hgraph]

theorem dependsOn_longRangeIntervalZeroIsolatedEvent (m : ℕ) :
    DependsOn (longRangeIntervalEdgeSupport (m + 1))
      (longRangeIntervalZeroIsolatedEvent m) := by
  intro ω η h
  have hgraph := dependsOnFun_longRangeIntervalOpenGraph (m + 1) h
  change longRangeIntervalOpenGraph ω (m + 1) =
    longRangeIntervalOpenGraph η (m + 1) at hgraph
  simp only [longRangeIntervalZeroIsolatedEvent, Set.mem_setOf_eq]
  rw [hgraph]

theorem measurableSet_longRangeIntervalFirstEdgeClosedDisconnectionEvent (m : ℕ) :
    MeasurableSet (longRangeIntervalFirstEdgeClosedDisconnectionEvent m) :=
  (dependsOn_longRangeIntervalFirstEdgeClosedDisconnectionEvent m).measurableSet

theorem measurableSet_longRangeIntervalOriginLongEdgeEvent (m : ℕ) :
    MeasurableSet (longRangeIntervalOriginLongEdgeEvent m) :=
  (dependsOn_longRangeIntervalOriginLongEdgeEvent m).measurableSet

theorem measurableSet_longRangeIntervalMergeEvent (m : ℕ) :
    MeasurableSet (longRangeIntervalMergeEvent m) :=
  (dependsOn_longRangeIntervalMergeEvent m).measurableSet

theorem measurableSet_longRangeIntervalZeroIsolatedEvent (m : ℕ) :
    MeasurableSet (longRangeIntervalZeroIsolatedEvent m) :=
  (dependsOn_longRangeIntervalZeroIsolatedEvent m).measurableSet

theorem indepSet_longRangeInterval_insertion_firstEdge
    (p : LongRangeProfile) (m : ℕ) :
    IndepSet
      (longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
        longRangeIntervalOriginLongEdgeEvent m)
      {ω | longRangeFirstEdge ∈ ω} (longRangeMeasure p) := by
  change IndepSet _ _ (inhomogeneousSetBernoulli (longRangeEdgeDensity p))
  apply inhomogeneousSetBernoulli_indepSet_of_dependsOn
    (E := (longRangeIntervalEdgeSupport (m + 1)).erase longRangeFirstEdge)
    (F := {longRangeFirstEdge})
  · simp
  · exact (dependsOn_longRangeIntervalFirstEdgeClosedDisconnectionEvent m).inter
      (dependsOn_longRangeIntervalOriginLongEdgeEvent m)
  · intro ω η h
    exact h longRangeFirstEdge (by simp)

/-- The finite Bernoulli insertion estimate in Kalikow's proof. -/
theorem longRange_firstDensity_mul_insertionEvent_le_merge
    (p : LongRangeProfile) (m : ℕ) :
    (p 1 : ℝ) * (longRangeMeasure p).real
        (longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
          longRangeIntervalOriginLongEdgeEvent m) ≤
      (longRangeMeasure p).real (longRangeIntervalMergeEvent m) := by
  have hind := (indepSet_longRangeInterval_insertion_firstEdge p m).measure_inter_eq_mul
  have hindReal : (longRangeMeasure p).real
      ((longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
        longRangeIntervalOriginLongEdgeEvent m) ∩
        {ω | longRangeFirstEdge ∈ ω}) =
      (longRangeMeasure p).real
          (longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
            longRangeIntervalOriginLongEdgeEvent m) *
        (longRangeMeasure p).real {ω | longRangeFirstEdge ∈ ω} := by
    simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hind
  have hopen : (longRangeMeasure p).real {ω | longRangeFirstEdge ∈ ω} =
      (p 1 : ℝ) := by
    rw [longRangeMeasure_real_edgeOpen]
    simp [longRangeFirstEdge, longRangeEdgeDensity]
  rw [mul_comm]
  rw [← hopen, ← hindReal]
  exact measureReal_mono (longRangeInterval_insertion_subset_merge m)

private theorem integrable_eventIndicator_longRange
    (p : LongRangeProfile) {A : Set LongRangeConfiguration} (hA : MeasurableSet A) :
    Integrable (A.indicator (fun _ ↦ (1 : ℝ))) (longRangeMeasure p) := by
  apply integrable_of_bounded_measurable (measurable_const.indicator hA) (C := 1)
  intro ω
  by_cases hω : ω ∈ A <;> simp [hω]

theorem longRangeInterval_mergeIndicator_le_countDifference_add_isolated
    (m : ℕ) (ω : LongRangeConfiguration) :
    (longRangeIntervalMergeEvent m).indicator (fun _ ↦ (1 : ℝ)) ω ≤
      (longRangeIntervalDeleteZeroComponentCount ω m : ℝ) -
        longRangeIntervalComponentCount ω (m + 1) +
        (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ (1 : ℝ)) ω := by
  by_cases hmerge : ω ∈ longRangeIntervalMergeEvent m
  · rw [Set.indicator_of_mem hmerge]
    have hlt : longRangeIntervalComponentCount ω (m + 1) <
        longRangeIntervalDeleteZeroComponentCount ω m := hmerge
    have hcastlt : (longRangeIntervalComponentCount ω (m + 1) : ℝ) <
        longRangeIntervalDeleteZeroComponentCount ω m := by exact_mod_cast hlt
    have hsucc : (longRangeIntervalComponentCount ω (m + 1) : ℝ) + 1 ≤
        longRangeIntervalDeleteZeroComponentCount ω m := by
      have hnat := Nat.succ_le_iff.mpr hlt
      exact_mod_cast hnat
    have hdiff : (1 : ℝ) ≤
        (longRangeIntervalDeleteZeroComponentCount ω m : ℝ) -
          longRangeIntervalComponentCount ω (m + 1) := by
      linarith
    have hindNonneg : (0 : ℝ) ≤
        (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ (1 : ℝ)) ω := by
      by_cases hω : ω ∈ longRangeIntervalZeroIsolatedEvent m <;> simp [hω]
    linarith
  · rw [Set.indicator_of_notMem hmerge]
    by_cases hle : longRangeIntervalComponentCount ω (m + 1) ≤
        longRangeIntervalDeleteZeroComponentCount ω m
    · have hcast : (longRangeIntervalComponentCount ω (m + 1) : ℝ) ≤
          longRangeIntervalDeleteZeroComponentCount ω m := by exact_mod_cast hle
      have hindNonneg : (0 : ℝ) ≤
          (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ (1 : ℝ)) ω := by
        by_cases hω : ω ∈ longRangeIntervalZeroIsolatedEvent m <;> simp [hω]
      linarith
    · have hlt : longRangeIntervalDeleteZeroComponentCount ω m <
          longRangeIntervalComponentCount ω (m + 1) := Nat.lt_of_not_ge hle
      have hisolated : ω ∈ longRangeIntervalZeroIsolatedEvent m := by
        exact longRangeInterval_zero_isolated_of_deleteZero_lt_full hlt
      rw [Set.indicator_of_mem hisolated]
      have hbound := longRangeIntervalComponentCount_full_le_deleteZero_add_one ω m
      have hcast : (longRangeIntervalComponentCount ω (m + 1) : ℝ) ≤
          longRangeIntervalDeleteZeroComponentCount ω m + 1 := by exact_mod_cast hbound
      linarith

/-- The expectation-telescoping bound (12.18): a strict merge can only be paid for by the
drop in expected component count, apart from configurations where the new endpoint is isolated. -/
theorem longRangeMeasure_real_merge_le_integral_sub_add_isolated
    (p : LongRangeProfile) (m : ℕ) :
    (longRangeMeasure p).real (longRangeIntervalMergeEvent m) ≤
      (∫ ω, (longRangeIntervalComponentCount ω m : ℝ) ∂longRangeMeasure p) -
        (∫ ω, (longRangeIntervalComponentCount ω (m + 1) : ℝ)
          ∂longRangeMeasure p) +
        (longRangeMeasure p).real (longRangeIntervalZeroIsolatedEvent m) := by
  let f : LongRangeConfiguration → ℝ :=
    (longRangeIntervalMergeEvent m).indicator (fun _ ↦ 1)
  let g : LongRangeConfiguration → ℝ := fun ω ↦
    (longRangeIntervalDeleteZeroComponentCount ω m : ℝ) -
      longRangeIntervalComponentCount ω (m + 1) +
      (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ 1) ω
  have hf : Integrable f (longRangeMeasure p) :=
    integrable_eventIndicator_longRange p (measurableSet_longRangeIntervalMergeEvent m)
  have hg : Integrable g (longRangeMeasure p) :=
    ((integrable_longRangeIntervalDeleteZeroComponentCount p m).sub
      (integrable_longRangeIntervalComponentCount p (m + 1))).add
      (integrable_eventIndicator_longRange p
        (measurableSet_longRangeIntervalZeroIsolatedEvent m))
  have hle : ∫ ω, f ω ∂longRangeMeasure p ≤
      ∫ ω, g ω ∂longRangeMeasure p :=
    integral_mono hf hg (longRangeInterval_mergeIndicator_le_countDifference_add_isolated m)
  dsimp [f, g] at hle
  have hleft : (∫ ω, (longRangeIntervalMergeEvent m).indicator
      (fun _ ↦ (1 : ℝ)) ω ∂longRangeMeasure p) =
      (longRangeMeasure p).real (longRangeIntervalMergeEvent m) := by
    rw [integral_indicator_const (1 : ℝ)
      (measurableSet_longRangeIntervalMergeEvent m), smul_eq_mul, mul_one]
  have hright : (∫ ω,
      (longRangeIntervalDeleteZeroComponentCount ω m : ℝ) -
        longRangeIntervalComponentCount ω (m + 1) +
        (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ (1 : ℝ)) ω
      ∂longRangeMeasure p) =
      (∫ ω, (longRangeIntervalComponentCount ω m : ℝ) ∂longRangeMeasure p) -
        (∫ ω, (longRangeIntervalComponentCount ω (m + 1) : ℝ)
          ∂longRangeMeasure p) +
        (longRangeMeasure p).real (longRangeIntervalZeroIsolatedEvent m) := by
    let D : LongRangeConfiguration → ℝ := fun ω ↦
      longRangeIntervalDeleteZeroComponentCount ω m
    let C : LongRangeConfiguration → ℝ := fun ω ↦
      longRangeIntervalComponentCount ω (m + 1)
    let J : LongRangeConfiguration → ℝ :=
      (longRangeIntervalZeroIsolatedEvent m).indicator (fun _ ↦ 1)
    have hD : Integrable D (longRangeMeasure p) :=
      integrable_longRangeIntervalDeleteZeroComponentCount p m
    have hC : Integrable C (longRangeMeasure p) :=
      integrable_longRangeIntervalComponentCount p (m + 1)
    have hJ : Integrable J (longRangeMeasure p) :=
      integrable_eventIndicator_longRange p
        (measurableSet_longRangeIntervalZeroIsolatedEvent m)
    have hsubIntegral : (∫ ω, (D - C) ω ∂longRangeMeasure p) =
        (∫ ω, D ω ∂longRangeMeasure p) -
          ∫ ω, C ω ∂longRangeMeasure p := by
      simpa only [Pi.sub_apply] using integral_sub hD hC
    calc
      (∫ ω,
          (longRangeIntervalDeleteZeroComponentCount ω m : ℝ) -
            longRangeIntervalComponentCount ω (m + 1) +
            (longRangeIntervalZeroIsolatedEvent m).indicator
              (fun _ ↦ (1 : ℝ)) ω ∂longRangeMeasure p) =
          ∫ ω, (D - C + J) ω ∂longRangeMeasure p := by rfl
      _ = (∫ ω, (D - C) ω ∂longRangeMeasure p) +
          ∫ ω, J ω ∂longRangeMeasure p := integral_add (hD.sub hC) hJ
      _ = ((∫ ω, D ω ∂longRangeMeasure p) -
          ∫ ω, C ω ∂longRangeMeasure p) +
          ∫ ω, J ω ∂longRangeMeasure p := by rw [hsubIntegral]
      _ = _ := by
        dsimp [D, C, J]
        rw [integral_longRangeIntervalDeleteZeroComponentCount,
          integral_indicator_const (1 : ℝ)
            (measurableSet_longRangeIntervalZeroIsolatedEvent m),
          smul_eq_mul, mul_one]
  rwa [hleft, hright] at hle

/-! ### Vanishing isolation error -/

/-- Positive origin edges of lengths `2,...,m+1`. -/
def longRangeIntervalOriginLongEdges (m : ℕ) : Finset (Sym2 ℤ) :=
  (Finset.range m).image fun j ↦ longRangeOriginEdge (j + 1, true)

theorem longRangeOriginEdge_true_add_one_injective :
    Function.Injective (fun j : ℕ ↦ longRangeOriginEdge (j + 1, true)) := by
  intro a b hab
  have hstep := longRangeOriginEdge_injective hab
  have hfst := congrArg Prod.fst hstep
  simp at hfst
  omega

theorem longRangeIntervalOriginLongEdgeEvent_eq (m : ℕ) :
    longRangeIntervalOriginLongEdgeEvent m =
      { ω | ∃ e ∈ longRangeIntervalOriginLongEdges m, e ∈ ω } := by
  ext ω
  simp only [longRangeIntervalOriginLongEdgeEvent,
    longRangeIntervalOriginLongEdges, Set.mem_setOf_eq, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, h0i⟩
    refine ⟨longRangeOriginEdge (i.val - 1, true), ?_, ?_⟩
    · refine ⟨i.val - 2, by omega, ?_⟩
      have hidx : i.val - 2 + 1 = i.val - 1 := by omega
      rw [hidx]
    · rw [longRangeIntervalOpenGraph_adj] at h0i
      have hedge : longRangeOriginEdge (i.val - 1, true) =
          s(((0 : Fin (m + 2)).val : ℤ), (i.val : ℤ)) := by
        apply Sym2.eq_iff.mpr
        left
        constructor
        · rfl
        · norm_num [longRangeOriginEdge, longRangeStepDisplacement,
            Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
      rw [hedge]
      exact h0i.1
  · rintro ⟨e, ⟨j, hj, rfl⟩, he⟩
    let i : Fin (m + 2) := ⟨j + 2, by omega⟩
    refine ⟨i, by simp [i], ?_⟩
    rw [longRangeIntervalOpenGraph_adj]
    constructor
    · convert he using 1
    · apply Fin.ne_of_val_ne
      simp [i]

theorem longRangeIntervalOriginLongEdgeEvent_compl_eq (m : ℕ) :
    (longRangeIntervalOriginLongEdgeEvent m)ᶜ =
      {ω | Disjoint (longRangeIntervalOriginLongEdges m : Set (Sym2 ℤ)) ω} := by
  rw [longRangeIntervalOriginLongEdgeEvent_eq]
  ext ω
  simp [Set.disjoint_left]

theorem longRangeMeasure_real_originLongEdge_compl (p : LongRangeProfile) (m : ℕ) :
    (longRangeMeasure p).real (longRangeIntervalOriginLongEdgeEvent m)ᶜ =
      ∏ j ∈ Finset.range m, (1 - (p (j + 2) : ℝ)) := by
  rw [longRangeIntervalOriginLongEdgeEvent_compl_eq,
    longRangeMeasure_real_disjoint_finset, longRangeIntervalOriginLongEdges,
    Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro j _hj
    rw [longRangeEdgeDistance_originEdge]
  · intro a _ha b _hb hab
    exact longRangeOriginEdge_true_add_one_injective hab

theorem longRangeIntervalZeroIsolatedEvent_subset_longEdge_compl (m : ℕ) :
    longRangeIntervalZeroIsolatedEvent m ⊆
      (longRangeIntervalOriginLongEdgeEvent m)ᶜ := by
  intro ω hiso hlong
  rcases hlong with ⟨i, _hi, h0i⟩
  exact hiso i h0i

theorem longRangeMeasure_real_zeroIsolated_le_longEdge_compl
    (p : LongRangeProfile) (m : ℕ) :
    (longRangeMeasure p).real (longRangeIntervalZeroIsolatedEvent m) ≤
      (longRangeMeasure p).real (longRangeIntervalOriginLongEdgeEvent m)ᶜ :=
  measureReal_mono (longRangeIntervalZeroIsolatedEvent_subset_longEdge_compl m)

theorem longRange_shiftedPartialSums_tendsto_atTop_of_not_summable
    (p : LongRangeProfile) (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    Tendsto (fun m : ℕ ↦ ∑ j ∈ Finset.range m, (p (j + 2) : ℝ))
      atTop atTop := by
  have htail : ¬Summable fun j : ℕ ↦ (p (j + 2) : ℝ) := by
    intro hs
    apply hdiv
    apply (summable_nat_add_iff 2).mp
    simpa only [Nat.add_comm] using hs
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun j ↦ unitInterval.nonneg (p (j + 2)))).mp htail

theorem longRange_closedLongEdgeProduct_le_exp
    (p : LongRangeProfile) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 - (p (j + 2) : ℝ)) ≤
      Real.exp (-(∑ j ∈ Finset.range m, (p (j + 2) : ℝ))) := by
  calc
    ∏ j ∈ Finset.range m, (1 - (p (j + 2) : ℝ)) ≤
        ∏ j ∈ Finset.range m, Real.exp (-(p (j + 2) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact sub_nonneg.mpr (unitInterval.le_one _)
      · intro j _hj
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-(∑ j ∈ Finset.range m, (p (j + 2) : ℝ))) := by
      rw [← Real.exp_sum]
      congr 2
      simp

theorem longRange_closedLongEdgeProduct_tendsto_zero_of_not_summable
    (p : LongRangeProfile) (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    Tendsto (fun m : ℕ ↦
      ∏ j ∈ Finset.range m, (1 - (p (j + 2) : ℝ))) atTop (nhds 0) := by
  have hsum := longRange_shiftedPartialSums_tendsto_atTop_of_not_summable p hdiv
  have hexp : Tendsto (fun m : ℕ ↦
      Real.exp (-(∑ j ∈ Finset.range m, (p (j + 2) : ℝ)))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum)
  exact squeeze_zero
    (fun m ↦ Finset.prod_nonneg fun j _hj ↦
      sub_nonneg.mpr (unitInterval.le_one (p (j + 2))))
    (longRange_closedLongEdgeProduct_le_exp p) hexp

theorem longRangeMeasure_real_originLongEdge_compl_tendsto_zero_of_not_summable
    (p : LongRangeProfile) (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    Tendsto (fun m : ℕ ↦
      (longRangeMeasure p).real (longRangeIntervalOriginLongEdgeEvent m)ᶜ)
      atTop (nhds 0) := by
  simpa only [longRangeMeasure_real_originLongEdge_compl] using
    longRange_closedLongEdgeProduct_tendsto_zero_of_not_summable p hdiv

/-- A nonnegative sequence cannot decrease by a fixed positive amount at every sufficiently
late step. -/
theorem exists_large_sub_succ_lt_of_nonneg
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (N : ℕ) : ∃ m ≥ N, a m - a (m + 1) < epsilon := by
  by_contra h
  push_neg at h
  have hiter : ∀ k : ℕ, a (N + k) ≤ a N - (k : ℝ) * epsilon := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hdrop := h (N + k) (by omega)
        have hidx : N + k + 1 = N + (k + 1) := by omega
        rw [hidx] at hdrop
        push_cast
        linarith
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (a N / epsilon)
  have hkpos : a N < (k : ℝ) * epsilon := by
    have := (mul_lt_mul_of_pos_right hk hepsilon)
    field_simp at this
    simpa [mul_comm] using this
  have hnonneg := ha (N + k)
  have hupper := hiter k
  linarith

theorem exists_large_integral_componentCount_drop_lt
    (p : LongRangeProfile) {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℕ) :
    ∃ m ≥ N,
      (∫ ω, (longRangeIntervalComponentCount ω m : ℝ) ∂longRangeMeasure p) -
        (∫ ω, (longRangeIntervalComponentCount ω (m + 1) : ℝ)
          ∂longRangeMeasure p) < epsilon := by
  apply exists_large_sub_succ_lt_of_nonneg
  · intro n
    exact integral_nonneg fun ω ↦ Nat.cast_nonneg _
  · exact hepsilon

/-! ### Finite adjacent disconnection -/

/-- Zero and one are disconnected inside `0,...,m+1`. -/
def longRangeIntervalAdjacentDisconnectionEvent (m : ℕ) :
    Set LongRangeConfiguration :=
  {ω | ¬(longRangeIntervalOpenGraph ω (m + 1)).Reachable 0 1}

theorem dependsOn_longRangeIntervalAdjacentDisconnectionEvent (m : ℕ) :
    DependsOn (longRangeIntervalEdgeSupport (m + 1))
      (longRangeIntervalAdjacentDisconnectionEvent m) := by
  intro ω η h
  have hgraph := dependsOnFun_longRangeIntervalOpenGraph (m + 1) h
  change longRangeIntervalOpenGraph ω (m + 1) =
    longRangeIntervalOpenGraph η (m + 1) at hgraph
  change (¬(longRangeIntervalOpenGraph ω (m + 1)).Reachable 0 1) ↔
    ¬(longRangeIntervalOpenGraph η (m + 1)).Reachable 0 1
  rw [hgraph]

theorem measurableSet_longRangeIntervalAdjacentDisconnectionEvent (m : ℕ) :
    MeasurableSet (longRangeIntervalAdjacentDisconnectionEvent m) :=
  (dependsOn_longRangeIntervalAdjacentDisconnectionEvent m).measurableSet

theorem longRangeIntervalAdjacentDisconnection_subset_firstEdgeClosed (m : ℕ) :
    longRangeIntervalAdjacentDisconnectionEvent m ⊆
      longRangeIntervalFirstEdgeClosedDisconnectionEvent m := by
  intro ω hdis
  change ¬(longRangeIntervalOpenGraph ω (m + 1)).Reachable 0 1 at hdis
  change ¬(longRangeIntervalOpenGraph
    (longRangeEraseFirstEdge ω) (m + 1)).Reachable 0 1
  intro herased
  apply hdis
  apply herased.mono
  intro i j hij
  rw [longRangeIntervalOpenGraph_adj] at hij ⊢
  exact ⟨(mem_longRangeEraseFirstEdge_iff.mp hij.1).1, hij.2⟩

theorem longRangeIntervalFirstEdgeClosed_subset_split (m : ℕ) :
    longRangeIntervalFirstEdgeClosedDisconnectionEvent m ⊆
      (longRangeIntervalFirstEdgeClosedDisconnectionEvent m ∩
        longRangeIntervalOriginLongEdgeEvent m) ∪
      (longRangeIntervalOriginLongEdgeEvent m)ᶜ := by
  intro ω hdis
  by_cases hlong : ω ∈ longRangeIntervalOriginLongEdgeEvent m
  · exact Or.inl ⟨hdis, hlong⟩
  · exact Or.inr hlong

/-- Finite Kalikow inequality: adjacent disconnection is controlled by the telescoping merge
event and by the probability that no sufficiently long origin edge is present. -/
theorem longRange_firstDensity_mul_adjacentDisconnection_le
    (p : LongRangeProfile) (m : ℕ) :
    (p 1 : ℝ) * (longRangeMeasure p).real
        (longRangeIntervalAdjacentDisconnectionEvent m) ≤
      (longRangeMeasure p).real (longRangeIntervalMergeEvent m) +
        (longRangeMeasure p).real (longRangeIntervalOriginLongEdgeEvent m)ᶜ := by
  let A := longRangeIntervalFirstEdgeClosedDisconnectionEvent m
  let B := longRangeIntervalOriginLongEdgeEvent m
  have hactual : (longRangeMeasure p).real
      (longRangeIntervalAdjacentDisconnectionEvent m) ≤
      (longRangeMeasure p).real A :=
    measureReal_mono (longRangeIntervalAdjacentDisconnection_subset_firstEdgeClosed m)
  have hsplit : (longRangeMeasure p).real A ≤
      (longRangeMeasure p).real (A ∩ B) + (longRangeMeasure p).real Bᶜ := by
    calc
      (longRangeMeasure p).real A ≤
          (longRangeMeasure p).real ((A ∩ B) ∪ Bᶜ) :=
        measureReal_mono (longRangeIntervalFirstEdgeClosed_subset_split m)
      _ ≤ _ := measureReal_union_le _ _
  have hinsert : (p 1 : ℝ) * (longRangeMeasure p).real (A ∩ B) ≤
      (longRangeMeasure p).real (longRangeIntervalMergeEvent m) :=
    longRange_firstDensity_mul_insertionEvent_le_merge p m
  have hp0 : (0 : ℝ) ≤ p 1 := unitInterval.nonneg _
  have hp1 : (p 1 : ℝ) ≤ 1 := unitInterval.le_one _
  have hmulActual := mul_le_mul_of_nonneg_left hactual hp0
  have hmulSplit := mul_le_mul_of_nonneg_left hsplit hp0
  have htailNonneg : (0 : ℝ) ≤
      (longRangeMeasure p).real Bᶜ := measureReal_nonneg
  have htailMul : (p 1 : ℝ) * (longRangeMeasure p).real Bᶜ ≤
      (longRangeMeasure p).real Bᶜ := by nlinarith
  dsimp [A, B] at hactual hsplit hinsert hmulActual hmulSplit htailMul ⊢
  nlinarith

theorem longRangeIntervalAdjacentDisconnection_antitone :
    Antitone longRangeIntervalAdjacentDisconnectionEvent := by
  intro m n hmn ω hn
  change ¬(longRangeIntervalOpenGraph ω (n + 1)).Reachable 0 1 at hn
  change ¬(longRangeIntervalOpenGraph ω (m + 1)).Reachable 0 1
  intro hm
  have hsize : m + 2 ≤ n + 2 := by omega
  let F : longRangeIntervalOpenGraph ω (m + 1) →g
      longRangeIntervalOpenGraph ω (n + 1) := {
    toFun := Fin.castLE hsize
    map_rel' := by
      intro i j hij
      rw [longRangeIntervalOpenGraph_adj] at hij ⊢
      simpa using hij
  }
  have hmapped := hm.map F
  exact hn (by simpa [F] using hmapped)

theorem antitone_longRangeMeasure_real_intervalAdjacentDisconnection
    (p : LongRangeProfile) :
    Antitone fun m ↦ (longRangeMeasure p).real
      (longRangeIntervalAdjacentDisconnectionEvent m) := by
  intro m n hmn
  exact measureReal_mono (longRangeIntervalAdjacentDisconnection_antitone hmn)

/-- Kalikow's conclusion under the direct nearest-neighbour support hypothesis: if `p₁>0`
and the total intensity diverges, the finite-interval probability that zero and one remain
disconnected tends to zero. -/
theorem longRangeMeasure_real_intervalAdjacentDisconnection_tendsto_zero
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    Tendsto (fun m ↦ (longRangeMeasure p).real
      (longRangeIntervalAdjacentDisconnectionEvent m)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let delta : ℝ := (p 1 : ℝ) * epsilon / 4
  have hdelta : 0 < delta := by positivity
  have htail :=
    longRangeMeasure_real_originLongEdge_compl_tendsto_zero_of_not_summable p hdiv
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail delta hdelta
  obtain ⟨m, hmN, hdrop⟩ :=
    exists_large_integral_componentCount_drop_lt p hdelta N
  have htailm : (longRangeMeasure p).real
      (longRangeIntervalOriginLongEdgeEvent m)ᶜ < delta := by
    have hm := hN m hmN
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hm
  have hisolated : (longRangeMeasure p).real
      (longRangeIntervalZeroIsolatedEvent m) ≤
      (longRangeMeasure p).real (longRangeIntervalOriginLongEdgeEvent m)ᶜ :=
    longRangeMeasure_real_zeroIsolated_le_longEdge_compl p m
  have hmerge := longRangeMeasure_real_merge_le_integral_sub_add_isolated p m
  have hfinite := longRange_firstDensity_mul_adjacentDisconnection_le p m
  have hsmall : (longRangeMeasure p).real
      (longRangeIntervalAdjacentDisconnectionEvent m) < epsilon := by
    have hprobNonneg : (0 : ℝ) ≤ (longRangeMeasure p).real
        (longRangeIntervalAdjacentDisconnectionEvent m) := measureReal_nonneg
    dsimp [delta] at hdrop htailm ⊢
    nlinarith
  refine ⟨m, ?_⟩
  intro n hmn
  have hmono := antitone_longRangeMeasure_real_intervalAdjacentDisconnection p hmn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hmono.trans_lt hsmall

/-! ### Passage to the half-line and the full integer line -/

/-- Failure of an origin-to-one connection in every finite nonnegative interval. -/
def longRangeNonnegativeAdjacentDisconnectionEvent : Set LongRangeConfiguration :=
  ⋂ m : ℕ, longRangeIntervalAdjacentDisconnectionEvent m

theorem measurableSet_longRangeNonnegativeAdjacentDisconnectionEvent :
    MeasurableSet longRangeNonnegativeAdjacentDisconnectionEvent :=
  MeasurableSet.iInter measurableSet_longRangeIntervalAdjacentDisconnectionEvent

theorem longRangeMeasure_real_nonnegativeAdjacentDisconnection_eq_zero
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    (longRangeMeasure p).real longRangeNonnegativeAdjacentDisconnectionEvent = 0 := by
  have hmeasure : Tendsto
      (fun m : ℕ ↦ longRangeMeasure p
        (longRangeIntervalAdjacentDisconnectionEvent m)) atTop
      (nhds (longRangeMeasure p longRangeNonnegativeAdjacentDisconnectionEvent)) := by
    simpa only [longRangeNonnegativeAdjacentDisconnectionEvent, Function.comp_apply] using
      (tendsto_measure_iInter_atTop
        (fun m ↦ (measurableSet_longRangeIntervalAdjacentDisconnectionEvent m).nullMeasurableSet)
        longRangeIntervalAdjacentDisconnection_antitone
        ⟨0, measure_ne_top _ _⟩)
  have hreal : Tendsto
      (fun m : ℕ ↦ (longRangeMeasure p).real
        (longRangeIntervalAdjacentDisconnectionEvent m)) atTop
      (nhds ((longRangeMeasure p).real
        longRangeNonnegativeAdjacentDisconnectionEvent)) := by
    simpa [Measure.real] using
      (ENNReal.tendsto_toReal (measure_ne_top (longRangeMeasure p)
        longRangeNonnegativeAdjacentDisconnectionEvent)).comp hmeasure
  exact tendsto_nhds_unique hreal
    (longRangeMeasure_real_intervalAdjacentDisconnection_tendsto_zero p hp1 hdiv)

theorem longRangeConnectionEvent_compl_subset_nonnegativeDisconnection :
    (longRangeConnectionEvent 0 1)ᶜ ⊆
      longRangeNonnegativeAdjacentDisconnectionEvent := by
  intro ω hfull
  change ω ∈ ⋂ m : ℕ, longRangeIntervalAdjacentDisconnectionEvent m
  rw [Set.mem_iInter]
  intro m
  change ¬(longRangeIntervalOpenGraph ω (m + 1)).Reachable 0 1
  intro hfinite
  apply hfull
  apply longRangeOpenGraph_reachable_iff.mp
  let F : longRangeIntervalOpenGraph ω (m + 1) →g longRangeOpenGraph ω := {
    toFun := fun i ↦ (i.val : ℤ)
    map_rel' := by
      intro i j hij
      rw [longRangeIntervalOpenGraph_adj] at hij
      exact longRangeOpenGraph_adj.mpr ⟨hij.1, by
        intro hval
        exact hij.2 (Fin.ext (Int.ofNat_inj.mp hval))⟩
  }
  simpa [F] using hfinite.map F

theorem longRangeMeasure_real_adjacentConnection_eq_one
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    (longRangeMeasure p).real (longRangeConnectionEvent 0 1) = 1 := by
  have hcompl : (longRangeMeasure p).real (longRangeConnectionEvent 0 1)ᶜ = 0 := by
    apply le_antisymm
    · calc
        (longRangeMeasure p).real (longRangeConnectionEvent 0 1)ᶜ ≤
            (longRangeMeasure p).real
              longRangeNonnegativeAdjacentDisconnectionEvent :=
          measureReal_mono longRangeConnectionEvent_compl_subset_nonnegativeDisconnection
        _ = 0 := longRangeMeasure_real_nonnegativeAdjacentDisconnection_eq_zero p hp1 hdiv
    · exact measureReal_nonneg
  rw [measureReal_compl (measurableSet_longRangeConnectionEvent 0 1), probReal_univ] at hcompl
  linarith

/-- Integer translation is a graph isomorphism from the pullback configuration to the
original configuration. -/
def longRangeOpenGraphTranslationIso (a : ℤ) (ω : LongRangeConfiguration) :
    longRangeOpenGraph (longRangeConfigurationPullback a ω) ≃g
      longRangeOpenGraph ω where
  __ := Equiv.addRight a
  map_rel_iff' := by
    intro x y
    rw [longRangeOpenGraph_adj, longRangeOpenGraph_adj]
    simp [longRangeConfigurationPullback, longRangeEdgeTranslateEmbedding_mk]

theorem longRangeTranslatedEvent_connectionEvent (a x y : ℤ) :
    longRangeTranslatedEvent a (longRangeConnectionEvent x y) =
      longRangeConnectionEvent (x + a) (y + a) := by
  ext ω
  change longRangeConfigurationPullback a ω ∈ longRangeConnectionEvent x y ↔
    ω ∈ longRangeConnectionEvent (x + a) (y + a)
  rw [← longRangeOpenGraph_reachable_iff, ← longRangeOpenGraph_reachable_iff]
  simpa [longRangeOpenGraphTranslationIso] using
    (longRangeOpenGraphTranslationIso a ω).reachable_iff.symm

theorem longRangeMeasure_real_adjacentConnection_eq_one_at
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) (x : ℤ) :
    (longRangeMeasure p).real (longRangeConnectionEvent x (x + 1)) = 1 := by
  calc
    (longRangeMeasure p).real (longRangeConnectionEvent x (x + 1)) =
        (longRangeMeasure p).real
          (longRangeTranslatedEvent x (longRangeConnectionEvent 0 1)) := by
      simpa [add_comm, add_left_comm, add_assoc] using congrArg
        (fun A ↦ (longRangeMeasure p).real A)
        (longRangeTranslatedEvent_connectionEvent x 0 1).symm
    _ = (longRangeMeasure p).real (longRangeConnectionEvent 0 1) :=
      longRangeMeasure_real_translatedEvent p
        (measurableSet_longRangeConnectionEvent 0 1) x
    _ = 1 := longRangeMeasure_real_adjacentConnection_eq_one p hp1 hdiv

theorem longRangeConnected_of_all_adjacent_connected
    {ω : LongRangeConfiguration}
    (hω : ∀ x : ℤ, ω ∈ longRangeConnectionEvent x (x + 1)) :
    ω ∈ longRangeConnectedEvent := by
  rw [mem_longRangeConnectedEvent_iff]
  have hzero : ∀ z : ℤ, (longRangeOpenGraph ω).Reachable 0 z := by
    intro z
    cases z with
    | ofNat n =>
        induction n with
        | zero =>
            simpa using ((longRangeOpenGraph ω).reachable_refl 0)
        | succ n ih =>
            have hstep := longRangeOpenGraph_reachable_iff.mpr (hω (n : ℤ))
            convert ih.trans hstep using 1 <;> simp
    | negSucc n =>
        induction n with
        | zero =>
            have hstep := longRangeOpenGraph_reachable_iff.mpr (hω (-1))
            convert hstep.symm using 1 <;> norm_num
        | succ n ih =>
            let k : ℤ := -((n : ℤ) + 2)
            have hstep := longRangeOpenGraph_reachable_iff.mpr (hω k)
            have hk : k + 1 = -((n : ℤ) + 1) := by dsimp [k]; omega
            have hback : (longRangeOpenGraph ω).Reachable
                (-((n : ℤ) + 1)) k := by
              rw [← hk]
              exact hstep.symm
            convert ih.trans hback using 1 <;> simp [k] <;> omega
  intro x y
  exact longRangeOpenGraph_reachable_iff.mp ((hzero x).symm.trans (hzero y))

/-- **Kalikow's theorem with a direct nearest-neighbour generator.** Divergent total
intensity and `p₁>0` make the one-dimensional long-range graph connected almost surely. -/
theorem longRange_ae_connected_of_firstDensity_pos_of_not_summable
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    ∀ᵐ ω ∂longRangeMeasure p, ω ∈ longRangeConnectedEvent := by
  have hx : ∀ x : ℤ, ∀ᵐ ω ∂longRangeMeasure p,
      ω ∈ longRangeConnectionEvent x (x + 1) := fun x ↦
    ae_mem_of_measureReal_eq_one (longRangeMeasure p)
      (measurableSet_longRangeConnectionEvent x (x + 1))
      (longRangeMeasure_real_adjacentConnection_eq_one_at p hp1 hdiv x)
  filter_upwards [ae_all_iff.mpr hx] with ω hω
  exact longRangeConnected_of_all_adjacent_connected hω

theorem longRangeConnectedProbability_eq_one_of_firstDensity_pos_of_not_summable
    (p : LongRangeProfile) (hp1 : 0 < (p 1 : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    longRangeConnectedProbability p = 1 := by
  have hae := longRange_ae_connected_of_firstDensity_pos_of_not_summable p hp1 hdiv
  have hm : longRangeMeasure p longRangeConnectedEvent =
      longRangeMeasure p Set.univ :=
    (ae_mem_iff_measure_eq measurableSet_longRangeConnectedEvent.nullMeasurableSet).mp hae
  rw [longRangeConnectedProbability, measureReal_def, hm]
  simp

end Percolation
