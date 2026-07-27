import Percolation.Bernoulli.Inhomogeneous

/-!
# One-dimensional long-range bond percolation

This file supplies the probability and graph layer used in Grimmett, *Percolation* (2nd ed.),
§12.3.  Vertices are the integers and every unordered pair of distinct vertices is a possible
bond.  Its opening probability depends only on the distance between its endpoints.

The construction deliberately uses `Set (Sym2 ℤ)` as the sample space.  Diagonal pairs are
assigned density zero and `SimpleGraph.fromEdgeSet` removes them, so the representation has no
junk self-loops while remaining a literal countable product space.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Finset unitInterval ENNReal

/-- The complete probability profile for one-dimensional long-range percolation.  The source
only indexes positive distances; `prob_zero` records the harmless zero extension used to put the
law on all unordered integer pairs. -/
structure LongRangeProfile where
  prob : ℕ → I
  prob_zero : prob 0 = 0

namespace LongRangeProfile

instance : CoeFun LongRangeProfile fun _ ↦ ℕ → I := ⟨LongRangeProfile.prob⟩

@[simp]
theorem apply_zero (p : LongRangeProfile) : p 0 = 0 :=
  p.prob_zero

/-- The source convention that every positive-distance probability is strictly below one. -/
def IsStrict (p : LongRangeProfile) : Prop :=
  ∀ n, 0 < n → (p n : ℝ) < 1

end LongRangeProfile

/-- The distance between the endpoints of an unordered integer pair. -/
def longRangeEdgeDistance : Sym2 ℤ → ℕ :=
  Sym2.lift ⟨fun x y ↦ (y - x).natAbs, by
    intro x y
    dsimp
    rw [show x - y = -(y - x) by ring, Int.natAbs_neg]⟩

@[simp]
theorem longRangeEdgeDistance_mk (x y : ℤ) :
    longRangeEdgeDistance s(x, y) = (y - x).natAbs := by
  simp [longRangeEdgeDistance, Sym2.lift_mk]

@[simp]
theorem longRangeEdgeDistance_diag (x : ℤ) :
    longRangeEdgeDistance s(x, x) = 0 := by
  simp

theorem longRangeEdgeDistance_pos_iff {x y : ℤ} :
    0 < longRangeEdgeDistance s(x, y) ↔ x ≠ y := by
  simp [longRangeEdgeDistance_mk, sub_eq_zero, eq_comm]

/-- Long-range configurations contain arbitrary unordered integer pairs. -/
abbrev LongRangeConfiguration := Set (Sym2 ℤ)

/-- Density of an unordered pair under a distance profile. -/
def longRangeEdgeDensity (p : LongRangeProfile) (e : Sym2 ℤ) : I :=
  p (longRangeEdgeDistance e)

@[simp]
theorem longRangeEdgeDensity_mk (p : LongRangeProfile) (x y : ℤ) :
    longRangeEdgeDensity p s(x, y) = p (y - x).natAbs := by
  simp [longRangeEdgeDensity]

@[simp]
theorem longRangeEdgeDensity_diag (p : LongRangeProfile) (x : ℤ) :
    longRangeEdgeDensity p s(x, x) = 0 := by
  simp [longRangeEdgeDensity]

/-- The independent long-range bond law with profile `p`. -/
noncomputable def longRangeMeasure (p : LongRangeProfile) :
    Measure LongRangeConfiguration :=
  inhomogeneousSetBernoulli (longRangeEdgeDensity p)

noncomputable instance longRangeMeasure.isProbabilityMeasure (p : LongRangeProfile) :
    IsProbabilityMeasure (longRangeMeasure p) := by
  rw [longRangeMeasure]
  infer_instance

@[simp]
theorem longRangeMeasure_real_edgeOpen (p : LongRangeProfile) (e : Sym2 ℤ) :
    (longRangeMeasure p).real {ω | e ∈ ω} = longRangeEdgeDensity p e := by
  simp [longRangeMeasure]

@[simp]
theorem longRangeMeasure_real_edgeClosed (p : LongRangeProfile) (e : Sym2 ℤ) :
    (longRangeMeasure p).real {ω | e ∉ ω} = 1 - longRangeEdgeDensity p e := by
  simp [longRangeMeasure]

/-- Exact probability that a prescribed finite family of long-range bonds is open. -/
theorem longRangeMeasure_real_superset_finset (p : LongRangeProfile)
    (s : Finset (Sym2 ℤ)) :
    (longRangeMeasure p).real {ω | (s : Set (Sym2 ℤ)) ⊆ ω} =
      ∏ e ∈ s, (p (longRangeEdgeDistance e) : ℝ) := by
  simpa [longRangeMeasure, longRangeEdgeDensity] using
    inhomogeneousSetBernoulli_real_superset_finset s (longRangeEdgeDensity p)

/-- Exact probability that a prescribed finite family of long-range bonds is closed. -/
theorem longRangeMeasure_real_disjoint_finset (p : LongRangeProfile)
    (s : Finset (Sym2 ℤ)) :
    (longRangeMeasure p).real {ω | Disjoint (s : Set (Sym2 ℤ)) ω} =
      ∏ e ∈ s, (1 - (p (longRangeEdgeDistance e) : ℝ)) := by
  simpa [longRangeMeasure, longRangeEdgeDensity] using
    inhomogeneousSetBernoulli_real_disjoint_finset s (longRangeEdgeDensity p)

/-! ### Integer translations -/

/-- Translate both endpoints of an unordered integer pair. -/
def longRangeEdgeTranslateEmbedding (a : ℤ) : Sym2 ℤ ↪ Sym2 ℤ :=
  (Equiv.addRight a).toEmbedding.sym2Map

@[simp]
theorem longRangeEdgeTranslateEmbedding_mk (a x y : ℤ) :
    longRangeEdgeTranslateEmbedding a s(x, y) = s(x + a, y + a) := by
  rfl

@[simp]
theorem longRangeEdgeDistance_translate (a : ℤ) (e : Sym2 ℤ) :
    longRangeEdgeDistance (longRangeEdgeTranslateEmbedding a e) =
      longRangeEdgeDistance e := by
  induction e using Sym2.inductionOn with
  | _ x y => simp [longRangeEdgeTranslateEmbedding_mk]

/-- Pull a configuration back by translation of both endpoints. -/
def longRangeConfigurationPullback (a : ℤ) (ω : LongRangeConfiguration) :
    LongRangeConfiguration :=
  longRangeEdgeTranslateEmbedding a ⁻¹' ω

/-- The long-range product law is invariant under every integer translation. -/
theorem longRangeMeasure_map_configurationPullback (p : LongRangeProfile) (a : ℤ) :
    (longRangeMeasure p).map (longRangeConfigurationPullback a) =
      longRangeMeasure p := by
  change (inhomogeneousSetBernoulli (longRangeEdgeDensity p)).map
      (fun ω ↦ longRangeEdgeTranslateEmbedding a ⁻¹' ω) =
    inhomogeneousSetBernoulli (longRangeEdgeDensity p)
  rw [inhomogeneousSetBernoulli_map_preimage_embedding]
  congr 1
  funext e
  simp [longRangeEdgeDensity]

/-- Translate an event by pulling configurations back along the corresponding edge
translation. -/
def longRangeTranslatedEvent (a : ℤ) (A : Set LongRangeConfiguration) :
    Set LongRangeConfiguration :=
  longRangeConfigurationPullback a ⁻¹' A

theorem measurable_longRangeConfigurationPullback (a : ℤ) :
    Measurable (longRangeConfigurationPullback a) := by
  exact measurable_preimage_embedding (longRangeEdgeTranslateEmbedding a)

theorem measurableSet_longRangeTranslatedEvent {A : Set LongRangeConfiguration}
    (hA : MeasurableSet A) (a : ℤ) :
    MeasurableSet (longRangeTranslatedEvent a A) :=
  hA.preimage (measurable_longRangeConfigurationPullback a)

/-- Every translated event has the same probability as the origin event. -/
theorem longRangeMeasure_real_translatedEvent (p : LongRangeProfile)
    {A : Set LongRangeConfiguration} (hA : MeasurableSet A) (a : ℤ) :
    (longRangeMeasure p).real (longRangeTranslatedEvent a A) =
      (longRangeMeasure p).real A := by
  have hmap := longRangeMeasure_map_configurationPullback p a
  have happ := congrArg (fun μ : Measure LongRangeConfiguration ↦ μ A) hmap
  change (Measure.map (longRangeConfigurationPullback a) (longRangeMeasure p)) A =
    (longRangeMeasure p) A at happ
  rw [Measure.map_apply (measurable_longRangeConfigurationPullback a) hA] at happ
  exact congrArg ENNReal.toReal happ

/-- A translated finite cylinder is supported by the correspondingly translated edge set. -/
theorem dependsOn_longRangeTranslatedEvent {E : Finset (Sym2 ℤ)}
    {A : Set LongRangeConfiguration} (hA : DependsOn E A) (a : ℤ) :
    DependsOn (E.map (longRangeEdgeTranslateEmbedding a))
      (longRangeTranslatedEvent a A) := by
  intro ω η hagree
  apply hA
  intro e he
  exact hagree (longRangeEdgeTranslateEmbedding a e) (Finset.mem_map.mpr ⟨e, he, rfl⟩)

/-- The largest absolute endpoint in a finite long-range edge set. -/
def longRangeEdgeSetRadius (E : Finset (Sym2 ℤ)) : ℕ :=
  E.sup fun e ↦ e.toFinset.sup Int.natAbs

theorem endpoint_natAbs_le_longRangeEdgeSetRadius
    {E : Finset (Sym2 ℤ)} {e : Sym2 ℤ} (he : e ∈ E)
    {x : ℤ} (hx : x ∈ e) :
    x.natAbs ≤ longRangeEdgeSetRadius E := by
  unfold longRangeEdgeSetRadius
  exact (Finset.le_sup (s := e.toFinset) (f := Int.natAbs)
    (Sym2.mem_toFinset.mpr hx)).trans
      (Finset.le_sup (s := E) (f := fun e ↦ e.toFinset.sup Int.natAbs) he)

/-- If two translates of edges from the same finite support coincide, then their translation
offsets differ by at most twice the endpoint radius. -/
theorem natAbs_sub_le_two_mul_edgeSetRadius_of_translate_eq
    {E : Finset (Sym2 ℤ)} {e f : Sym2 ℤ} (he : e ∈ E) (hf : f ∈ E)
    {a b : ℤ}
    (hEq : longRangeEdgeTranslateEmbedding a e =
      longRangeEdgeTranslateEmbedding b f) :
    (a - b).natAbs ≤ 2 * longRangeEdgeSetRadius E := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    induction f using Sym2.inductionOn with
    | _ z w =>
      rw [longRangeEdgeTranslateEmbedding_mk,
        longRangeEdgeTranslateEmbedding_mk, Sym2.eq_iff] at hEq
      rcases hEq with hEq | hEq
      · have hab : a - b = z - x := by omega
        rw [hab]
        calc
          (z - x).natAbs ≤ z.natAbs + x.natAbs := Int.natAbs_sub_le z x
          _ ≤ longRangeEdgeSetRadius E + longRangeEdgeSetRadius E :=
            Nat.add_le_add
              (endpoint_natAbs_le_longRangeEdgeSetRadius hf (by simp))
              (endpoint_natAbs_le_longRangeEdgeSetRadius he (by simp))
          _ = 2 * longRangeEdgeSetRadius E := by omega
      · have hab : a - b = w - x := by omega
        rw [hab]
        calc
          (w - x).natAbs ≤ w.natAbs + x.natAbs := Int.natAbs_sub_le w x
          _ ≤ longRangeEdgeSetRadius E + longRangeEdgeSetRadius E :=
            Nat.add_le_add
              (endpoint_natAbs_le_longRangeEdgeSetRadius hf (by simp))
              (endpoint_natAbs_le_longRangeEdgeSetRadius he (by simp))
          _ = 2 * longRangeEdgeSetRadius E := by omega

theorem disjoint_longRangeTranslatedEdgeSets_of_far
    (E : Finset (Sym2 ℤ)) {a b : ℤ}
    (hab : 2 * longRangeEdgeSetRadius E < (a - b).natAbs) :
    Disjoint (E.map (longRangeEdgeTranslateEmbedding a))
      (E.map (longRangeEdgeTranslateEmbedding b)) := by
  rw [Finset.disjoint_left]
  intro g hga hgb
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hga
  obtain ⟨f, hf, hEq⟩ := Finset.mem_map.mp hgb
  exact (not_le_of_gt hab)
    (natAbs_sub_le_two_mul_edgeSetRadius_of_translate_eq he hf hEq.symm)

/-- The finite set of unordered pairs traversed by a walk in the complete graph on `ℤ`. -/
def longRangeWalkEdgeFinset {x y : ℤ} (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    Finset (Sym2 ℤ) :=
  w.edges.toFinset

@[simp]
theorem mem_longRangeWalkEdgeFinset_iff {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) (e : Sym2 ℤ) :
    e ∈ longRangeWalkEdgeFinset w ↔ e ∈ w.edges := by
  simp [longRangeWalkEdgeFinset]

/-- Every pair traversed by `w` is declared open. -/
def longRangeWalkIsOpen (ω : LongRangeConfiguration) {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) : Prop :=
  ∀ e ∈ w.edges, e ∈ ω

theorem longRangeWalkIsOpen_event_eq {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    {ω : LongRangeConfiguration | longRangeWalkIsOpen ω w} =
      {ω : LongRangeConfiguration | (longRangeWalkEdgeFinset w : Set (Sym2 ℤ)) ⊆ ω} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h e he
    exact h e ((mem_longRangeWalkEdgeFinset_iff w e).mp he)
  · intro h e he
    exact h ((mem_longRangeWalkEdgeFinset_iff w e).mpr he)

theorem measurableSet_longRangeWalkIsOpen {x y : ℤ}
    (w : (⊤ : SimpleGraph ℤ).Walk x y) :
    MeasurableSet {ω : LongRangeConfiguration | longRangeWalkIsOpen ω w} := by
  rw [longRangeWalkIsOpen_event_eq]
  exact measurableSet_superset_finset (longRangeWalkEdgeFinset w)

/-- The event that `x` and `y` are joined by a finite open long-range walk. -/
def longRangeConnectionEvent (x y : ℤ) : Set LongRangeConfiguration :=
  {ω | ∃ w : (⊤ : SimpleGraph ℤ).Walk x y, longRangeWalkIsOpen ω w}

theorem measurableSet_longRangeConnectionEvent (x y : ℤ) :
    MeasurableSet (longRangeConnectionEvent x y) := by
  letI : Countable ((⊤ : SimpleGraph ℤ).Walk x y) :=
    (show Function.Injective
        (fun w : (⊤ : SimpleGraph ℤ).Walk x y ↦ w.support) from
      fun _ _ h ↦ SimpleGraph.Walk.ext_support h).countable
  rw [show longRangeConnectionEvent x y =
      ⋃ w : (⊤ : SimpleGraph ℤ).Walk x y,
        {ω | longRangeWalkIsOpen ω w} by
    ext ω
    simp [longRangeConnectionEvent]]
  exact MeasurableSet.iUnion measurableSet_longRangeWalkIsOpen

theorem isIncreasingEvent_longRangeConnectionEvent (x y : ℤ) :
    IsIncreasingEvent (longRangeConnectionEvent x y) := by
  intro ω η hωη
  rintro ⟨w, hw⟩
  exact ⟨w, fun e he ↦ hωη (hw e he)⟩

theorem longRangeConnectionEvent_self (x : ℤ) :
    longRangeConnectionEvent x x = Set.univ := by
  ext ω
  simp only [longRangeConnectionEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨SimpleGraph.Walk.nil, by simp [longRangeWalkIsOpen]⟩

/-- The open simple graph encoded by a configuration. -/
def longRangeOpenGraph (ω : LongRangeConfiguration) : SimpleGraph ℤ :=
  SimpleGraph.fromEdgeSet ω

theorem longRangeOpenGraph_adj {ω : LongRangeConfiguration} {x y : ℤ} :
    (longRangeOpenGraph ω).Adj x y ↔ s(x, y) ∈ ω ∧ x ≠ y := by
  simp [longRangeOpenGraph, SimpleGraph.fromEdgeSet_adj]

/-- Identity-on-vertices inclusion of the open graph into the complete graph. -/
def longRangeOpenGraphHom (ω : LongRangeConfiguration) :
    longRangeOpenGraph ω →g (⊤ : SimpleGraph ℤ) where
  toFun := id
  map_rel' := fun {x y} h ↦ (SimpleGraph.top_adj x y).mpr (longRangeOpenGraph_adj.mp h).2

theorem longRangeWalkIsOpen_map_openGraphHom {ω : LongRangeConfiguration}
    {x y : ℤ} (w : (longRangeOpenGraph ω).Walk x y) :
    longRangeWalkIsOpen ω (w.map (longRangeOpenGraphHom ω)) := by
  induction w with
  | nil =>
      intro e he
      simp at he
  | @cons u v y huv w ih =>
      intro e he
      simp only [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.edges_cons,
        List.mem_cons] at he
      rcases he with rfl | he
      · exact (longRangeOpenGraph_adj.mp huv).1
      · exact ih e he

theorem nonempty_longRangeOpenGraph_walk_of_isOpen {ω : LongRangeConfiguration}
    {x y : ℤ} (w : (⊤ : SimpleGraph ℤ).Walk x y)
    (hopen : longRangeWalkIsOpen ω w) :
    Nonempty ((longRangeOpenGraph ω).Walk x y) := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v y huv w ih =>
      have hopenTail : longRangeWalkIsOpen ω w := by
        intro e he
        exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
      rcases ih hopenTail with ⟨q⟩
      have hopenHead : s(u, v) ∈ ω := by
        exact hopen s(u, v) (by simp [SimpleGraph.Walk.edges_cons])
      exact ⟨SimpleGraph.Walk.cons
        (longRangeOpenGraph_adj.mpr ⟨hopenHead, (SimpleGraph.top_adj u v).mp huv⟩) q⟩

theorem longRangeOpenGraph_reachable_iff {ω : LongRangeConfiguration} {x y : ℤ} :
    (longRangeOpenGraph ω).Reachable x y ↔ ω ∈ longRangeConnectionEvent x y := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.map (longRangeOpenGraphHom ω), longRangeWalkIsOpen_map_openGraphHom w⟩
  · rintro ⟨w, hopen⟩
    exact nonempty_longRangeOpenGraph_walk_of_isOpen w hopen

/-- The open cluster of `x`, represented without any finite-cardinality convention. -/
def longRangeCluster (ω : LongRangeConfiguration) (x : ℤ) : Set ℤ :=
  {y | (longRangeOpenGraph ω).Reachable x y}

@[simp]
theorem mem_longRangeCluster_iff {ω : LongRangeConfiguration} {x y : ℤ} :
    y ∈ longRangeCluster ω x ↔ ω ∈ longRangeConnectionEvent x y := by
  exact longRangeOpenGraph_reachable_iff

/-- Rooted percolation, encoded by connections to vertices of arbitrarily large absolute value.
The following theorem identifies it with infinitude of the root cluster. -/
def longRangePercolationEvent (x : ℤ) : Set LongRangeConfiguration :=
  {ω | ∀ n : ℕ, ∃ y : ℤ, n ≤ y.natAbs ∧ ω ∈ longRangeConnectionEvent x y}

theorem measurableSet_longRangePercolationEvent (x : ℤ) :
    MeasurableSet (longRangePercolationEvent x) := by
  rw [show longRangePercolationEvent x =
      ⋂ n : ℕ, ⋃ y : ℤ,
        if n ≤ y.natAbs then longRangeConnectionEvent x y else ∅ by
    ext ω
    simp [longRangePercolationEvent]]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun y ↦ by
    split_ifs
    · exact measurableSet_longRangeConnectionEvent x y
    · exact MeasurableSet.empty

theorem isIncreasingEvent_longRangePercolationEvent (x : ℤ) :
    IsIncreasingEvent (longRangePercolationEvent x) := by
  intro ω η hωη hω n
  obtain ⟨y, hny, hxy⟩ := hω n
  exact ⟨y, hny, isIncreasingEvent_longRangeConnectionEvent x y hωη hxy⟩

theorem mem_longRangePercolationEvent_iff_cluster_infinite
    {ω : LongRangeConfiguration} {x : ℤ} :
    ω ∈ longRangePercolationEvent x ↔ (longRangeCluster ω x).Infinite := by
  constructor
  · intro h hfinite
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ y ∈ longRangeCluster ω x, y.natAbs < n := by
      classical
      let s := hfinite.toFinset
      refine ⟨(s.sup Int.natAbs) + 1, ?_⟩
      intro y hy
      have hys : y ∈ s := by simpa [s] using hy
      exact lt_of_le_of_lt (Finset.le_sup (f := Int.natAbs) hys) (Nat.lt_succ_self _)
    obtain ⟨y, hny, hxy⟩ := h n
    exact (not_le_of_gt (hn y (mem_longRangeCluster_iff.mpr hxy))) hny
  · intro hinf n
    by_contra h
    push Not at h
    have hsub : longRangeCluster ω x ⊆ {y : ℤ | y.natAbs < n} := by
      intro y hy
      by_contra hlt
      exact h y (Nat.le_of_not_gt hlt) (mem_longRangeCluster_iff.mp hy)
    have hfinite : ({y : ℤ | y.natAbs < n} : Set ℤ).Finite := by
      apply (Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset
      intro y hy
      have hycast : (y.natAbs : ℤ) < n := by exact_mod_cast hy
      constructor
      · calc
          -(n : ℤ) ≤ -(y.natAbs : ℤ) := neg_le_neg hycast.le
          _ = -|y| := by rw [Int.natCast_natAbs]
          _ ≤ y := neg_abs_le y
      · calc
          y ≤ |y| := le_abs_self y
          _ = (y.natAbs : ℤ) := Int.natCast_natAbs y |>.symm
          _ ≤ n := hycast.le
    exact hinf (hfinite.subset hsub)

/-- The event that every open connected component is finite. -/
def longRangeAllComponentsFiniteEvent : Set LongRangeConfiguration :=
  {ω | ∀ x : ℤ, (longRangeCluster ω x).Finite}

theorem measurableSet_longRangeAllComponentsFiniteEvent :
    MeasurableSet longRangeAllComponentsFiniteEvent := by
  rw [show longRangeAllComponentsFiniteEvent =
      ⋂ x : ℤ, (longRangePercolationEvent x)ᶜ by
    ext ω
    simp only [longRangeAllComponentsFiniteEvent, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_compl_iff]
    constructor
    · intro h x hx
      exact (mem_longRangePercolationEvent_iff_cluster_infinite.mp hx) (h x)
    · intro h x
      exact Set.not_infinite.mp fun hx ↦
        h x (mem_longRangePercolationEvent_iff_cluster_infinite.mpr hx)]
  exact MeasurableSet.iInter fun x ↦ (measurableSet_longRangePercolationEvent x).compl

/-- The event that the random graph is connected. -/
def longRangeConnectedEvent : Set LongRangeConfiguration :=
  {ω | (longRangeOpenGraph ω).Connected}

theorem mem_longRangeConnectedEvent_iff {ω : LongRangeConfiguration} :
    ω ∈ longRangeConnectedEvent ↔
      ∀ x y : ℤ, ω ∈ longRangeConnectionEvent x y := by
  rw [longRangeConnectedEvent, Set.mem_setOf_eq, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hpre, _⟩ x y
    exact longRangeOpenGraph_reachable_iff.mp (hpre x y)
  · intro h
    exact ⟨fun x y ↦ longRangeOpenGraph_reachable_iff.mpr (h x y), ⟨0⟩⟩

theorem measurableSet_longRangeConnectedEvent :
    MeasurableSet longRangeConnectedEvent := by
  rw [show longRangeConnectedEvent =
      ⋂ x : ℤ, ⋂ y : ℤ, longRangeConnectionEvent x y by
    ext ω
    simp [mem_longRangeConnectedEvent_iff]]
  exact MeasurableSet.iInter fun x ↦ MeasurableSet.iInter fun y ↦
    measurableSet_longRangeConnectionEvent x y

/-- Root percolation probability for a long-range profile. -/
noncomputable def longRangeTheta (p : LongRangeProfile) : ℝ :=
  (longRangeMeasure p).real (longRangePercolationEvent 0)

/-- Long-range percolation probability is monotone under coordinatewise enlargement of the
distance profile. -/
theorem longRangeTheta_mono {p q : LongRangeProfile} (hpq : ∀ n, p n ≤ q n) :
    longRangeTheta p ≤ longRangeTheta q := by
  exact IsIncreasingEvent.inhomogeneousSetBernoulli_real_mono
    (isIncreasingEvent_longRangePercolationEvent 0)
    (measurableSet_longRangePercolationEvent 0)
    (fun e ↦ hpq (longRangeEdgeDistance e))

/-- Connectivity probability for a long-range profile. -/
noncomputable def longRangeConnectedProbability (p : LongRangeProfile) : ℝ :=
  (longRangeMeasure p).real longRangeConnectedEvent

end Percolation
