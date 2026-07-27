import Percolation.Bernoulli.BK
import Percolation.Critical.VertexIndependence

/-!
# Disjoint open connections (Grimmett (2.17))

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.3, equation (2.17), p. 38
(source id `grimmett-percolation-1999`).

The BK inequality applies to increasing events depending on finitely many edges; Grimmett
drops this restriction for the canonical application by exhausting the lattice with boxes
`B(n)` and passing to the limit. Here the same limit is taken along the directed family of
all finite edge sets:

* `Percolation.connectionEventIn` — connection by an open walk using only edges of a finite
  set `E` (increasing, supported on `E`);
* `Percolation.ExistsPairwiseDisjointOpenWalks` — the event that prescribed pairs of
  vertices are joined by pairwise edge-disjoint open walks;
* `Percolation.bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalks_le_prod` —
  **Grimmett (2.17)**: the probability of pairwise edge-disjoint open connections is at
  most the product of the individual connection probabilities.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

/-! ### Monotonicity of the iterated disjoint occurrence in the events -/

theorem finiteDisjointOccurrence_mono {ι κ : Type*} {J : Finset κ}
    {A B : κ → Set (Set ι)} (h : ∀ i ∈ J, A i ⊆ B i) :
    FiniteDisjointOccurrence J A ⊆ FiniteDisjointOccurrence J B := by
  rintro ω ⟨H, hdisj, hH⟩
  exact ⟨H, hdisj, fun i hi => ⟨(hH i hi).1, h i hi (hH i hi).2⟩⟩

/-! ### Truncated connection events -/

/-- Connection by an open walk whose edges all lie in the finite set `E` — Grimmett's
"open path inside the box". -/
def connectionEventIn (d : ℕ) (E : Finset (CubicEdge d)) (x y : Cubic d) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ w : (cubicGraph d).Walk x y, walkIsOpen ω w ∧ walkEdgeFinset w ⊆ E}

theorem connectionEventIn_subset (d : ℕ) (E : Finset (CubicEdge d)) (x y : Cubic d) :
    connectionEventIn d E x y ⊆ connectionEvent d x y := by
  rintro ω ⟨w, hw, -⟩
  exact ⟨w, hw⟩

theorem connectionEventIn_mono {d : ℕ} {E F : Finset (CubicEdge d)} (hEF : E ⊆ F)
    (x y : Cubic d) : connectionEventIn d E x y ⊆ connectionEventIn d F x y := by
  rintro ω ⟨w, hw, hsub⟩
  exact ⟨w, hw, hsub.trans hEF⟩

theorem isIncreasingEvent_connectionEventIn (d : ℕ) (E : Finset (CubicEdge d))
    (x y : Cubic d) : IsIncreasingEvent (connectionEventIn d E x y) := by
  rintro ω η hωη ⟨w, hw, hsub⟩
  exact ⟨w, fun e he => hωη (hw e he), hsub⟩

theorem dependsOn_connectionEventIn (d : ℕ) (E : Finset (CubicEdge d)) (x y : Cubic d) :
    DependsOn E (connectionEventIn d E x y) := by
  have key : ∀ ω η : EdgeConfiguration d, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) →
      ω ∈ connectionEventIn d E x y → η ∈ connectionEventIn d E x y := by
    rintro ω η hagree ⟨w, hw, hsub⟩
    refine ⟨w, fun e he => ?_, hsub⟩
    have hmem : (⟨e, w.edges_subset_edgeSet he⟩ : CubicEdge d) ∈ E :=
      hsub ((mem_walkEdgeFinset_iff w _).mpr he)
    exact (hagree _ hmem).mp (hw e he)
  intro ω η hagree
  exact ⟨key ω η hagree, key η ω fun e he => (hagree e he).symm⟩

/-! ### Pairwise edge-disjoint open connections -/

/-- The event that the vertex pairs `(u i, v i)`, `i ∈ J`, are joined by pairwise
edge-disjoint open walks — the left side of Grimmett (2.17). -/
def ExistsPairwiseDisjointOpenWalks (d : ℕ) {κ : Type*} (J : Finset κ)
    (u v : κ → Cubic d) : Set (EdgeConfiguration d) :=
  {ω | ∃ w : ∀ i : κ, (cubicGraph d).Walk (u i) (v i),
    (∀ i ∈ J, walkIsOpen ω (w i)) ∧
    (↑J : Set κ).Pairwise fun i j =>
      Disjoint (walkEdgeFinset (w i)) (walkEdgeFinset (w j))}

/-- Pairwise edge-disjoint open connections are an instance of the iterated disjoint
occurrence of the connection events: the walks' edge sets are the witnesses. -/
theorem existsPairwiseDisjointOpenWalks_subset (d : ℕ) {κ : Type*} (J : Finset κ)
    (u v : κ → Cubic d) :
    ExistsPairwiseDisjointOpenWalks d J u v ⊆
      FiniteDisjointOccurrence J (fun i => connectionEvent d (u i) (v i)) := by
  rintro ω ⟨w, hopen, hdisj⟩
  refine ⟨fun i => walkEdgeFinset (w i), hdisj, fun i hi => ⟨?_, ?_⟩⟩
  · intro e he
    rw [Finset.mem_coe, mem_walkEdgeFinset_iff] at he
    have := hopen i hi _ he
    rwa [show (⟨(e : Sym2 (Cubic d)), (w i).edges_subset_edgeSet he⟩ : CubicEdge d) = e from
      Subtype.ext rfl] at this
  · refine ⟨w i, fun e he => ?_⟩
    show (⟨e, (w i).edges_subset_edgeSet he⟩ : CubicEdge d) ∈
      (↑(walkEdgeFinset (w i)) : Set (CubicEdge d))
    rw [Finset.mem_coe, mem_walkEdgeFinset_iff]
    exact he

/-- The iterated disjoint occurrence of the full connection events is exhausted by the
truncated ones: witnesses are finite, hence lie in some finite edge set. -/
theorem iUnion_finiteDisjointOccurrence_connectionEventIn (d : ℕ) {κ : Type*}
    (J : Finset κ) (u v : κ → Cubic d) :
    (⋃ E : Finset (CubicEdge d),
        FiniteDisjointOccurrence J (fun i => connectionEventIn d E (u i) (v i))) =
      FiniteDisjointOccurrence J (fun i => connectionEvent d (u i) (v i)) := by
  classical
  ext ω
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨E, hE⟩
    exact finiteDisjointOccurrence_mono
      (fun i _ => connectionEventIn_subset d E (u i) (v i)) hE
  · rintro ⟨H, hdisj, hH⟩
    refine ⟨J.biUnion H, H, hdisj, fun i hi => ⟨(hH i hi).1, ?_⟩⟩
    obtain ⟨wi, hwi⟩ := (hH i hi).2
    refine ⟨wi, hwi, fun e he => ?_⟩
    rw [mem_walkEdgeFinset_iff] at he
    have hmem := hwi _ he
    rw [show (⟨(e : Sym2 (Cubic d)), wi.edges_subset_edgeSet he⟩ : CubicEdge d) = e from
      Subtype.ext rfl] at hmem
    exact Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩

/-- **Grimmett (2.17)**: the probability that prescribed vertex pairs are joined by
pairwise edge-disjoint open walks is at most the product of the connection
probabilities. -/
theorem bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalks_le_prod (d : ℕ)
    {κ : Type*} (p : I) (J : Finset κ) (u v : κ → Cubic d) :
    (bernoulliBondMeasure d p).real (ExistsPairwiseDisjointOpenWalks d J u v) ≤
      ∏ i ∈ J, (bernoulliBondMeasure d p).real (connectionEvent d (u i) (v i)) := by
  classical
  set μ := bernoulliBondMeasure d p with hμ
  set C : ℝ := ∏ i ∈ J, μ.real (connectionEvent d (u i) (v i)) with hC
  have hC0 : (0 : ℝ) ≤ C := Finset.prod_nonneg fun i _ => measureReal_nonneg
  have hbound : ∀ E : Finset (CubicEdge d),
      μ.real (FiniteDisjointOccurrence J
        (fun i => connectionEventIn d E (u i) (v i))) ≤ C := by
    intro E
    refine (bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod p
      (fun i _ => isIncreasingEvent_connectionEventIn d E (u i) (v i))
      (E := fun _ => E)
      (fun i _ => dependsOn_connectionEventIn d E (u i) (v i))).trans ?_
    refine Finset.prod_le_prod (fun i _ => measureReal_nonneg) fun i _ =>
      measureReal_mono (connectionEventIn_subset d E (u i) (v i))
  have hmono : Monotone fun E : Finset (CubicEdge d) =>
      FiniteDisjointOccurrence J (fun i => connectionEventIn d E (u i) (v i)) :=
    fun E F hEF => finiteDisjointOccurrence_mono
      fun i _ => connectionEventIn_mono hEF (u i) (v i)
  have hsup : μ (FiniteDisjointOccurrence J
      (fun i => connectionEvent d (u i) (v i))) =
      ⨆ E : Finset (CubicEdge d), μ (FiniteDisjointOccurrence J
        (fun i => connectionEventIn d E (u i) (v i))) := by
    rw [← iUnion_finiteDisjointOccurrence_connectionEventIn d J u v]
    exact hmono.directed_le.measure_iUnion
  have hchain : μ (ExistsPairwiseDisjointOpenWalks d J u v) ≤ ENNReal.ofReal C := by
    refine (measure_mono (existsPairwiseDisjointOpenWalks_subset d J u v)).trans ?_
    rw [hsup]
    refine iSup_le fun E => ?_
    have h := hbound E
    rw [measureReal_def] at h
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC0).mpr h
  have hfinal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
  rw [ENNReal.toReal_ofReal hC0] at hfinal
  exact hfinal

end Percolation
