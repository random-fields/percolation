import Percolation.Critical.ResidualTerminal
import Percolation.Bernoulli.BK

/-!
# Conditional domination of pivotal-sausage gaps

This file turns the residual deterministic inclusion into Grimmett's
conditional stochastic-domination estimate (Lemma 5.12).  The conditioning
is implemented by a finite partition into pivotal-exploration cylinders.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

/-- The pivotal dart at the end of a nonempty prescribed sausage prefix. -/
noncomputable def prefixMarkedPivotalDart
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (cubicGraph d).Dart :=
  (radiusPivotalDarts hprefix.1)[rs.length - 1]'(by
    have hle := sausageGapPrefix_length_le_pivotalDarts_length hprefix hbudget
    omega)

theorem prefixMarkedPivotalDart_mem
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    prefixMarkedPivotalDart hprefix hbudget hpos ∈ radiusPivotalDarts hprefix.1 := by
  exact List.getElem_mem _

theorem prefixMarkedPivotalDart_idxOf_add_one
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (radiusPivotalDarts hprefix.1).idxOf
        (prefixMarkedPivotalDart hprefix hbudget hpos) + 1 = rs.length := by
  have hi : rs.length - 1 < (radiusPivotalDarts hprefix.1).length := by
    have hle := sausageGapPrefix_length_le_pivotalDarts_length hprefix hbudget
    omega
  rw [prefixMarkedPivotalDart,
    (radiusPivotalDarts_nodup hprefix.1).idxOf_getElem]
  omega

/-- The finite cylinder key attached to the last pivotal edge of a nonempty
prefix: explored support together with its open trace. -/
noncomputable def pivotalExplorationKey
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    Finset (CubicEdge d) × Finset (CubicEdge d) := by
  let a := prefixMarkedPivotalDart hprefix hbudget hpos
  let F := radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω
  exact (F, restrictTo F ω)

theorem pivotalExplorationKey_snd_subset_fst
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (pivotalExplorationKey hprefix hbudget hpos).2 ⊆
      (pivotalExplorationKey hprefix hbudget hpos).1 := by
  simp [pivotalExplorationKey, restrictTo_subset]

/-- A configuration in the same pivotal-exploration cylinder has the same
marked dart, deleted cluster, explored support, and trace. -/
theorem pivotalExplorationKey_eq_of_agree
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d} {rs : List ℕ}
    (hω : ω ∈ sausageGapPrefixEvent d x n rs)
    (hη : η ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n
      (cubicEdgeOfDart (prefixMarkedPivotalDart hω hbudget hpos)) ω,
      (f ∈ ω ↔ f ∈ η)) :
    pivotalExplorationKey hη hbudget hpos =
      pivotalExplorationKey hω hbudget hpos := by
  classical
  let a := prefixMarkedPivotalDart hω hbudget hpos
  have haω : a ∈ radiusPivotalDarts hω.1 := by
    simpa [a] using prefixMarkedPivotalDart_mem hω hbudget hpos
  have haη : a ∈ radiusPivotalDarts hη.1 :=
    pivotalDart_mem_of_agree_pivotalExploration hω.1 haω hη.1 (by
      simpa [a] using hagree)
  have htake := radiusPivotalDarts_take_through_eq_of_agree_pivotalExploration
    hω.1 haω hη.1 (by simpa [a] using hagree)
  have hidx : (radiusPivotalDarts hω.1).idxOf a =
      (radiusPivotalDarts hη.1).idxOf a := by
    have hlen := congrArg List.length htake
    rw [List.length_take, List.length_take,
      Nat.min_eq_left (by
        have := List.idxOf_lt_length_iff.mpr haω
        omega),
      Nat.min_eq_left (by
        have := List.idxOf_lt_length_iff.mpr haη
        omega)] at hlen
    omega
  have haωidx := prefixMarkedPivotalDart_idxOf_add_one hω hbudget hpos
  have haηidx : (radiusPivotalDarts hη.1).idxOf a + 1 = rs.length := by
    rw [← hidx]
    simpa [a] using haωidx
  have hmarked : prefixMarkedPivotalDart hη hbudget hpos = a := by
    unfold prefixMarkedPivotalDart
    have hindex : rs.length - 1 = (radiusPivotalDarts hη.1).idxOf a := by omega
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by
      have := List.idxOf_lt_length_iff.mpr haη
      omega), hindex, List.getElem?_idxOf haη]
  have hD : radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω =
      radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) η :=
    radiusDeletedReachableVertices_eq_of_agree_incident (by simpa [a] using hagree)
  have hF : radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω =
      radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) η := by
    unfold radiusDeletedIncidentEdges
    rw [hD]
  have htrace : restrictTo
      (radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω) ω =
      restrictTo
        (radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) η) η := by
    rw [← hF]
    apply Finset.ext
    intro f
    rw [mem_restrictTo, mem_restrictTo]
    by_cases hf : f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω
    · simp only [hf, true_and]
      exact hagree f (by simpa [a] using hf)
    · simp [hf]
  simp only [pivotalExplorationKey]
  rw [hmarked]
  exact Prod.ext hF.symm htrace.symm

theorem radiusPivotalDarts_idxOf_eq_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    (radiusPivotalDarts hω).idxOf a = (radiusPivotalDarts hη).idxOf a := by
  have haη := pivotalDart_mem_of_agree_pivotalExploration hω ha hη hagree
  have htake := radiusPivotalDarts_take_through_eq_of_agree_pivotalExploration
    hω ha hη hagree
  have hlen := congrArg List.length htake
  rw [List.length_take, List.length_take,
    Nat.min_eq_left (by
      have := List.idxOf_lt_length_iff.mpr ha
      omega),
    Nat.min_eq_left (by
      have := List.idxOf_lt_length_iff.mpr haη
      omega)] at hlen
  omega

theorem pivotalExplorationKey_fst_subset_ballEdges
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (pivotalExplorationKey hprefix hbudget hpos).1 ⊆
      cubicMetricBallEdges d x n := by
  intro f hf
  rw [pivotalExplorationKey] at hf
  exact (mem_radiusDeletedIncidentEdges_iff.mp hf).1

/-- Traces on the finite radius support which realize the prescribed prefix. -/
noncomputable def sausageGapPrefixTraces
    (d : ℕ) (x : Cubic d) (n : ℕ) (rs : List ℕ) :
    Finset (Finset (CubicEdge d)) := by
  classical
  exact (cubicMetricBallEdges d x n).powerset.filter fun s ↦
    (s : Set (CubicEdge d)) ∈ sausageGapPrefixEvent d x n rs

@[simp]
theorem mem_sausageGapPrefixTraces
    {d n : ℕ} {x : Cubic d} {rs : List ℕ} {s : Finset (CubicEdge d)} :
    s ∈ sausageGapPrefixTraces d x n rs ↔
      s ⊆ cubicMetricBallEdges d x n ∧
        (s : Set (CubicEdge d)) ∈ sausageGapPrefixEvent d x n rs := by
  classical
  simp [sausageGapPrefixTraces]

noncomputable def pivotalExplorationKeyOfTrace
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    (s : {t : Finset (CubicEdge d) //
      t ∈ sausageGapPrefixTraces d x n rs}) :
    Finset (CubicEdge d) × Finset (CubicEdge d) :=
  pivotalExplorationKey (mem_sausageGapPrefixTraces.mp s.2).2 hbudget hpos

/-- The finite set of distinct pivotal-exploration cylinders which meet the
prefix event. -/
noncomputable def pivotalExplorationKeys
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    Finset (Finset (CubicEdge d) × Finset (CubicEdge d)) := by
  classical
  exact (sausageGapPrefixTraces d x n rs).attach.image
    (pivotalExplorationKeyOfTrace hbudget hpos)

/-- The radius event restricted to one pivotal-exploration cylinder. -/
def pivotalExplorationCell {d n : ℕ} {x : Cubic d}
    (k : Finset (CubicEdge d) × Finset (CubicEdge d)) :
    Set (EdgeConfiguration d) :=
  radiusConnectionEvent d x n ∩ finiteCylinder k.1 k.2

/-- Every valid exploration cell consists of configurations with the
prescribed sausage prefix. -/
theorem pivotalExplorationCell_subset_prefix
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    {k : Finset (CubicEdge d) × Finset (CubicEdge d)}
    (hk : k ∈ pivotalExplorationKeys (x := x) hbudget hpos) :
    pivotalExplorationCell (d := d) (n := n) (x := x) k ⊆
      sausageGapPrefixEvent d x n rs := by
  classical
  rw [pivotalExplorationKeys, Finset.mem_image] at hk
  obtain ⟨s, _hsAttach, hsk⟩ := hk
  rw [← hsk]
  let hs := (mem_sausageGapPrefixTraces.mp s.2).2
  let a := prefixMarkedPivotalDart hs hbudget hpos
  rintro η ⟨hηA, hηC⟩
  apply mem_sausageGapPrefixEvent_of_agree_pivotalExploration hs
    (prefixMarkedPivotalDart_mem hs hbudget hpos)
    (prefixMarkedPivotalDart_idxOf_add_one hs hbudget hpos) hηA
  intro f hf
  have hC := hηC f (by
    simpa [pivotalExplorationKeyOfTrace, pivotalExplorationKey, a] using hf)
  simpa [pivotalExplorationKeyOfTrace, pivotalExplorationKey, a,
    mem_restrictTo, hf] using hC.symm

theorem pivotalExplorationKey_snd_subset_fst_of_mem
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    {k : Finset (CubicEdge d) × Finset (CubicEdge d)}
    (hk : k ∈ pivotalExplorationKeys (x := x) hbudget hpos) :
    k.2 ⊆ k.1 := by
  classical
  rw [pivotalExplorationKeys, Finset.mem_image] at hk
  obtain ⟨s, _hs, hsk⟩ := hk
  rw [← hsk]
  exact pivotalExplorationKey_snd_subset_fst _ _ _

/-- Inside a valid cell, the cell key is the actual exploration key of every
configuration in that cell. -/
theorem pivotalExplorationKey_eq_of_mem_cell
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    {k : Finset (CubicEdge d) × Finset (CubicEdge d)}
    (hk : k ∈ pivotalExplorationKeys (x := x) hbudget hpos)
    {η : EdgeConfiguration d}
    (hηcell : η ∈ pivotalExplorationCell (d := d) (n := n) (x := x) k) :
    pivotalExplorationKey
        (pivotalExplorationCell_subset_prefix hbudget hpos hk hηcell)
        hbudget hpos = k := by
  classical
  rw [pivotalExplorationKeys, Finset.mem_image] at hk
  obtain ⟨s, _hsAttach, hsk⟩ := hk
  let hs := (mem_sausageGapPrefixTraces.mp s.2).2
  have hk' : pivotalExplorationKeyOfTrace hbudget hpos s ∈
      pivotalExplorationKeys (x := x) hbudget hpos := by
    rw [pivotalExplorationKeys, Finset.mem_image]
    exact ⟨s, by simp, rfl⟩
  have hηcell' : η ∈ pivotalExplorationCell (d := d) (n := n) (x := x)
      (pivotalExplorationKeyOfTrace hbudget hpos s) := by
    rw [hsk]
    exact hηcell
  let hηprefix' := pivotalExplorationCell_subset_prefix hbudget hpos hk' hηcell'
  have hkey' : pivotalExplorationKey hηprefix' hbudget hpos =
      pivotalExplorationKeyOfTrace hbudget hpos s := by
    apply pivotalExplorationKey_eq_of_agree hs hηprefix' hbudget hpos
    intro f hf
    have hC := hηcell'.2 f (by
      simpa [pivotalExplorationKeyOfTrace, pivotalExplorationKey] using hf)
    simpa [pivotalExplorationKeyOfTrace, pivotalExplorationKey,
      mem_restrictTo, hf] using hC.symm
  calc
    pivotalExplorationKey
        (pivotalExplorationCell_subset_prefix hbudget hpos hk hηcell)
        hbudget hpos = pivotalExplorationKey hηprefix' hbudget hpos := by congr
    _ = pivotalExplorationKeyOfTrace hbudget hpos s := hkey'
    _ = k := hsk

/-- The prescribed prefix is the finite disjoint union of its pivotal
exploration cells. -/
theorem sausageGapPrefixEvent_eq_iUnion_pivotalExplorationCells
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    sausageGapPrefixEvent d x n rs =
      ⋃ k ∈ pivotalExplorationKeys (x := x) hbudget hpos,
        pivotalExplorationCell (d := d) (n := n) (x := x) k := by
  classical
  ext η
  constructor
  · intro hη
    let E := cubicMetricBallEdges d x n
    let s := restrictTo E η
    have hsE : s ⊆ E := restrictTo_subset E η
    have hagree : ∀ e ∈ E, (e ∈ η ↔ e ∈ (s : Set (CubicEdge d))) := by
      intro e he
      simp [s, mem_restrictTo, he]
    have hsPrefix : (s : Set (CubicEdge d)) ∈ sausageGapPrefixEvent d x n rs :=
      (dependsOn_sausageGapPrefixEvent d x n rs hagree).mp hη
    have hsTr : s ∈ sausageGapPrefixTraces d x n rs :=
      mem_sausageGapPrefixTraces.mpr ⟨hsE, hsPrefix⟩
    let st : {t : Finset (CubicEdge d) //
        t ∈ sausageGapPrefixTraces d x n rs} := ⟨s, hsTr⟩
    let k := pivotalExplorationKeyOfTrace hbudget hpos st
    rw [Set.mem_iUnion₂]
    refine ⟨k, ?_, hη.1, ?_⟩
    · rw [pivotalExplorationKeys, Finset.mem_image]
      exact ⟨st, by simp, rfl⟩
    · intro e heF
      have heE : e ∈ E := by
        exact pivotalExplorationKey_fst_subset_ballEdges hsPrefix hbudget hpos heF
      have htrace : k.2 = restrictTo k.1 (s : Set (CubicEdge d)) := by
        simp [k, st, pivotalExplorationKeyOfTrace, pivotalExplorationKey]
      rw [htrace, mem_restrictTo]
      simp [heF, s, mem_restrictTo, heE]
  · rw [Set.mem_iUnion₂]
    rintro ⟨k, hk, hηcell⟩
    exact pivotalExplorationCell_subset_prefix hbudget hpos hk hηcell

theorem pairwiseDisjoint_pivotalExplorationCells
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    Set.PairwiseDisjoint
      (↑(pivotalExplorationKeys (x := x) hbudget hpos) :
        Set (Finset (CubicEdge d) × Finset (CubicEdge d)))
      (pivotalExplorationCell (d := d) (n := n) (x := x)) := by
  intro k hk l hl hkl
  change Disjoint
    (pivotalExplorationCell (d := d) (n := n) (x := x) k)
    (pivotalExplorationCell (d := d) (n := n) (x := x) l)
  rw [Set.disjoint_left]
  intro η hηk hηl
  have hkEq := pivotalExplorationKey_eq_of_mem_cell hbudget hpos hk hηk
  have hlEq := pivotalExplorationKey_eq_of_mem_cell hbudget hpos hl hηl
  apply hkl
  calc
    k = pivotalExplorationKey
        (pivotalExplorationCell_subset_prefix hbudget hpos hk hηk)
        hbudget hpos := hkEq.symm
    _ = pivotalExplorationKey
        (pivotalExplorationCell_subset_prefix hbudget hpos hl hηl)
        hbudget hpos := by congr
    _ = l := hlEq

theorem measurableSet_pivotalExplorationCell_of_mem
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length)
    {k : Finset (CubicEdge d) × Finset (CubicEdge d)}
    (hk : k ∈ pivotalExplorationKeys (x := x) hbudget hpos) :
    MeasurableSet (pivotalExplorationCell (d := d) (n := n) (x := x) k) :=
  (measurableSet_radiusConnectionEvent d x n).inter
    (measurableSet_finiteCylinder
      (pivotalExplorationKey_snd_subset_fst_of_mem hbudget hpos hk))

theorem bernoulliBondMeasure_real_sausageGapPrefixEvent_eq_sum_cells
    {d n : ℕ} {x : Cubic d} {rs : List ℕ}
    (p : I) (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (bernoulliBondMeasure d p).real (sausageGapPrefixEvent d x n rs) =
      ∑ k ∈ pivotalExplorationKeys (x := x) hbudget hpos,
        (bernoulliBondMeasure d p).real
          (pivotalExplorationCell (d := d) (n := n) (x := x) k) := by
  rw [sausageGapPrefixEvent_eq_iUnion_pivotalExplorationCells hbudget hpos]
  exact measureReal_biUnion_finset
    (pairwiseDisjoint_pivotalExplorationCells hbudget hpos)
    (fun _ hk ↦ measurableSet_pivotalExplorationCell_of_mem hbudget hpos hk)

/-- The long-next-gap estimate on one exploration cylinder.  This is the
precise finite-conditioning step in Grimmett's proof of Lemma 5.12. -/
theorem bernoulliBondMeasure_real_long_inter_pivotalExplorationCell_le
    {d n r : ℕ} {x : Cubic d} {rs : List ℕ}
    (p : I) (hpos : 0 < rs.length)
    (hprefixBudget : rs.sum + rs.length ≤ n)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n)
    {k : Finset (CubicEdge d) × Finset (CubicEdge d)}
    (hk : k ∈ pivotalExplorationKeys (x := x) hprefixBudget hpos) :
    (bernoulliBondMeasure d p).real
        (sausageGapPrefixNextLongEvent d x n rs r ∩
          pivotalExplorationCell (d := d) (n := n) (x := x) k) ≤
      radiusTail d p (r + 1) *
        (bernoulliBondMeasure d p).real
          (pivotalExplorationCell (d := d) (n := n) (x := x) k) := by
  classical
  rw [pivotalExplorationKeys, Finset.mem_image] at hk
  obtain ⟨s, _hsAttach, hsk⟩ := hk
  rw [← hsk]
  let hs := (mem_sausageGapPrefixTraces.mp s.2).2
  let a := prefixMarkedPivotalDart hs hprefixBudget hpos
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) (s : Set (CubicEdge d))
  let F := radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) (s : Set (CubicEdge d))
  let t := restrictTo F (s : Set (CubicEdge d))
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let L := residualLocalRadiusEvent d x n D a.toProd.2 (r + 1)
  let R := radiusConnectionEventOffExploration d x n D a.toProd.2
    (cubicMetricSphere d x n)
  have hkey : pivotalExplorationKeyOfTrace hprefixBudget hpos s = (F, t) := by
    rfl
  rw [hkey]
  have hsubset :
      sausageGapPrefixNextLongEvent d x n rs r ∩
          pivotalExplorationCell (d := d) (n := n) (x := x) (F, t) ⊆
        OpenWitnessDisjointOccurrence L R ∩ finiteCylinder F t := by
    rintro η ⟨⟨hηprefix, hηlong⟩, hηA, hηC⟩
    have haS : a ∈ radiusPivotalDarts hs.1 := by
      simpa [a] using prefixMarkedPivotalDart_mem hs hprefixBudget hpos
    have hagree : ∀ f ∈ F, (f ∈ (s : Set (CubicEdge d)) ↔ f ∈ η) := by
      intro f hf
      have hC := hηC f hf
      simpa [t, mem_restrictTo, hf] using hC.symm
    have haη : a ∈ radiusPivotalDarts hηprefix.1 :=
      pivotalDart_mem_of_agree_pivotalExploration hs.1 haS hηprefix.1 (by
        simpa [F, a] using hagree)
    have hidx := radiusPivotalDarts_idxOf_eq_of_agree_pivotalExploration
      hs.1 haS hηprefix.1 (by simpa [F, a] using hagree)
    have hmarkS := prefixMarkedPivotalDart_idxOf_add_one hs hprefixBudget hpos
    have hmarkη : (radiusPivotalDarts hηprefix.1).idxOf a + 1 = rs.length := by
      rw [← hidx]
      simpa [a] using hmarkS
    have hD : radiusDeletedReachableVertices d x n (cubicEdgeOfDart a)
        (s : Set (CubicEdge d)) =
        radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) η :=
      radiusDeletedReachableVertices_eq_of_agree_incident (by
        simpa [F, a] using hagree)
    have hdet := sausageGapPrefixNextLong_mem_residual_disjointOccurrence
      hηprefix haη hmarkη hbudget hηlong
    refine ⟨?_, hηC⟩
    simpa [L, R, D, hD] using hdet
  have htF : t ⊆ F := restrictTo_subset F (s : Set (CubicEdge d))
  have hdisj : Disjoint E F := by
    simpa [E, F, D, radiusDeletedIncidentEdges] using
      (Finset.sdiff_disjoint : Disjoint
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D)
        (radiusIncidentEdgesOf d x n D))
  have hLdep : DependsOn E L := by
    simpa [E, L] using dependsOn_residualLocalRadiusEvent d x n D a.toProd.2 (r + 1)
  have hRdep : DependsOn E R := by
    simpa [E, R] using dependsOn_radiusConnectionEventOffExploration d x n D
      a.toProd.2 (cubicMetricSphere d x n)
  have hLRdep : DependsOn E (OpenWitnessDisjointOccurrence L R) :=
    hLdep.openWitnessDisjointOccurrence hRdep
  have hfactor :
      (bernoulliBondMeasure d p).real
          (OpenWitnessDisjointOccurrence L R ∩ finiteCylinder F t) =
        (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence L R) *
          finiteBernoulliWeight F (p : ℝ) t := by
    simpa [bernoulliBondMeasure] using
      setBernoulli_real_inter_finiteCylinder_of_disjoint p htF hLRdep hdisj
  have hBK :
      (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence L R) ≤
        (bernoulliBondMeasure d p).real L *
          (bernoulliBondMeasure d p).real R := by
    apply bernoulliBondMeasure_real_disjointOccurrence_le_mul p
    · simpa [L] using isIncreasingEvent_residualLocalRadiusEvent d x n D
        a.toProd.2 (r + 1)
    · simpa [R] using isIncreasingEvent_connectionEventOff d E D a.toProd.2
        (cubicMetricSphere d x n)
    · exact hLdep
    · exact hRdep
  have hLle : (bernoulliBondMeasure d p).real L ≤ radiusTail d p (r + 1) := by
    simpa [L] using bernoulliBondMeasure_real_residualLocalRadiusEvent_le
      (x := x) (y := a.toProd.2) p D
  have hcell :
      (bernoulliBondMeasure d p).real
          (pivotalExplorationCell (d := d) (n := n) (x := x) (F, t)) =
        (bernoulliBondMeasure d p).real R *
          finiteBernoulliWeight F (p : ℝ) t := by
    simpa [pivotalExplorationCell, a, D, F, t, R] using
      radiusConnectionEvent_inter_pivotalExplorationCylinder_measure
        hs.1 (prefixMarkedPivotalDart_mem hs hprefixBudget hpos) p
  have hw : 0 ≤ finiteBernoulliWeight F (p : ℝ) t :=
    finiteBernoulliWeight_nonneg p.2.1 p.2.2 t
  calc
    (bernoulliBondMeasure d p).real
        (sausageGapPrefixNextLongEvent d x n rs r ∩
          pivotalExplorationCell (d := d) (n := n) (x := x) (F, t)) ≤
        (bernoulliBondMeasure d p).real
          (OpenWitnessDisjointOccurrence L R ∩ finiteCylinder F t) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ = (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence L R) *
        finiteBernoulliWeight F (p : ℝ) t := hfactor
    _ ≤ ((bernoulliBondMeasure d p).real L *
        (bernoulliBondMeasure d p).real R) *
          finiteBernoulliWeight F (p : ℝ) t :=
      mul_le_mul_of_nonneg_right hBK hw
    _ ≤ (radiusTail d p (r + 1) *
        (bernoulliBondMeasure d p).real R) *
          finiteBernoulliWeight F (p : ℝ) t := by
      gcongr
    _ = radiusTail d p (r + 1) *
        (bernoulliBondMeasure d p).real
          (pivotalExplorationCell (d := d) (n := n) (x := x) (F, t)) := by
      rw [hcell]
      ring

theorem sausageGapPrefixNextLongEvent_eq_iUnion_inter_cells
    {d n r : ℕ} {x : Cubic d} {rs : List ℕ}
    (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    sausageGapPrefixNextLongEvent d x n rs r =
      ⋃ k ∈ pivotalExplorationKeys (x := x) hbudget hpos,
        sausageGapPrefixNextLongEvent d x n rs r ∩
          pivotalExplorationCell (d := d) (n := n) (x := x) k := by
  rw [← Set.inter_iUnion₂]
  rw [← sausageGapPrefixEvent_eq_iUnion_pivotalExplorationCells hbudget hpos]
  exact (Set.inter_eq_left.mpr (fun _ h ↦ h.1)).symm

theorem bernoulliBondMeasure_real_sausageGapPrefixNextLongEvent_eq_sum_cells
    {d n r : ℕ} {x : Cubic d} {rs : List ℕ}
    (p : I) (hbudget : rs.sum + rs.length ≤ n) (hpos : 0 < rs.length) :
    (bernoulliBondMeasure d p).real (sausageGapPrefixNextLongEvent d x n rs r) =
      ∑ k ∈ pivotalExplorationKeys (x := x) hbudget hpos,
        (bernoulliBondMeasure d p).real
          (sausageGapPrefixNextLongEvent d x n rs r ∩
            pivotalExplorationCell (d := d) (n := n) (x := x) k) := by
  conv_lhs => rw [sausageGapPrefixNextLongEvent_eq_iUnion_inter_cells hbudget hpos]
  exact measureReal_biUnion_finset
    ((pairwiseDisjoint_pivotalExplorationCells hbudget hpos).mono
      fun _ ↦ Set.inter_subset_right)
    (fun k hk ↦ (measurableSet_sausageGapPrefixNextLongEvent d x n rs r).inter
      (measurableSet_pivotalExplorationCell_of_mem hbudget hpos hk))

/-- Long-tail form of Grimmett's Lemma 5.12 for a nonempty conditioned
prefix. -/
theorem sausageGap_conditional_tail_le_of_pos
    {d n r : ℕ} {x : Cubic d} {rs : List ℕ}
    (p : I) (hpos : 0 < rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n) :
    (bernoulliBondMeasure d p).real
        (sausageGapPrefixNextLongEvent d x n rs r) ≤
      radiusTail d p (r + 1) *
        (bernoulliBondMeasure d p).real (sausageGapPrefixEvent d x n rs) := by
  let hprefixBudget : rs.sum + rs.length ≤ n := by omega
  rw [bernoulliBondMeasure_real_sausageGapPrefixNextLongEvent_eq_sum_cells
      p hprefixBudget hpos,
    bernoulliBondMeasure_real_sausageGapPrefixEvent_eq_sum_cells
      p hprefixBudget hpos]
  calc
    ∑ k ∈ pivotalExplorationKeys (x := x) hprefixBudget hpos,
        (bernoulliBondMeasure d p).real
          (sausageGapPrefixNextLongEvent d x n rs r ∩
            pivotalExplorationCell (d := d) (n := n) (x := x) k) ≤
      ∑ k ∈ pivotalExplorationKeys (x := x) hprefixBudget hpos,
        radiusTail d p (r + 1) *
          (bernoulliBondMeasure d p).real
            (pivotalExplorationCell (d := d) (n := n) (x := x) k) := by
      gcongr with k hk
      exact bernoulliBondMeasure_real_long_inter_pivotalExplorationCell_le
        p hpos hprefixBudget hbudget hk
    _ = radiusTail d p (r + 1) *
        ∑ k ∈ pivotalExplorationKeys (x := x) hprefixBudget hpos,
          (bernoulliBondMeasure d p).real
            (pivotalExplorationCell (d := d) (n := n) (x := x) k) := by
      rw [Finset.mul_sum]

/-- **Grimmett, Lemma 5.12.** Conditional on any feasible values of the
preceding sausage gaps, the next gap is stochastically dominated by an
independent copy of the cluster radius.  The inequality is written without
division by the conditioning probability. -/
theorem sausageGap_conditional_cdf_ge
    {d n r : ℕ} (p : I) (rs : List ℕ)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n) :
    (1 - radiusTail d p (r + 1)) *
        (bernoulliBondMeasure d p).real
          (sausageGapPrefixEvent d cubicOrigin n rs) ≤
      (bernoulliBondMeasure d p).real
        (sausageGapPrefixNextShortEvent d cubicOrigin n rs r) := by
  cases rs with
  | nil =>
      simpa [sausageGapPrefixEvent, sausageGapPrefixNextShortEvent,
        firstSausageShortEvent] using firstSausageGap_cdf_ge (d := d) p (by omega)
  | cons q qs =>
      let rs := q :: qs
      let μ := bernoulliBondMeasure d p
      let B := sausageGapPrefixEvent d cubicOrigin n rs
      let S := sausageGapPrefixNextShortEvent d cubicOrigin n rs r
      let L := sausageGapPrefixNextLongEvent d cubicOrigin n rs r
      have hpos : 0 < rs.length := by simp [rs]
      have hcover : B ⊆ S ∪ L := by
        intro ω hω
        by_cases h : sausageGap d cubicOrigin n ω (rs.length + 1) ≤ r
        · exact Or.inl ⟨hω, h⟩
        · exact Or.inr ⟨hω, lt_of_not_ge h⟩
      have hbase : μ.real B ≤ μ.real (S ∪ L) :=
        measureReal_mono hcover (measure_ne_top μ (S ∪ L))
      have hunion : μ.real (S ∪ L) ≤ μ.real S + μ.real L :=
        measureReal_union_le S L
      have hlong : μ.real L ≤ radiusTail d p (r + 1) * μ.real B := by
        simpa [μ, L, B, rs] using sausageGap_conditional_tail_le_of_pos
          (d := d) (x := cubicOrigin) p hpos hbudget
      calc
        (1 - radiusTail d p (r + 1)) * μ.real B =
            μ.real B - radiusTail d p (r + 1) * μ.real B := by ring
        _ ≤ μ.real S := by linarith
        _ = (bernoulliBondMeasure d p).real
            (sausageGapPrefixNextShortEvent d cubicOrigin n (q :: qs) r) := rfl

end Percolation

#print axioms Percolation.sausageGap_conditional_cdf_ge
