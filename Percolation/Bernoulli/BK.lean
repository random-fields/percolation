import Percolation.Bernoulli.FiniteCube

/-!
# The BK inequality

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.3, Theorems (2.12) and (2.15) and the
iterated form (2.14), pp. 37–41 (source id `grimmett-percolation-1999`).

The event `A ∘ B` that increasing events `A` and `B` *occur disjointly* is witnessed by two
disjoint finite sets of open coordinates, the first guaranteeing `A` and the second
guaranteeing `B` (Grimmett p. 37). The BK inequality bounds `P(A ∘ B) ≤ P(A) P(B)`, the
complementary direction to FKG.

* `Percolation.Forces`, `Percolation.DisjointOccurrence` — Grimmett's general disjoint
  occurrence, where each witness set forces its event through the cylinder it spans;
* `Percolation.OpenWitnessDisjointOccurrence` — the open-witness form used for increasing
  events (`H ⊆ K(ω)` with the sub-configuration `H` itself realizing `A`, p. 37), shown to
  agree with the general form for increasing events
  (`disjointOccurrence_eq_openWitnessDisjointOccurrence`);
* `Percolation.TraceDisjointOccurrence` — the finite-cube trace of the operation, with
  `eventTrace_openWitnessDisjointOccurrence` as compatibility;
* `Percolation.finiteBernoulliProbability_traceDisjointOccurrence_le_mul` — the finite BK
  core, proved by van den Berg's two-copy interpolation on the doubled cube
  `{0,1}^{E ⊕ E}` following Grimmett pp. 39–41: the mixed event `bkEvent S` reads the
  `B`-witness coordinates of `S` from the second copy, the one-coordinate step (2.21) is the
  measure-preserving injection `φ` of p. 41 (identity where possible, swap of the two copies
  at the new coordinate otherwise), and the endpoints `S = ∅`, `S = E` are the disjoint
  occurrence and the product `P(T) P(U)` respectively;
* `Percolation.setBernoulli_real_disjointOccurrence_le_mul` — **Theorem (2.12)/(2.15)** for
  finitely supported increasing events of the ambient product measure, with the
  `bernoulliBondMeasure` specialization;
* `Percolation.FiniteDisjointOccurrence` and
  `Percolation.setBernoulli_real_finiteDisjointOccurrence_le_prod` — the iterated
  inequality (2.14) for finitely many increasing events with pairwise disjoint witnesses.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Finset unitInterval

variable {ι : Type*}

/-! ### Witnesses forcing an event -/

/-- The finite coordinate set `K` *forces* the event `A` from the configuration `ω` when
every configuration agreeing with `ω` on `K` lies in `A` — Grimmett's "knowing the states of
the coordinates in `K` guarantees the occurrence of `A`" (p. 37 and the product-space forcing
of p. 39). -/
def Forces (K : Finset ι) (ω : Set ι) (A : Set (Set ι)) : Prop :=
  ∀ η : Set ι, (∀ e ∈ K, (e ∈ η ↔ e ∈ ω)) → η ∈ A

theorem Forces.mem {K : Finset ι} {ω : Set ι} {A : Set (Set ι)} (h : Forces K ω A) :
    ω ∈ A :=
  h ω fun _ _ => Iff.rfl

/-- A forcing witness of open coordinates realizes the event on its own: the
sub-configuration `↑K` agrees with `ω` on `K`. -/
theorem Forces.coe_mem {K : Finset ι} {ω : Set ι} {A : Set (Set ι)} (h : Forces K ω A)
    (hKω : (↑K : Set ι) ⊆ ω) : (↑K : Set ι) ∈ A :=
  h (↑K) fun _ he => iff_of_true (Finset.mem_coe.mpr he) (hKω (Finset.mem_coe.mpr he))

/-- For an increasing event, an open witness realizing the event forces it: any
configuration agreeing with `ω` on `K` contains the open set `↑K` (Grimmett p. 37). -/
theorem IsIncreasingEvent.forces {K : Finset ι} {ω : Set ι} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hmem : (↑K : Set ι) ∈ A) (hKω : (↑K : Set ι) ⊆ ω) :
    Forces K ω A := by
  intro η hη
  refine hA (fun e he => ?_) hmem
  have heK : e ∈ K := Finset.mem_coe.mp he
  exact (hη e heK).mpr (hKω he)

/-! ### Disjoint occurrence -/

/-- **Disjoint occurrence** `A ∘ B` (Grimmett p. 37): there exist disjoint finite sets of
open coordinates of `ω`, the first forcing `A` and the second forcing `B`. -/
def DisjointOccurrence (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ H K : Finset ι, Disjoint H K ∧ (↑H : Set ι) ⊆ ω ∧ (↑K : Set ι) ⊆ ω ∧
    Forces H ω A ∧ Forces K ω B}

/-- The open-witness form of disjoint occurrence for increasing events (Grimmett p. 37):
disjoint sets `H, K ⊆ K(ω)` of open coordinates such that the sub-configurations `↑H` and
`↑K` themselves realize `A` and `B`. For increasing `A`, `B` this agrees with
`DisjointOccurrence` (`disjointOccurrence_eq_openWitnessDisjointOccurrence`). -/
def OpenWitnessDisjointOccurrence (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ H K : Finset ι, Disjoint H K ∧ (↑H : Set ι) ⊆ ω ∧ (↑K : Set ι) ⊆ ω ∧
    (↑H : Set ι) ∈ A ∧ (↑K : Set ι) ∈ B}

theorem mem_disjointOccurrence {A B : Set (Set ι)} {ω : Set ι} :
    ω ∈ DisjointOccurrence A B ↔ ∃ H K : Finset ι, Disjoint H K ∧ (↑H : Set ι) ⊆ ω ∧
      (↑K : Set ι) ⊆ ω ∧ Forces H ω A ∧ Forces K ω B :=
  Iff.rfl

theorem mem_openWitnessDisjointOccurrence {A B : Set (Set ι)} {ω : Set ι} :
    ω ∈ OpenWitnessDisjointOccurrence A B ↔ ∃ H K : Finset ι, Disjoint H K ∧
      (↑H : Set ι) ⊆ ω ∧ (↑K : Set ι) ⊆ ω ∧ (↑H : Set ι) ∈ A ∧ (↑K : Set ι) ∈ B :=
  Iff.rfl

/-- For increasing events the two forms of disjoint occurrence coincide (Grimmett p. 37:
for increasing events one may take the witnesses to be sets of open coordinates realizing
the events). -/
theorem disjointOccurrence_eq_openWitnessDisjointOccurrence {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    DisjointOccurrence A B = OpenWitnessDisjointOccurrence A B := by
  ext ω
  constructor
  · rintro ⟨H, K, hd, hHω, hKω, hHA, hKB⟩
    exact ⟨H, K, hd, hHω, hKω, hHA.coe_mem hHω, hKB.coe_mem hKω⟩
  · rintro ⟨H, K, hd, hHω, hKω, hHA, hKB⟩
    exact ⟨H, K, hd, hHω, hKω, hA.forces hHA hHω, hB.forces hKB hKω⟩

/-- `A ∘ B ⊆ A ∩ B` for increasing events (Grimmett p. 38). -/
theorem openWitnessDisjointOccurrence_subset_inter {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    OpenWitnessDisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨H, K, _, hHω, hKω, hHA, hKB⟩
  exact ⟨hA hHω hHA, hB hKω hKB⟩

/-- The open-witness disjoint occurrence is increasing: witnesses of open coordinates
persist when further coordinates open (Grimmett p. 38). -/
theorem isIncreasingEvent_openWitnessDisjointOccurrence (A B : Set (Set ι)) :
    IsIncreasingEvent (OpenWitnessDisjointOccurrence A B) := by
  rintro ω η hωη ⟨H, K, hd, hHω, hKω, hHA, hKB⟩
  exact ⟨H, K, hd, hHω.trans hωη, hKω.trans hωη, hHA, hKB⟩

/-- `A ∘ B` is increasing when `A` and `B` are (Grimmett p. 38), for the general
forcing-witness form. -/
theorem IsIncreasingEvent.disjointOccurrence {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (DisjointOccurrence A B) := by
  rw [disjointOccurrence_eq_openWitnessDisjointOccurrence hA hB]
  exact isIncreasingEvent_openWitnessDisjointOccurrence A B

/-- Disjoint occurrence of finitely supported events is finitely supported: witnesses may
be intersected with the common support `E`, since an event depending on `E` is realized by
the trace of its witness on `E`. -/
theorem DependsOn.openWitnessDisjointOccurrence {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) :
    DependsOn E (OpenWitnessDisjointOccurrence A B) := by
  classical
  have key : ∀ ω η : Set ι, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) →
      ω ∈ OpenWitnessDisjointOccurrence A B → η ∈ OpenWitnessDisjointOccurrence A B := by
    rintro ω η hagree ⟨H, K, hd, hHω, hKω, hHA, hKB⟩
    refine ⟨H ∩ E, K ∩ E, hd.mono Finset.inter_subset_left Finset.inter_subset_left,
      ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨heH, heE⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp he)
      exact (hagree e heE).mp (hHω (Finset.mem_coe.mpr heH))
    · intro e he
      obtain ⟨heK, heE⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp he)
      exact (hagree e heE).mp (hKω (Finset.mem_coe.mpr heK))
    · exact (hA fun e he => by simp [he]).mp hHA
    · exact (hB fun e he => by simp [he]).mp hKB
  exact fun ω η h => ⟨key ω η h, key η ω fun e he => (h e he).symm⟩

/-! ### Trace-level disjoint occurrence -/

/-- Disjoint occurrence of trace events on the finite cube: two disjoint sub-traces of `s`,
one in `T` and one in `U`. -/
def TraceDisjointOccurrence (T U : Set (Finset ι)) : Set (Finset ι) :=
  {s | ∃ H K : Finset ι, Disjoint H K ∧ H ⊆ s ∧ K ⊆ s ∧ H ∈ T ∧ K ∈ U}

theorem mem_traceDisjointOccurrence {T U : Set (Finset ι)} {s : Finset ι} :
    s ∈ TraceDisjointOccurrence T U ↔ ∃ H K : Finset ι, Disjoint H K ∧ H ⊆ s ∧ K ⊆ s ∧
      H ∈ T ∧ K ∈ U :=
  Iff.rfl

theorem isIncreasingTrace_traceDisjointOccurrence (T U : Set (Finset ι)) :
    IsIncreasingTrace (TraceDisjointOccurrence T U) := by
  rintro s t hst ⟨H, K, hd, hHs, hKs, hHT, hKU⟩
  exact ⟨H, K, hd, hHs.trans hst, hKs.trans hst, hHT, hKU⟩

/-- The trace of an open-witness disjoint occurrence is the disjoint occurrence of the
traces: witnesses inside a finite configuration are finite sub-traces. -/
theorem eventTrace_openWitnessDisjointOccurrence (A B : Set (Set ι)) :
    eventTrace (OpenWitnessDisjointOccurrence A B) =
      TraceDisjointOccurrence (eventTrace A) (eventTrace B) := by
  ext s
  constructor
  · rintro ⟨H, K, hd, hHs, hKs, hHA, hKB⟩
    exact ⟨H, K, hd, Finset.coe_subset.mp hHs, Finset.coe_subset.mp hKs, hHA, hKB⟩
  · rintro ⟨H, K, hd, hHs, hKs, hHA, hKB⟩
    exact ⟨H, K, hd, Finset.coe_subset.mpr hHs, Finset.coe_subset.mpr hKs, hHA, hKB⟩

/-! ### Finite-cube probability transport -/

/-- The finite-cube probability as the weight of the trace's powerset filter. -/
theorem finiteBernoulliProbability_eq_sum_filter (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) [DecidablePred (· ∈ T)] :
    finiteBernoulliProbability E p T =
      ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeight E p s := by
  rw [finiteBernoulliProbability_eq_sum_indicator, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ T
  · rw [Set.indicator_of_mem hs, if_pos hs, mul_one]
  · rw [Set.indicator_of_notMem hs, if_neg hs, mul_zero]

/-- **Injection transport of finite-cube probabilities.** A cardinality-preserving
injection of one trace event into another cannot decrease the probability — the abstract
form of Grimmett's "measure-preserving injection `φ`" step (p. 41). -/
theorem finiteBernoulliProbability_le_of_injOn {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T U : Set (Finset ι)} (φ : Finset ι → Finset ι)
    (hsub : ∀ s, s ⊆ E → s ∈ T → φ s ⊆ E)
    (hmem : ∀ s, s ⊆ E → s ∈ T → φ s ∈ U)
    (hcard : ∀ s, s ⊆ E → s ∈ T → (φ s).card = s.card)
    (hinj : ∀ s, s ⊆ E → s ∈ T → ∀ t, t ⊆ E → t ∈ T → φ s = φ t → s = t) :
    finiteBernoulliProbability E p T ≤ finiteBernoulliProbability E p U := by
  classical
  rw [finiteBernoulliProbability_eq_sum_filter, finiteBernoulliProbability_eq_sum_filter]
  have hstep1 : ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeight E p s =
      ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeight E p (φ s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
    rw [finiteBernoulliWeight, finiteBernoulliWeight,
      hcard s (Finset.mem_powerset.mp hsE) hsT]
  have hstep2 : ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeight E p (φ s) =
      ∑ t ∈ (E.powerset.filter (· ∈ T)).image φ, finiteBernoulliWeight E p t := by
    refine (Finset.sum_image fun s hs t ht h => ?_).symm
    obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
    obtain ⟨htE, htT⟩ := Finset.mem_filter.mp ht
    exact hinj s (Finset.mem_powerset.mp hsE) hsT t (Finset.mem_powerset.mp htE) htT h
  rw [hstep1, hstep2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ =>
    finiteBernoulliWeight_nonneg hp0 hp1 t
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
  have hsE' := Finset.mem_powerset.mp hsE
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hsub s hsE' hsT), hmem s hsE' hsT⟩

/-! #### Inhomogeneous probability transport -/

theorem finiteBernoulliProbabilityFamily_eq_sum_indicator [DecidableEq ι]
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily E q T =
      ∑ s ∈ E.powerset,
        finiteBernoulliWeightFamily E q s * T.indicator (fun _ ↦ 1) s := by
  rfl

theorem finiteBernoulliProbabilityFamily_eq_sum_filter [DecidableEq ι]
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) [DecidablePred (· ∈ T)] :
    finiteBernoulliProbabilityFamily E q T =
      ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeightFamily E q s := by
  rw [finiteBernoulliProbabilityFamily_eq_sum_indicator, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : s ∈ T
  · rw [Set.indicator_of_mem hs, if_pos hs, mul_one]
  · rw [Set.indicator_of_notMem hs, if_neg hs, mul_zero]

/-- Injection transport for an inhomogeneous finite product measure. -/
theorem finiteBernoulliProbabilityFamily_le_of_injOn [DecidableEq ι]
    {E : Finset ι} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    {T U : Set (Finset ι)} (φ : Finset ι → Finset ι)
    (hsub : ∀ s, s ⊆ E → s ∈ T → φ s ⊆ E)
    (hmem : ∀ s, s ⊆ E → s ∈ T → φ s ∈ U)
    (hweight : ∀ s, s ⊆ E → s ∈ T →
      finiteBernoulliWeightFamily E q (φ s) = finiteBernoulliWeightFamily E q s)
    (hinj : ∀ s, s ⊆ E → s ∈ T → ∀ t, t ⊆ E → t ∈ T → φ s = φ t → s = t) :
    finiteBernoulliProbabilityFamily E q T ≤ finiteBernoulliProbabilityFamily E q U := by
  classical
  rw [finiteBernoulliProbabilityFamily_eq_sum_filter,
    finiteBernoulliProbabilityFamily_eq_sum_filter]
  have hstep1 :
      ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeightFamily E q s =
        ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeightFamily E q (φ s) := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
    exact (hweight s (Finset.mem_powerset.mp hsE) hsT).symm
  have hstep2 :
      ∑ s ∈ E.powerset.filter (· ∈ T), finiteBernoulliWeightFamily E q (φ s) =
        ∑ t ∈ (E.powerset.filter (· ∈ T)).image φ,
          finiteBernoulliWeightFamily E q t := by
    refine (Finset.sum_image fun s hs t ht h ↦ ?_).symm
    obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
    obtain ⟨htE, htT⟩ := Finset.mem_filter.mp ht
    exact hinj s (Finset.mem_powerset.mp hsE) hsT t
      (Finset.mem_powerset.mp htE) htT h
  rw [hstep1, hstep2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t ht _ ↦
    finiteBernoulliWeightFamily_nonneg hq0 hq1
      (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hsE, hsT⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hsub s (Finset.mem_powerset.mp hsE) hsT),
      hmem s (Finset.mem_powerset.mp hsE) hsT⟩

/-! ### The two-copy cube

Following Grimmett pp. 39–41, the finite BK core is proved on the doubled cube
`{0,1}^{E ⊕ E}`: a doubled trace `w : Finset (ι ⊕ ι)` carries two independent copies
`w.toLeft`, `w.toRight` of a trace on `E`. The interpolating event `bkEvent S T U` asks for
a disjoint occurrence, in the doubled coordinates, of `T` read from the first copy and of
`U` read through `S` — coordinates in `S` from the second copy, the rest from the first
(Grimmett's `A' ∘ B'_k`, p. 40). -/

section TwoCopy

variable [DecidableEq ι]

/-- The composite trace of Grimmett's event `B'_k` (p. 39): coordinates in `S` are read
from the second copy of the doubled trace, coordinates outside `S` from the first copy. -/
def bkMixRead (S : Finset ι) (w : Finset (ι ⊕ ι)) : Finset ι :=
  w.toRight ∩ S ∪ w.toLeft \ S

theorem mem_bkMixRead {S : Finset ι} {w : Finset (ι ⊕ ι)} {b : ι} :
    b ∈ bkMixRead S w ↔ (Sum.inr b ∈ w ∧ b ∈ S) ∨ (Sum.inl b ∈ w ∧ b ∉ S) := by
  simp [bkMixRead]

/-- Reading through `∅` is reading the first copy. -/
theorem bkMixRead_empty (w : Finset (ι ⊕ ι)) : bkMixRead (∅ : Finset ι) w = w.toLeft := by
  ext b
  simp [mem_bkMixRead]

/-- For `a ∉ S` the second-copy state of `a` is not read through `S`. -/
theorem bkMixRead_erase_inr {S : Finset ι} {a : ι} (haS : a ∉ S) (w : Finset (ι ⊕ ι)) :
    bkMixRead S (w.erase (Sum.inr a)) = bkMixRead S w := by
  ext b
  by_cases hb : b = a
  · subst hb
    simp [mem_bkMixRead, haS]
  · simp [mem_bkMixRead, hb]

/-- If neither copy of the coordinate `a` belongs to the witness, enlarging `S` by `a` does
not change the composite reading. -/
theorem bkMixRead_insert_of_notMem {S : Finset ι} {a : ι}
    {w : Finset (ι ⊕ ι)} (h1 : Sum.inl a ∉ w) (h2 : Sum.inr a ∉ w) :
    bkMixRead (insert a S) w = bkMixRead S w := by
  ext b
  by_cases hb : b = a
  · subst hb
    simp [mem_bkMixRead, h1, h2]
  · simp [mem_bkMixRead, hb]

/-- The key exchange identity behind Grimmett's injection (p. 41): moving the witness's
use of coordinate `a` from the first copy to the second copy reads the same composite trace
through `insert a S` as the original witness read through `S`. -/
theorem bkMixRead_insert_swapWitness {S : Finset ι} {a : ι} (haS : a ∉ S)
    {w : Finset (ι ⊕ ι)} (h1 : Sum.inl a ∈ w) :
    bkMixRead (insert a S) (insert (Sum.inr a) (w.erase (Sum.inl a))) = bkMixRead S w := by
  ext b
  by_cases hb : b = a
  · subst hb
    simp [mem_bkMixRead, haS, h1]
  · simp [mem_bkMixRead, hb]

theorem toLeft_erase_inr (w : Finset (ι ⊕ ι)) (a : ι) :
    (w.erase (Sum.inr a)).toLeft = w.toLeft := by
  ext b
  simp

/-- The transposition of the two copies at the coordinate `a` — Grimmett's exchange of
`x_k` and `y_k` defining the injection `φ` (p. 40). -/
def bkSwap (a : ι) (w : Finset (ι ⊕ ι)) : Finset (ι ⊕ ι) :=
  w.map (Equiv.swap (Sum.inl a) (Sum.inr a)).toEmbedding

theorem mem_bkSwap {a : ι} {w : Finset (ι ⊕ ι)} {z : ι ⊕ ι} :
    z ∈ bkSwap a w ↔ Equiv.swap (Sum.inl a) (Sum.inr a) z ∈ w := by
  rw [bkSwap, Finset.mem_map_equiv, Equiv.symm_swap]

@[simp] theorem inl_mem_bkSwap {a : ι} {w : Finset (ι ⊕ ι)} :
    Sum.inl a ∈ bkSwap a w ↔ Sum.inr a ∈ w := by
  rw [mem_bkSwap, Equiv.swap_apply_left]

@[simp] theorem inr_mem_bkSwap {a : ι} {w : Finset (ι ⊕ ι)} :
    Sum.inr a ∈ bkSwap a w ↔ Sum.inl a ∈ w := by
  rw [mem_bkSwap, Equiv.swap_apply_right]

theorem mem_bkSwap_of_ne {a : ι} {w : Finset (ι ⊕ ι)} {z : ι ⊕ ι}
    (h1 : z ≠ Sum.inl a) (h2 : z ≠ Sum.inr a) : z ∈ bkSwap a w ↔ z ∈ w := by
  rw [mem_bkSwap, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem bkSwap_bkSwap (a : ι) (w : Finset (ι ⊕ ι)) : bkSwap a (bkSwap a w) = w := by
  ext z
  rw [mem_bkSwap, mem_bkSwap, Equiv.swap_apply_self]

theorem card_bkSwap (a : ι) (w : Finset (ι ⊕ ι)) : (bkSwap a w).card = w.card :=
  Finset.card_map _

/-- The swap preserves the doubled support. -/
theorem bkSwap_subset_disjSum {E : Finset ι} {a : ι} (haE : a ∈ E)
    {w : Finset (ι ⊕ ι)} (hw : w ⊆ E.disjSum E) : bkSwap a w ⊆ E.disjSum E := by
  intro z hz
  rw [mem_bkSwap] at hz
  by_cases h1 : z = Sum.inl a
  · subst h1
    simpa using haE
  · by_cases h2 : z = Sum.inr a
    · subst h2
      simpa using haE
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hz
      exact hw hz

/-- The swap fixes any doubled trace containing both copies of `a`. -/
theorem bkSwap_eq_self_of_mem {a : ι} {w : Finset (ι ⊕ ι)} (h1 : Sum.inl a ∈ w)
    (h2 : Sum.inr a ∈ w) : bkSwap a w = w := by
  ext z
  rw [mem_bkSwap]
  by_cases hz1 : z = Sum.inl a
  · subst hz1
    rw [Equiv.swap_apply_left]
    exact iff_of_true h2 h1
  · by_cases hz2 : z = Sum.inr a
    · subst hz2
      rw [Equiv.swap_apply_right]
      exact iff_of_true h1 h2
    · rw [Equiv.swap_apply_of_ne_of_ne hz1 hz2]

/-- Grimmett's interpolating event `A' ∘ B'_k` on the doubled cube (pp. 39–40): a disjoint
occurrence, in the doubled coordinates, of the trace event `T` read from the first copy
and of `U` read through `S`. -/
def bkEvent (S : Finset ι) (T U : Set (Finset ι)) : Set (Finset (ι ⊕ ι)) :=
  TraceDisjointOccurrence {w | w.toLeft ∈ T} {w | bkMixRead S w ∈ U}

theorem mem_bkEvent {S : Finset ι} {T U : Set (Finset ι)} {w : Finset (ι ⊕ ι)} :
    w ∈ bkEvent S T U ↔ ∃ H K : Finset (ι ⊕ ι), Disjoint H K ∧ H ⊆ w ∧ K ⊆ w ∧
      H.toLeft ∈ T ∧ bkMixRead S K ∈ U :=
  Iff.rfl

/-! #### The endpoint `S = ∅` (Grimmett (2.20)) -/

/-- At `S = ∅` both events are read from the first copy, and the doubled disjoint
occurrence is exactly the disjoint occurrence of the traces on the first copy. -/
theorem bkEvent_empty (T U : Set (Finset ι)) :
    bkEvent (∅ : Finset ι) T U =
      {w : Finset (ι ⊕ ι) | w.toLeft ∈ TraceDisjointOccurrence T U} := by
  ext w
  rw [Set.mem_setOf_eq, mem_bkEvent, mem_traceDisjointOccurrence]
  constructor
  · rintro ⟨H, K, hd, hHw, hKw, hHT, hKU⟩
    rw [bkMixRead_empty] at hKU
    refine ⟨H.toLeft, K.toLeft, ?_, Finset.toLeft_subset_toLeft hHw,
      Finset.toLeft_subset_toLeft hKw, hHT, hKU⟩
    rw [Finset.disjoint_left] at hd ⊢
    intro b hbH hbK
    exact hd (Finset.mem_toLeft.mp hbH) (Finset.mem_toLeft.mp hbK)
  · rintro ⟨h, k, hd, hhw, hkw, hhT, hkU⟩
    refine ⟨h.disjSum ∅, k.disjSum ∅, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro (b | b) hz hz'
      · exact Finset.disjoint_left.mp hd (Finset.inl_mem_disjSum.mp hz)
          (Finset.inl_mem_disjSum.mp hz')
      · exact absurd (Finset.inr_mem_disjSum.mp hz) (Finset.notMem_empty b)
    · rintro (b | b) hz
      · exact Finset.mem_toLeft.mp (hhw (Finset.inl_mem_disjSum.mp hz))
      · exact absurd (Finset.inr_mem_disjSum.mp hz) (Finset.notMem_empty b)
    · rintro (b | b) hz
      · exact Finset.mem_toLeft.mp (hkw (Finset.inl_mem_disjSum.mp hz))
      · exact absurd (Finset.inr_mem_disjSum.mp hz) (Finset.notMem_empty b)
    · rwa [Finset.toLeft_disjSum]
    · rwa [bkMixRead_empty, Finset.toLeft_disjSum]

/-! #### The endpoint `S = E` and the product factorization (Grimmett p. 40) -/

omit [DecidableEq ι] in
/-- The doubled Bernoulli weight of a doubled trace is the product of the weights of its
two copies: the doubled cube carries the product measure `P₁₂ = P₁ × P₂` (Grimmett
p. 39). -/
theorem finiteBernoulliWeight_disjSum {E : Finset ι} (p : ℝ) {w : Finset (ι ⊕ ι)}
    (hw : w ⊆ E.disjSum E) :
    finiteBernoulliWeight (E.disjSum E) p w =
      finiteBernoulliWeight E p w.toLeft * finiteBernoulliWeight E p w.toRight := by
  obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp hw
  have hcards : w.toLeft.card + w.toRight.card = w.card :=
    Finset.card_toLeft_add_card_toRight
  have hL' : w.toLeft.card ≤ E.card := Finset.card_le_card hL
  have hR' : w.toRight.card ≤ E.card := Finset.card_le_card hR
  rw [finiteBernoulliWeight, finiteBernoulliWeight, finiteBernoulliWeight,
    Finset.card_disjSum, ← hcards]
  have hsub : E.card + E.card - (w.toLeft.card + w.toRight.card) =
      (E.card - w.toLeft.card) + (E.card - w.toRight.card) := by
    omega
  rw [hsub, pow_add, pow_add]
  ring

/-! #### Inhomogeneous doubled weights -/

/-- The doubled cube uses the same coordinate density on each copy. -/
def doubledBernoulliDensity (q : ι → ℝ) : ι ⊕ ι → ℝ := Sum.elim q q

theorem finiteBernoulliWeightFamily_map_equiv
    (E : Finset ι) (q : ι → ℝ) (f : ι ≃ ι)
    (hE : E.map f.toEmbedding = E) (hq : ∀ a, q (f a) = q a)
    (s : Finset ι) :
    finiteBernoulliWeightFamily E q (s.map f.toEmbedding) =
      finiteBernoulliWeightFamily E q s := by
  unfold finiteBernoulliWeightFamily
  rw [Finset.prod_map]
  have hsdiff : E \ s.map f.toEmbedding = (E \ s).map f.toEmbedding := by
    calc
      E \ s.map f.toEmbedding = E.map f.toEmbedding \ s.map f.toEmbedding := by rw [hE]
      _ = (E \ s).map f.toEmbedding :=
        (Finset.map_sdiff (f := f.toEmbedding) E s).symm
  rw [hsdiff, Finset.prod_map]
  have hq' (a : ι) : q (f.toEmbedding a) = q a := hq a
  simp_rw [hq']

theorem doubledBernoulliDensity_swap (q : ι → ℝ) (a : ι) (z : ι ⊕ ι) :
    doubledBernoulliDensity q (Equiv.swap (Sum.inl a) (Sum.inr a) z) =
      doubledBernoulliDensity q z := by
  rcases z with z | z <;> by_cases hz : z = a
  · subst z
    simp [doubledBernoulliDensity]
  · simp [doubledBernoulliDensity, Equiv.swap_apply_of_ne_of_ne, hz]
  · subst z
    simp [doubledBernoulliDensity]
  · simp [doubledBernoulliDensity, Equiv.swap_apply_of_ne_of_ne, hz]

theorem finiteBernoulliWeightFamily_bkSwap
    {E : Finset ι} {q : ι → ℝ} {a : ι} (haE : a ∈ E) (w : Finset (ι ⊕ ι)) :
    finiteBernoulliWeightFamily (E.disjSum E) (doubledBernoulliDensity q) (bkSwap a w) =
      finiteBernoulliWeightFamily (E.disjSum E) (doubledBernoulliDensity q) w := by
  have hsupport : bkSwap a (E.disjSum E) = E.disjSum E :=
    bkSwap_eq_self_of_mem (by simpa using haE) (by simpa using haE)
  exact finiteBernoulliWeightFamily_map_equiv (E.disjSum E)
    (doubledBernoulliDensity q) (Equiv.swap (Sum.inl a) (Sum.inr a)) hsupport
    (doubledBernoulliDensity_swap q a) w

theorem finiteBernoulliWeightFamily_disjSum
    {E : Finset ι} (q : ι → ℝ) {w : Finset (ι ⊕ ι)} (hw : w ⊆ E.disjSum E) :
    finiteBernoulliWeightFamily (E.disjSum E) (doubledBernoulliDensity q) w =
      finiteBernoulliWeightFamily E q w.toLeft *
        finiteBernoulliWeightFamily E q w.toRight := by
  unfold finiteBernoulliWeightFamily doubledBernoulliDensity
  obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp hw
  rw [show w = w.toLeft.disjSum w.toRight by
    exact (@Finset.toLeft_disjSum_toRight _ _ w).symm]
  have hsdiff : E.disjSum E \ (w.toLeft.disjSum w.toRight) =
      (E \ w.toLeft).disjSum (E \ w.toRight) := by
    ext (a | a) <;> simp
  rw [hsdiff]
  simp
  ring

/-- Product factorization for two independent copies of an inhomogeneous cube. -/
theorem finiteBernoulliProbabilityFamily_disjSum_left_right
    (E : Finset ι) (q : ι → ℝ) (T U : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
        {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} =
      finiteBernoulliProbabilityFamily E q T * finiteBernoulliProbabilityFamily E q U := by
  rw [finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator,
    finiteBernoulliProbabilityFamily_eq_sum_indicator, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_nbij' (fun w ↦ (w.toLeft, w.toRight))
    (fun x ↦ x.1.disjSum x.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hw)
    rw [Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr hL, Finset.mem_powerset.mpr hR⟩
  · intro x hx
    rw [Finset.mem_product] at hx
    exact Finset.mem_powerset.mpr
      (Finset.disjSum_mono (Finset.mem_powerset.mp hx.1)
        (Finset.mem_powerset.mp hx.2))
  · intro w _
    exact Finset.toLeft_disjSum_toRight
  · intro x _
    simp
  · intro w hw
    rw [finiteBernoulliWeightFamily_disjSum q (Finset.mem_powerset.mp hw)]
    by_cases h1 : w.toLeft ∈ T
    · by_cases h2 : w.toRight ∈ U
      · have hmem : w ∈ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
          ⟨h1, h2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1,
          Set.indicator_of_mem h2]
        ring
      · have hmem : w ∉ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
          fun hc ↦ h2 hc.2
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h2]
        ring
    · have hmem : w ∉ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
        fun hc ↦ h1 hc.1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]
      ring

theorem finiteBernoulliProbabilityFamily_disjSum_left
    (E : Finset ι) (q : ι → ℝ) (T : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
        {w : Finset (ι ⊕ ι) | w.toLeft ∈ T} =
      finiteBernoulliProbabilityFamily E q T := by
  have h := finiteBernoulliProbabilityFamily_disjSum_left_right E q T Set.univ
  simpa using h

omit [DecidableEq ι] in
/-- Product factorization on the doubled cube: the probability that the first copy lies in
`T` and the second in `U` is `P(T) P(U)` (Grimmett p. 40, "since `P₁₂` is a product
measure"). -/
theorem finiteBernoulliProbability_disjSum_left_right (E : Finset ι) (p : ℝ)
    (T U : Set (Finset ι)) :
    finiteBernoulliProbability (E.disjSum E) p
        {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} =
      finiteBernoulliProbability E p T * finiteBernoulliProbability E p U := by
  rw [finiteBernoulliProbability_eq_sum_indicator,
    finiteBernoulliProbability_eq_sum_indicator,
    finiteBernoulliProbability_eq_sum_indicator, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_nbij' (fun w => (w.toLeft, w.toRight)) (fun x => x.1.disjSum x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hw)
    rw [Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr hL, Finset.mem_powerset.mpr hR⟩
  · intro x hx
    rw [Finset.mem_product] at hx
    exact Finset.mem_powerset.mpr
      (Finset.disjSum_mono (Finset.mem_powerset.mp hx.1) (Finset.mem_powerset.mp hx.2))
  · intro w _
    exact Finset.toLeft_disjSum_toRight
  · intro x _
    simp
  · intro w hw
    rw [finiteBernoulliWeight_disjSum p (Finset.mem_powerset.mp hw)]
    by_cases h1 : w.toLeft ∈ T
    · by_cases h2 : w.toRight ∈ U
      · have hmem : w ∈ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} := ⟨h1, h2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        ring
      · have hmem : w ∉ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
          fun hc => h2 hc.2
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h2]
        ring
    · have hmem : w ∉ {w : Finset (ι ⊕ ι) | w.toLeft ∈ T ∧ w.toRight ∈ U} :=
        fun hc => h1 hc.1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]
      ring

omit [DecidableEq ι] in
/-- Events read from the first copy keep their probability on the doubled cube: the second
copy integrates out. -/
theorem finiteBernoulliProbability_disjSum_left (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliProbability (E.disjSum E) p
        {w : Finset (ι ⊕ ι) | w.toLeft ∈ T} = finiteBernoulliProbability E p T := by
  have h := finiteBernoulliProbability_disjSum_left_right E p T Set.univ
  simpa using h

/-- At `S = E`, membership in `bkEvent E T U` over the doubled powerset is the product
event: the `U`-witness lives entirely on the second copy, so disjointness from the
`T`-witness is automatic (Grimmett p. 40: `A' ∘ B'_m = A' ∩ B'_m`). -/
theorem mem_bkEvent_self_iff {E : Finset ι} {T U : Set (Finset ι)}
    (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) {w : Finset (ι ⊕ ι)}
    (hw : w ⊆ E.disjSum E) :
    w ∈ bkEvent E T U ↔ w.toLeft ∈ T ∧ w.toRight ∈ U := by
  obtain ⟨hL, hR⟩ := Finset.subset_disjSum.mp hw
  rw [mem_bkEvent]
  constructor
  · rintro ⟨H, K, hd, hHw, hKw, hHT, hKU⟩
    refine ⟨hT (Finset.toLeft_subset_toLeft hHw) hHT, hU ?_ hKU⟩
    intro b hb
    rcases mem_bkMixRead.mp hb with ⟨hbK, _⟩ | ⟨hbK, hbE⟩
    · exact Finset.mem_toRight.mpr (hKw hbK)
    · exact absurd (Finset.inl_mem_disjSum.mp (hw (hKw hbK))) hbE
  · rintro ⟨h1, h2⟩
    refine ⟨w.toLeft.disjSum ∅, (∅ : Finset ι).disjSum w.toRight, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro (b | b) hz hz'
      · exact absurd (Finset.inl_mem_disjSum.mp hz') (Finset.notMem_empty b)
      · exact absurd (Finset.inr_mem_disjSum.mp hz) (Finset.notMem_empty b)
    · rintro (b | b) hz
      · exact Finset.mem_toLeft.mp (Finset.inl_mem_disjSum.mp hz)
      · exact absurd (Finset.inr_mem_disjSum.mp hz) (Finset.notMem_empty b)
    · rintro (b | b) hz
      · exact absurd (Finset.inl_mem_disjSum.mp hz) (Finset.notMem_empty b)
      · exact Finset.mem_toRight.mp (Finset.inr_mem_disjSum.mp hz)
    · rwa [Finset.toLeft_disjSum]
    · have hread : bkMixRead E ((∅ : Finset ι).disjSum w.toRight) = w.toRight := by
        ext b
        rw [mem_bkMixRead, Finset.inr_mem_disjSum, Finset.inl_mem_disjSum]
        constructor
        · rintro (⟨hb, _⟩ | ⟨hb, _⟩)
          · exact hb
          · exact absurd hb (Finset.notMem_empty b)
        · intro hb
          exact Or.inl ⟨hb, hR hb⟩
      rwa [hread]

/-- The doubled probability at `S = E` is the product `P(T) P(U)`. -/
theorem finiteBernoulliProbability_bkEvent_self {E : Finset ι} (p : ℝ)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) :
    finiteBernoulliProbability (E.disjSum E) p (bkEvent E T U) =
      finiteBernoulliProbability E p T * finiteBernoulliProbability E p U := by
  rw [← finiteBernoulliProbability_disjSum_left_right]
  exact finiteBernoulliProbability_congr p fun w hw =>
    mem_bkEvent_self_iff hT hU (Finset.mem_powerset.mp hw)

/-- Inhomogeneous endpoint `S=E`: the doubled event factors into the two marginals. -/
theorem finiteBernoulliProbabilityFamily_bkEvent_self {E : Finset ι} (q : ι → ℝ)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) :
    finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
        (bkEvent E T U) =
      finiteBernoulliProbabilityFamily E q T * finiteBernoulliProbabilityFamily E q U := by
  rw [← finiteBernoulliProbabilityFamily_disjSum_left_right]
  exact finiteBernoulliProbabilityFamily_congr fun w hw ↦
    mem_bkEvent_self_iff hT hU (Finset.mem_powerset.mp hw)

/-! #### The interpolation step (Grimmett (2.21), pp. 40–41) -/

/-- If some witness pair for `w ∈ bkEvent S T U` does not use the first copy of `a`, then
`w` already lies in the enlarged event `bkEvent (insert a S) T U` — Grimmett's cases
`C₁ ∪ C₂'` of p. 41, where the identity map suffices. -/
theorem mem_bkEvent_insert_of_inl_notMem {S : Finset ι} {a : ι} (haS : a ∉ S)
    {T U : Set (Finset ι)} {w H K : Finset (ι ⊕ ι)} (hd : Disjoint H K) (hHw : H ⊆ w)
    (hKw : K ⊆ w) (hHT : H.toLeft ∈ T) (hKU : bkMixRead S K ∈ U)
    (hK : Sum.inl a ∉ K) : w ∈ bkEvent (insert a S) T U := by
  refine mem_bkEvent.mpr ⟨H, K.erase (Sum.inr a), hd.mono_right (Finset.erase_subset _ _),
    hHw, (Finset.erase_subset _ _).trans hKw, hHT, ?_⟩
  rw [bkMixRead_insert_of_notMem (fun hc => hK (Finset.mem_of_mem_erase hc))
      (Finset.notMem_erase _ _),
    bkMixRead_erase_inr haS]
  exact hKU

/-- If the witness pair for `w ∈ bkEvent S T U` uses the first copy of `a` in its
`U`-witness, then the swapped configuration lies in the enlarged event — Grimmett's case
`C₂''` of p. 41, where `φ` exchanges the two copies at `a`. -/
theorem bkSwap_mem_bkEvent_insert {S : Finset ι} {a : ι} (haS : a ∉ S)
    {T U : Set (Finset ι)} {w H K : Finset (ι ⊕ ι)} (hd : Disjoint H K) (hHw : H ⊆ w)
    (hKw : K ⊆ w) (hHT : H.toLeft ∈ T) (hKU : bkMixRead S K ∈ U)
    (hK : Sum.inl a ∈ K) : bkSwap a w ∈ bkEvent (insert a S) T U := by
  have hinlH : Sum.inl a ∉ H := Finset.disjoint_right.mp hd hK
  have hinlw : Sum.inl a ∈ w := hKw hK
  set K₀ : Finset (ι ⊕ ι) := K.erase (Sum.inr a) with hK₀
  have hK₀K : K₀ ⊆ K := Finset.erase_subset _ _
  have hinlK₀ : Sum.inl a ∈ K₀ :=
    Finset.mem_erase.mpr ⟨by simp, hK⟩
  refine mem_bkEvent.mpr
    ⟨H.erase (Sum.inr a), insert (Sum.inr a) (K₀.erase (Sum.inl a)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨hzne, hzH⟩ := Finset.mem_erase.mp hz
    rcases Finset.mem_insert.mp hz' with rfl | hzK
    · exact hzne rfl
    · exact Finset.disjoint_left.mp hd hzH (hK₀K (Finset.mem_of_mem_erase hzK))
  · intro z hz
    obtain ⟨hzne, hzH⟩ := Finset.mem_erase.mp hz
    have hzne' : z ≠ Sum.inl a := fun hc => hinlH (hc ▸ hzH)
    exact (mem_bkSwap_of_ne hzne' hzne).mpr (hHw hzH)
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzK
    · exact inr_mem_bkSwap.mpr hinlw
    · obtain ⟨hzne, hzK₀⟩ := Finset.mem_erase.mp hzK
      obtain ⟨hzne', hzK'⟩ := Finset.mem_erase.mp hzK₀
      exact (mem_bkSwap_of_ne hzne hzne').mpr (hKw hzK')
  · rwa [toLeft_erase_inr]
  · rw [bkMixRead_insert_swapWitness haS hinlK₀, hK₀, bkMixRead_erase_inr haS]
    exact hKU

/-- **No cross-collision** (Grimmett p. 41): if `w` occurs in `bkEvent S T U` but not in
the enlarged event while its swap occurs in both, we reach a contradiction; this is what
makes the map `φ` injective across its identity and swap branches. -/
theorem bkEvent_swap_collision {S : Finset ι} {a : ι} (haS : a ∉ S)
    {T U : Set (Finset ι)} {w : Finset (ι ⊕ ι)}
    (hw : w ∈ bkEvent S T U) (hwT : w ∉ bkEvent (insert a S) T U)
    (hsw : bkSwap a w ∈ bkEvent S T U)
    (hswT : bkSwap a w ∈ bkEvent (insert a S) T U) : False := by
  obtain ⟨H, K, hd, hHw, hKw, hHT, hKU⟩ := mem_bkEvent.mp hw
  -- the `U`-witness of `w` must use the first copy of `a`, so `Sum.inl a ∈ w`
  have hK : Sum.inl a ∈ K := by
    by_contra h
    exact hwT (mem_bkEvent_insert_of_inl_notMem haS hd hHw hKw hHT hKU h)
  have hinlw : Sum.inl a ∈ w := hKw hK
  obtain ⟨H', K', hd', hHw', hKw', hHT', hKU'⟩ := mem_bkEvent.mp hsw
  by_cases hcase : Sum.inl a ∈ H' ∨ Sum.inl a ∈ K'
  -- if the swapped witnesses use the first copy of `a`, then both copies are open in `w`,
  -- the swap fixes `w`, and `w ∈ bkEvent (insert a S) T U` after all
  · have hinlsw : Sum.inl a ∈ bkSwap a w := hcase.elim (fun h => hHw' h) fun h => hKw' h
    have hinrw : Sum.inr a ∈ w := inl_mem_bkSwap.mp hinlsw
    rw [bkSwap_eq_self_of_mem hinlw hinrw] at hswT
    exact hwT hswT
  -- otherwise the swapped witnesses avoid both copies of `a` (after discarding the unread
  -- second copy), hence transport back to `w` and avoid the first copy of `a`
  · have h1 : Sum.inl a ∉ H' := fun h => hcase (Or.inl h)
    have h2 : Sum.inl a ∉ K' := fun h => hcase (Or.inr h)
    have htrans : ∀ z ∈ bkSwap a w, z ≠ Sum.inl a → z ≠ Sum.inr a → z ∈ w :=
      fun z hz hz1 hz2 => (mem_bkSwap_of_ne hz1 hz2).mp hz
    refine hwT (mem_bkEvent_insert_of_inl_notMem (H := H'.erase (Sum.inr a))
      (K := K'.erase (Sum.inr a)) haS
      (hd'.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)) ?_ ?_ ?_ ?_ ?_)
    · intro z hz
      obtain ⟨hzne, hzH⟩ := Finset.mem_erase.mp hz
      exact htrans z (hHw' hzH) (fun hc => h1 (hc ▸ hzH)) hzne
    · intro z hz
      obtain ⟨hzne, hzK⟩ := Finset.mem_erase.mp hz
      exact htrans z (hKw' hzK) (fun hc => h2 (hc ▸ hzK)) hzne
    · rwa [toLeft_erase_inr]
    · rwa [bkMixRead_erase_inr haS]
    · intro hc
      exact h2 (Finset.mem_of_mem_erase hc)

/-- **The one-coordinate interpolation step, Grimmett (2.21)**: transferring the reading
of one more coordinate to the second copy cannot decrease the doubled probability. The
injection is the identity where possible and the two-copy swap at `a` otherwise
(pp. 40–41). -/
theorem finiteBernoulliProbability_bkEvent_le_insert {E S : Finset ι} {a : ι}
    (haE : a ∈ E) (haS : a ∉ S) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T U : Set (Finset ι)) :
    finiteBernoulliProbability (E.disjSum E) p (bkEvent S T U) ≤
      finiteBernoulliProbability (E.disjSum E) p (bkEvent (insert a S) T U) := by
  classical
  refine finiteBernoulliProbability_le_of_injOn hp0 hp1
    (fun w => if w ∈ bkEvent (insert a S) T U then w else bkSwap a w) ?_ ?_ ?_ ?_
  · intro w hwE _
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rwa [if_pos hw]
    · rw [if_neg hw]
      exact bkSwap_subset_disjSum haE hwE
  · intro w _ hwS
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rwa [if_pos hw]
    · rw [if_neg hw]
      obtain ⟨H, K, hd, hHw, hKw, hHT, hKU⟩ := mem_bkEvent.mp hwS
      by_cases hK : Sum.inl a ∈ K
      · exact bkSwap_mem_bkEvent_insert haS hd hHw hKw hHT hKU hK
      · exact absurd (mem_bkEvent_insert_of_inl_notMem haS hd hHw hKw hHT hKU hK) hw
  · intro w _ _
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rw [if_pos hw]
    · rw [if_neg hw]
      exact card_bkSwap a w
  · intro w₁ _ hw₁ w₂ _ hw₂ heq
    dsimp only at heq
    by_cases h1 : w₁ ∈ bkEvent (insert a S) T U
    · by_cases h2 : w₂ ∈ bkEvent (insert a S) T U
      · rwa [if_pos h1, if_pos h2] at heq
      · rw [if_pos h1, if_neg h2] at heq
        subst heq
        exact (bkEvent_swap_collision haS hw₂ h2 hw₁ h1).elim
    · by_cases h2 : w₂ ∈ bkEvent (insert a S) T U
      · rw [if_neg h1, if_pos h2] at heq
        subst heq
        exact (bkEvent_swap_collision haS hw₁ h1 hw₂ h2).elim
      · rw [if_neg h1, if_neg h2] at heq
        have := congrArg (bkSwap a) heq
        rwa [bkSwap_bkSwap, bkSwap_bkSwap] at this

/-- The one-coordinate interpolation step for arbitrary coordinate densities. -/
theorem finiteBernoulliProbabilityFamily_bkEvent_le_insert
    {E S : Finset ι} {a : ι} (haE : a ∈ E) (haS : a ∉ S)
    {q : ι → ℝ} (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (T U : Set (Finset ι)) :
    finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
        (bkEvent S T U) ≤
      finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
        (bkEvent (insert a S) T U) := by
  classical
  have hdouble0 : ∀ z ∈ E.disjSum E, 0 ≤ doubledBernoulliDensity q z := by
    rintro (e | e) he <;> simp only [doubledBernoulliDensity, Sum.elim_inl,
      Sum.elim_inr] <;> exact hq0 e (by simpa using he)
  have hdouble1 : ∀ z ∈ E.disjSum E, doubledBernoulliDensity q z ≤ 1 := by
    rintro (e | e) he <;> simp only [doubledBernoulliDensity, Sum.elim_inl,
      Sum.elim_inr] <;> exact hq1 e (by simpa using he)
  refine finiteBernoulliProbabilityFamily_le_of_injOn hdouble0 hdouble1
    (fun w ↦ if w ∈ bkEvent (insert a S) T U then w else bkSwap a w) ?_ ?_ ?_ ?_
  · intro w hwE _
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rwa [if_pos hw]
    · rw [if_neg hw]
      exact bkSwap_subset_disjSum haE hwE
  · intro w _ hwS
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rwa [if_pos hw]
    · rw [if_neg hw]
      obtain ⟨H, K, hd, hHw, hKw, hHT, hKU⟩ := mem_bkEvent.mp hwS
      by_cases hK : Sum.inl a ∈ K
      · exact bkSwap_mem_bkEvent_insert haS hd hHw hKw hHT hKU hK
      · exact absurd (mem_bkEvent_insert_of_inl_notMem haS hd hHw hKw hHT hKU hK) hw
  · intro w _ _
    dsimp only
    by_cases hw : w ∈ bkEvent (insert a S) T U
    · rw [if_pos hw]
    · rw [if_neg hw]
      exact finiteBernoulliWeightFamily_bkSwap haE w
  · intro w₁ _ hw₁ w₂ _ hw₂ heq
    dsimp only at heq
    by_cases h1 : w₁ ∈ bkEvent (insert a S) T U
    · by_cases h2 : w₂ ∈ bkEvent (insert a S) T U
      · rwa [if_pos h1, if_pos h2] at heq
      · rw [if_pos h1, if_neg h2] at heq
        subst heq
        exact (bkEvent_swap_collision haS hw₂ h2 hw₁ h1).elim
    · by_cases h2 : w₂ ∈ bkEvent (insert a S) T U
      · rw [if_neg h1, if_pos h2] at heq
        subst heq
        exact (bkEvent_swap_collision haS hw₁ h1 hw₂ h2).elim
      · rw [if_neg h1, if_neg h2] at heq
        have := congrArg (bkSwap a) heq
        rwa [bkSwap_bkSwap, bkSwap_bkSwap] at this

/-- The interpolation chain from `S = ∅` to any `S ⊆ E` (Grimmett p. 40, iterating
(2.21)). -/
theorem finiteBernoulliProbability_bkEvent_empty_le {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T U : Set (Finset ι)) :
    ∀ S : Finset ι, S ⊆ E →
      finiteBernoulliProbability (E.disjSum E) p (bkEvent (∅ : Finset ι) T U) ≤
        finiteBernoulliProbability (E.disjSum E) p (bkEvent S T U) := by
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => le_rfl
  | insert a S haS ih =>
    intro hsub
    have haE : a ∈ E := hsub (Finset.mem_insert_self a S)
    have hSE : S ⊆ E := (Finset.subset_insert a S).trans hsub
    exact (ih hSE).trans
      (finiteBernoulliProbability_bkEvent_le_insert haE haS hp0 hp1 T U)

/-- The full inhomogeneous interpolation chain. -/
theorem finiteBernoulliProbabilityFamily_bkEvent_empty_le
    {E : Finset ι} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    (T U : Set (Finset ι)) :
    ∀ S : Finset ι, S ⊆ E →
      finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
          (bkEvent (∅ : Finset ι) T U) ≤
        finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
          (bkEvent S T U) := by
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ ↦ le_rfl
  | insert a S haS ih =>
      intro hsub
      have haE : a ∈ E := hsub (Finset.mem_insert_self a S)
      have hSE : S ⊆ E := (Finset.subset_insert a S).trans hsub
      exact (ih hSE).trans
        (finiteBernoulliProbabilityFamily_bkEvent_le_insert haE haS hq0 hq1 T U)

end TwoCopy

/-! ### The finite BK core -/

/-- **The BK inequality on the finite cube** (Grimmett Theorem (2.12), proved on the trace
model of pp. 39–41): for increasing trace events,
`P(T ∘ U) ≤ P(T) P(U)`. -/
theorem finiteBernoulliProbability_traceDisjointOccurrence_le_mul [DecidableEq ι]
    {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) :
    finiteBernoulliProbability E p (TraceDisjointOccurrence T U) ≤
      finiteBernoulliProbability E p T * finiteBernoulliProbability E p U :=
  calc finiteBernoulliProbability E p (TraceDisjointOccurrence T U)
      = finiteBernoulliProbability (E.disjSum E) p (bkEvent (∅ : Finset ι) T U) := by
        rw [bkEvent_empty, finiteBernoulliProbability_disjSum_left]
    _ ≤ finiteBernoulliProbability (E.disjSum E) p (bkEvent E T U) :=
        finiteBernoulliProbability_bkEvent_empty_le hp0 hp1 T U E Finset.Subset.rfl
    _ = finiteBernoulliProbability E p T * finiteBernoulliProbability E p U :=
        finiteBernoulliProbability_bkEvent_self p hT hU

/-- **Inhomogeneous finite BK inequality.** Each coordinate may have its own density `q e`;
the two-copy swap still preserves weight because it exchanges equal-density copies of the same
coordinate. -/
theorem finiteBernoulliProbabilityFamily_traceDisjointOccurrence_le_mul [DecidableEq ι]
    {E : Finset ι} {q : ι → ℝ}
    (hq0 : ∀ e ∈ E, 0 ≤ q e) (hq1 : ∀ e ∈ E, q e ≤ 1)
    {T U : Set (Finset ι)} (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) :
    finiteBernoulliProbabilityFamily E q (TraceDisjointOccurrence T U) ≤
      finiteBernoulliProbabilityFamily E q T * finiteBernoulliProbabilityFamily E q U :=
  calc
    finiteBernoulliProbabilityFamily E q (TraceDisjointOccurrence T U) =
        finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
          (bkEvent (∅ : Finset ι) T U) := by
      rw [bkEvent_empty, finiteBernoulliProbabilityFamily_disjSum_left]
    _ ≤ finiteBernoulliProbabilityFamily (E.disjSum E) (doubledBernoulliDensity q)
          (bkEvent E T U) :=
      finiteBernoulliProbabilityFamily_bkEvent_empty_le hq0 hq1 T U E Finset.Subset.rfl
    _ = finiteBernoulliProbabilityFamily E q T * finiteBernoulliProbabilityFamily E q U :=
      finiteBernoulliProbabilityFamily_bkEvent_self q hT hU

/-! ### Theorem (2.12)/(2.15): the BK inequality -/

/-- **The BK inequality** (Grimmett Theorems (2.12) and (2.15), van den Berg–Kesten): for
increasing events depending on finitely many coordinates,
`P(A ∘ B) ≤ P(A) P(B)`. -/
theorem setBernoulli_real_disjointOccurrence_le_mul (p : I) {E F : Finset ι}
    {A B : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real (OpenWitnessDisjointOccurrence A B) ≤
      setBer((Set.univ : Set ι), p).real A * setBer((Set.univ : Set ι), p).real B := by
  classical
  have hA' : DependsOn (E ∪ F) A := hA.mono Finset.subset_union_left
  have hB' : DependsOn (E ∪ F) B := hB.mono Finset.subset_union_right
  rw [hA'.setBernoulli_real_eq_finiteBernoulliProbability p,
    hB'.setBernoulli_real_eq_finiteBernoulliProbability p,
    (hA'.openWitnessDisjointOccurrence hB').setBernoulli_real_eq_finiteBernoulliProbability
      p,
    eventTrace_openWitnessDisjointOccurrence]
  exact finiteBernoulliProbability_traceDisjointOccurrence_le_mul p.2.1 p.2.2
    hAinc.isIncreasingTrace_eventTrace hBinc.isIncreasingTrace_eventTrace

/-- The BK inequality for the forcing-witness form of disjoint occurrence, via the
equivalence of the two forms for increasing events. -/
theorem setBernoulli_real_forcesDisjointOccurrence_le_mul (p : I) {E F : Finset ι}
    {A B : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real (DisjointOccurrence A B) ≤
      setBer((Set.univ : Set ι), p).real A * setBer((Set.univ : Set ι), p).real B := by
  rw [disjointOccurrence_eq_openWitnessDisjointOccurrence hAinc hBinc]
  exact setBernoulli_real_disjointOccurrence_le_mul p hAinc hBinc hA hB

/-- **Theorem (2.15)** for the cubic lattice: BK for the Bernoulli bond measure. -/
theorem bernoulliBondMeasure_real_disjointOccurrence_le_mul {d : ℕ} (p : I)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence A B) ≤
      (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_disjointOccurrence_le_mul p hAinc hBinc hA hB

/-! ### The iterated BK inequality (2.14) -/

/-- The `k`-fold disjoint occurrence `A₁ ∘ A₂ ∘ ⋯ ∘ A_k` (Grimmett (2.14)): pairwise
disjoint finite sets of open coordinates, the `i`-th realizing `A i`. -/
def FiniteDisjointOccurrence {κ : Type*} (J : Finset κ) (A : κ → Set (Set ι)) :
    Set (Set ι) :=
  {ω | ∃ H : κ → Finset ι, ((↑J : Set κ).Pairwise fun i j => Disjoint (H i) (H j)) ∧
    ∀ i ∈ J, (↑(H i) : Set ι) ⊆ ω ∧ (↑(H i) : Set ι) ∈ A i}

theorem mem_finiteDisjointOccurrence {κ : Type*} {J : Finset κ} {A : κ → Set (Set ι)}
    {ω : Set ι} :
    ω ∈ FiniteDisjointOccurrence J A ↔ ∃ H : κ → Finset ι,
      ((↑J : Set κ).Pairwise fun i j => Disjoint (H i) (H j)) ∧
      ∀ i ∈ J, (↑(H i) : Set ι) ⊆ ω ∧ (↑(H i) : Set ι) ∈ A i :=
  Iff.rfl

@[simp] theorem finiteDisjointOccurrence_empty {κ : Type*} (A : κ → Set (Set ι)) :
    FiniteDisjointOccurrence (∅ : Finset κ) A = Set.univ := by
  refine Set.eq_univ_of_forall fun ω => ⟨fun _ => ∅, ?_, ?_⟩
  · simp
  · exact fun i hi => absurd hi (Finset.notMem_empty i)

theorem isIncreasingEvent_finiteDisjointOccurrence {κ : Type*} (J : Finset κ)
    (A : κ → Set (Set ι)) : IsIncreasingEvent (FiniteDisjointOccurrence J A) := by
  rintro ω η hωη ⟨H, hpair, hmem⟩
  exact ⟨H, hpair, fun i hi => ⟨(hmem i hi).1.trans hωη, (hmem i hi).2⟩⟩

/-- A finite disjoint occurrence of finitely supported events is finitely supported on the
union of the supports. -/
theorem dependsOn_finiteDisjointOccurrence [DecidableEq ι] {κ : Type*} {J : Finset κ}
    {E : κ → Finset ι} {A : κ → Set (Set ι)} (hdep : ∀ i ∈ J, DependsOn (E i) (A i)) :
    DependsOn (J.biUnion E) (FiniteDisjointOccurrence J A) := by
  have key : ∀ ω η : Set ι, (∀ e ∈ J.biUnion E, (e ∈ ω ↔ e ∈ η)) →
      ω ∈ FiniteDisjointOccurrence J A → η ∈ FiniteDisjointOccurrence J A := by
    rintro ω η hagree ⟨H, hpair, hmem⟩
    refine ⟨fun i => H i ∩ E i, fun i hi j hj hij =>
      (hpair hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left,
      fun i hi => ⟨?_, ?_⟩⟩
    · intro e he
      obtain ⟨heH, heE⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp he)
      exact (hagree e (Finset.mem_biUnion.mpr ⟨i, hi, heE⟩)).mp
        ((hmem i hi).1 (Finset.mem_coe.mpr heH))
    · exact (hdep i hi fun e he => by simp [he]).mp (hmem i hi).2
  exact fun ω η h => ⟨key ω η h, key η ω fun e he => (h e he).symm⟩

/-- The induction step for (2.14): a `k+1`-fold disjoint occurrence is a disjoint
occurrence of the new event and the `k`-fold one, the witness of the latter being the
union of the remaining witnesses. -/
theorem finiteDisjointOccurrence_insert_subset {κ : Type*} [DecidableEq κ] {J : Finset κ}
    {i : κ} (hiJ : i ∉ J) (A : κ → Set (Set ι)) :
    FiniteDisjointOccurrence (insert i J) A ⊆
      OpenWitnessDisjointOccurrence (A i) (FiniteDisjointOccurrence J A) := by
  classical
  rintro ω ⟨H, hpair, hmem⟩
  have hiJ' : (i : κ) ∈ (↑(insert i J) : Set κ) := by simp
  refine ⟨H i, J.biUnion H, ?_, (hmem i (Finset.mem_insert_self i J)).1, ?_,
    (hmem i (Finset.mem_insert_self i J)).2, ?_⟩
  · rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact hpair hiJ' (by simp [hj]) fun hc => hiJ (hc ▸ hj)
  · intro e he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact (hmem j (Finset.mem_insert_of_mem hj)).1 (Finset.mem_coe.mpr hej)
  · refine ⟨H, hpair.mono (Finset.coe_subset.mpr (Finset.subset_insert i J)),
      fun j hj => ⟨?_, ?_⟩⟩
    · exact Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem H hj)
    · exact (hmem j (Finset.mem_insert_of_mem hj)).2

/-- **The iterated BK inequality** (Grimmett (2.14)):
`P(A₁ ∘ A₂ ∘ ⋯ ∘ A_k) ≤ ∏ᵢ P(Aᵢ)` for increasing finitely supported events. -/
theorem setBernoulli_real_finiteDisjointOccurrence_le_prod {κ : Type*} (p : I)
    {J : Finset κ} {E : κ → Finset ι} {A : κ → Set (Set ι)}
    (hinc : ∀ i ∈ J, IsIncreasingEvent (A i)) (hdep : ∀ i ∈ J, DependsOn (E i) (A i)) :
    setBer((Set.univ : Set ι), p).real (FiniteDisjointOccurrence J A) ≤
      ∏ i ∈ J, setBer((Set.univ : Set ι), p).real (A i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [finiteDisjointOccurrence_empty, Finset.prod_empty, probReal_univ]
  | insert i J hiJ ih =>
    have hdepJ : ∀ j ∈ J, DependsOn (E j) (A j) :=
      fun j hj => hdep j (Finset.mem_insert_of_mem hj)
    calc setBer((Set.univ : Set ι), p).real (FiniteDisjointOccurrence (insert i J) A)
        ≤ setBer((Set.univ : Set ι), p).real
            (OpenWitnessDisjointOccurrence (A i) (FiniteDisjointOccurrence J A)) :=
          measureReal_mono (finiteDisjointOccurrence_insert_subset hiJ A)
            (measure_ne_top _ _)
      _ ≤ setBer((Set.univ : Set ι), p).real (A i) *
            setBer((Set.univ : Set ι), p).real (FiniteDisjointOccurrence J A) :=
          setBernoulli_real_disjointOccurrence_le_mul p
            (hinc i (Finset.mem_insert_self i J))
            (isIncreasingEvent_finiteDisjointOccurrence J A)
            (hdep i (Finset.mem_insert_self i J))
            (dependsOn_finiteDisjointOccurrence hdepJ)
      _ ≤ setBer((Set.univ : Set ι), p).real (A i) *
            ∏ j ∈ J, setBer((Set.univ : Set ι), p).real (A j) :=
          mul_le_mul_of_nonneg_left
            (ih (fun j hj => hinc j (Finset.mem_insert_of_mem hj)) hdepJ)
            measureReal_nonneg
      _ = ∏ j ∈ insert i J, setBer((Set.univ : Set ι), p).real (A j) := by
          rw [Finset.prod_insert hiJ]

/-- The iterated BK inequality (2.14) for the cubic lattice. -/
theorem bernoulliBondMeasure_real_finiteDisjointOccurrence_le_prod {d : ℕ} {κ : Type*}
    (p : I) {J : Finset κ} {E : κ → Finset (CubicEdge d)}
    {A : κ → Set (EdgeConfiguration d)}
    (hinc : ∀ i ∈ J, IsIncreasingEvent (A i)) (hdep : ∀ i ∈ J, DependsOn (E i) (A i)) :
    (bernoulliBondMeasure d p).real (FiniteDisjointOccurrence J A) ≤
      ∏ i ∈ J, (bernoulliBondMeasure d p).real (A i) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_finiteDisjointOccurrence_le_prod p hinc hdep

/-!
### Reimer's inequality (anti-target)

Grimmett states Theorem (2.19) — Reimer's inequality `P(A □ B) ≤ P(A) P(B)` for
**arbitrary** events `A, B`, with the square operation `A □ B` defined through cylinders on
complementary witness sets (p. 38) — without proof, citing Reimer (1997). It is recorded
here as an anti-target: it is neither stated nor axiomatized in this development.
-/

end Percolation
