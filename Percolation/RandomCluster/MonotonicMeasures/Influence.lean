import Percolation.RandomCluster.MonotonicMeasures.Tilt

/-!
# Influences and permutation symmetry on finite cubes

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, Lemma 2.50.

This file adds the elementary finite-cube influence interface needed for the sharp
threshold theorem. The deep influence lower bound from Theorem 2.28 is not asserted here;
we only formalize the symmetry lemma saying that invariant measures and events have equal
coordinate influences along a transitive permutation orbit.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace FiniteCubeMeasure

/-- The action on configurations corresponding to `(πω)(e) = ω(π e)`. -/
def permConfig (σ : Equiv.Perm ι) (ω : Set ι) : Set ι :=
  σ ⁻¹' ω

omit [Fintype ι] in
theorem mem_permConfig (σ : Equiv.Perm ι) (ω : Set ι) (e : ι) :
    e ∈ permConfig σ ω ↔ σ e ∈ ω :=
  Iff.rfl

omit [Fintype ι] in
theorem permConfig_id (ω : Set ι) :
    permConfig (Equiv.refl ι) ω = ω := by
  rfl

omit [Fintype ι] in
theorem permConfig_comp (σ τ : Equiv.Perm ι) (ω : Set ι) :
    permConfig σ (permConfig τ ω) = permConfig (σ.trans τ) ω := by
  ext e
  simp [permConfig]

omit [Fintype ι] in
theorem permConfig_symm_permConfig (σ : Equiv.Perm ι) (ω : Set ι) :
    permConfig σ.symm (permConfig σ ω) = ω := by
  ext e
  simp [permConfig]

omit [Fintype ι] in
theorem permConfig_permConfig_symm (σ : Equiv.Perm ι) (ω : Set ι) :
    permConfig σ (permConfig σ.symm ω) = ω := by
  ext e
  simp [permConfig]

omit [Fintype ι] in
/-- Configurations are permuted by a coordinate permutation. -/
noncomputable def configPermEquiv (σ : Equiv.Perm ι) : Set ι ≃ Set ι where
  toFun := permConfig σ
  invFun := permConfig σ.symm
  left_inv := permConfig_symm_permConfig σ
  right_inv := permConfig_permConfig_symm σ

/-- A finite-cube measure invariant under a coordinate permutation. -/
def PermInvariantMeasure (μ : FiniteCubeMeasure ι) (σ : Equiv.Perm ι) : Prop :=
  ∀ ω : Set ι, μ (permConfig σ ω) = μ ω

/-- An event invariant under a coordinate permutation. -/
def PermInvariantEvent (A : Set (Set ι)) (σ : Equiv.Perm ι) : Prop :=
  ∀ ω : Set ι, permConfig σ ω ∈ A ↔ ω ∈ A

omit [Fintype ι] in
/-- A family of coordinate permutations acts transitively on coordinates. -/
def PermFamilyTransitive (Γ : Set (Equiv.Perm ι)) : Prop :=
  ∀ e f : ι, ∃ σ ∈ Γ, σ e = f

/-- A measure is invariant under every coordinate permutation in a family. -/
def PermFamilyInvariantMeasure (μ : FiniteCubeMeasure ι) (Γ : Set (Equiv.Perm ι)) :
    Prop :=
  ∀ σ ∈ Γ, PermInvariantMeasure μ σ

omit [Fintype ι] in
/-- An event is invariant under every coordinate permutation in a family. -/
def PermFamilyInvariantEvent (A : Set (Set ι)) (Γ : Set (Equiv.Perm ι)) : Prop :=
  ∀ σ ∈ Γ, PermInvariantEvent A σ

theorem tiltWeight_permConfig (p : ℝ) (σ : Equiv.Perm ι) (ω : Set ι) :
    tiltWeight p (permConfig σ ω) = tiltWeight p ω := by
  classical
  unfold tiltWeight
  exact Fintype.prod_equiv σ (fun e => if e ∈ permConfig σ ω then p else 1 - p)
    (fun e => if e ∈ ω then p else 1 - p) fun e => by simp [permConfig]

theorem permInvariantMeasure_tilt {μ : FiniteCubeMeasure ι} {σ : Equiv.Perm ι}
    (hμ : PermInvariantMeasure μ σ) {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    PermInvariantMeasure (tilt μ p h0 h1) σ := by
  intro ω
  rw [tilt_apply, tilt_apply, tiltWeight_permConfig, hμ]

theorem permInvariantMeasure_symm {μ : FiniteCubeMeasure ι} {σ : Equiv.Perm ι}
    (hμ : PermInvariantMeasure μ σ) :
    PermInvariantMeasure μ σ.symm := by
  intro ω
  have h := hμ (permConfig σ.symm ω)
  rw [permConfig_permConfig_symm] at h
  exact h.symm

omit [Fintype ι] in
theorem permInvariantEvent_symm {A : Set (Set ι)} {σ : Equiv.Perm ι}
    (hA : PermInvariantEvent A σ) :
    PermInvariantEvent A σ.symm := by
  intro ω
  have h := hA (permConfig σ.symm ω)
  rw [permConfig_permConfig_symm] at h
  exact h.symm

/-- Ambient coordinate-open event `{J_e = 1}`. -/
def coordOpenAmbient (e : ι) : Set (Set ι) :=
  {ω | e ∈ ω}

/-- Ambient coordinate-closed event `{J_e = 0}`. -/
def coordClosedAmbient (e : ι) : Set (Set ι) :=
  {ω | e ∉ ω}

/-- Conditional probability of an event given that coordinate `e` is open. -/
noncomputable def probGivenOpen (μ : FiniteCubeMeasure ι) (A : Set (Set ι)) (e : ι) :
    ℝ :=
  μ.prob (A ∩ coordOpenAmbient e) / μ.prob (coordOpenAmbient e)

/-- Conditional probability of an event given that coordinate `e` is closed. -/
noncomputable def probGivenClosed (μ : FiniteCubeMeasure ι) (A : Set (Set ι)) (e : ι) :
    ℝ :=
  μ.prob (A ∩ coordClosedAmbient e) / μ.prob (coordClosedAmbient e)

/-- Influence of coordinate `e` on event `A`, in the sense used before Lemma 2.50. -/
noncomputable def influence (μ : FiniteCubeMeasure ι) (A : Set (Set ι)) (e : ι) : ℝ :=
  probGivenOpen μ A e - probGivenClosed μ A e

theorem prob_eq_prob_permConfig_preimage (μ : FiniteCubeMeasure ι) (σ : Equiv.Perm ι)
    (hμ : PermInvariantMeasure μ σ) (B : Set (Set ι)) :
    μ.prob B = μ.prob {ω | permConfig σ.symm ω ∈ B} := by
  classical
  have hμs := permInvariantMeasure_symm (μ := μ) (σ := σ) hμ
  rw [prob, prob, expect, expect]
  rw [Fintype.sum_equiv (configPermEquiv σ) (fun ω : Set ι =>
      μ ω * B.indicator (fun _ => (1 : ℝ)) ω)
      (fun η : Set ι =>
        μ (permConfig σ.symm η) * B.indicator (fun _ => (1 : ℝ)) (permConfig σ.symm η))]
  · exact Finset.sum_congr rfl fun η _ => by
      rw [hμs]
      by_cases hB : permConfig σ.symm η ∈ B <;> simp [hB]
  · intro η
    simp [configPermEquiv, permConfig_symm_permConfig]

theorem prob_inter_coordOpen_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι}
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    μ.prob (A ∩ coordOpenAmbient f) = μ.prob (A ∩ coordOpenAmbient e) := by
  classical
  have hAs := permInvariantEvent_symm (A := A) (σ := σ) hA
  have hsfe : σ.symm f = e := by
    rw [← hef, Equiv.symm_apply_apply]
  rw [prob_eq_prob_permConfig_preimage μ σ hμ]
  congr 1
  ext ω
  rw [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_inter_iff, hAs ω]
  simp [coordOpenAmbient, permConfig, hsfe]

theorem prob_inter_coordClosed_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι}
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    μ.prob (A ∩ coordClosedAmbient f) = μ.prob (A ∩ coordClosedAmbient e) := by
  classical
  have hAs := permInvariantEvent_symm (A := A) (σ := σ) hA
  have hsfe : σ.symm f = e := by
    rw [← hef, Equiv.symm_apply_apply]
  rw [prob_eq_prob_permConfig_preimage μ σ hμ]
  congr 1
  ext ω
  rw [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_inter_iff, hAs ω]
  simp [coordClosedAmbient, permConfig, hsfe]

theorem prob_coordOpen_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {σ : Equiv.Perm ι} {e f : ι} (hμ : PermInvariantMeasure μ σ) (hef : σ e = f) :
    μ.prob (coordOpenAmbient f) = μ.prob (coordOpenAmbient e) := by
  simpa using prob_inter_coordOpen_eq_of_permInvariant μ hμ
    (A := Set.univ) (σ := σ) (e := e) (f := f) (fun _ => by simp) hef

theorem prob_coordClosed_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {σ : Equiv.Perm ι} {e f : ι} (hμ : PermInvariantMeasure μ σ) (hef : σ e = f) :
    μ.prob (coordClosedAmbient f) = μ.prob (coordClosedAmbient e) := by
  simpa using prob_inter_coordClosed_eq_of_permInvariant μ hμ
    (A := Set.univ) (σ := σ) (e := e) (f := f) (fun _ => by simp) hef

theorem probGivenOpen_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι}
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    probGivenOpen μ A f = probGivenOpen μ A e := by
  rw [probGivenOpen, probGivenOpen, prob_inter_coordOpen_eq_of_permInvariant μ hμ hA hef,
    prob_coordOpen_eq_of_permInvariant μ hμ hef]

theorem probGivenClosed_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι}
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    probGivenClosed μ A f = probGivenClosed μ A e := by
  rw [probGivenClosed, probGivenClosed, prob_inter_coordClosed_eq_of_permInvariant μ hμ hA hef,
    prob_coordClosed_eq_of_permInvariant μ hμ hef]

/-- Lemma 2.50, finite-cube form: invariant events have equal influences along orbits. -/
theorem influence_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι}
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    influence μ A f = influence μ A e := by
  rw [influence, influence, probGivenOpen_eq_of_permInvariant μ hμ hA hef,
    probGivenClosed_eq_of_permInvariant μ hμ hA hef]

/-- Lemma 2.50 for the tilted family `μ_p`: invariant events have equal influences
under a coordinate permutation taking `e` to `f`. -/
theorem influence_tilt_eq_of_permInvariant (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {σ : Equiv.Perm ι} {e f : ι} {p : ℝ}
    (h0 : 0 < p) (h1 : p < 1)
    (hμ : PermInvariantMeasure μ σ) (hA : PermInvariantEvent A σ) (hef : σ e = f) :
    influence (tilt μ p h0 h1) A f = influence (tilt μ p h0 h1) A e :=
  influence_eq_of_permInvariant (tilt μ p h0 h1)
    (permInvariantMeasure_tilt hμ h0 h1) hA hef

/-- Lemma 2.50 packaged for a transitive family of symmetries. -/
theorem influence_eq_of_permFamilyTransitive (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {Γ : Set (Equiv.Perm ι)}
    (hΓ : PermFamilyTransitive Γ) (hμ : PermFamilyInvariantMeasure μ Γ)
    (hA : PermFamilyInvariantEvent A Γ) (e f : ι) :
    influence μ A e = influence μ A f := by
  obtain ⟨σ, hσΓ, hσef⟩ := hΓ e f
  exact (influence_eq_of_permInvariant μ (hμ σ hσΓ) (hA σ hσΓ) hσef).symm

/-- Lemma 2.50 for a tilted family whose base measure and event are invariant under a
transitive family of coordinate permutations. -/
theorem influence_tilt_eq_of_permFamilyTransitive (μ : FiniteCubeMeasure ι)
    {A : Set (Set ι)} {Γ : Set (Equiv.Perm ι)} {p : ℝ}
    (h0 : 0 < p) (h1 : p < 1) (hΓ : PermFamilyTransitive Γ)
    (hμ : PermFamilyInvariantMeasure μ Γ) (hA : PermFamilyInvariantEvent A Γ)
    (e f : ι) :
    influence (tilt μ p h0 h1) A e = influence (tilt μ p h0 h1) A f := by
  obtain ⟨σ, hσΓ, hσef⟩ := hΓ e f
  exact (influence_tilt_eq_of_permInvariant μ h0 h1 (hμ σ hσΓ) (hA σ hσΓ)
    hσef).symm

end FiniteCubeMeasure

end Percolation
