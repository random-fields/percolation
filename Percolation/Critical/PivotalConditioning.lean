import Percolation.Critical.PivotalExploration
import Percolation.Critical.Translation
import Percolation.Bernoulli.FKGInfinite

/-!
# Off-exploration connections and finite conditioning

This file replaces the informal phrase "connected off `Γ`" in Grimmett's
proof of Lemma 5.12 by a finite-support event.  Its walks may start at the
marked far endpoint, but every later vertex avoids the explored vertex set.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

private theorem idxOf_filter_lt_idxOf_filter_iff
    { α : Type* } [DecidableEq α] (P : α → Bool) (l : List α)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hPa : P a = true) (hPb : P b = true) :
    (l.filter P).idxOf a < (l.filter P).idxOf b ↔ l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
      by_cases hca : c = a
      · subst c
        simp only [List.mem_cons, true_or] at ha
        by_cases hab : a = b
        · subst b
          simp
        · simp [hPa, hab]
      · have haL : a ∈ l := (List.mem_cons.mp ha).resolve_left fun h ↦ hca h.symm
        by_cases hcb : c = b
        · subst c
          simp [hca, hPb]
        · have hbL : b ∈ l := (List.mem_cons.mp hb).resolve_left fun h ↦ hcb h.symm
          by_cases hc : P c = true
          · simpa [hca, hcb, hc] using ih haL hbL
          · have hc' : P c = false := Bool.eq_false_of_not_eq_true hc
            simpa [hca, hcb, hc'] using ih haL hbL

private theorem idxOf_filter_le_idxOf_filter_iff
    { α : Type* } [DecidableEq α] (P : α → Bool) (l : List α)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hPa : P a = true) (hPb : P b = true) :
    (l.filter P).idxOf a ≤ (l.filter P).idxOf b ↔ l.idxOf a ≤ l.idxOf b := by
  constructor <;> intro h
  · by_contra h'
    have := (idxOf_filter_lt_idxOf_filter_iff P l hb ha hPb hPa).mpr (by omega)
    omega
  · by_contra h'
    have := (idxOf_filter_lt_idxOf_filter_iff P l hb ha hPb hPa).mp (by omega)
    omega

private theorem pairwise_idxOf_lt_of_nodup
    { α : Type* } [DecidableEq α] {l : List α} (hl : l.Nodup) :
    l.Pairwise fun a b ↦ l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hl
      rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb
        have hab : a ≠ b := fun h ↦ hl.1 (h ▸ hb)
        simp [hab]
      · have htail := ih hl.2
        apply List.Pairwise.imp_of_mem _ htail
        intro b c hb hc hbc
        have hab : a ≠ b := fun h ↦ hl.1 (h ▸ hb)
        have hac : a ≠ c := fun h ↦ hl.1 (h ▸ hc)
        exact by
          simpa [hab, hac] using hbc

/-- An open connection from `y` to a finite target set using only `E`, with
every vertex after the initial vertex outside the explored set `D`. -/
def connectionEventOff (d : ℕ) (E : Finset (CubicEdge d))
    (D : Finset (Cubic d)) (y : Cubic d) (T : Finset (Cubic d)) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ z ∈ T, ∃ q : (cubicGraph d).Walk y z,
    walkIsOpen ω q ∧ walkEdgeFinset q ⊆ E ∧
      ∀ v ∈ q.support.tail, v ∉ D}

theorem isIncreasingEvent_connectionEventOff
    (d : ℕ) (E : Finset (CubicEdge d)) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    IsIncreasingEvent (connectionEventOff d E D y T) := by
  rintro ω η hωη ⟨z, hz, q, hqopen, hqsub, hqoff⟩
  exact ⟨z, hz, q, fun g hg ↦ hωη (hqopen g hg), hqsub, hqoff⟩

theorem dependsOn_connectionEventOff
    (d : ℕ) (E : Finset (CubicEdge d)) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    DependsOn E (connectionEventOff d E D y T) := by
  have forward : ∀ {ω η : EdgeConfiguration d},
      (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) →
      ω ∈ connectionEventOff d E D y T →
      η ∈ connectionEventOff d E D y T := by
    rintro ω η hagree ⟨z, hz, q, hqopen, hqsub, hqoff⟩
    refine ⟨z, hz, q, ?_, hqsub, hqoff⟩
    intro g hg
    let e : CubicEdge d := ⟨g, q.edges_subset_edgeSet hg⟩
    exact (hagree e (hqsub ((mem_walkEdgeFinset_iff q e).mpr hg))).mp (hqopen g hg)
  intro ω η hagree
  exact ⟨forward hagree, forward fun e he ↦ (hagree e he).symm⟩

theorem measurableSet_connectionEventOff
    (d : ℕ) (E : Finset (CubicEdge d)) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    MeasurableSet (connectionEventOff d E D y T) :=
  (dependsOn_connectionEventOff d E D y T).measurableSet

theorem connectionEventOff_mono_edges {d : ℕ}
    {E F : Finset (CubicEdge d)} (hEF : E ⊆ F)
    (D : Finset (Cubic d)) (y : Cubic d) (T : Finset (Cubic d)) :
    connectionEventOff d E D y T ⊆ connectionEventOff d F D y T := by
  rintro ω ⟨z, hz, q, hqopen, hqsub, hqoff⟩
  exact ⟨z, hz, q, hqopen, hqsub.trans hEF, hqoff⟩

/-- Forgetting the off-exploration constraint gives an ordinary connection
to the target set. -/
theorem connectionEventOff_subset_exists_connection {d : ℕ}
    (E : Finset (CubicEdge d)) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    connectionEventOff d E D y T ⊆
      {ω | ∃ z ∈ T, ω ∈ connectionEvent d y z} := by
  rintro ω ⟨z, hz, q, hqopen, -⟩
  exact ⟨z, hz, q, hqopen⟩

/-- An off-exploration connection to a metric sphere is bounded by the
unrestricted radius tail, uniformly in the explored graph. -/
theorem bernoulliBondMeasure_real_connectionEventOff_sphere_le
    {d m : ℕ} (p : I) (E : Finset (CubicEdge d))
    (D : Finset (Cubic d)) (y : Cubic d) :
    (bernoulliBondMeasure d p).real
        (connectionEventOff d E D y (cubicMetricSphere d y m)) ≤
      radiusTail d p m := by
  calc
    (bernoulliBondMeasure d p).real
        (connectionEventOff d E D y (cubicMetricSphere d y m)) ≤
        (bernoulliBondMeasure d p).real (radiusConnectionEvent d y m) := by
      apply measureReal_mono
      intro ω hω
      rw [mem_radiusConnectionEvent_iff_exists_connection]
      exact connectionEventOff_subset_exists_connection E D y
        (cubicMetricSphere d y m) hω
      exact MeasureTheory.measure_ne_top _ _
    _ = radiusTail d p m :=
      bernoulliBondMeasure_real_radiusConnectionEvent_eq_radiusTail p y

/-- The off event naturally used after exposing `D`: only coordinates outside
the incident-edge exploration remain random. -/
def radiusConnectionEventOffExploration
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) : Set (EdgeConfiguration d) :=
  connectionEventOff d
    (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) D y T

theorem dependsOn_radiusConnectionEventOffExploration
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    DependsOn (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D)
      (radiusConnectionEventOffExploration d x n D y T) :=
  dependsOn_connectionEventOff d _ D y T

theorem measurableSet_radiusConnectionEventOffExploration
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d))
    (y : Cubic d) (T : Finset (Cubic d)) :
    MeasurableSet (radiusConnectionEventOffExploration d x n D y T) :=
  (dependsOn_radiusConnectionEventOffExploration d x n D y T).measurableSet

private theorem exists_open_near_connection_of_open_walk_to_outside
    {d : ℕ} {E F : Finset (CubicEdge d)} {D : Finset (Cubic d)}
    {ζ : EdgeConfiguration d} {e : CubicEdge d} {near far u z : Cubic d}
    (heval : (e : Sym2 (Cubic d)) = s(near, far))
    (hfar : far ∉ D) (hu : u ∈ D) (hz : z ∉ D)
    (q : (cubicGraph d).Walk u z) (hqopen : walkIsOpen ζ q)
    (hqsub : walkEdgeFinset q ⊆ E)
    (hF : ∀ f ∈ E, (∃ y ∈ D, y ∈ (f : Sym2 (Cubic d))) → f ∈ F)
    (hboundary : ∀ f ∈ E,
      cubicEdgeCrossesFinset D f → f ∈ ζ → f = e) :
    e ∈ ζ ∧ ζ ∈ connectionEventIn d (F.erase e) u near := by
  classical
  induction q with
  | nil => exact (hz hu).elim
  | @cons u v z huv q ih =>
      let f : CubicEdge d := ⟨s(u, v), by
        rw [SimpleGraph.mem_edgeSet]
        exact huv⟩
      have hfWalk : f ∈ walkEdgeFinset (SimpleGraph.Walk.cons huv q) := by
        rw [mem_walkEdgeFinset_iff]
        simp [f]
      have hfE : f ∈ E := hqsub hfWalk
      have hfζ : f ∈ ζ := by
        have := hqopen s(u, v) (by simp)
        simpa [f, edgeOpen] using this
      by_cases hv : v ∈ D
      · have hqopenTail : walkIsOpen ζ q :=
          walkIsOpen_of_edges_subset hqopen (by intro g hg; simp [hg])
        have hqsubTail : walkEdgeFinset q ⊆ E := by
          intro g hg
          apply hqsub
          rw [mem_walkEdgeFinset_iff] at hg ⊢
          simp [hg]
        obtain ⟨heζ, p, hpopen, hpsub⟩ := ih hv hz hqopenTail hqsubTail
        have hfF : f ∈ F := hF f hfE ⟨u, hu, by simp [f]⟩
        have hfe : f ≠ e := by
          intro h
          have hs : s(u, v) = s(near, far) :=
            (show (f : Sym2 (Cubic d)) = s(near, far) from
              (congrArg Subtype.val h).trans heval)
          rcases Sym2.eq_iff.mp hs with hs | hs
          · exact hfar (hs.2 ▸ hv)
          · exact hfar (hs.1 ▸ hu)
        let step : (cubicGraph d).Walk u v :=
          SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
        have hstepopen : walkIsOpen ζ step := by
          intro g hg
          simp only [step, SimpleGraph.Walk.edges_cons,
            SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
          subst g
          simpa [f, edgeOpen] using hfζ
        refine ⟨heζ, step.append p, walkIsOpen_append hstepopen hpopen, ?_⟩
        intro g hg
        rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
          List.mem_append] at hg
        rcases hg with hg | hg
        · have hgf : g = f := by
            apply Subtype.ext
            simpa [step, f] using hg
          subst g
          exact Finset.mem_erase.mpr ⟨hfe, hfF⟩
        · exact hpsub ((mem_walkEdgeFinset_iff p g).mpr hg)
      · have hfCross : cubicEdgeCrossesFinset D f := by
          change cubicEdgeCrossesFinset D
            ⟨s(u, v), by rw [SimpleGraph.mem_edgeSet]; exact huv⟩
          rw [cubicEdgeCrossesFinset_mk _ huv]
          exact Or.inl ⟨hu, hv⟩
        have hfe : f = e := hboundary f hfE hfCross hfζ
        have hs : s(u, v) = s(near, far) :=
          (show (f : Sym2 (Cubic d)) = s(near, far) from
            (congrArg Subtype.val hfe).trans heval)
        have hune : u = near := by
          rcases Sym2.eq_iff.mp hs with hs | hs
          · exact hs.1
          · exact (hfar (hs.1 ▸ hu)).elim
        refine ⟨hfe ▸ hfζ, (SimpleGraph.Walk.nil : (cubicGraph d).Walk u u).copy
          rfl hune, ?_, ?_⟩
        · simp [walkIsOpen]
        · intro g hg
          rw [mem_walkEdgeFinset_iff] at hg
          simp at hg

/-- If a configuration reaches the outer sphere while every open edge leaving
`D` is the marked edge, then the marked edge is open and the origin reaches
its near endpoint using only explored incident edges. -/
theorem radiusConnectionEvent_imp_pivotalExplorationInside
    {d n : ℕ} {x near far : Cubic d} {ζ : EdgeConfiguration d}
    {D : Finset (Cubic d)} {e : CubicEdge d}
    (heval : (e : Sym2 (Cubic d)) = s(near, far))
    (hx : x ∈ D) (hfar : far ∉ D)
    (hDsphere : Disjoint D (cubicMetricSphere d x n))
    (hboundary : ∀ f ∈ cubicMetricBallEdges d x n,
      cubicEdgeCrossesFinset D f → f ∈ ζ → f = e)
    (hζ : ζ ∈ radiusConnectionEvent d x n) :
    e ∈ ζ ∧
      ζ ∈ connectionEventIn d ((radiusIncidentEdgesOf d x n D).erase e) x near := by
  let W := canonicalRadiusWitness hζ
  have hz : W.endpoint ∉ D := by
    intro hzD
    exact Finset.disjoint_left.mp hDsphere hzD W.sphere_mem
  exact exists_open_near_connection_of_open_walk_to_outside heval hfar hx hz
    W.walk W.isOpen W.edge_subset (by
      intro f hfE hinc
      rw [mem_radiusIncidentEdgesOf_iff]
      exact ⟨hfE, hinc⟩) hboundary

/-- Reconstruct the radius event from the explored-side connection, the open
marked edge, and an off-exploration continuation. -/
theorem pivotalExplorationInside_and_off_imp_radiusConnectionEvent
    {d n : ℕ} {x near far : Cubic d} {ζ : EdgeConfiguration d}
    {D : Finset (Cubic d)} {e : CubicEdge d}
    (heval : (e : Sym2 (Cubic d)) = s(near, far))
    (heE : e ∈ cubicMetricBallEdges d x n)
    (heζ : e ∈ ζ)
    (hinside : ζ ∈ connectionEventIn d
      ((radiusIncidentEdgesOf d x n D).erase e) x near)
    (hoff : ζ ∈ radiusConnectionEventOffExploration d x n D far
      (cubicMetricSphere d x n)) :
    ζ ∈ radiusConnectionEvent d x n := by
  rcases hinside with ⟨q, hqopen, hqsub⟩
  rcases hoff with ⟨z, hz, r, hropen, hrsub, hroff⟩
  have hAdj : (cubicGraph d).Adj near far := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [← heval]
    exact e.2
  let step : (cubicGraph d).Walk near far :=
    SimpleGraph.Walk.cons hAdj SimpleGraph.Walk.nil
  have hstepopen : walkIsOpen ζ step := by
    intro g hg
    simp only [step, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
    subst g
    have hsub : (⟨s(near, far), by
        rw [SimpleGraph.mem_edgeSet]
        exact hAdj⟩ : CubicEdge d) = e := Subtype.ext heval.symm
    simpa [hsub, edgeOpen] using heζ
  refine ⟨z, hz, q.append (step.append r),
    walkIsOpen_append hqopen (walkIsOpen_append hstepopen hropen), ?_⟩
  intro g hg
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at hg
  rcases hg with hg | hg
  · have hgF := Finset.mem_erase.mp (hqsub ((mem_walkEdgeFinset_iff q g).mpr hg)) |>.2
    exact (mem_radiusIncidentEdgesOf_iff.mp hgF).1
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at hg
    rcases hg with hg | hg
    · have hge : g = e := by
        apply Subtype.ext
        have hgs : (g : Sym2 (Cubic d)) = s(near, far) := by
          simpa [step] using hg
        exact hgs.trans heval.symm
      exact hge ▸ heE
    · exact Finset.mem_sdiff.mp (hrsub ((mem_walkEdgeFinset_iff r g).mpr hg)) |>.1

/-- Once the deleted cluster at a pivotal edge has been exposed, occurrence
of `Aₙ(x)` is exactly an off-exploration connection from the marked far
endpoint to the target sphere.  This is equation (5.15) before taking
probabilities. -/
theorem radiusConnectionEvent_iff_connectionEventOffExploration_of_agree
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    η ∈ radiusConnectionEvent d x n ↔
      η ∈ radiusConnectionEventOffExploration d x n
        (radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω)
        a.toProd.2 (cubicMetricSphere d x n) := by
  classical
  let e := cubicEdgeOfDart a
  let D := radiusDeletedReachableVertices d x n e ω
  let F := radiusDeletedIncidentEdges d x n e ω
  have haData := (mem_radiusPivotalDarts_iff hω a).mp ha
  have hePiv : IsPivotal (radiusConnectionEvent d x n) e ω := haData.2
  have hafst : a.toProd.1 ∈ D := by
    simpa [D, e] using pivotalDart_fst_mem_radiusDeletedReachableVertices hω ha
  have hasnd : a.toProd.2 ∉ D := by
    simpa [D, e] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hω ha
  have hDsphere : Disjoint D (cubicMetricSphere d x n) := by
    simpa [D, e] using
      radiusDeletedReachableVertices_disjoint_sphere_of_pivotal hePiv
  have hDη : D = radiusDeletedReachableVertices d x n e η := by
    simpa [D, F, e] using
      radiusDeletedReachableVertices_eq_of_agree_incident hagree
  have heF : e ∈ F := by
    apply radiusDeletedBoundaryEdges_subset_incidentEdges
    simpa [F, e] using cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha
  have heω : e ∈ ω :=
    pivotal_open_of_mem_event (isIncreasingEvent_radiusConnectionEvent d x n) hω hePiv
  constructor
  · intro hη
    let W := canonicalRadiusWitness hη
    have hWend : W.endpoint ∉ D := by
      intro hendD
      exact Finset.disjoint_left.mp hDsphere hendD W.sphere_mem
    obtain ⟨u, huD, q, hqSub, hqOutside⟩ :=
      exists_isSubwalk_suffix_from_last_region W.walk
        ⟨x, by simp, by simpa [D] using
          center_mem_radiusDeletedReachableVertices d n x e ω⟩ hWend
    cases q with
    | nil =>
        exact (hWend (by simpa using huD)).elim
    | @cons u v z huv r =>
        have hvNot : v ∉ D := by
          exact hqOutside v (by simp)
        let f : CubicEdge d := ⟨s(u, v), by
          rw [SimpleGraph.mem_edgeSet]
          exact huv⟩
        have hfWedge : (f : Sym2 (Cubic d)) ∈ W.walk.edges :=
          hqSub.edges_subset (by simp [f])
        have hfE : f ∈ cubicMetricBallEdges d x n :=
          W.edge_subset ((mem_walkEdgeFinset_iff W.walk f).mpr hfWedge)
        have hfF : f ∈ F := by
          change f ∈ radiusDeletedIncidentEdges d x n e ω
          rw [mem_radiusDeletedIncidentEdges_iff]
          exact ⟨hfE, u, huD, by simp [f]⟩
        have hfη : f ∈ η := by
          simpa [f] using W.isOpen s(u, v) hfWedge
        have hfω : f ∈ ω := (hagree f (by simpa [F] using hfF)).mpr hfη
        have hfBoundary : f ∈ radiusDeletedBoundaryEdges d x n e ω := by
          rw [mem_radiusDeletedBoundaryEdges_iff]
          refine ⟨hfE, ?_⟩
          change cubicEdgeCrossesFinset D f
          rw [show f = ⟨s(u, v), by
            rw [SimpleGraph.mem_edgeSet]
            exact huv⟩ from rfl, cubicEdgeCrossesFinset_mk _ huv]
          exact Or.inl ⟨huD, hvNot⟩
        have hfe : f = e := mem_radiusDeletedBoundaryEdges_of_open_imp_eq
          (by simpa [e] using hfBoundary) hfω
        have huvEq : u = a.toProd.1 ∧ v = a.toProd.2 := by
          have hsym := congrArg Subtype.val hfe
          change s(u, v) = s(a.toProd.1, a.toProd.2) at hsym
          rcases Sym2.eq_iff.mp hsym with h | h
          · exact h
          · exact (hasnd (h.1 ▸ huD)).elim
        have hrOpen : walkIsOpen η r :=
          walkIsOpen_of_isSubwalk W.isOpen
            ((SimpleGraph.Walk.isSubwalk_cons r huv).trans hqSub)
        have hrSub : walkEdgeFinset r ⊆
            cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D := by
          intro g hg
          have hgW : (g : Sym2 (Cubic d)) ∈ W.walk.edges :=
            (((SimpleGraph.Walk.isSubwalk_cons r huv).trans hqSub).edges_subset
              ((mem_walkEdgeFinset_iff r g).mp hg))
          apply Finset.mem_sdiff.mpr
          refine ⟨W.edge_subset ((mem_walkEdgeFinset_iff W.walk g).mpr hgW), ?_⟩
          intro hgInc
          rcases (mem_radiusIncidentEdgesOf_iff.mp hgInc).2 with ⟨t, htD, htg⟩
          have htSupport : t ∈ r.support :=
            r.mem_support_of_mem_edges ((mem_walkEdgeFinset_iff r g).mp hg) htg
          exact hqOutside t (by simpa using htSupport) htD
        have hrOff : ∀ t ∈ r.support.tail, t ∉ D := by
          intro t ht
          exact hqOutside t (by simpa using List.mem_of_mem_tail ht)
        change η ∈ connectionEventOff d
          (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) D
          a.toProd.2 (cubicMetricSphere d x n)
        refine ⟨W.endpoint, W.sphere_mem, r.copy huvEq.2 rfl, ?_, ?_, ?_⟩
        · exact (walkIsOpen_copy r huvEq.2 rfl).mpr hrOpen
        · intro g hg
          apply hrSub
          rw [mem_walkEdgeFinset_iff] at hg ⊢
          simpa using hg
        · intro t ht
          apply hrOff t
          simpa using ht
  · intro hOff
    change η ∈ connectionEventOff d
      (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) D
      a.toProd.2 (cubicMetricSphere d x n) at hOff
    rcases hOff with ⟨z, hz, r, hrOpen, hrSub, hrOff⟩
    have hafstη : a.toProd.1 ∈ radiusDeletedReachableVertices d x n e η := by
      rw [← hDη]
      exact hafst
    rcases (mem_radiusDeletedReachableVertices_iff.mp hafstη).2 with
      ⟨q, hqOpen, hqSub⟩
    have heη : e ∈ η := (hagree e (by simpa [F] using heF)).mp heω
    let step : (cubicGraph d).Walk a.toProd.1 a.toProd.2 :=
      SimpleGraph.Walk.cons a.adj SimpleGraph.Walk.nil
    have hstepOpen : walkIsOpen η step := by
      intro g hg
      simp only [step, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
      subst g
      simpa [e, cubicEdgeOfDart, edgeOpen] using heη
    have hqOpenη : walkIsOpen η q := fun g hg ↦ (hqOpen g hg).1
    refine ⟨z, hz, q.append (step.append r),
      walkIsOpen_append hqOpenη (walkIsOpen_append hstepOpen hrOpen), ?_⟩
    intro g hg
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hg
    rcases hg with hg | hg
    · exact (Finset.mem_erase.mp (hqSub ((mem_walkEdgeFinset_iff q g).mpr hg))).2
    · rw [SimpleGraph.Walk.edges_append, List.mem_append] at hg
      rcases hg with hg | hg
      · have hge : g = e := by
          apply Subtype.ext
          simpa [step, e, cubicEdgeOfDart] using hg
        exact hge ▸ (mem_radiusDeletedBoundaryEdges_iff.mp
          (cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha)).1
      · exact Finset.mem_sdiff.mp (hrSub ((mem_walkEdgeFinset_iff r g).mpr hg)) |>.1

/-- Splicing a disjoint coordinate block does not change an event. -/
theorem preimage_spliceOn_eq_self_of_dependsOn_disjoint
    { ι : Type* } [DecidableEq ι] {E F s : Finset ι}
    (hs : s ⊆ F) {A : Set (Set ι)} (hA : DependsOn E A)
    (hEF : Disjoint E F) :
    (fun ω ↦ spliceOn F s ω) ⁻¹' A = A := by
  ext ω
  exact hA fun e heE ↦ by
    have heF : e ∉ F := Finset.disjoint_left.mp hEF heE
    rw [mem_spliceOn_of_notMem hs heF]

/-- Independence of a supported event from a disjoint finite trace cylinder. -/
theorem setBernoulli_real_inter_finiteCylinder_of_disjoint
    { ι : Type* } [DecidableEq ι] (p : I) {E F s : Finset ι}
    (hs : s ⊆ F) {A : Set (Set ι)} (hA : DependsOn E A)
    (hEF : Disjoint E F) :
    setBer((Set.univ : Set ι), p).real (A ∩ finiteCylinder F s) =
      setBer((Set.univ : Set ι), p).real A *
        finiteBernoulliWeight F (p : ℝ) s := by
  rw [setBernoulli_real_inter_finiteCylinder p hs hA.measurableSet,
    preimage_spliceOn_eq_self_of_dependsOn_disjoint hs hA hEF]

/-- Exact cylinder form of Grimmett (5.15).  The trace on all edges incident
to the deleted cluster is frozen; the remaining factor is precisely the
off-exploration connection probability. -/
theorem radiusConnectionEvent_inter_pivotalExplorationCylinder_measure
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (p : I) :
    let e := cubicEdgeOfDart a
    let D := radiusDeletedReachableVertices d x n e ω
    let F := radiusDeletedIncidentEdges d x n e ω
    let s := restrictTo F ω
    (bernoulliBondMeasure d p).real
        (radiusConnectionEvent d x n ∩ finiteCylinder F s) =
      (bernoulliBondMeasure d p).real
          (radiusConnectionEventOffExploration d x n D a.toProd.2
            (cubicMetricSphere d x n)) *
        finiteBernoulliWeight F (p : ℝ) s := by
  classical
  dsimp only
  let e := cubicEdgeOfDart a
  let D := radiusDeletedReachableVertices d x n e ω
  let F := radiusDeletedIncidentEdges d x n e ω
  let s := restrictTo F ω
  let C := finiteCylinder F s
  let R := radiusConnectionEventOffExploration d x n D a.toProd.2
    (cubicMetricSphere d x n)
  have hs : s ⊆ F := restrictTo_subset F ω
  have hset : radiusConnectionEvent d x n ∩ C = R ∩ C := by
    ext η
    constructor
    · rintro ⟨hηA, hηC⟩
      refine ⟨(radiusConnectionEvent_iff_connectionEventOffExploration_of_agree
        hω ha ?_).mp hηA, hηC⟩
      intro f hfF
      have htrace := hηC f hfF
      rw [mem_restrictTo] at htrace
      exact ⟨fun hfω ↦ htrace.mpr ⟨hfF, hfω⟩,
        fun hfη ↦ (htrace.mp hfη).2⟩
    · rintro ⟨hηR, hηC⟩
      refine ⟨(radiusConnectionEvent_iff_connectionEventOffExploration_of_agree
        hω ha ?_).mpr hηR, hηC⟩
      intro f hfF
      have htrace := hηC f hfF
      rw [mem_restrictTo] at htrace
      exact ⟨fun hfω ↦ htrace.mpr ⟨hfF, hfω⟩,
        fun hfη ↦ (htrace.mp hfη).2⟩
  rw [hset]
  change (bernoulliBondMeasure d p).real (R ∩ C) = _
  have hR := dependsOn_radiusConnectionEventOffExploration d x n D a.toProd.2
    (cubicMetricSphere d x n)
  have hdisj : Disjoint
      (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) F := by
    apply Finset.disjoint_of_subset_right (show F ⊆ radiusIncidentEdgesOf d x n D by
      intro f hf
      simpa [F, D, radiusDeletedIncidentEdges] using hf)
    exact Finset.sdiff_disjoint
  simpa [R, C, F, D, s, bernoulliBondMeasure] using
    setBernoulli_real_inter_finiteCylinder_of_disjoint p hs hR hdisj

/-- Outside the exposed incident coordinates, pivotality for the original
radius event is exactly pivotality for the residual off-exploration event. -/
theorem isPivotal_radiusConnectionEvent_iff_offExploration
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    {f : CubicEdge d}
    (hf : f ∉ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω) :
    IsPivotal (radiusConnectionEvent d x n) f ω ↔
      IsPivotal
        (radiusConnectionEventOffExploration d x n
          (radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω)
          a.toProd.2 (cubicMetricSphere d x n)) f ω := by
  have hins : ∀ g ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (g ∈ ω ↔ g ∈ insert f ω) := by
    intro g hg
    simp only [Set.mem_insert_iff]
    constructor
    · exact Or.inr
    · rintro (rfl | hgω)
      · exact (hf hg).elim
      · exact hgω
  have hdel : ∀ g ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (g ∈ ω ↔ g ∈ ω \ {f}) := by
    intro g hg
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun hgω ↦ ⟨hgω, fun hgf ↦ hf (hgf ▸ hg)⟩, And.left⟩
  unfold IsPivotal
  rw [radiusConnectionEvent_iff_connectionEventOffExploration_of_agree hω ha hins,
    radiusConnectionEvent_iff_connectionEventOffExploration_of_agree hω ha hdel]

/-- Closing one explored coordinate has the same effect on the radius event
for every configuration in the same exploration cylinder that realizes the
outer continuation.  Consequently all pivotal edges up to the marked edge,
and their order, are cylinder data. -/
theorem diff_mem_radiusConnectionEvent_iff_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η))
    {g : CubicEdge d}
    (hgF : g ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω) :
    ω \ {g} ∈ radiusConnectionEvent d x n ↔
      η \ {g} ∈ radiusConnectionEvent d x n := by
  classical
  let e := cubicEdgeOfDart a
  let D := radiusDeletedReachableVertices d x n e ω
  let F := radiusDeletedIncidentEdges d x n e ω
  let R := radiusConnectionEventOffExploration d x n D a.toProd.2
    (cubicMetricSphere d x n)
  have heval : (e : Sym2 (Cubic d)) = s(a.toProd.1, a.toProd.2) := by
    rfl
  have haPiv := (mem_radiusPivotalDarts_iff hω a).mp ha |>.2
  have hxD : x ∈ D := by
    simpa [D] using center_mem_radiusDeletedReachableVertices d n x e ω
  have hfar : a.toProd.2 ∉ D := by
    simpa [D, e] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hω ha
  have hDsphere : Disjoint D (cubicMetricSphere d x n) := by
    simpa [D, e] using radiusDeletedReachableVertices_disjoint_sphere_of_pivotal haPiv
  have heBoundary := cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha
  have heE : e ∈ cubicMetricBallEdges d x n := by
    exact (mem_radiusDeletedBoundaryEdges_iff.mp (by simpa [e] using heBoundary)).1
  have hRω : ω ∈ R := by
    apply (radiusConnectionEvent_iff_connectionEventOffExploration_of_agree hω ha ?_).mp hω
    intro f hf
    rfl
  have hRη : η ∈ R := by
    exact (radiusConnectionEvent_iff_connectionEventOffExploration_of_agree hω ha
      hagree).mp hη
  have hRdep : DependsOn (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) R :=
    dependsOn_radiusConnectionEventOffExploration d x n D a.toProd.2
      (cubicMetricSphere d x n)
  have hgF' : g ∈ F := by simpa [F, e] using hgF
  have hRdiff : ∀ {ζ : EdgeConfiguration d}, ζ ∈ R → ζ \ {g} ∈ R := by
    intro ζ hζR
    apply (hRdep fun f hf ↦ ?_).mp hζR
    have hfNotF : f ∉ F := by
      intro hfF
      have hfInc : f ∈ radiusIncidentEdgesOf d x n D := by
        simpa [F, D, radiusDeletedIncidentEdges] using hfF
      exact (Finset.mem_sdiff.mp hf).2 hfInc
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun hfζ ↦ ⟨hfζ, fun hfg ↦ hfNotF (hfg ▸ hgF')⟩, And.left⟩
  have hBoundaryω : ∀ f ∈ cubicMetricBallEdges d x n,
      cubicEdgeCrossesFinset D f → f ∈ ω \ {g} → f = e := by
    intro f hfE hfCross hfOpen
    apply mem_radiusDeletedBoundaryEdges_of_open_imp_eq
    · rw [mem_radiusDeletedBoundaryEdges_iff]
      exact ⟨hfE, by simpa [D, e] using hfCross⟩
    · exact hfOpen.1
  have hBoundaryη : ∀ f ∈ cubicMetricBallEdges d x n,
      cubicEdgeCrossesFinset D f → f ∈ η \ {g} → f = e := by
    intro f hfE hfCross hfOpen
    have hfB : f ∈ radiusDeletedBoundaryEdges d x n e ω := by
      rw [mem_radiusDeletedBoundaryEdges_iff]
      exact ⟨hfE, by simpa [D] using hfCross⟩
    have hfF : f ∈ F := radiusDeletedBoundaryEdges_subset_incidentEdges hfB
    apply mem_radiusDeletedBoundaryEdges_of_open_imp_eq hfB
    exact (hagree f (by simpa [F, e] using hfF)).mpr hfOpen.1
  constructor
  · intro hωdel
    obtain ⟨heOpen, hinside⟩ :=
      radiusConnectionEvent_imp_pivotalExplorationInside
        (e := e) (D := D) (near := a.toProd.1) (far := a.toProd.2)
        heval hxD hfar hDsphere hBoundaryω hωdel
    have hinsideη : η \ {g} ∈ connectionEventIn d
        ((radiusIncidentEdgesOf d x n D).erase e) x a.toProd.1 := by
      apply (dependsOn_connectionEventIn d _ x a.toProd.1 (fun f hf ↦ ?_)).mp hinside
      have hfF : f ∈ F := by
        have := Finset.mem_erase.mp hf |>.2
        simpa [F, D, radiusDeletedIncidentEdges] using this
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      exact and_congr (hagree f (by simpa [F, e] using hfF)) Iff.rfl
    have heOpenη : e ∈ η \ {g} := by
      exact ⟨(hagree e (by
        have heF : e ∈ F := radiusDeletedBoundaryEdges_subset_incidentEdges
          (by simpa [e] using heBoundary)
        simpa [F, e] using heF)).mp heOpen.1, heOpen.2⟩
    apply pivotalExplorationInside_and_off_imp_radiusConnectionEvent
      (e := e) (D := D) (near := a.toProd.1) (far := a.toProd.2)
      heval heE heOpenη hinsideη
    exact hRdiff hRη
  · intro hηdel
    obtain ⟨heOpen, hinside⟩ :=
      radiusConnectionEvent_imp_pivotalExplorationInside
        (e := e) (D := D) (near := a.toProd.1) (far := a.toProd.2)
        heval hxD hfar hDsphere hBoundaryη hηdel
    have hinsideω : ω \ {g} ∈ connectionEventIn d
        ((radiusIncidentEdgesOf d x n D).erase e) x a.toProd.1 := by
      apply (dependsOn_connectionEventIn d _ x a.toProd.1 (fun f hf ↦ ?_)).mpr hinside
      have hfF : f ∈ F := by
        have := Finset.mem_erase.mp hf |>.2
        simpa [F, D, radiusDeletedIncidentEdges] using this
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      exact and_congr (hagree f (by simpa [F, e] using hfF)) Iff.rfl
    have heOpenω : e ∈ ω \ {g} := by
      exact ⟨(hagree e (by
        have heF : e ∈ F := radiusDeletedBoundaryEdges_subset_incidentEdges
          (by simpa [e] using heBoundary)
        simpa [F, e] using heF)).mpr heOpen.1, heOpen.2⟩
    apply pivotalExplorationInside_and_off_imp_radiusConnectionEvent
      (e := e) (D := D) (near := a.toProd.1) (far := a.toProd.2)
      heval heE heOpenω hinsideω
    exact hRdiff hRω

theorem isPivotal_radiusConnectionEvent_iff_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η))
    {g : CubicEdge d}
    (hgF : g ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω) :
    IsPivotal (radiusConnectionEvent d x n) g ω ↔
      IsPivotal (radiusConnectionEvent d x n) g η := by
  let A := radiusConnectionEvent d x n
  have hinc := isIncreasingEvent_radiusConnectionEvent d x n
  rw [hinc.isPivotal_iff, hinc.isPivotal_iff]
  have hinsω : insert g ω ∈ A := hinc (Set.subset_insert g ω) hω
  have hinsη : insert g η ∈ A := hinc (Set.subset_insert g η) hη
  have hdiff := diff_mem_radiusConnectionEvent_iff_of_agree_pivotalExploration
    hω ha hη hagree hgF
  constructor
  · rintro ⟨_, hclosed⟩
    exact ⟨hinsη, fun hηdel ↦ hclosed (hdiff.mpr hηdel)⟩
  · rintro ⟨_, hclosed⟩
    exact ⟨hinsω, fun hωdel ↦ hclosed (hdiff.mp hωdel)⟩

/-- The marked oriented pivotal dart itself is fixed by its exploration
cylinder. -/
theorem pivotalDart_mem_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    a ∈ radiusPivotalDarts hη := by
  classical
  let e := cubicEdgeOfDart a
  let D := radiusDeletedReachableVertices d x n e ω
  have heF : e ∈ radiusDeletedIncidentEdges d x n e ω :=
    radiusDeletedBoundaryEdges_subset_incidentEdges
      (by simpa [e] using cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha)
  have hePivη : IsPivotal (radiusConnectionEvent d x n) e η :=
    (isPivotal_radiusConnectionEvent_iff_of_agree_pivotalExploration
      hω ha hη hagree heF).mp ((mem_radiusPivotalDarts_iff hω a).mp ha).2
  let Wη := canonicalRadiusWitness hη
  have heWalk : (e : Sym2 (Cubic d)) ∈ Wη.walk.edges :=
    pivotal_mem_witness_walk hη Wη.sphere_mem Wη.walk Wη.isOpen Wη.edge_subset hePivη
  rw [SimpleGraph.Walk.edges] at heWalk
  rcases List.mem_map.mp heWalk with ⟨c, hcW, hce⟩
  have hceSub : cubicEdgeOfDart c = e := by
    apply Subtype.ext
    exact hce
  have hcPiv : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart c) η := by
    rw [hceSub]
    exact hePivη
  have hc : c ∈ radiusPivotalDarts hη :=
    (mem_radiusPivotalDarts_iff hη c).mpr ⟨hcW, hcPiv⟩
  have hDη : D = radiusDeletedReachableVertices d x n e η := by
    simpa [D, e] using radiusDeletedReachableVertices_eq_of_agree_incident hagree
  have hcfst : c.toProd.1 ∈ D := by
    rw [hDη]
    simpa [hceSub] using pivotalDart_fst_mem_radiusDeletedReachableVertices hη hc
  have hasnd : a.toProd.2 ∉ D := by
    simpa [D, e] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hω ha
  have hsym : s(c.toProd.1, c.toProd.2) = s(a.toProd.1, a.toProd.2) := by
    have := congrArg Subtype.val hceSub
    change c.edge = a.edge at this
    exact this
  have hca : c = a := by
    rcases Sym2.eq_iff.mp hsym with h | h
    · exact SimpleGraph.Dart.ext c a (Prod.ext h.1 h.2)
    · exact (hasnd (h.1 ▸ hcfst)).elim
  rwa [← hca]

/-- Every pivotal dart no later than the marked dart is fixed by the larger
exploration cylinder. -/
theorem pivotalDart_mem_of_idxOf_le_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω)
    (hba : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
      (canonicalRadiusWitness hω).walk.darts.idxOf a)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    b ∈ radiusPivotalDarts hη := by
  apply pivotalDart_mem_of_agree_pivotalExploration hω hb hη
  intro f hf
  apply hagree f
  exact radiusDeletedIncidentEdges_subset_of_pivotalDart_idxOf_le
    hω ha hb hba hf

theorem radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω) :
    (radiusPivotalDarts hω).idxOf b ≤ (radiusPivotalDarts hω).idxOf a ↔
      (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf a := by
  classical
  let P := fun q : (cubicGraph d).Dart ↦
    decide (IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart q) ω)
  have haData := (mem_radiusPivotalDarts_iff hω a).mp ha
  have hbData := (mem_radiusPivotalDarts_iff hω b).mp hb
  have hPa : P a = true := by simp [P, haData.2]
  have hPb : P b = true := by simp [P, hbData.2]
  simpa [radiusPivotalDarts, P] using
    idxOf_filter_le_idxOf_filter_iff P (canonicalRadiusWitness hω).walk.darts
      hbData.1 haData.1 hPb hPa

theorem radiusPivotalDarts_pairwise_walk_idxOf_lt
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) :
    (radiusPivotalDarts hω).Pairwise fun a b ↦
      (canonicalRadiusWitness hω).walk.darts.idxOf a <
        (canonicalRadiusWitness hω).walk.darts.idxOf b := by
  classical
  have hpair := pairwise_idxOf_lt_of_nodup
    (SimpleGraph.Walk.darts_nodup_of_support_nodup
      (canonicalRadiusWitness hω).isPath.support_nodup)
  exact hpair.sublist List.filter_sublist

/-- The complete pivotal prefix through the marked dart is fixed by the
exploration cylinder.  This is the formal path-independence/order assertion
used in Grimmett's definition of `B_e`. -/
theorem radiusPivotalDarts_take_through_eq_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    (radiusPivotalDarts hω).take ((radiusPivotalDarts hω).idxOf a + 1) =
      (radiusPivotalDarts hη).take ((radiusPivotalDarts hη).idxOf a + 1) := by
  classical
  let Lω := radiusPivotalDarts hω
  let Lη := radiusPivotalDarts hη
  let Pω := Lω.take (Lω.idxOf a + 1)
  let Pη := Lη.take (Lη.idxOf a + 1)
  have haη : a ∈ Lη := pivotalDart_mem_of_agree_pivotalExploration hω ha hη hagree
  have hD := radiusDeletedReachableVertices_eq_of_agree_incident hagree
  have hF : radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω =
      radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) η := by
    unfold radiusDeletedIncidentEdges
    rw [hD]
  have hsubωη : Pω ⊆ Pη := by
    intro b hbP
    have hbω : b ∈ Lω := List.mem_of_mem_take hbP
    have hbIdxω : Lω.idxOf b ≤ Lω.idxOf a := by
      rw [List.mem_take_iff_idxOf_lt hbω] at hbP
      omega
    have hbRawω : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf a :=
      (radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le hω ha hbω).mp
        (by simpa [Lω] using hbIdxω)
    have hbη : b ∈ Lη := by
      simpa [Lη] using pivotalDart_mem_of_idxOf_le_of_agree_pivotalExploration
        hω ha hbω hbRawω hη hagree
    have hbFω : cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hω ha hbω).mpr hbRawω
    have hbFη : cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) η := by
      rw [← hF]
      exact hbFω
    have hbRawη : (canonicalRadiusWitness hη).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hη).walk.darts.idxOf a :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hη haη hbη).mp hbFη
    have hbIdxη : Lη.idxOf b ≤ Lη.idxOf a := by
      simpa [Lη] using
        (radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le hη haη hbη).mpr hbRawη
    change b ∈ Lη.take (Lη.idxOf a + 1)
    rw [List.mem_take_iff_idxOf_lt hbη]
    omega
  have hsubηω : Pη ⊆ Pω := by
    intro c hcP
    have hcη : c ∈ Lη := List.mem_of_mem_take hcP
    have hcIdxη : Lη.idxOf c ≤ Lη.idxOf a := by
      rw [List.mem_take_iff_idxOf_lt hcη] at hcP
      omega
    have hcRawη : (canonicalRadiusWitness hη).walk.darts.idxOf c ≤
        (canonicalRadiusWitness hη).walk.darts.idxOf a :=
      (radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le hη haη hcη).mp
        (by simpa [Lη] using hcIdxη)
    have hcFη : cubicEdgeOfDart c ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) η :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hη haη hcη).mpr hcRawη
    have hcFω : cubicEdgeOfDart c ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω := by
      rw [hF]
      exact hcFη
    have hcPivω : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart c) ω :=
      (isPivotal_radiusConnectionEvent_iff_of_agree_pivotalExploration
        hω ha hη hagree hcFω).mpr
          ((mem_radiusPivotalDarts_iff hη c).mp hcη).2
    let Wω := canonicalRadiusWitness hω
    have hcEdgeWω : (cubicEdgeOfDart c : Sym2 (Cubic d)) ∈ Wω.walk.edges :=
      pivotal_mem_witness_walk hω Wω.sphere_mem Wω.walk Wω.isOpen
        Wω.edge_subset hcPivω
    rw [SimpleGraph.Walk.edges] at hcEdgeWω
    rcases List.mem_map.mp hcEdgeWω with ⟨b, hbWω, hbcEdge⟩
    have hbEdge : cubicEdgeOfDart b = cubicEdgeOfDart c := Subtype.ext hbcEdge
    have hbPivω : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart b) ω := by
      rw [hbEdge]
      exact hcPivω
    have hbω : b ∈ Lω := by
      simpa [Lω] using (mem_radiusPivotalDarts_iff hω b).mpr ⟨hbWω, hbPivω⟩
    have hbFω : cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω := by
      rw [hbEdge]
      exact hcFω
    have hbRawω : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf a :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hω ha hbω).mp hbFω
    have hbη : b ∈ Lη := by
      simpa [Lη] using pivotalDart_mem_of_idxOf_le_of_agree_pivotalExploration
        hω ha hbω hbRawω hη hagree
    have hbc : b = c := by
      apply List.inj_on_of_nodup_map (f := SimpleGraph.Dart.edge)
        (l := (canonicalRadiusWitness hη).walk.darts)
        (by simpa [SimpleGraph.Walk.edges] using
          (canonicalRadiusWitness hη).isPath.isTrail.edges_nodup)
      · exact (mem_radiusPivotalDarts_iff hη b).mp (by simpa [Lη] using hbη) |>.1
      · exact (mem_radiusPivotalDarts_iff hη c).mp hcη |>.1
      · exact congrArg Subtype.val hbEdge
    have hbIdxω : Lω.idxOf b ≤ Lω.idxOf a := by
      simpa [Lω] using
        (radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le hω ha hbω).mpr hbRawω
    change c ∈ Lω.take (Lω.idxOf a + 1)
    rw [← hbc, List.mem_take_iff_idxOf_lt hbω]
    omega
  have hpairω : Pω.Pairwise fun b c ↦
      (canonicalRadiusWitness hω).walk.darts.idxOf b <
        (canonicalRadiusWitness hω).walk.darts.idxOf c := by
    simpa [Pω, Lω] using
      (radiusPivotalDarts_pairwise_walk_idxOf_lt hω).take
        (i := (radiusPivotalDarts hω).idxOf a + 1)
  have hpairηRaw := (radiusPivotalDarts_pairwise_walk_idxOf_lt hη).take
    (i := (radiusPivotalDarts hη).idxOf a + 1)
  have hpairη : Pη.Pairwise fun b c ↦
      (canonicalRadiusWitness hω).walk.darts.idxOf b <
        (canonicalRadiusWitness hω).walk.darts.idxOf c := by
    apply List.Pairwise.imp_of_mem _ hpairηRaw
    intro b c hbP hcP hbcη
    have hbPω := hsubηω hbP
    have hcPω := hsubηω hcP
    have hbω : b ∈ Lω := List.mem_of_mem_take hbPω
    have hcω : c ∈ Lω := List.mem_of_mem_take hcPω
    have hcIdxω : Lω.idxOf c ≤ Lω.idxOf a := by
      rw [List.mem_take_iff_idxOf_lt hcω] at hcPω
      omega
    have hcRawω : (canonicalRadiusWitness hω).walk.darts.idxOf c ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf a :=
      (radiusPivotalDarts_idxOf_le_iff_walk_idxOf_le hω ha hcω).mp
        (by simpa [Lω] using hcIdxω)
    have hFcSub := radiusDeletedIncidentEdges_subset_of_pivotalDart_idxOf_le
      hω ha hcω hcRawω
    have hagreeC : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart c) ω,
        (f ∈ ω ↔ f ∈ η) := fun f hf ↦ hagree f (hFcSub hf)
    have hDc := radiusDeletedReachableVertices_eq_of_agree_incident hagreeC
    have hFc : radiusDeletedIncidentEdges d x n (cubicEdgeOfDart c) ω =
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart c) η := by
      unfold radiusDeletedIncidentEdges
      rw [hDc]
    have hbη : b ∈ radiusPivotalDarts hη := by
      exact List.mem_of_mem_take hbP
    have hcη : c ∈ radiusPivotalDarts hη := by
      exact List.mem_of_mem_take hcP
    have hbRawηLe : (canonicalRadiusWitness hη).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hη).walk.darts.idxOf c := hbcη.le
    have hbFcη : cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart c) η :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hη hcη hbη).mpr hbRawηLe
    have hbFcω : cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart c) ω := by
      rw [hFc]
      exact hbFcη
    have hbRawωLe : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf c :=
      (pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le hω hcω hbω).mp hbFcω
    have hne : b ≠ c := by
      intro h
      subst c
      exact (Nat.lt_irrefl _ hbcη)
    have hbWω := (mem_radiusPivotalDarts_iff hω b).mp hbω |>.1
    have hidxne : (canonicalRadiusWitness hω).walk.darts.idxOf b ≠
        (canonicalRadiusWitness hω).walk.darts.idxOf c := by
      intro hidx
      exact hne ((List.idxOf_inj hbWω).mp hidx)
    omega
  simpa [Pω, Pη, Lω, Lη] using
    (List.Subset.antisymm_of_pairwise hpairω hpairη hsubωη hsubηω)

private theorem list_getElem?_eq_of_take_eq { α : Type* }
    {L M : List α} {k i : ℕ} (hLM : L.take k = M.take k) (hi : i < k) :
    L[i]? = M[i]? := by
  calc
    L[i]? = (L.take k)[i]? := (List.getElem?_take_of_lt hi).symm
    _ = (M.take k)[i]? := congrArg (fun q : List α ↦ q[i]?) hLM
    _ = M[i]? := List.getElem?_take_of_lt hi

private theorem sausageGapOfList_eq_of_take_eq
    {d k n : ℕ} {x : Cubic d} {L M : List ((cubicGraph d).Dart)}
    (hLM : L.take k = M.take k) :
    sausageGapOfList x n L k = sausageGapOfList x n M k := by
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero =>
          simp only [sausageGapOfList]
          rw [list_getElem?_eq_of_take_eq hLM (by omega)]
      | succ k =>
          simp only [sausageGapOfList]
          rw [list_getElem?_eq_of_take_eq hLM (i := k + 1) (by omega),
            list_getElem?_eq_of_take_eq hLM (i := k) (by omega)]

/-- All sausage gaps through the marked pivotal edge are fixed by the
exploration cylinder. -/
theorem sausageGap_eq_of_le_marked_idx_of_agree_pivotalExploration
    {d n k : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (hk : k ≤ (radiusPivotalDarts hω).idxOf a + 1)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    sausageGap d x n ω k = sausageGap d x n η k := by
  classical
  have haη := pivotalDart_mem_of_agree_pivotalExploration hω ha hη hagree
  have hprefix := radiusPivotalDarts_take_through_eq_of_agree_pivotalExploration
    hω ha hη hagree
  have hidx : (radiusPivotalDarts hω).idxOf a =
      (radiusPivotalDarts hη).idxOf a := by
    have haLenω : (radiusPivotalDarts hω).idxOf a <
        (radiusPivotalDarts hω).length := List.idxOf_lt_length_iff.2 ha
    have haLenη : (radiusPivotalDarts hη).idxOf a <
        (radiusPivotalDarts hη).length := List.idxOf_lt_length_iff.2 haη
    have hlen := congrArg List.length hprefix
    rw [List.length_take, List.length_take,
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)] at hlen
    omega
  have htake : (radiusPivotalDarts hω).take k =
      (radiusPivotalDarts hη).take k := by
    have := congrArg (List.take k) hprefix
    have hkη : k ≤ (radiusPivotalDarts hη).idxOf a + 1 := by omega
    rw [List.take_take, List.take_take, Nat.min_eq_left hk,
      Nat.min_eq_left hkη] at this
    exact this
  unfold sausageGap
  simp only [hω, hη, ↓reduceDIte]
  exact sausageGapOfList_eq_of_take_eq htake

/-- The event fixing all sausage gaps through a marked pivotal edge is a
cylinder event on that edge's finite exploration support, once the exterior
continuation `Aₙ` is required. -/
theorem mem_sausageGapPrefixEvent_of_agree_pivotalExploration
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d} {rs : List ℕ}
    (hω : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω.1)
    (hmark : (radiusPivotalDarts hω.1).idxOf a + 1 = rs.length)
    (hη : η ∈ radiusConnectionEvent d x n)
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω,
      (f ∈ ω ↔ f ∈ η)) :
    η ∈ sausageGapPrefixEvent d x n rs := by
  refine ⟨hη, ?_⟩
  intro i hi
  calc
    sausageGap d x n η (i + 1) = sausageGap d x n ω (i + 1) :=
      (sausageGap_eq_of_le_marked_idx_of_agree_pivotalExploration hω.1 ha
        (k := i + 1) (by omega) hη hagree).symm
    _ = rs[i] := hω.2 i hi

end Percolation

#print axioms Percolation.bernoulliBondMeasure_real_connectionEventOff_sphere_le
#print axioms Percolation.radiusPivotalDarts_take_through_eq_of_agree_pivotalExploration
#print axioms Percolation.mem_sausageGapPrefixEvent_of_agree_pivotalExploration
