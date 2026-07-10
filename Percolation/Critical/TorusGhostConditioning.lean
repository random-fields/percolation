import Percolation.Critical.TorusGhostJoint
import Percolation.Critical.TorusAnimals

/-!
# Finite-volume cluster conditioning for the ghost field

This file makes the conditioning steps in Grimmett's proofs of Lemmas 5.51 and 5.53
finite and explicit.  A discovered origin cluster fixes all incident edge coordinates and
all green coordinates on the cluster.  Connections which avoid that cluster ignore exactly
that coordinate block, so inhomogeneous finite-cube independence applies.
-/

namespace Percolation

open Set
open scoped BigOperators unitInterval Classical

noncomputable section

noncomputable def closedPivotalTrace {i : Type*}
    (T : Set (Finset i)) (e : i) : Set (Finset i) := by
  classical
  exact {s | e ∉ s ∧ s ∈ pivotalTrace T e}

/-- Pivotality ignores the pivotal coordinate, so its closed section has probability
`(1-p)` times the pivotal probability. -/
theorem finiteBernoulliProbability_closedPivotalTrace
    {i : Type*} [DecidableEq i] {E : Finset i} {T : Set (Finset i)}
    {e : i} (he : e ∈ E) (p : ℝ) :
    finiteBernoulliProbability E p (closedPivotalTrace T e) =
      (1 - p) * finiteBernoulliProbability E p (pivotalTrace T e) := by
  letI : DecidableEq i := Classical.decEq i
  let E₀ := E.erase e
  have he₀ : e ∉ E₀ := Finset.notMem_erase e E
  have hE : E = insert e E₀ := (Finset.insert_erase he).symm
  have hopenClosed : insertTraceSection e (closedPivotalTrace T e) = ∅ := by
    ext s
    simp [insertTraceSection, closedPivotalTrace]
  have hclosed : finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
      (closedPivotalTrace T e) =
      finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
        (pivotalTrace T e) := by
    apply finiteBernoulliProbabilityFamily_congr
    intro s hs
    have hes : e ∉ s := fun hes ↦ he₀ (Finset.mem_powerset.mp hs hes)
    simp [closedPivotalTrace, hes]
  have hopenPiv : insertTraceSection e (pivotalTrace T e) =
      pivotalTrace T e := by
    ext s
    change insert e s ∈ pivotalTrace T e ↔ s ∈ pivotalTrace T e
    simpa only [mem_pivotalTrace] using isPivotalTrace_insert T e s
  have hempty : finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
      (∅ : Set (Finset i)) = 0 := by
    unfold finiteBernoulliProbabilityFamily finiteBernoulliExpectationFamily
    simp
  calc
    finiteBernoulliProbability E p (closedPivotalTrace T e) =
        finiteBernoulliProbabilityFamily E (fun _ ↦ p)
          (closedPivotalTrace T e) :=
      (finiteBernoulliProbabilityFamily_const E p _).symm
    _ = p * finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
          (insertTraceSection e (closedPivotalTrace T e)) +
        (1 - p) * finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
          (closedPivotalTrace T e) := by
      rw [hE, finiteBernoulliProbabilityFamily_insert he₀]
    _ = (1 - p) * finiteBernoulliProbabilityFamily E₀ (fun _ ↦ p)
          (pivotalTrace T e) := by
      rw [hopenClosed, hempty, hclosed]
      ring
    _ = (1 - p) * finiteBernoulliProbabilityFamily E (fun _ ↦ p)
          (pivotalTrace T e) := by
      rw [hE, finiteBernoulliProbabilityFamily_insert he₀, hopenPiv]
      ring
    _ = (1 - p) * finiteBernoulliProbability E p (pivotalTrace T e) := by
      rw [finiteBernoulliProbabilityFamily_const]

def torusGhostClosedPivotalJointTrace (d N : ℕ)
    (e : CubicTorusEdge d N) : Set (Finset (TorusGhostCoordinate d N)) :=
  {s | s.toLeft ∈ closedPivotalTrace (torusHitEdgeTrace d N s.toRight) e}

theorem finiteBernoulliProbabilityFamily_torusGhostClosedPivotalJointTrace
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) (e : CubicTorusEdge d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClosedPivotalJointTrace d N e) =
      finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
        (fun G ↦ finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
          (closedPivotalTrace (torusHitEdgeTrace d N G) e)) := by
  unfold finiteBernoulliProbabilityFamily torusGhostCoordinateFinset
    torusGhostCoordinateDensity
  rw [finiteBernoulliExpectationFamily_disjSum_mixed]
  simp_rw [finiteBernoulliExpectationFamily_const]
  rw [finiteBernoulliExpectation_comm]
  apply finiteBernoulliExpectation_congr
  intro G hG
  unfold finiteBernoulliProbability
  apply finiteBernoulliExpectation_congr
  intro ω hω
  change (torusGhostClosedPivotalJointTrace d N e).indicator
      (fun _ ↦ (1 : ℝ)) (ω.disjSum G) =
    (closedPivotalTrace (torusHitEdgeTrace d N G) e).indicator
      (fun _ ↦ (1 : ℝ)) ω
  have hmem : ω.disjSum G ∈ torusGhostClosedPivotalJointTrace d N e ↔
      ω ∈ closedPivotalTrace (torusHitEdgeTrace d N G) e := by
    simp [torusGhostClosedPivotalJointTrace]
  by_cases h : ω.disjSum G ∈ torusGhostClosedPivotalJointTrace d N e
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem fun h' ↦ h (hmem.mpr h')]

/-- The left side of finite-volume Lemma 5.51 is the expected number of closed pivotal
edges in the joint edge/green cube. -/
theorem one_sub_mul_torusGhostThetaPDerivative_eq_sum_closedPivotal
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    (1 - (p : ℝ)) * torusGhostThetaPDerivative d N hN p γ =
      ∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClosedPivotalJointTrace d N e) := by
  simp_rw [finiteBernoulliProbabilityFamily_torusGhostClosedPivotalJointTrace]
  unfold torusGhostThetaPDerivative
  calc
    (1 - (p : ℝ)) *
        finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
          (fun G ↦ ∑ e ∈ cubicTorusEdgeFinset d N hN,
            finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
              (pivotalTrace (torusHitEdgeTrace d N G) e)) =
      finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
        (fun G ↦ (1 - (p : ℝ)) *
          (∑ e ∈ cubicTorusEdgeFinset d N hN,
            finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
              (pivotalTrace (torusHitEdgeTrace d N G) e))) := by
        rw [finiteBernoulliExpectation_const_mul]
    _ = finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
        (fun G ↦ ∑ e ∈ cubicTorusEdgeFinset d N hN,
          finiteBernoulliProbability (cubicTorusEdgeFinset d N hN) p
            (closedPivotalTrace (torusHitEdgeTrace d N G) e)) := by
      apply finiteBernoulliExpectation_congr
      intro G hG
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [finiteBernoulliProbability_closedPivotalTrace he]
    _ = ∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliExpectation (cubicTorusVertexFinset d N hN) γ
          (fun G ↦ finiteBernoulliProbability
            (cubicTorusEdgeFinset d N hN) p
            (closedPivotalTrace (torusHitEdgeTrace d N G) e)) := by
      rw [finiteBernoulliExpectation_finset_sum]

/-- Adding one edge to a closed configuration can enlarge the origin cluster only through
that edge.  The newly reached part is connected to the outside endpoint by an old-open walk
using no edge incident to the old cluster. -/
theorem mem_openCluster_insert_edge_cases
    (d N : ℕ) (hN : 2 ≤ N) (w : Finset (CubicTorusEdge d N))
    (e : CubicTorusEdge d N) {z : CubicTorus d N}
    (hz : z ∈ cubicTorusOpenCluster d N
      (insert e (w : Set (CubicTorusEdge d N)))) :
    z ∈ cubicTorusOpenCluster d N (w : Set (CubicTorusEdge d N)) ∨
      ∃ x ∈ e.1, x ∈ cubicTorusOpenCluster d N
          (w : Set (CubicTorusEdge d N)) ∧
        ∃ y ∈ e.1, y ∉ cubicTorusOpenCluster d N
            (w : Set (CubicTorusEdge d N)) ∧
          ∃ q : (cubicTorusGraph d N).Walk y z,
            torusWalkIsOpen (w : Set (CubicTorusEdge d N)) q ∧
              ∀ f : CubicTorusEdge d N, f.1 ∈ q.edges →
                f ∉ cubicTorusIncidentEdges d N hN
                  (cubicTorusOpenClusterFinset d N hN
                    (w : Set (CubicTorusEdge d N))) := by
  let C := cubicTorusOpenCluster d N (w : Set (CubicTorusEdge d N))
  let S := cubicTorusOpenClusterFinset d N hN
    (w : Set (CubicTorusEdge d N))
  have hmemS (v : CubicTorus d N) : v ∈ S ↔ v ∈ C := by
    exact mem_cubicTorusOpenClusterFinset hN
  obtain ⟨q, hq⟩ := hz
  have aux : ∀ {u v : CubicTorus d N}
      (q : (cubicTorusGraph d N).Walk u v), u ∈ C →
      torusWalkIsOpen (insert e (w : Set (CubicTorusEdge d N))) q →
      v ∈ C ∨
        ∃ x ∈ e.1, x ∈ C ∧ ∃ y ∈ e.1, y ∉ C ∧
          ∃ r : (cubicTorusGraph d N).Walk y v,
            torusWalkIsOpen (w : Set (CubicTorusEdge d N)) r ∧
              v ∉ C ∧
              ∀ f : CubicTorusEdge d N, f.1 ∈ r.edges →
                f ∉ cubicTorusIncidentEdges d N hN S := by
    intro u v q
    induction q using SimpleGraph.Walk.concatRec with
    | Hnil =>
        intro huC hopen
        exact Or.inl huC
    | @Hconcat u v t q hvt ih =>
        intro huC hopen
        have hopenq : torusWalkIsOpen
            (insert e (w : Set (CubicTorusEdge d N))) q := by
          intro f hf
          apply hopen f
          rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
            List.mem_append]
          exact Or.inl hf
        let f : CubicTorusEdge d N :=
          ⟨s(v, t), (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr hvt⟩
        have hfopen : f ∈ insert e (w : Set (CubicTorusEdge d N)) := by
          apply hopen f.1
          rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
            List.mem_append, List.mem_singleton]
          exact Or.inr rfl
        rcases ih huC hopenq with hvC |
          ⟨x, hxe, hxC, y, hye, hyC, r, hr, hvC, hav⟩
        · rcases hfopen with hfe | hfw
          · by_cases htC : t ∈ C
            · exact Or.inl htC
            · right
              refine ⟨v, ?_, hvC, t, ?_, htC, .nil, ?_, ?_, ?_⟩
              · have hval := congrArg Subtype.val hfe
                rw [← hval]
                simp [f]
              · have hval := congrArg Subtype.val hfe
                rw [← hval]
                simp [f]
              · intro g hg
                cases hg
              · exact htC
              · intro g hg
                cases hg
          · exact Or.inl (endpoint_mem_torusOpenCluster_of_open_incident
              hfw hvC (by simp [f]) (by simp [f]))
        · rcases hfopen with hfe | hfw
          · by_cases htC : t ∈ C
            · exact Or.inl htC
            · exfalso
              have hxy : x ≠ y := fun hxy ↦ hyC (hxy ▸ hxC)
              have hexy : e.1 = s(x, y) :=
                (Sym2.mem_and_mem_iff hxy).mp ⟨hxe, hye⟩
              have hfval := congrArg Subtype.val hfe
              have hpairs : s(v, t) = s(x, y) := hfval.trans hexy
              rcases Sym2.eq_iff.mp hpairs with hsame | hswap
              · exact hvC (hsame.1 ▸ hxC)
              · exact htC (hswap.2 ▸ hxC)
          · have htC : t ∉ C := by
              intro htC
              exact hvC (endpoint_mem_torusOpenCluster_of_open_incident
                hfw htC (by simp [f]) (by simp [f]))
            have hfAvoid : f ∉ cubicTorusIncidentEdges d N hN S := by
              intro hfInc
              obtain ⟨c, hcf, hcS⟩ := mem_cubicTorusIncidentEdges.mp hfInc
              have hcC := (hmemS c).mp hcS
              exact hvC (endpoint_mem_torusOpenCluster_of_open_incident
                hfw hcC hcf (by simp [f]))
            right
            refine ⟨x, hxe, hxC, y, hye, hyC, r.concat hvt, ?_, htC, ?_⟩
            · intro g hg
              rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
                List.mem_append, List.mem_singleton] at hg
              rcases hg with hg | hg
              · exact hr g hg
              · have hgf :
                    (⟨g, (r.concat hvt).edges_subset_edgeSet
                      (by rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
                        List.mem_append]; exact Or.inr (by simpa using hg))⟩ :
                      CubicTorusEdge d N) = f := by
                    apply Subtype.ext
                    simpa [f] using hg
                simpa [hgf] using hfw
            · intro g hg
              rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
                List.mem_append, List.mem_singleton] at hg
              rcases hg with hg | hg
              · exact hav g hg
              · have hgf : g = f := by
                    apply Subtype.ext
                    simpa [f] using hg
                simpa [hgf] using hfAvoid
  rcases aux q (cubicTorusOrigin_mem_openCluster d N
      (w : Set (CubicTorusEdge d N))) hq with hzC |
    ⟨x, hxe, hxC, y, hye, hyC, r, hr, hzC, hav⟩
  · exact Or.inl hzC
  · exact Or.inr ⟨x, hxe, hxC, y, hye, hyC, r, hr, hav⟩

namespace CubicTorusBondAnimal

noncomputable def ghostBlockSupport {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    Finset (TorusGhostCoordinate d N) :=
  (cubicTorusIncidentEdges d N hN A.vertices).disjSum A.vertices

noncomputable def ghostBlockPattern {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    Finset (TorusGhostCoordinate d N) :=
  A.edges.disjSum ∅

theorem ghostBlockPattern_subset_support {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    A.ghostBlockPattern ⊆ A.ghostBlockSupport :=
  Finset.disjSum_mono A.edges_subset_incident (Finset.empty_subset _)

theorem ghostBlockSupport_subset_coordinateFinset
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    A.ghostBlockSupport ⊆ torusGhostCoordinateFinset d N hN := by
  apply Finset.disjSum_mono
  · intro e he
    exact mem_cubicTorusEdgeFinset hN e
  · exact A.vertices_subset

theorem edges_union_boundary {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    A.edges ∪ A.boundary = cubicTorusIncidentEdges d N hN A.vertices := by
  unfold boundary
  exact Finset.union_sdiff_of_subset A.edges_subset_incident

theorem mem_ghostBlockCylinder_iff
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (s : Finset (TorusGhostCoordinate d N)) :
    s ∈ finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern ↔
      (s.toLeft : Set (CubicTorusEdge d N)) ∈ A.clusterCylinder ∧
        Disjoint A.vertices s.toRight := by
  unfold finiteTraceCylinder ghostBlockSupport ghostBlockPattern clusterCylinder
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have hleft : cubicTorusIncidentEdges d N hN A.vertices ∩ s.toLeft =
        A.edges := by
      apply Finset.ext
      intro e
      have hm := Finset.ext_iff.mp h (Sum.inl e)
      simpa using hm
    have hright : A.vertices ∩ s.toRight = ∅ := by
      apply Finset.ext
      intro x
      have hm := Finset.ext_iff.mp h (Sum.inr x)
      simpa using hm
    constructor
    · rw [mem_finiteCylinder]
      intro e he
      rw [A.edges_union_boundary] at he
      have hm := Finset.ext_iff.mp hleft e
      simpa [he] using hm
    · rw [Finset.disjoint_iff_inter_eq_empty]
      exact hright
  · rintro ⟨hedge, hgreen⟩
    apply Finset.ext
    intro a
    rcases a with e | x
    · have hinc_iff : e ∈ cubicTorusIncidentEdges d N hN A.vertices ∩ s.toLeft ↔
          e ∈ A.edges := by
        constructor
        · intro he
          have hmem := (mem_finiteCylinder.mp hedge) e
          rw [A.edges_union_boundary] at hmem
          exact (hmem (Finset.mem_inter.mp he).1).mp (Finset.mem_inter.mp he).2
        · intro he
          apply Finset.mem_inter.mpr
          refine ⟨A.edges_subset_incident he, ?_⟩
          exact (mem_finiteCylinder.mp hedge e
            (by rw [A.edges_union_boundary]; exact A.edges_subset_incident he)).mpr he
      simpa using hinc_iff
    · simp only [Finset.mem_inter, Finset.inr_mem_disjSum,
        Finset.notMem_empty, iff_false]
      rintro ⟨hxA, hxs⟩
      exact Finset.disjoint_left.mp hgreen hxA (Finset.mem_toRight.mpr hxs)

end CubicTorusBondAnimal

noncomputable def torusBoundarySteps (d N : ℕ)
    (S : Finset (CubicTorus d N)) :
    Finset (CubicTorus d N × CubicDirection d) :=
  (S ×ˢ (Finset.univ : Finset (CubicDirection d))).filter
    (fun xa ↦ cubicTorusStepFrom xa.1 xa.2 ∉ S)

@[simp]
theorem mem_torusBoundarySteps {d N : ℕ}
    {S : Finset (CubicTorus d N)} {x : CubicTorus d N}
    {a : CubicDirection d} :
    (x, a) ∈ torusBoundarySteps d N S ↔
      x ∈ S ∧ cubicTorusStepFrom x a ∉ S := by
  simp [torusBoundarySteps]

theorem torusBoundarySteps_card_le (d N : ℕ)
    (S : Finset (CubicTorus d N)) :
    (torusBoundarySteps d N S).card ≤ S.card * (2 * d) := by
  calc
    (torusBoundarySteps d N S).card ≤
        (S ×ˢ (Finset.univ : Finset (CubicDirection d))).card :=
      Finset.card_filter_le _ _
    _ = S.card * (d * 2) := by simp [Fintype.card_prod]
    _ = S.card * (2 * d) := by rw [Nat.mul_comm d 2]

/-- A connection from `y` to a green vertex using no edge incident to `S`. -/
def torusGhostReachAvoidingTrace (d N : ℕ) (hN : 2 ≤ N)
    (S : Finset (CubicTorus d N)) (y : CubicTorus d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  {s | ∃ z ∈ s.toRight, z ∉ S ∧
    ∃ w : (cubicTorusGraph d N).Walk y z,
      torusWalkIsOpen (s.toLeft : Set (CubicTorusEdge d N)) w ∧
        ∀ e : CubicTorusEdge d N, e.1 ∈ w.edges →
          e ∉ cubicTorusIncidentEdges d N hN S}

def torusGhostClusterBlockReachTrace
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN)
    (b : CubicTorus d N × CubicDirection d) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern ∩
    torusGhostReachAvoidingTrace d N hN A.vertices
      (cubicTorusStepFrom b.1 b.2)

noncomputable def torusGhostClusterBlockReachUnion
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (torusBoundarySteps d N A.vertices)
    (torusGhostClusterBlockReachTrace A)

noncomputable def torusGhostClusterBlockReachSizeUnion
    (d N n : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
    torusGhostClusterBlockReachUnion

noncomputable def torusGhostClusterBlockReachAll (d N : ℕ) (hN : 2 ≤ N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace
    (Finset.range ((cubicTorusVertexFinset d N hN).card + 1))
    (fun n ↦ torusGhostClusterBlockReachSizeUnion d N n hN)

noncomputable def torusBoundaryStepsForEdge (hN : 2 ≤ N)
    (S : Finset (CubicTorus d N)) (e : CubicTorusEdge d N) :
    Finset (CubicTorus d N × CubicDirection d) :=
  (torusBoundarySteps d N S).filter
    (fun b ↦ cubicTorusStepEdge hN b.1 b.2 = e)

noncomputable def torusGhostClusterBlockReachUnionForEdge
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (e : CubicTorusEdge d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (torusBoundaryStepsForEdge hN A.vertices e)
    (torusGhostClusterBlockReachTrace A)

noncomputable def torusGhostClusterBlockReachSizeUnionForEdge
    (d N n : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
    (fun A ↦ torusGhostClusterBlockReachUnionForEdge A e)

noncomputable def torusGhostClusterBlockReachAllForEdge
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N) :
    Set (Finset (TorusGhostCoordinate d N)) :=
  finsetUnionTrace
    (Finset.range ((cubicTorusVertexFinset d N hN).card + 1))
    (fun n ↦ torusGhostClusterBlockReachSizeUnionForEdge d N n hN e)

/-- Every closed pivotal configuration is covered by one green-free cluster block and one
outside connection indexed by an oriented boundary step. -/
theorem torusGhostClosedPivotalJointTrace_subset_clusterBlocks
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N) :
    torusGhostClosedPivotalJointTrace d N e ⊆
      torusGhostClusterBlockReachAllForEdge d N hN e := by
  intro s hs
  unfold torusGhostClusterBlockReachAllForEdge
    torusGhostClusterBlockReachSizeUnionForEdge
    torusGhostClusterBlockReachUnionForEdge finsetUnionTrace
  simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
  change ∃ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
    ∃ A : CubicTorusBondAnimal d N n hN,
      ∃ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
        s ∈ torusGhostClusterBlockReachTrace A b
  rcases hs with ⟨heClosed, hePiv⟩
  have hpiv := mem_pivotalTrace.mp hePiv
  have hpivCases :=
    (isIncreasingTrace_torusHitEdgeTrace d N s.toRight).isPivotalTrace_iff
      e s.toLeft |>.mp hpiv
  have hhitInsert := hpivCases.1
  have hnotHit : s.toLeft ∉ torusHitEdgeTrace d N s.toRight := by
    rintro ⟨z, hzG, q, hq⟩
    apply hpivCases.2
    refine ⟨z, hzG, q, ?_⟩
    intro f hf
    have hfOpen := hq f hf
    apply Finset.mem_coe.mpr
    simp only [Finset.mem_erase]
    exact ⟨fun hfe ↦ heClosed (hfe ▸ hfOpen), hfOpen⟩
  obtain ⟨z, hzG, hzInsert⟩ := hhitInsert
  have hzInsert' : z ∈ cubicTorusOpenCluster d N
      (insert e (s.toLeft : Set (CubicTorusEdge d N))) := by
    simpa using hzInsert
  rcases mem_openCluster_insert_edge_cases d N hN s.toLeft e hzInsert' with
    hzOld | ⟨x, hxe, hxOld, y, hye, hyOld, q, hqOpen, hqAvoid⟩
  · exact (hnotHit ⟨z, hzG, hzOld⟩).elim
  · let S := cubicTorusOpenClusterFinset d N hN
        (s.toLeft : Set (CubicTorusEdge d N))
    let n := S.card
    have hnRange : n ∈
        Finset.range ((cubicTorusVertexFinset d N hN).card + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.card_le_card (restrictTo_subset _ _))
    let A : CubicTorusBondAnimal d N n hN :=
      CubicTorusBondAnimal.ofConfiguration
        (s.toLeft : Set (CubicTorusEdge d N)) rfl
    have hgreen : Disjoint A.vertices s.toRight := by
      rw [Finset.disjoint_left]
      intro v hvA hvG
      apply hnotHit
      refine ⟨v, hvG, ?_⟩
      exact (mem_cubicTorusOpenClusterFinset hN).mp hvA
    have hblock : s ∈
        finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern :=
      (A.mem_ghostBlockCylinder_iff s).mpr
        ⟨CubicTorusBondAnimal.ofConfiguration_mem_clusterCylinder
          (s.toLeft : Set (CubicTorusEdge d N)) rfl, hgreen⟩
    have hxy : x ≠ y := fun hxy ↦ hyOld (hxy ▸ hxOld)
    have heq : e.1 = s(x, y) :=
      (Sym2.mem_and_mem_iff hxy).mp ⟨hxe, hye⟩
    have hxyAdj : (cubicTorusGraph d N).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]
      exact heq ▸ e.2
    obtain ⟨a, ha⟩ :=
      (cubicTorusGraph_adj_iff_exists_stepFrom hN x y).mp hxyAdj
    let b : CubicTorus d N × CubicDirection d := (x, a)
    have hb : b ∈ torusBoundarySteps d N A.vertices := by
      rw [mem_torusBoundarySteps]
      constructor
      · exact (mem_cubicTorusOpenClusterFinset hN).mpr hxOld
      · rw [← ha]
        intro hyA
        exact hyOld ((mem_cubicTorusOpenClusterFinset hN).mp hyA)
    have hbe : b ∈ torusBoundaryStepsForEdge hN A.vertices e := by
      rw [torusBoundaryStepsForEdge, Finset.mem_filter]
      refine ⟨hb, ?_⟩
      apply Subtype.ext
      change s(x, cubicTorusStepFrom x a) = e.1
      rw [← ha, ← heq]
    have hzOutside : z ∉ A.vertices := by
      intro hzA
      exact hnotHit ⟨z, hzG,
        (mem_cubicTorusOpenClusterFinset hN).mp hzA⟩
    have houtside : s ∈ torusGhostReachAvoidingTrace d N hN A.vertices
        (cubicTorusStepFrom b.1 b.2) := by
      refine ⟨z, hzG, hzOutside, q.copy ha rfl, ?_, ?_⟩
      · intro f hf
        apply hqOpen f
        simpa [SimpleGraph.Walk.edges_copy] using hf
      · intro f hf
        apply hqAvoid f
        simpa [SimpleGraph.Walk.edges_copy] using hf
    exact ⟨n, hnRange, A, b, hbe, hblock, houtside⟩

theorem torusGhostReachAvoidingTrace_subset_reach
    (d N : ℕ) (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (y : CubicTorus d N) :
    torusGhostReachAvoidingTrace d N hN S y ⊆
      torusGhostReachJointTrace d N y := by
  rintro s ⟨z, hzG, hzS, w, hw, hav⟩
  exact ⟨z, hzG, w, hw⟩

theorem traceIgnores_torusGhostReachAvoidingTrace
    (d N : ℕ) (hN : 2 ≤ N) (S : Finset (CubicTorus d N))
    (y : CubicTorus d N) :
    TraceIgnores
      ((cubicTorusIncidentEdges d N hN S).disjSum S)
      (torusGhostReachAvoidingTrace d N hN S y) := by
  intro s t hagree
  constructor
  · rintro ⟨z, hzG, hzS, w, hw, hav⟩
    have hzOutside : (Sum.inr z : TorusGhostCoordinate d N) ∉
        (cubicTorusIncidentEdges d N hN S).disjSum S := by
      simp [hzS]
    have hzGt : z ∈ t.toRight := by
      rw [Finset.mem_toRight]
      exact (hagree (Sum.inr z) hzOutside).mp (Finset.mem_toRight.mp hzG)
    refine ⟨z, hzGt, hzS, w, ?_, hav⟩
    intro e he
    let e' : CubicTorusEdge d N := ⟨e, w.edges_subset_edgeSet he⟩
    have heNot := hav e' he
    have heOutside : (Sum.inl e' : TorusGhostCoordinate d N) ∉
        (cubicTorusIncidentEdges d N hN S).disjSum S := by
      simp [heNot]
    have heOpen : e' ∈ s.toLeft := hw e he
    exact Finset.mem_toLeft.mpr ((hagree (Sum.inl e') heOutside).mp
      (Finset.mem_toLeft.mp heOpen))
  · rintro ⟨z, hzG, hzS, w, hw, hav⟩
    have hzOutside : (Sum.inr z : TorusGhostCoordinate d N) ∉
        (cubicTorusIncidentEdges d N hN S).disjSum S := by
      simp [hzS]
    have hzGs : z ∈ s.toRight := by
      rw [Finset.mem_toRight]
      exact (hagree (Sum.inr z) hzOutside).mpr (Finset.mem_toRight.mp hzG)
    refine ⟨z, hzGs, hzS, w, ?_, hav⟩
    intro e he
    let e' : CubicTorusEdge d N := ⟨e, w.edges_subset_edgeSet he⟩
    have heNot := hav e' he
    have heOutside : (Sum.inl e' : TorusGhostCoordinate d N) ∉
        (cubicTorusIncidentEdges d N hN S).disjSum S := by
      simp [heNot]
    have heOpen : e' ∈ t.toLeft := hw e he
    exact Finset.mem_toLeft.mpr ((hagree (Sum.inl e') heOutside).mpr
      (Finset.mem_toLeft.mp heOpen))

theorem finiteBernoulliProbabilityFamily_torusGhostReachAvoidingTrace_le_theta
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (S : Finset (CubicTorus d N)) (y : CubicTorus d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostReachAvoidingTrace d N hN S y) ≤
      torusGhostThetaPolynomial d N hN p γ := by
  calc
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostReachAvoidingTrace d N hN S y) ≤
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostReachJointTrace d N y) := by
      apply finiteBernoulliProbabilityFamily_mono
      · intro a ha
        rcases a with a | a <;>
          simp [torusGhostCoordinateDensity, p.2.1, γ.2.1]
      · intro a ha
        rcases a with a | a <;>
          simp [torusGhostCoordinateDensity, p.2.2, γ.2.2]
      · exact torusGhostReachAvoidingTrace_subset_reach d N hN S y
    _ = torusGhostThetaPolynomial d N hN p γ :=
      finiteBernoulliProbabilityFamily_torusGhostReachJointTrace d N hN p γ y

/-- The finite cluster/green-free block factors from any connection avoiding it. -/
theorem finiteBernoulliProbabilityFamily_ghostBlock_inter_reachAvoiding
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I) (y : CubicTorus d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern ∩
          torusGhostReachAvoidingTrace d N hN A.vertices y) =
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostReachAvoidingTrace d N hN A.vertices y) := by
  apply finiteBernoulliProbabilityFamily_finiteTraceCylinder_inter_indep
  · exact A.ghostBlockSupport_subset_coordinateFinset
  · exact A.ghostBlockPattern_subset_support
  · exact traceIgnores_torusGhostReachAvoidingTrace d N hN A.vertices y

theorem torusGhostCoordinateDensity_nonneg
    {d N : ℕ} {hN : 2 ≤ N} (p γ : I) :
    ∀ a ∈ torusGhostCoordinateFinset d N hN,
      0 ≤ torusGhostCoordinateDensity p γ a := by
  intro a ha
  rcases a with a | a <;>
    simp [torusGhostCoordinateDensity, p.2.1, γ.2.1]

theorem torusGhostCoordinateDensity_le_one
    {d N : ℕ} {hN : 2 ≤ N} (p γ : I) :
    ∀ a ∈ torusGhostCoordinateFinset d N hN,
      torusGhostCoordinateDensity p γ a ≤ 1 := by
  intro a ha
  rcases a with a | a <;>
    simp [torusGhostCoordinateDensity, p.2.2, γ.2.2]

theorem finiteBernoulliProbabilityFamily_ghostBlock
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) =
      (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card *
        (1 - (γ : ℝ)) ^ n := by
  rw [finiteBernoulliProbabilityFamily_finiteTraceCylinder
    (torusGhostCoordinateDensity p γ)
    A.ghostBlockSupport_subset_coordinateFinset
    A.ghostBlockPattern_subset_support]
  unfold CubicTorusBondAnimal.ghostBlockSupport
    CubicTorusBondAnimal.ghostBlockPattern torusGhostCoordinateDensity
  rw [finiteBernoulliWeightFamily_disjSum_mixed
    (fun _ : CubicTorusEdge d N ↦ (p : ℝ))
    (fun _ : CubicTorus d N ↦ (γ : ℝ))
    (Finset.disjSum_mono A.edges_subset_incident (Finset.empty_subset _))]
  simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
  rw [
    finiteBernoulliWeightFamily_const A.edges_subset_incident,
    finiteBernoulliWeightFamily_const (Finset.empty_subset A.vertices)]
  unfold finiteBernoulliWeight
  have hboundary :
      (cubicTorusIncidentEdges d N hN A.vertices).card - A.edges.card =
        A.boundary.card := by
    rw [CubicTorusBondAnimal.boundary,
      Finset.card_sdiff_of_subset A.edges_subset_incident]
  rw [hboundary, A.vertices_card]
  simp

theorem finiteBernoulliProbabilityFamily_ghostBlock_nonneg
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I) :
    0 ≤ finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
      (torusGhostCoordinateDensity p γ)
      (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) :=
  finiteBernoulliProbabilityFamily_nonneg
    (torusGhostCoordinateDensity_nonneg p γ)
    (torusGhostCoordinateDensity_le_one p γ) _

theorem torusGhostThetaPolynomial_nonneg_joint
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    0 ≤ torusGhostThetaPolynomial d N hN p γ := by
  rw [← finiteBernoulliProbabilityFamily_torusGhostHitJointTrace d N hN p γ]
  exact finiteBernoulliProbabilityFamily_nonneg
    (torusGhostCoordinateDensity_nonneg p γ)
    (torusGhostCoordinateDensity_le_one p γ) _

theorem finiteBernoulliProbabilityFamily_clusterBlockReach_le
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I)
    (b : CubicTorus d N × CubicDirection d) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachTrace A b) ≤
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
        torusGhostThetaPolynomial d N hN p γ := by
  unfold torusGhostClusterBlockReachTrace
  rw [finiteBernoulliProbabilityFamily_ghostBlock_inter_reachAvoiding]
  exact mul_le_mul_of_nonneg_left
    (finiteBernoulliProbabilityFamily_torusGhostReachAvoidingTrace_le_theta
      d N hN p γ A.vertices (cubicTorusStepFrom b.1 b.2))
    (finiteBernoulliProbabilityFamily_ghostBlock_nonneg A p γ)

theorem finiteBernoulliProbabilityFamily_clusterBlockReachUnion_le
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachUnion A) ≤
      (n * (2 * d) : ℕ) *
        (finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
        torusGhostThetaPolynomial d N hN p γ) := by
  let B := torusBoundarySteps d N A.vertices
  let c := finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
      (torusGhostCoordinateDensity p γ)
      (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
    torusGhostThetaPolynomial d N hN p γ
  have hc : 0 ≤ c := mul_nonneg
    (finiteBernoulliProbabilityFamily_ghostBlock_nonneg A p γ)
    (torusGhostThetaPolynomial_nonneg_joint d N hN p γ)
  calc
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachUnion A) ≤
      ∑ b ∈ B, finiteBernoulliProbabilityFamily
        (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachTrace A b) := by
      unfold torusGhostClusterBlockReachUnion B
      exact finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
        (torusGhostCoordinateDensity_nonneg p γ)
        (torusGhostCoordinateDensity_le_one p γ) _ _
    _ ≤ ∑ _b ∈ B, c := by
      apply Finset.sum_le_sum
      intro b hb
      exact finiteBernoulliProbabilityFamily_clusterBlockReach_le A p γ b
    _ = (B.card : ℝ) * c := by simp
    _ ≤ (n * (2 * d) : ℕ) * c := by
      apply mul_le_mul_of_nonneg_right _ hc
      exact_mod_cast (torusBoundarySteps_card_le d N A.vertices).trans_eq
        (by rw [A.vertices_card])

theorem sum_card_torusBoundaryStepsForEdge
    (d N : ℕ) (hN : 2 ≤ N) (S : Finset (CubicTorus d N)) :
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      (torusBoundaryStepsForEdge hN S e).card) =
      (torusBoundarySteps d N S).card := by
  simp_rw [torusBoundaryStepsForEdge, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  let e := cubicTorusStepEdge hN b.1 b.2
  rw [Finset.sum_eq_single e]
  · simp [e]
  · intro f hf hfe
    simp [e, hfe.symm]
  · intro heNot
    exact (heNot (mem_cubicTorusEdgeFinset hN e)).elim

theorem finiteBernoulliProbabilityFamily_clusterBlockReachAllForEdge_le_sum
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) (e : CubicTorusEdge d N) :
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachAllForEdge d N hN e) ≤
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        ∑ A : CubicTorusBondAnimal d N n hN,
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachUnionForEdge A e) := by
  calc
    finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachAllForEdge d N hN e) ≤
      ∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockReachSizeUnionForEdge d N n hN e) := by
      unfold torusGhostClusterBlockReachAllForEdge
      exact finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
        (torusGhostCoordinateDensity_nonneg p γ)
        (torusGhostCoordinateDensity_le_one p γ) _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      unfold torusGhostClusterBlockReachSizeUnionForEdge
      simpa using finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
        (E := torusGhostCoordinateFinset d N hN)
        (q := torusGhostCoordinateDensity p γ)
        (torusGhostCoordinateDensity_nonneg p γ)
        (torusGhostCoordinateDensity_le_one p γ)
        (Finset.univ : Finset (CubicTorusBondAnimal d N n hN))
        (fun A ↦ torusGhostClusterBlockReachUnionForEdge A e)

theorem sum_edge_clusterBlockReachUnionForEdge_le
    {d N n : ℕ} {hN : 2 ≤ N}
    (A : CubicTorusBondAnimal d N n hN) (p γ : I) :
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachUnionForEdge A e)) ≤
      (n * (2 * d) : ℕ) *
        (finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
        torusGhostThetaPolynomial d N hN p γ) := by
  let c := finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
      (torusGhostCoordinateDensity p γ)
      (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
    torusGhostThetaPolynomial d N hN p γ
  have hc : 0 ≤ c := mul_nonneg
    (finiteBernoulliProbabilityFamily_ghostBlock_nonneg A p γ)
    (torusGhostThetaPolynomial_nonneg_joint d N hN p γ)
  calc
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClusterBlockReachUnionForEdge A e)) ≤
      ∑ e ∈ cubicTorusEdgeFinset d N hN,
        ∑ b ∈ torusBoundaryStepsForEdge hN A.vertices e,
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachTrace A b) := by
      apply Finset.sum_le_sum
      intro e he
      unfold torusGhostClusterBlockReachUnionForEdge
      exact finiteBernoulliProbabilityFamily_finsetUnionTrace_le_sum
        (torusGhostCoordinateDensity_nonneg p γ)
        (torusGhostCoordinateDensity_le_one p γ) _ _
    _ ≤ ∑ e ∈ cubicTorusEdgeFinset d N hN,
        ∑ _b ∈ torusBoundaryStepsForEdge hN A.vertices e, c := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro b hb
      exact finiteBernoulliProbabilityFamily_clusterBlockReach_le A p γ b
    _ = ((∑ e ∈ cubicTorusEdgeFinset d N hN,
        (torusBoundaryStepsForEdge hN A.vertices e).card : ℕ) : ℝ) * c := by
      have hcast :
          ((∑ e ∈ cubicTorusEdgeFinset d N hN,
            (torusBoundaryStepsForEdge hN A.vertices e).card : ℕ) : ℝ) =
            ∑ e ∈ cubicTorusEdgeFinset d N hN,
              ((torusBoundaryStepsForEdge hN A.vertices e).card : ℝ) := by
        norm_cast
      rw [hcast, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      simp
    _ = ((torusBoundarySteps d N A.vertices).card : ℝ) * c := by
      rw [sum_card_torusBoundaryStepsForEdge]
    _ ≤ (n * (2 * d) : ℕ) * c := by
      apply mul_le_mul_of_nonneg_right _ hc
      exact_mod_cast (torusBoundarySteps_card_le d N A.vertices).trans_eq
        (by rw [A.vertices_card])

theorem sum_ghostBlockProbability_eq_clusterSizeProbability
    (d N n : ℕ) (hN : 2 ≤ N) (p γ : I) :
    (∑ A : CubicTorusBondAnimal d N n hN,
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern)) =
      (1 - (γ : ℝ)) ^ n * torusFiniteClusterSizeProbability d N hN p n := by
  simp_rw [finiteBernoulliProbabilityFamily_ghostBlock]
  rw [torusFiniteClusterSizeProbability_eq_sum_animals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  ring

/-- The animal-indexed green-free block mass, weighted by cluster size, is exactly the
finite ghost susceptibility. -/
theorem sum_ghostBlockProbability_mul_size_eq_susceptibility
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      (n : ℝ) *
        ∑ A : CubicTorusBondAnimal d N n hN,
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern)) =
      torusGhostSusceptibilityPolynomial d N hN p γ := by
  simp_rw [sum_ghostBlockProbability_eq_clusterSizeProbability]
  unfold torusGhostSusceptibilityPolynomial
  change (∑ n ∈ Finset.range ((cubicTorusVertexFinset d N hN).card + 1),
      (n : ℝ) * ((1 - (γ : ℝ)) ^ n *
        torusFiniteClusterSizeProbability d N hN p n)) =
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
      (fun ω ↦
        ((cubicTorusOpenClusterFinset d N hN
          (ω : Set (CubicTorusEdge d N))).card : ℝ) *
          (1 - (γ : ℝ)) ^
            (cubicTorusOpenClusterFinset d N hN
              (ω : Set (CubicTorusEdge d N))).card)
  rw [torusFiniteBernoulliExpectation_eq_sum_clusterSizes d N hN (p : ℝ)
    (fun n ↦ (n : ℝ) * (1 - (γ : ℝ)) ^ n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability]
  ring

/-- Finite-volume form of the cluster-conditioning estimate in (5.67): the expected
number of closed pivotal edges is at most `2d θ_N χ_N`. -/
theorem sum_torusGhostClosedPivotalJointTrace_le
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I) :
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClosedPivotalJointTrace d N e)) ≤
      (2 * d : ℕ) * torusGhostThetaPolynomial d N hN p γ *
        torusGhostSusceptibilityPolynomial d N hN p γ := by
  let R := Finset.range ((cubicTorusVertexFinset d N hN).card + 1)
  calc
    (∑ e ∈ cubicTorusEdgeFinset d N hN,
      finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
        (torusGhostCoordinateDensity p γ)
        (torusGhostClosedPivotalJointTrace d N e)) ≤
      ∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClusterBlockReachAllForEdge d N hN e) := by
      apply Finset.sum_le_sum
      intro e he
      apply finiteBernoulliProbabilityFamily_mono
      · exact torusGhostCoordinateDensity_nonneg p γ
      · exact torusGhostCoordinateDensity_le_one p γ
      · exact torusGhostClosedPivotalJointTrace_subset_clusterBlocks d N hN e
    _ ≤ ∑ e ∈ cubicTorusEdgeFinset d N hN,
        ∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachUnionForEdge A e) := by
      apply Finset.sum_le_sum
      intro e he
      exact finiteBernoulliProbabilityFamily_clusterBlockReachAllForEdge_le_sum
        d N hN p γ e
    _ = ∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
        ∑ e ∈ cubicTorusEdgeFinset d N hN,
          finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (torusGhostClusterBlockReachUnionForEdge A e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ ≤ ∑ n ∈ R, ∑ A : CubicTorusBondAnimal d N n hN,
        (n * (2 * d) : ℕ) *
          (finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
            (torusGhostCoordinateDensity p γ)
            (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
          torusGhostThetaPolynomial d N hN p γ) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro A hA
      exact sum_edge_clusterBlockReachUnionForEdge_le A p γ
    _ = (2 * d : ℕ) * torusGhostThetaPolynomial d N hN p γ *
        (∑ n ∈ R, (n : ℝ) *
          ∑ A : CubicTorusBondAnimal d N n hN,
            finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ A : CubicTorusBondAnimal d N n hN,
          (n * (2 * d) : ℕ) *
            (finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
              (torusGhostCoordinateDensity p γ)
              (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) *
            torusGhostThetaPolynomial d N hN p γ)) =
          ((n * (2 * d) : ℕ) * torusGhostThetaPolynomial d N hN p γ) *
            ∑ A : CubicTorusBondAnimal d N n hN,
              finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
                (torusGhostCoordinateDensity p γ)
                (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A hA
            ring
        _ = (2 * d : ℕ) * torusGhostThetaPolynomial d N hN p γ *
            ((n : ℝ) *
              ∑ A : CubicTorusBondAnimal d N n hN,
                finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
                  (torusGhostCoordinateDensity p γ)
                  (finiteTraceCylinder A.ghostBlockSupport A.ghostBlockPattern)) := by
            push_cast
            ring
    _ = (2 * d : ℕ) * torusGhostThetaPolynomial d N hN p γ *
        torusGhostSusceptibilityPolynomial d N hN p γ := by
      rw [sum_ghostBlockProbability_mul_size_eq_susceptibility]

/-- Finite-volume Lemma 5.51, equation (5.52). -/
theorem torusGhostTheta_p_deriv_le
    (d N : ℕ) (hN : 2 ≤ N) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    (1 - (p : ℝ)) * torusGhostThetaPDerivative d N hN p γ ≤
      (2 * d : ℕ) * (1 - (γ : ℝ)) *
        torusGhostThetaPolynomial d N hN p γ *
          torusGhostThetaGammaDerivative d N hN p γ := by
  calc
    (1 - (p : ℝ)) * torusGhostThetaPDerivative d N hN p γ =
      ∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliProbabilityFamily (torusGhostCoordinateFinset d N hN)
          (torusGhostCoordinateDensity p γ)
          (torusGhostClosedPivotalJointTrace d N e) :=
      one_sub_mul_torusGhostThetaPDerivative_eq_sum_closedPivotal d N hN p γ
    _ ≤ (2 * d : ℕ) * torusGhostThetaPolynomial d N hN p γ *
        torusGhostSusceptibilityPolynomial d N hN p γ :=
      sum_torusGhostClosedPivotalJointTrace_le d N hN p γ
    _ = (2 * d : ℕ) * (1 - (γ : ℝ)) *
        torusGhostThetaPolynomial d N hN p γ *
          torusGhostThetaGammaDerivative d N hN p γ := by
      rw [torusGhostSusceptibility_eq_one_sub_mul_gammaDerivative
        d N hN p γ hγ0 hγ1]
      ring

end

end Percolation
