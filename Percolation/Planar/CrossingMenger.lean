import Percolation.Planar.Crossings
import Percolation.Core.EdgeMengerToSet
import Percolation.Bernoulli.Sprinkling

/-!
# Rectangle crossings and finite terminal-set Menger

This module connects the finite square-lattice crossing event to the terminal-set Menger
infrastructure.  It is the deterministic bridge used by Grimmett Lemma 11.22 and equation
(7.75); no planar probability estimate is asserted here.
-/

namespace Percolation

open scoped unitInterval

/-- Vertices of the finite square-lattice rectangle, as a finite subtype. -/
abbrev SquareRectangleVertex (m n : ℕ) :=
  {x : SquareVertex // x ∈ squareRectangleVertices m n}

/-- The open graph induced on the finite rectangle. -/
noncomputable def squareRectangleOpenGraph (m n : ℕ) (ω : EdgeConfiguration 2) :
    SimpleGraph (SquareRectangleVertex m n) :=
  (cubicOpenGraph 2 ω).induce (squareRectangleVertices m n : Set SquareVertex)

/-- Left-side terminals in the finite induced graph. -/
noncomputable def squareRectangleLeftTerminals (m n : ℕ) :
    Finset (SquareRectangleVertex m n) :=
  Finset.univ.filter fun x ↦ x.1 ∈ squareRectangleLeft m n

/-- Right-side terminals in the finite induced graph. -/
noncomputable def squareRectangleRightTerminals (m n : ℕ) :
    Finset (SquareRectangleVertex m n) :=
  Finset.univ.filter fun x ↦ x.1 ∈ squareRectangleRight m n

@[simp]
theorem mem_squareRectangleLeftTerminals {m n : ℕ} {x : SquareRectangleVertex m n} :
    x ∈ squareRectangleLeftTerminals m n ↔ x.1 ∈ squareRectangleLeft m n := by
  simp [squareRectangleLeftTerminals]

@[simp]
theorem mem_squareRectangleRightTerminals {m n : ℕ} {x : SquareRectangleVertex m n} :
    x ∈ squareRectangleRightTerminals m n ↔ x.1 ∈ squareRectangleRight m n := by
  simp [squareRectangleRightTerminals]

/-- Forget the rectangle subtype while retaining open adjacency. -/
noncomputable def squareRectangleOpenGraphToOpenHom (m n : ℕ) (ω : EdgeConfiguration 2) :
    squareRectangleOpenGraph m n ω →g cubicOpenGraph 2 ω where
  toFun := Subtype.val
  map_rel' := SimpleGraph.induce_adj.mp

/-- The ambient square-lattice walk underlying a walk of the induced open rectangle graph. -/
noncomputable def ambientWalkOfSquareRectangleOpenWalk {m n : ℕ} {ω : EdgeConfiguration 2}
    {x y : SquareRectangleVertex m n}
    (w : (squareRectangleOpenGraph m n ω).Walk x y) :
    squareGraph.Walk x.1 y.1 :=
  (w.map (squareRectangleOpenGraphToOpenHom m n ω)).map (cubicOpenGraphHom 2 ω)

theorem walkIsOpen_ambientWalkOfSquareRectangleOpenWalk {m n : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareRectangleVertex m n}
    (w : (squareRectangleOpenGraph m n ω).Walk x y) :
    walkIsOpen ω (ambientWalkOfSquareRectangleOpenWalk w) :=
  walkIsOpen_map_cubicOpenGraphHom
    (w.map (squareRectangleOpenGraphToOpenHom m n ω))

theorem support_ambientWalkOfSquareRectangleOpenWalk_subset {m n : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareRectangleVertex m n}
    (w : (squareRectangleOpenGraph m n ω).Walk x y) :
    ∀ z ∈ (ambientWalkOfSquareRectangleOpenWalk w).support,
      z ∈ squareRectangleVertices m n := by
  intro z hz
  let wOpen := w.map (squareRectangleOpenGraphToOpenHom m n ω)
  have hsAmbient : (ambientWalkOfSquareRectangleOpenWalk w).support =
      wOpen.support.map (cubicOpenGraphHom 2 ω) :=
    by
      simpa [ambientWalkOfSquareRectangleOpenWalk, wOpen] using
        (SimpleGraph.Walk.support_map (cubicOpenGraphHom 2 ω) wOpen)
  have hzOpenMap : z ∈ wOpen.support.map (cubicOpenGraphHom 2 ω) :=
    (congrArg (fun l ↦ z ∈ l) hsAmbient).mp hz
  obtain ⟨z₀, hz₀, hz₀eq⟩ := List.mem_map.mp hzOpenMap
  have hz₀eq' : z₀ = z := by simpa [cubicOpenGraphHom] using hz₀eq
  subst z₀
  have hsOpen : wOpen.support =
      w.support.map (squareRectangleOpenGraphToOpenHom m n ω) :=
    SimpleGraph.Walk.support_map (squareRectangleOpenGraphToOpenHom m n ω) w
  have hzSubtypeMap : z ∈ w.support.map (squareRectangleOpenGraphToOpenHom m n ω) :=
    (congrArg (fun l ↦ z ∈ l) hsOpen).mp hz₀
  obtain ⟨z₁, _hz₁, hz₁eq⟩ := List.mem_map.mp hzSubtypeMap
  have : z₁.1 = z := by simpa [squareRectangleOpenGraphToOpenHom] using hz₁eq
  rw [← this]
  exact z₁.2

theorem edge_subset_ambientWalkOfSquareRectangleOpenWalk {m n : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareRectangleVertex m n}
    (w : (squareRectangleOpenGraph m n ω).Walk x y) :
    walkEdgeFinset (ambientWalkOfSquareRectangleOpenWalk w) ⊆
      squareRectangleEdges m n :=
  walkEdgeFinset_subset_squareRectangleEdges_of_support _
    (support_ambientWalkOfSquareRectangleOpenWalk_subset w)

/-- A finite-graph terminal walk gives a source-facing open crossing record. -/
noncomputable def openSquareRectangleCrossingOfWalkBetween {m n : ℕ}
    {ω : EdgeConfiguration 2}
    (P : EdgeMenger.WalkBetweenFinsets (squareRectangleOpenGraph m n ω)
      (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n)) :
    OpenSquareRectangleCrossing m n ω where
  start := P.start.1.1
  finish := P.finish.1.1
  walk := ambientWalkOfSquareRectangleOpenWalk P.walk
  start_mem := mem_squareRectangleLeftTerminals.mp P.start.2
  finish_mem := mem_squareRectangleRightTerminals.mp P.finish.2
  isOpen := walkIsOpen_ambientWalkOfSquareRectangleOpenWalk P.walk
  edges_subset := edge_subset_ambientWalkOfSquareRectangleOpenWalk P.walk

private theorem support_subset_squareRectangleVertices_of_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n ω) :
    ∀ z ∈ C.walk.support, z ∈ squareRectangleVertices m n := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact (Finset.mem_filter.mp C.finish_mem).1
  · let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
    have he' : e' ∈ walkEdgeFinset C.walk := (mem_walkEdgeFinset_iff C.walk e').mpr he
    exact endpoint_mem_squareRectangle_of_edge_mem (C.edges_subset he') hze

private theorem edge_mem_cubicOpenGraph_of_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n ω) (e : Sym2 SquareVertex)
    (he : e ∈ C.walk.edges) : e ∈ (cubicOpenGraph 2 ω).edgeSet := by
  let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
  have hopen : e' ∈ ω := C.isOpen e' he
  let u := e.out.1
  let v := e.out.2
  have hadj : squareGraph.Adj u v := by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [u, v, e.out_eq] using C.walk.edges_subset_edgeSet he
  rw [← e.out_eq, SimpleGraph.mem_edgeSet]
  apply cubicOpenGraph_adj.mpr
  refine ⟨hadj, ?_⟩
  have heq :
      (⟨s(u, v), (SimpleGraph.mem_edgeSet squareGraph).mpr hadj⟩ : SquareEdge) = e' := by
    apply Subtype.ext
    exact e.out_eq
  rw [heq]
  exact hopen

/-- A source-facing open crossing can be lifted to a walk of the finite induced open graph. -/
noncomputable def walkBetweenFinsetsOfOpenSquareRectangleCrossing {m n : ℕ}
    {ω : EdgeConfiguration 2} (C : OpenSquareRectangleCrossing m n ω) :
    EdgeMenger.WalkBetweenFinsets (squareRectangleOpenGraph m n ω)
      (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n) := by
  let wOpen : (cubicOpenGraph 2 ω).Walk C.start C.finish :=
    C.walk.transfer (cubicOpenGraph 2 ω) (edge_mem_cubicOpenGraph_of_crossing C)
  have hsupport : ∀ z ∈ wOpen.support, z ∈ squareRectangleVertices m n := by
    intro z hz
    apply support_subset_squareRectangleVertices_of_crossing C z
    simpa [wOpen, SimpleGraph.Walk.support_transfer] using hz
  let wInd := wOpen.induce (squareRectangleVertices m n : Set SquareVertex) hsupport
  let start : {v // v ∈ squareRectangleLeftTerminals m n} :=
    ⟨⟨C.start, (Finset.mem_filter.mp C.start_mem).1⟩,
      mem_squareRectangleLeftTerminals.mpr C.start_mem⟩
  let finish : {v // v ∈ squareRectangleRightTerminals m n} :=
    ⟨⟨C.finish, (Finset.mem_filter.mp C.finish_mem).1⟩,
      mem_squareRectangleRightTerminals.mpr C.finish_mem⟩
  exact
    { start := start
      finish := finish
      walk := wInd.copy rfl rfl }

theorem edges_ambientWalkOfSquareRectangleOpenWalk {m n : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareRectangleVertex m n}
    (w : (squareRectangleOpenGraph m n ω).Walk x y) :
    (ambientWalkOfSquareRectangleOpenWalk w).edges =
      w.edges.map (Sym2.map Subtype.val) := by
  let h := squareRectangleOpenGraphToOpenHom m n ω
  let q := w.map h
  have hq : (q.map (cubicOpenGraphHom 2 ω)).edges =
      q.edges.map (Sym2.map (cubicOpenGraphHom 2 ω)) :=
    SimpleGraph.Walk.edges_map (cubicOpenGraphHom 2 ω) q
  have hw : q.edges = w.edges.map (Sym2.map h) :=
    SimpleGraph.Walk.edges_map h w
  calc
    (ambientWalkOfSquareRectangleOpenWalk w).edges =
        q.edges.map (Sym2.map (cubicOpenGraphHom 2 ω)) := by
      simpa [ambientWalkOfSquareRectangleOpenWalk, q, h] using hq
    _ = (w.edges.map (Sym2.map h)).map
        (Sym2.map (cubicOpenGraphHom 2 ω)) := by rw [hw]
    _ = w.edges.map (Sym2.map Subtype.val) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _he
      change Sym2.map (cubicOpenGraphHom 2 ω) (Sym2.map h e) =
        Sym2.map Subtype.val e
      rw [Sym2.map_map]
      apply Sym2.map_congr
      intro z _hz
      rfl

private theorem edges_walkBetweenFinsetsOfOpenSquareRectangleCrossing_map
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (C : OpenSquareRectangleCrossing m n ω) :
    (walkBetweenFinsetsOfOpenSquareRectangleCrossing C).walk.edges.map
        (Sym2.map Subtype.val) = C.walk.edges := by
  classical
  unfold walkBetweenFinsetsOfOpenSquareRectangleCrossing
  dsimp only
  let wOpen : (cubicOpenGraph 2 ω).Walk C.start C.finish :=
    C.walk.transfer (cubicOpenGraph 2 ω) (edge_mem_cubicOpenGraph_of_crossing C)
  have hsupport : ∀ z ∈ wOpen.support, z ∈ squareRectangleVertices m n := by
    intro z hz
    apply support_subset_squareRectangleVertices_of_crossing C z
    simpa [wOpen, SimpleGraph.Walk.support_transfer] using hz
  let wInd := wOpen.induce (squareRectangleVertices m n : Set SquareVertex) hsupport
  have hmap := congrArg SimpleGraph.Walk.edges
    (SimpleGraph.Walk.map_induce wOpen hsupport)
  rw [SimpleGraph.Walk.edges_map] at hmap
  calc
    (wInd.copy rfl rfl).edges.map (Sym2.map Subtype.val) =
        wInd.edges.map (Sym2.map Subtype.val) := by simp
    _ = wOpen.edges := by simpa [wInd] using hmap
    _ = C.walk.edges := SimpleGraph.Walk.edges_transfer C.walk _

/-- The finite-graph terminal formulation and the source-facing crossing-family formulation
carry exactly the same edge-disjointness information. -/
theorem hasEdgeDisjointSquareRectangleCrossings_iff_terminalWalks
    (m n k : ℕ) (ω : EdgeConfiguration 2) :
    HasEdgeDisjointSquareRectangleCrossings m n k ω ↔
      ∃ P : Fin k → EdgeMenger.WalkBetweenFinsets (squareRectangleOpenGraph m n ω)
        (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n),
        Pairwise fun i j ↦ (P i).walk.edges.Disjoint (P j).walk.edges := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    let P : Fin k → EdgeMenger.WalkBetweenFinsets (squareRectangleOpenGraph m n ω)
        (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n) :=
      fun i ↦ walkBetweenFinsetsOfOpenSquareRectangleCrossing (C i)
    refine ⟨P, ?_⟩
    intro i j hij
    rw [List.disjoint_left]
    intro e hei hej
    have hmapI : Sym2.map Subtype.val e ∈ (C i).walk.edges := by
      have heMap : Sym2.map Subtype.val e ∈
          (P i).walk.edges.map (Sym2.map Subtype.val) :=
        List.mem_map.mpr ⟨e, hei, rfl⟩
      change Sym2.map Subtype.val e ∈
        (walkBetweenFinsetsOfOpenSquareRectangleCrossing (C i)).walk.edges.map
          (Sym2.map Subtype.val) at heMap
      exact (congrArg (fun l ↦ Sym2.map Subtype.val e ∈ l)
        (edges_walkBetweenFinsetsOfOpenSquareRectangleCrossing_map (C i))).mp heMap
    have hmapJ : Sym2.map Subtype.val e ∈ (C j).walk.edges := by
      have heMap : Sym2.map Subtype.val e ∈
          (P j).walk.edges.map (Sym2.map Subtype.val) :=
        List.mem_map.mpr ⟨e, hej, rfl⟩
      change Sym2.map Subtype.val e ∈
        (walkBetweenFinsetsOfOpenSquareRectangleCrossing (C j)).walk.edges.map
          (Sym2.map Subtype.val) at heMap
      exact (congrArg (fun l ↦ Sym2.map Subtype.val e ∈ l)
        (edges_walkBetweenFinsetsOfOpenSquareRectangleCrossing_map (C j))).mp heMap
    let e' : SquareEdge :=
      ⟨Sym2.map Subtype.val e,
        (C i).walk.edges_subset_edgeSet hmapI⟩
    have heFi : e' ∈ walkEdgeFinset (C i).walk :=
      (mem_walkEdgeFinset_iff (C i).walk e').mpr hmapI
    have heFj : e' ∈ walkEdgeFinset (C j).walk := by
      apply (mem_walkEdgeFinset_iff (C j).walk e').mpr
      simpa [e'] using hmapJ
    exact Finset.disjoint_left.mp (hC hij) heFi heFj
  · rintro ⟨P, hP⟩
    let C : Fin k → OpenSquareRectangleCrossing m n ω := fun i ↦
      openSquareRectangleCrossingOfWalkBetween (P i)
    refine ⟨C, ?_⟩
    intro i j hij
    rw [Finset.disjoint_left]
    intro e hei hej
    have hei' : (e : Sym2 SquareVertex) ∈
        (ambientWalkOfSquareRectangleOpenWalk (P i).walk).edges :=
      (mem_walkEdgeFinset_iff _ e).mp hei
    have hej' : (e : Sym2 SquareVertex) ∈
        (ambientWalkOfSquareRectangleOpenWalk (P j).walk).edges :=
      (mem_walkEdgeFinset_iff _ e).mp hej
    rw [edges_ambientWalkOfSquareRectangleOpenWalk] at hei' hej'
    obtain ⟨ei, heiP, heiEq⟩ := List.mem_map.mp hei'
    obtain ⟨ej, hejP, hejEq⟩ := List.mem_map.mp hej'
    have heij : ei = ej := by
      apply Sym2.map.injective Subtype.val_injective
      exact heiEq.trans hejEq.symm
    exact List.disjoint_left.mp (hP hij) heiP (heij ▸ hejP)

/-- Rectangle crossings survive every cut of fewer than `k` open rectangle edges exactly when
there are `k` pairwise edge-disjoint crossings. -/
theorem hasEdgeDisjointSquareRectangleCrossings_iff_isEdgeReachableBetweenFinsets
    (m n k : ℕ) (ω : EdgeConfiguration 2) :
    HasEdgeDisjointSquareRectangleCrossings m n k ω ↔
      EdgeMenger.IsEdgeReachableBetweenFinsets (squareRectangleOpenGraph m n ω) k
        (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n) :=
  (hasEdgeDisjointSquareRectangleCrossings_iff_terminalWalks m n k ω).trans
    EdgeMenger.isEdgeReachableBetweenFinsets_iff_exists_pairwise_edgeDisjoint_walks.symm

/-- Monotonicity of the induced rectangle open graph under inclusion of configurations. -/
noncomputable def squareRectangleOpenGraphMonoHom {m n : ℕ}
    {ω η : EdgeConfiguration 2} (hωη : ω ⊆ η) :
    squareRectangleOpenGraph m n ω →g squareRectangleOpenGraph m n η where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply SimpleGraph.induce_adj.mpr
    obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp (SimpleGraph.induce_adj.mp hxy)
    exact cubicOpenGraph_adj.mpr ⟨hadj, hωη hopen⟩

/-- The ambient square-lattice edge represented by an edge of the finite rectangle open graph. -/
noncomputable def squareEdgeOfRectangleOpenEdge {m n : ℕ} {ω : EdgeConfiguration 2}
    (e : (squareRectangleOpenGraph m n ω).edgeSet) : SquareEdge := by
  let f : squareRectangleOpenGraph m n ω →g squareGraph :=
    (cubicOpenGraphHom 2 ω).comp (squareRectangleOpenGraphToOpenHom m n ω)
  exact ⟨Sym2.map f e.1, f.map_mem_edgeSet e.2⟩

theorem squareEdgeOfRectangleOpenEdge_val {m n : ℕ} {ω : EdgeConfiguration 2}
    (e : (squareRectangleOpenGraph m n ω).edgeSet) :
    (squareEdgeOfRectangleOpenEdge e : Sym2 SquareVertex) =
      Sym2.map Subtype.val e.1 := by
  apply Sym2.map_congr
  intro x _hx
  rfl

theorem squareEdgeOfRectangleOpenEdge_injective {m n : ℕ}
    {ω : EdgeConfiguration 2} :
    Function.Injective (squareEdgeOfRectangleOpenEdge
      (m := m) (n := n) (ω := ω)) := by
  intro e f hef
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  have hval := congrArg (fun q : SquareEdge ↦ (q : Sym2 SquareVertex)) hef
  simpa [squareEdgeOfRectangleOpenEdge_val] using hval

theorem squareEdgeOfRectangleOpenEdge_mem_configuration {m n : ℕ}
    {ω : EdgeConfiguration 2}
    (e : (squareRectangleOpenGraph m n ω).edgeSet) :
    squareEdgeOfRectangleOpenEdge e ∈ ω := by
  let u := e.1.out.1
  let v := e.1.out.2
  have hadjRect : (squareRectangleOpenGraph m n ω).Adj u v := by
    rw [← SimpleGraph.mem_edgeSet]
    change s(e.1.out.1, e.1.out.2) ∈ (squareRectangleOpenGraph m n ω).edgeSet
    exact (congrArg (fun q ↦ q ∈ (squareRectangleOpenGraph m n ω).edgeSet)
      e.1.out_eq).mpr e.2
  obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp
    (SimpleGraph.induce_adj.mp hadjRect)
  have heq : squareEdgeOfRectangleOpenEdge e =
      (⟨s(u.1, v.1), (SimpleGraph.mem_edgeSet squareGraph).mpr hadj⟩ : SquareEdge) := by
    apply Subtype.ext
    rw [squareEdgeOfRectangleOpenEdge_val]
    calc
      Sym2.map Subtype.val e.1 =
          Sym2.map Subtype.val s(e.1.out.1, e.1.out.2) :=
        congrArg (Sym2.map Subtype.val) e.1.out_eq.symm
      _ = s(u.1, v.1) := by rfl
  rw [heq]
  exact hopen

noncomputable def squareEdgeOfRectangleOpenEdgeEmbedding {m n : ℕ}
    {ω : EdgeConfiguration 2} :
    (squareRectangleOpenGraph m n ω).edgeSet ↪ SquareEdge where
  toFun := squareEdgeOfRectangleOpenEdge
  inj' := squareEdgeOfRectangleOpenEdge_injective

/-- For an increasing event, membership in its Hamming interior is equivalent to survival
after closing each finite set of at most `r` coordinates. -/
theorem IsIncreasingEvent.mem_interiorDepth_iff_diff_finset {ι : Type*}
    {A : Set (Set ι)} (hA : IsIncreasingEvent A) (r : ℕ) (ω : Set ι) :
    ω ∈ interiorDepth r A ↔
      ∀ D : Finset ι, D.card ≤ r → ω \ (D : Set ι) ∈ A := by
  constructor
  · intro hω D hD
    apply hω (ω \ (D : Set ι))
    exact ⟨D, hD, fun e he ↦ by simp [he]⟩
  · intro hclose ω' hnear
    obtain ⟨D, hD, hagree⟩ := hnear
    refine hA ?_ (hclose D hD)
    intro e he
    have heD : e ∉ D := he.2
    exact (hagree e heD).mp he.1

private theorem exists_crossing_disjoint_finset_of_card_lt
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hcross : HasEdgeDisjointSquareRectangleCrossings m n k ω)
    (D : Finset SquareEdge) (hD : D.card < k) :
    ∃ C : OpenSquareRectangleCrossing m n ω,
      Disjoint (walkEdgeFinset C.walk) D := by
  classical
  obtain ⟨C, hC⟩ := hcross
  by_contra hno
  push Not at hno
  have hall : ∀ i : Fin k, ∃ e, e ∈ walkEdgeFinset (C i).walk ∧ e ∈ D := by
    intro i
    exact Finset.not_disjoint_iff.mp (hno (C i))
  let chosen : Fin k → SquareEdge := fun i ↦ Classical.choose (hall i)
  have chosen_mem_walk (i : Fin k) : chosen i ∈ walkEdgeFinset (C i).walk :=
    (Classical.choose_spec (hall i)).1
  have chosen_mem_D (i : Fin k) : chosen i ∈ D :=
    (Classical.choose_spec (hall i)).2
  let f : Fin k → {e // e ∈ D} := fun i ↦ ⟨chosen i, chosen_mem_D i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hchosen : chosen i = chosen j := Subtype.ext_iff.mp hij
    exact Finset.disjoint_left.mp (hC hne) (chosen_mem_walk i)
      (hchosen ▸ chosen_mem_walk j)
  have hk : k ≤ D.card := by
    simpa using Fintype.card_le_of_injective f hf
  omega

/-- `r+1` edge-disjoint crossings remain a crossing after any Hamming perturbation of at most
`r` coordinates.  This is the easy direction of the Lemma 11.22 interior-depth adapter. -/
theorem hasEdgeDisjointSquareRectangleCrossings_imp_mem_interiorDepth
    {m n r : ℕ} {ω : EdgeConfiguration 2}
    (hcross : HasEdgeDisjointSquareRectangleCrossings m n (r + 1) ω) :
    ω ∈ interiorDepth r (squareRectangleCrossingEvent m n) := by
  rw [(isIncreasingEvent_squareRectangleCrossingEvent m n).mem_interiorDepth_iff_diff_finset]
  intro D hD
  obtain ⟨C, hCD⟩ := exists_crossing_disjoint_finset_of_card_lt hcross D (by omega)
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
  refine ⟨C.start, C.start_mem, C.finish, C.finish_mem, C.walk, ?_, C.edges_subset⟩
  intro e he
  let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
  have heFin : e' ∈ walkEdgeFinset C.walk :=
    (mem_walkEdgeFinset_iff C.walk e').mpr he
  exact ⟨C.isOpen e he, Finset.disjoint_left.mp hCD heFin⟩

/-- A configuration in the depth-`r` crossing interior survives every cut of fewer than
`r+1` edges in the finite induced open graph. -/
theorem mem_interiorDepth_imp_isEdgeReachableBetweenFinsets
    {m n r : ℕ} {ω : EdgeConfiguration 2}
    (hω : ω ∈ interiorDepth r (squareRectangleCrossingEvent m n)) :
    EdgeMenger.IsEdgeReachableBetweenFinsets (squareRectangleOpenGraph m n ω) (r + 1)
      (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n) := by
  classical
  rw [(isIncreasingEvent_squareRectangleCrossingEvent m n).mem_interiorDepth_iff_diff_finset]
    at hω
  intro s hs
  let H := squareRectangleOpenGraph m n ω
  have hsFinite : s.Finite := Set.finite_of_encard_le_coe hs.le
  let R : Finset H.edgeSet := Finset.univ.filter fun e ↦ e.1 ∈ s
  let edgeValEmbedding : H.edgeSet ↪ Sym2 (SquareRectangleVertex m n) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hRsubset : R.map edgeValEmbedding ⊆ hsFinite.toFinset := by
    intro e he
    obtain ⟨eH, heHR, rfl⟩ := Finset.mem_map.mp he
    have heS : eH.1 ∈ s := (Finset.mem_filter.mp heHR).2
    simpa using heS
  have hRcard : R.card ≤ hsFinite.toFinset.card := by
    rw [← Finset.card_map edgeValEmbedding]
    exact Finset.card_le_card hRsubset
  have hsCard : hsFinite.toFinset.card < r + 1 := by
    rw [← ENat.coe_lt_coe, ← hsFinite.encard_eq_coe_toFinset_card]
    exact hs
  let D : Finset SquareEdge := R.map squareEdgeOfRectangleOpenEdgeEmbedding
  have hD : D.card ≤ r := by
    have hDR : D.card = R.card := Finset.card_map _
    omega
  have hcross : ω \ (D : Set SquareEdge) ∈ squareRectangleCrossingEvent m n := hω D hD
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hcross
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := hcross
  let C : OpenSquareRectangleCrossing m n (ω \ (D : Set SquareEdge)) :=
    { start := x
      finish := y
      walk := w
      start_mem := hx
      finish_mem := hy
      isOpen := hwOpen
      edges_subset := hwEdges }
  let Pη := walkBetweenFinsetsOfOpenSquareRectangleCrossing C
  have hηω : ω \ (D : Set SquareEdge) ⊆ ω := Set.diff_subset
  let φ := squareRectangleOpenGraphMonoHom (m := m) (n := n) hηω
  let P : EdgeMenger.WalkBetweenFinsets H
      (squareRectangleLeftTerminals m n) (squareRectangleRightTerminals m n) :=
    { start := Pη.start
      finish := Pη.finish
      walk := Pη.walk.map φ }
  refine ⟨P.start.1, P.start.2, P.finish.1, P.finish.2, P.walk, ?_⟩
  intro e he
  have hmapEdges : P.walk.edges = Pη.walk.edges.map (Sym2.map φ) := by
    exact SimpleGraph.Walk.edges_map φ Pη.walk
  have heMap : e ∈ Pη.walk.edges.map (Sym2.map φ) :=
    (congrArg (fun l ↦ e ∈ l) hmapEdges).mp he
  obtain ⟨eη, heη, heηmap⟩ := List.mem_map.mp heMap
  have heEq : eη = e := by
    simpa [φ, squareRectangleOpenGraphMonoHom] using heηmap
  subst eη
  intro heS
  have heEdgeH : e ∈ H.edgeSet := P.walk.edges_subset_edgeSet he
  let eH : H.edgeSet := ⟨e, heEdgeH⟩
  have heHR : eH ∈ R := by
    change eH ∈ Finset.univ.filter fun q : H.edgeSet ↦ q.1 ∈ s
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heS⟩
  have heD : squareEdgeOfRectangleOpenEdge eH ∈ D := by
    exact Finset.mem_map.mpr ⟨eH, heHR, rfl⟩
  have heEdgeη : e ∈ (squareRectangleOpenGraph m n
      (ω \ (D : Set SquareEdge))).edgeSet := Pη.walk.edges_subset_edgeSet heη
  let eEta : (squareRectangleOpenGraph m n
      (ω \ (D : Set SquareEdge))).edgeSet := ⟨e, heEdgeη⟩
  have hopenEta : squareEdgeOfRectangleOpenEdge eEta ∈ ω \ (D : Set SquareEdge) :=
    squareEdgeOfRectangleOpenEdge_mem_configuration eEta
  have hedgeEq : squareEdgeOfRectangleOpenEdge eEta =
      squareEdgeOfRectangleOpenEdge eH := by
    apply Subtype.ext
    rw [squareEdgeOfRectangleOpenEdge_val, squareEdgeOfRectangleOpenEdge_val]
  exact hopenEta.2 (hedgeEq ▸ heD)

/-- **Rectangle interior-depth/Menger adapter (the deterministic content of Lemma 11.22).**
Depth `r` in the crossing event is exactly the existence of `r+1` edge-disjoint crossings. -/
theorem mem_interiorDepth_squareRectangleCrossingEvent_iff
    (m n r : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ interiorDepth r (squareRectangleCrossingEvent m n) ↔
      HasEdgeDisjointSquareRectangleCrossings m n (r + 1) ω := by
  constructor
  · intro h
    apply (hasEdgeDisjointSquareRectangleCrossings_iff_isEdgeReachableBetweenFinsets
      m n (r + 1) ω).mpr
    exact mem_interiorDepth_imp_isEdgeReachableBetweenFinsets h
  · exact hasEdgeDisjointSquareRectangleCrossings_imp_mem_interiorDepth

theorem mem_interiorDepth_squareRectangleCrossingEvent_iff_le_max
    {m n r : ℕ} (hm : 1 ≤ m) (ω : EdgeConfiguration 2) :
    ω ∈ interiorDepth r (squareRectangleCrossingEvent m n) ↔
      r + 1 ≤ maxEdgeDisjointSquareRectangleCrossings m n ω := by
  rw [mem_interiorDepth_squareRectangleCrossingEvent_iff,
    hasEdgeDisjointSquareRectangleCrossings_iff_le_max hm]

end Percolation
