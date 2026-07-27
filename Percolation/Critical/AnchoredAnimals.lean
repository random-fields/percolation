import Percolation.Critical.AnimalConcatenation

/-!
# Translation classes of rooted cubic bond animals

This module proves the rooted/anchored mass identity used in Grimmett's Lemma 6.102.  A rooted
animal with `n` vertices is equivalently a bottom-left anchored translation class together with
one of its `n` vertices selected as the root.
-/

namespace Percolation

open Set MeasureTheory
open scoped BigOperators ENNReal unitInterval

namespace CubicBondAnimal

variable {d n : ℕ}

noncomputable instance anchoredFintype : Fintype (Anchored d n) := Fintype.ofFinite _

/-- The inclusion of an animal's finite graph into the ambient cubic graph. -/
noncomputable def graphToCubicHom (A : CubicBondAnimal d n) :
    A.graph →g cubicGraph d where
  toFun x := x.1
  map_rel' := by
    rintro u v ⟨e, he, huv⟩
    rw [← SimpleGraph.mem_edgeSet]
    exact huv ▸ e.2

/-- Any two vertices of an `n`-vertex animal are at ambient graph distance at most `n-1`. -/
theorem cubicL1Dist_le_card_sub_one (A : CubicBondAnimal d n)
    {x y : Cubic d} (hx : x ∈ A.vertices) (hy : y ∈ A.vertices) :
    cubicL1Dist x y ≤ n - 1 := by
  obtain ⟨p, hp⟩ := A.graph_connected.exists_isPath
    (⟨x, hx⟩ : A.vertices) (⟨y, hy⟩ : A.vertices)
  have hcard : p.support.toFinset.card ≤ Fintype.card A.vertices := by
    simpa using Finset.card_le_card (Finset.subset_univ p.support.toFinset)
  have hlen : p.length ≤ n - 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support, Fintype.card_coe, A.vertices_card] at hcard
    omega
  let q := p.map A.graphToCubicHom
  exact (cubicL1Dist_le_walk_length q).trans (by simpa [q] using hlen)

/-- Translate all vertices of an animal from base point `a` to base point `b`. -/
noncomputable def translatedVertices (A : CubicBondAnimal d n) (a b : Cubic d) :
    Finset (Cubic d) :=
  A.vertices.map (cubicTranslationEquiv a b).toEmbedding

/-- Translate all occupied edges of an animal. -/
noncomputable def translatedEdges (A : CubicBondAnimal d n) (a b : Cubic d) :
    Finset (CubicEdge d) :=
  A.edges.map (cubicTranslationIso a b).mapEdgeSet.toEmbedding

@[simp] theorem mem_translatedVertices_iff (A : CubicBondAnimal d n) (a b x : Cubic d) :
    x ∈ A.translatedVertices a b ↔
      ∃ y ∈ A.vertices, cubicTranslate a b y = x := by
  rw [translatedVertices, Finset.mem_map]
  rfl

@[simp] theorem mem_translatedEdges_iff (A : CubicBondAnimal d n)
    (a b : Cubic d) (e : CubicEdge d) :
    e ∈ A.translatedEdges a b ↔
      ∃ f ∈ A.edges, (cubicTranslationIso a b).mapEdgeSet f = e := by
  rw [translatedEdges, Finset.mem_map]
  rfl

theorem translatedEdges_endpoints (A : CubicBondAnimal d n) (a b : Cubic d) :
    ∀ e ∈ A.translatedEdges a b, ∀ x ∈ (e : Sym2 (Cubic d)),
      x ∈ A.translatedVertices a b := by
  intro e he x hx
  rw [mem_translatedEdges_iff] at he
  obtain ⟨f, hf, rfl⟩ := he
  have hxmap : x ∈ Sym2.map (cubicTranslate a b) f.1 := by simpa using hx
  obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hxmap
  rw [mem_translatedVertices_iff]
  exact ⟨y, A.edge_endpoints f hf y hy, hyx⟩

theorem translatedVertices_subset_metricBall_from
    (A : CubicBondAnimal d n) {v : Cubic d} (hv : v ∈ A.vertices) :
    A.translatedVertices v cubicOrigin ⊆ cubicMetricBall d cubicOrigin (n - 1) := by
  intro x hx
  rw [mem_translatedVertices_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_cubicMetricBall_iff_l1Dist_le]
  have hdist := A.cubicL1Dist_le_card_sub_one hv hy
  simpa [cubicTranslate] using
    (show cubicL1Dist (cubicTranslate v cubicOrigin v)
        (cubicTranslate v cubicOrigin y) ≤ n - 1 from
      (cubicL1Dist_translate v cubicOrigin v y).symm ▸ hdist)

theorem translated_connected_from
    (A : CubicBondAnimal d n) {v : Cubic d} (hv : v ∈ A.vertices) :
    ∀ x ∈ A.translatedVertices v cubicOrigin,
      ∃ w : (cubicGraph d).Walk cubicOrigin x,
        walkEdgeFinset w ⊆ A.translatedEdges v cubicOrigin := by
  intro x hx
  rw [mem_translatedVertices_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨wv, hwv⟩ := A.connected v hv
  obtain ⟨wy, hwy⟩ := A.connected y hy
  let w0 : (cubicGraph d).Walk v y := wv.reverse.append wy
  have hw0 : walkEdgeFinset w0 ⊆ A.edges := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at he
    rcases he with he | he
    · apply hwv
      rw [mem_walkEdgeFinset_iff]
      simpa using he
    · exact hwy ((mem_walkEdgeFinset_iff wy e).mpr he)
  let T := cubicTranslationIso v cubicOrigin
  let wMap := w0.map T.toHom
  let w : (cubicGraph d).Walk cubicOrigin (cubicTranslate v cubicOrigin y) :=
    wMap.copy (by simp [T]) rfl
  refine ⟨w, fun e he ↦ ?_⟩
  rw [mem_translatedEdges_iff]
  have heMap : e.1 ∈ wMap.edges := by
    simpa [w, SimpleGraph.Walk.edges_copy] using
      (mem_walkEdgeFinset_iff w e).mp he
  rw [SimpleGraph.Walk.edges_map] at heMap
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp heMap
  let f' : CubicEdge d := ⟨f, w0.edges_subset_edgeSet hf⟩
  refine ⟨f', hw0 ((mem_walkEdgeFinset_iff w0 f').mpr hf), ?_⟩
  apply Subtype.ext
  simpa [T] using hfe

/-- Re-root an animal at one of its vertices, translating that vertex to the origin. -/
noncomputable def reRoot (A : CubicBondAnimal d n) (v : Cubic d) (hv : v ∈ A.vertices) :
    CubicBondAnimal d n where
  vertices := A.translatedVertices v cubicOrigin
  vertices_subset := A.translatedVertices_subset_metricBall_from hv
  edges := A.translatedEdges v cubicOrigin
  edges_subset := by
    intro e he
    apply cubicEdge_mem_cubicMetricBallEdges_of_out_mem
    · exact A.translatedVertices_subset_metricBall_from hv
        (A.translatedEdges_endpoints v cubicOrigin e he _ (Sym2.out_fst_mem e.1))
    · exact A.translatedVertices_subset_metricBall_from hv
        (A.translatedEdges_endpoints v cubicOrigin e he _ (Sym2.out_snd_mem e.1))
  origin_mem := by
    rw [mem_translatedVertices_iff]
    exact ⟨v, hv, by ext j; simp [cubicTranslate, cubicOrigin]⟩
  vertices_card := by rw [translatedVertices, Finset.card_map, A.vertices_card]
  edge_endpoints := A.translatedEdges_endpoints v cubicOrigin
  connected := A.translated_connected_from hv

@[simp] theorem reRoot_edges_card (A : CubicBondAnimal d n)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).edges.card = A.edges.card := by
  change (A.translatedEdges v cubicOrigin).card = A.edges.card
  rw [translatedEdges, Finset.card_map]

theorem map_cubicIncidentEdges_eq_translated
    (A : CubicBondAnimal d n) (a b : Cubic d) :
    (cubicIncidentEdges d A.vertices).map
        (cubicTranslationIso a b).mapEdgeSet.toEmbedding =
      cubicIncidentEdges d (A.translatedVertices a b) := by
  let T := cubicTranslationIso a b
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y, hyA, hyf⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp hf
    apply mem_cubicIncidentEdges_iff_exists_endpoint.mpr
    refine ⟨T y, Finset.mem_map.mpr ⟨y, hyA, rfl⟩, ?_⟩
    change cubicTranslate a b y ∈ Sym2.map (cubicTranslate a b) f.1
    exact Sym2.mem_map.mpr ⟨y, hyf, rfl⟩
  · intro he
    obtain ⟨x, hxT, hxe⟩ := mem_cubicIncidentEdges_iff_exists_endpoint.mp he
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_map.mp hxT
    let f : CubicEdge d := T.mapEdgeSet.symm e
    have hmap : T.mapEdgeSet f = e := T.mapEdgeSet.apply_symm_apply e
    apply Finset.mem_map.mpr
    refine ⟨f, mem_cubicIncidentEdges_iff_exists_endpoint.mpr ⟨y, hyA, ?_⟩, hmap⟩
    have hyMap : T y ∈ (T.mapEdgeSet f : Sym2 (Cubic d)) := hmap.symm ▸ hxe
    rw [SimpleGraph.Iso.mapEdgeSet_apply] at hyMap
    obtain ⟨z, hzf, hzy⟩ := Sym2.mem_map.mp hyMap
    simpa [T.injective hzy] using hzf

theorem reRoot_boundary_eq_map (A : CubicBondAnimal d n)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).boundary =
      A.boundary.map (cubicTranslationIso v cubicOrigin).mapEdgeSet.toEmbedding := by
  rw [boundary, boundary]
  change cubicIncidentEdges d (A.translatedVertices v cubicOrigin) \
      A.translatedEdges v cubicOrigin = _
  rw [← A.map_cubicIncidentEdges_eq_translated v cubicOrigin,
    translatedEdges, Finset.map_sdiff]

@[simp] theorem reRoot_boundary_card (A : CubicBondAnimal d n)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).boundary.card = A.boundary.card := by
  rw [A.reRoot_boundary_eq_map v hv, Finset.card_map]

theorem reRoot_bottomLeft (A : CubicBondAnimal d n)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).bottomLeft = cubicTranslate v cubicOrigin A.bottomLeft := by
  apply toLex_inj.mp
  apply le_antisymm
  · apply (A.reRoot v hv).bottomLeft_lex_le
    change cubicTranslate v cubicOrigin A.bottomLeft ∈ A.translatedVertices v cubicOrigin
    rw [mem_translatedVertices_iff]
    exact ⟨A.bottomLeft, A.bottomLeft_mem, rfl⟩
  · have hmem := (A.reRoot v hv).bottomLeft_mem
    change (A.reRoot v hv).bottomLeft ∈ A.translatedVertices v cubicOrigin at hmem
    rw [mem_translatedVertices_iff] at hmem
    obtain ⟨y, hyA, hyEq⟩ := hmem
    rw [← hyEq]
    exact (toLex_cubicTranslate_le_iff v cubicOrigin A.bottomLeft y).mpr
      (A.bottomLeft_lex_le hyA)

/-- Canonical representative of the translation class, with bottom-left vertex at the origin. -/
noncomputable def normalize (A : CubicBondAnimal d n) : CubicBondAnimal d n :=
  A.reRoot A.bottomLeft A.bottomLeft_mem

theorem normalize_isBottomLeftAnchored (A : CubicBondAnimal d n) :
    A.normalize.IsBottomLeftAnchored := by
  rw [IsBottomLeftAnchored, normalize, A.reRoot_bottomLeft]
  ext j
  simp [cubicTranslate, cubicOrigin]

/-- The canonical anchored representative of an arbitrary rooted animal. -/
noncomputable def toAnchored (A : CubicBondAnimal d n) : Anchored d n :=
  ⟨A.normalize, A.normalize_isBottomLeftAnchored⟩

theorem cubicTranslate_reRoot_comp (v w x : Cubic d) :
    cubicTranslate (cubicTranslate v cubicOrigin w) cubicOrigin
        (cubicTranslate v cubicOrigin x) =
      cubicTranslate w cubicOrigin x := by
  ext j
  simp [cubicTranslate, cubicOrigin]

@[simp] theorem cubicTranslate_origin_origin (x : Cubic d) :
    cubicTranslate cubicOrigin cubicOrigin x = x := by
  ext j
  simp [cubicTranslate, cubicOrigin]

theorem reRoot_reRoot (A : CubicBondAnimal d n)
    (v w : Cubic d) (hv : v ∈ A.vertices) (hw : w ∈ A.vertices) :
    let w' := cubicTranslate v cubicOrigin w
    let hw' : w' ∈ (A.reRoot v hv).vertices := by
      change w' ∈ A.translatedVertices v cubicOrigin
      exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
    (A.reRoot v hv).reRoot w' hw' = A.reRoot w hw := by
  dsimp only
  apply ext_data
  · change (A.translatedVertices v cubicOrigin).map
        (cubicTranslationEquiv (cubicTranslate v cubicOrigin w) cubicOrigin).toEmbedding =
      A.translatedVertices w cubicOrigin
    rw [translatedVertices, translatedVertices, Finset.map_map]
    apply congrArg (fun f : Cubic d ↪ Cubic d ↦ A.vertices.map f)
    apply Function.Embedding.ext
    intro x
    exact cubicTranslate_reRoot_comp v w x
  · change (A.translatedEdges v cubicOrigin).map
        (cubicTranslationIso (cubicTranslate v cubicOrigin w) cubicOrigin).mapEdgeSet.toEmbedding =
      A.translatedEdges w cubicOrigin
    rw [translatedEdges, translatedEdges, Finset.map_map]
    apply congrArg (fun f : CubicEdge d ↪ CubicEdge d ↦ A.edges.map f)
    apply Function.Embedding.ext
    intro e
    apply Subtype.ext
    change Sym2.map (cubicTranslate (cubicTranslate v cubicOrigin w) cubicOrigin)
        (Sym2.map (cubicTranslate v cubicOrigin) e.1) =
      Sym2.map (cubicTranslate w cubicOrigin) e.1
    rw [Sym2.map_map]
    apply congrArg (fun f : Cubic d → Cubic d ↦ Sym2.map f e.1)
    funext x
    exact cubicTranslate_reRoot_comp v w x

@[simp] theorem reRoot_origin (A : CubicBondAnimal d n) :
    A.reRoot cubicOrigin A.origin_mem = A := by
  apply ext_data
  · change A.translatedVertices cubicOrigin cubicOrigin = A.vertices
    rw [translatedVertices]
    have hid : (cubicTranslationEquiv cubicOrigin cubicOrigin).toEmbedding =
        Function.Embedding.refl (Cubic d) := by
      apply Function.Embedding.ext
      intro x
      exact cubicTranslate_origin_origin x
    rw [hid, Finset.map_refl]
  · change A.translatedEdges cubicOrigin cubicOrigin = A.edges
    rw [translatedEdges]
    have hid : (cubicTranslationIso cubicOrigin cubicOrigin).mapEdgeSet.toEmbedding =
        Function.Embedding.refl (CubicEdge d) := by
      apply Function.Embedding.ext
      intro e
      apply Subtype.ext
      change Sym2.map (cubicTranslate cubicOrigin cubicOrigin) e.1 = e.1
      calc
        Sym2.map (cubicTranslate cubicOrigin cubicOrigin) e.1 =
            Sym2.map id e.1 := congrArg (fun f : Cubic d → Cubic d ↦ Sym2.map f e.1)
              (funext cubicTranslate_origin_origin)
        _ = e.1 := by rw [Sym2.map_id]; rfl
    rw [hid, Finset.map_refl]

/-- An anchored translation class together with a selected vertex that will become the root. -/
abbrev PointedAnchored (d n : ℕ) := Σ A : Anchored d n, A.1.vertices

theorem normalizedRoot_mem (A : CubicBondAnimal d n) :
    cubicTranslate A.bottomLeft cubicOrigin cubicOrigin ∈ A.normalize.vertices := by
  change cubicTranslate A.bottomLeft cubicOrigin cubicOrigin ∈
    A.translatedVertices A.bottomLeft cubicOrigin
  rw [mem_translatedVertices_iff]
  exact ⟨cubicOrigin, A.origin_mem, rfl⟩

/-- Send a rooted animal to its anchored representative and remember the old root. -/
noncomputable def toPointedAnchored (A : CubicBondAnimal d n) : PointedAnchored d n :=
  ⟨A.toAnchored,
    ⟨cubicTranslate A.bottomLeft cubicOrigin cubicOrigin, A.normalizedRoot_mem⟩⟩

/-- Re-root an anchored animal at its selected vertex. -/
noncomputable def fromPointedAnchored (X : PointedAnchored d n) : CubicBondAnimal d n :=
  X.1.1.reRoot X.2.1 X.2.2

theorem fromPointedAnchored_toPointedAnchored (A : CubicBondAnimal d n) :
    fromPointedAnchored (toPointedAnchored A) = A := by
  change (A.reRoot A.bottomLeft A.bottomLeft_mem).reRoot
      (cubicTranslate A.bottomLeft cubicOrigin cubicOrigin) A.normalizedRoot_mem = A
  rw [A.reRoot_reRoot A.bottomLeft cubicOrigin A.bottomLeft_mem A.origin_mem,
    A.reRoot_origin]

theorem reRoot_congr_root (A : CubicBondAnimal d n)
    {v w : Cubic d} (hv : v ∈ A.vertices) (hw : w ∈ A.vertices) (hvw : v = w) :
    A.reRoot v hv = A.reRoot w hw := by
  subst w
  rfl

theorem normalize_reRoot_of_anchored (A : CubicBondAnimal d n)
    (hA : A.IsBottomLeftAnchored) (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).normalize = A := by
  unfold normalize
  let w' := cubicTranslate v cubicOrigin cubicOrigin
  have hw' : w' ∈ (A.reRoot v hv).vertices := by
    change w' ∈ A.translatedVertices v cubicOrigin
    exact Finset.mem_map.mpr ⟨cubicOrigin, A.origin_mem, rfl⟩
  have hBL : (A.reRoot v hv).bottomLeft = w' := by
    rw [A.reRoot_bottomLeft, hA]
  calc
    (A.reRoot v hv).reRoot (A.reRoot v hv).bottomLeft _ =
        (A.reRoot v hv).reRoot w' hw' :=
      (A.reRoot v hv).reRoot_congr_root _ _ hBL
    _ = A.reRoot cubicOrigin A.origin_mem :=
      A.reRoot_reRoot v cubicOrigin hv A.origin_mem
    _ = A := A.reRoot_origin

theorem toPointedAnchored_fromPointedAnchored (X : PointedAnchored d n) :
    toPointedAnchored (fromPointedAnchored X) = X := by
  rcases X with ⟨⟨A, hA⟩, ⟨v, hv⟩⟩
  change A.bottomLeft = cubicOrigin at hA
  have hN : (A.reRoot v hv).normalize = A := A.normalize_reRoot_of_anchored hA v hv
  apply Sigma.ext
  · apply Subtype.ext
    exact hN
  · rw [Subtype.heq_iff_coe_eq (fun x ↦ by
      change x ∈ (A.reRoot v hv).normalize.vertices ↔ x ∈ A.vertices
      rw [hN])]
    ext j
    simp [toPointedAnchored, fromPointedAnchored, toAnchored, normalize,
      reRoot_bottomLeft, hA, cubicTranslate, cubicOrigin]

/-- Rooted animals are equivalent to pointed anchored translation classes. -/
noncomputable def rootedEquivPointedAnchored :
    CubicBondAnimal d n ≃ PointedAnchored d n where
  toFun := toPointedAnchored
  invFun := fromPointedAnchored
  left_inv := fromPointedAnchored_toPointedAnchored
  right_inv := toPointedAnchored_fromPointedAnchored

/-- Bernoulli weight of a concrete animal: occupied edges contribute `p`, closed boundary
edges contribute `1-p`. -/
noncomputable def weight (p : ℝ) (A : CubicBondAnimal d n) : ℝ :=
  p ^ A.edges.card * (1 - p) ^ A.boundary.card

@[simp] theorem weight_reRoot (p : ℝ) (A : CubicBondAnimal d n)
    (v : Cubic d) (hv : v ∈ A.vertices) :
    (A.reRoot v hv).weight p = A.weight p := by
  simp [weight]

/-- Total weight of bottom-left anchored translation classes. -/
noncomputable def anchoredMass (d n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : Anchored d n, A.1.weight p

/-- Rooted mass is `n` times anchored mass.  This is the precise orbit-counting identity behind
the normalized probabilities in Grimmett's Lemma 6.102. -/
theorem sum_weight_eq_nat_mul_anchoredMass (d n : ℕ) (p : ℝ) :
    (∑ A : CubicBondAnimal d n, A.weight p) = n * anchoredMass d n p := by
  let e := rootedEquivPointedAnchored (d := d) (n := n)
  calc
    (∑ A : CubicBondAnimal d n, A.weight p) =
        ∑ A : CubicBondAnimal d n,
          (fromPointedAnchored (e A)).weight p := by
      apply Finset.sum_congr rfl
      intro A _
      rw [show e A = toPointedAnchored A by rfl,
        fromPointedAnchored_toPointedAnchored]
    _ =
        ∑ X : PointedAnchored d n, (fromPointedAnchored X).weight p := by
      exact e.sum_comp (fun X : PointedAnchored d n ↦
        (fromPointedAnchored X).weight p)
    _ = ∑ X : PointedAnchored d n, X.1.1.weight p := by
      apply Finset.sum_congr rfl
      intro X _
      exact weight_reRoot p X.1.1 X.2.1 X.2.2
    _ = ∑ A : Anchored d n, ∑ _x : A.1.vertices, A.1.weight p := by
      exact Fintype.sum_sigma (fun X : PointedAnchored d n ↦ X.1.1.weight p)
    _ = n * anchoredMass d n p := by
      rw [anchoredMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      simp [A.1.vertices_card, nsmul_eq_mul]

theorem finiteClusterSizeProbability_eq_nat_mul_anchoredMass
    (d n : ℕ) (p : I) :
    finiteClusterSizeProbability d p n = n * anchoredMass d n p := by
  rw [finiteClusterSizeProbability_eq_sum_animals]
  exact sum_weight_eq_nat_mul_anchoredMass d n p

theorem anchoredMass_eq_finiteClusterSizeProbability_div
    (d n : ℕ) (p : I) (hn : 0 < n) :
    anchoredMass d n p = finiteClusterSizeProbability d p n / n := by
  rw [finiteClusterSizeProbability_eq_nat_mul_anchoredMass]
  field_simp

theorem weight_concat (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (A : CubicBondAnimal d n) (B : CubicBondAnimal d m)
    (hA : A.IsBottomLeftAnchored) (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.concat B hA hB hd).weight p =
      p * (1 - p)⁻¹ ^ 2 * A.weight p * B.weight p := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
  have hbA := A.boundary_card_pos hd
  have hbB := B.boundary_card_pos hd
  rw [weight, weight, weight]
  change p ^ (A.concatenatedEdges B hd).card *
      (1 - p) ^ (A.concat B hA hB hd).boundary.card = _
  rw [A.concatenatedEdges_card B hB hd,
    A.concat_boundary_card B hA hB hd]
  have hOpen : p ^ (A.edges.card + B.edges.card + 1) =
      p ^ A.edges.card * p ^ B.edges.card * p := by
    rw [show A.edges.card + B.edges.card + 1 =
      (A.edges.card + B.edges.card) + 1 by omega, pow_succ, pow_add]
  have hClosed : (1 - p) ^ (A.boundary.card + B.boundary.card - 2) =
      (1 - p) ^ (A.boundary.card - 1) *
        (1 - p) ^ (B.boundary.card - 1) := by
    rw [show A.boundary.card + B.boundary.card - 2 =
      (A.boundary.card - 1) + (B.boundary.card - 1) by omega, pow_add]
  have hAClosed : (1 - p) ^ A.boundary.card =
      (1 - p) ^ (A.boundary.card - 1) * (1 - p) := by
    calc
      (1 - p) ^ A.boundary.card =
          (1 - p) ^ ((A.boundary.card - 1) + 1) := by congr 1; omega
      _ = (1 - p) ^ (A.boundary.card - 1) * (1 - p) := by rw [pow_succ]
  have hBClosed : (1 - p) ^ B.boundary.card =
      (1 - p) ^ (B.boundary.card - 1) * (1 - p) := by
    calc
      (1 - p) ^ B.boundary.card =
          (1 - p) ^ ((B.boundary.card - 1) + 1) := by congr 1; omega
      _ = (1 - p) ^ (B.boundary.card - 1) * (1 - p) := by rw [pow_succ]
  rw [hOpen, hClosed, hAClosed, hBClosed]
  field_simp

/-- Bernoulli weight of the root-preserving concatenation.  Anchoring is needed only for the
right factor, which is translated before being joined. -/
theorem weight_rootedConcat (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (A : CubicBondAnimal d n) (B : CubicBondAnimal d m)
    (hB : B.IsBottomLeftAnchored) (hd : 0 < d) :
    (A.rootedConcat B hB hd).weight p =
      p * (1 - p)⁻¹ ^ 2 * A.weight p * B.weight p := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
  have hbA := A.boundary_card_pos hd
  have hbB := B.boundary_card_pos hd
  rw [weight, weight, weight]
  change p ^ (A.concatenatedEdges B hd).card *
      (1 - p) ^ (A.rootedConcat B hB hd).boundary.card = _
  rw [A.concatenatedEdges_card B hB hd,
    A.rootedConcat_boundary_card B hB hd]
  have hOpen : p ^ (A.edges.card + B.edges.card + 1) =
      p ^ A.edges.card * p ^ B.edges.card * p := by
    rw [show A.edges.card + B.edges.card + 1 =
      (A.edges.card + B.edges.card) + 1 by omega, pow_succ, pow_add]
  have hClosed : (1 - p) ^ (A.boundary.card + B.boundary.card - 2) =
      (1 - p) ^ (A.boundary.card - 1) *
        (1 - p) ^ (B.boundary.card - 1) := by
    rw [show A.boundary.card + B.boundary.card - 2 =
      (A.boundary.card - 1) + (B.boundary.card - 1) by omega, pow_add]
  have hAClosed : (1 - p) ^ A.boundary.card =
      (1 - p) ^ (A.boundary.card - 1) * (1 - p) := by
    calc
      (1 - p) ^ A.boundary.card =
          (1 - p) ^ ((A.boundary.card - 1) + 1) := by congr 1; omega
      _ = (1 - p) ^ (A.boundary.card - 1) * (1 - p) := by rw [pow_succ]
  have hBClosed : (1 - p) ^ B.boundary.card =
      (1 - p) ^ (B.boundary.card - 1) * (1 - p) := by
    calc
      (1 - p) ^ B.boundary.card =
          (1 - p) ^ ((B.boundary.card - 1) + 1) := by congr 1; omega
      _ = (1 - p) ^ (B.boundary.card - 1) * (1 - p) := by rw [pow_succ]
  rw [hOpen, hClosed, hAClosed, hBClosed]
  field_simp

theorem anchoredMass_supermultiplicative
    (d m n : ℕ) (p : ℝ) (hd : 0 < d) (hp0 : 0 < p) (hp1 : p < 1) :
    p * (1 - p)⁻¹ ^ 2 * anchoredMass d m p * anchoredMass d n p ≤
      anchoredMass d (m + n) p := by
  let f := anchoredConcat (m := m) (n := n) hd
  let emb : Anchored d m × Anchored d n ↪ Anchored d (m + n) :=
    ⟨f, anchoredConcat_injective hd⟩
  have hnonneg (C : Anchored d (m + n)) : 0 ≤ C.1.weight p := by
    apply mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (sub_nonneg.mpr hp1.le) _)
  have hsum :
      (∑ AB : Anchored d m × Anchored d n, (f AB).1.weight p) ≤
        anchoredMass d (m + n) p := by
    calc
      (∑ AB : Anchored d m × Anchored d n, (f AB).1.weight p) =
          ∑ C ∈ (Finset.univ.map emb), C.1.weight p := by
        rw [Finset.sum_map]
        rfl
      _ ≤ ∑ C : Anchored d (m + n), C.1.weight p :=
        Finset.sum_le_univ_sum_of_nonneg hnonneg
      _ = anchoredMass d (m + n) p := rfl
  have hdomain :
      (∑ AB : Anchored d m × Anchored d n, (f AB).1.weight p) =
        p * (1 - p)⁻¹ ^ 2 * anchoredMass d m p * anchoredMass d n p := by
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ A : Anchored d m, ∀ B : Anchored d n,
        (f (A, B)).1.weight p =
          p * (1 - p)⁻¹ ^ 2 * A.1.weight p * B.1.weight p from fun A B ↦
      weight_concat p hp0 hp1 A.1 B.1 A.2 B.2 hd]
    rw [anchoredMass, anchoredMass]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
  rw [hdomain] at hsum
  exact hsum

/-- Grimmett's Lemma 6.102: exact cluster-size probabilities, normalized by their sizes, are
supermultiplicative up to the explicit joining-edge weight `p(1-p)⁻²`. -/
theorem finiteClusterSizeProbability_normalized_supermultiplicative
    (d m n : ℕ) (p : I) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 *
        (finiteClusterSizeProbability d p m / m) *
        (finiteClusterSizeProbability d p n / n) ≤
      finiteClusterSizeProbability d p (m + n) / (m + n) := by
  simpa [anchoredMass_eq_finiteClusterSizeProbability_div d m p hm,
    anchoredMass_eq_finiteClusterSizeProbability_div d n p hn,
    anchoredMass_eq_finiteClusterSizeProbability_div d (m + n) p (by omega)] using
    anchoredMass_supermultiplicative d m n p hd hp0 hp1

#print axioms rootedEquivPointedAnchored
#print axioms sum_weight_eq_nat_mul_anchoredMass
#print axioms finiteClusterSizeProbability_normalized_supermultiplicative

end CubicBondAnimal

end Percolation
