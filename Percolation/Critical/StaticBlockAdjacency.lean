import Percolation.Core.CubicWalkLevel
import Percolation.Critical.StaticBlocks

/-!
# Connectivity of neighboring good static blocks

The centers of neighboring coarse blocks are one block radius apart.  A crossing cluster in
one box therefore contains, inside the overlap, a connected piece of diameter at least the
block radius.  The uniqueness clause in the neighboring good box identifies this piece with
its selected largest cluster.  This is the deterministic content of equation (7.59).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private theorem finiteBoxGraphComponentDiameter_ge_pair
    {d : ℕ} {x : Cubic d} {n : ℕ}
    {G : SimpleGraph {y : Cubic d // y ∈ cubicMetricBox d x n}}
    (C : G.ConnectedComponent) {u v : Cubic d}
    (hu : u ∈ finiteBoxGraphComponentVertices C)
    (hv : v ∈ finiteBoxGraphComponentVertices C) :
    cubicLInfDist u v ≤ finiteBoxGraphComponentDiameter C := by
  rw [finiteBoxGraphComponentDiameter]
  have hinner : cubicLInfDist u v ≤
      (finiteBoxGraphComponentVertices C).sup (fun z ↦ cubicLInfDist u z) :=
    Finset.le_sup hv
  have houter :
      (finiteBoxGraphComponentVertices C).sup (fun z ↦ cubicLInfDist u z) ≤
        (finiteBoxGraphComponentVertices C).sup
          (fun y ↦ (finiteBoxGraphComponentVertices C).sup
            (fun z ↦ cubicLInfDist y z)) :=
    Finset.le_sup (s := finiteBoxGraphComponentVertices C)
      (f := fun y ↦ (finiteBoxGraphComponentVertices C).sup
        (fun z ↦ cubicLInfDist y z)) hu
  exact hinner.trans houter

private theorem epsilonGoodBlockCenter_step_pos_coord
    {d n : ℕ} (x : Cubic d) (i j : Fin d) :
    epsilonGoodBlockCenter n (cubicStepFrom x (i, true)) j =
      if j = i then epsilonGoodBlockCenter n x j + n
      else epsilonGoodBlockCenter n x j := by
  by_cases hji : j = i
  · subst j
    simp [epsilonGoodBlockCenter, cubicScale, cubicStepFrom, cubicDirectionIncrement]
    ring
  · simp [epsilonGoodBlockCenter, cubicScale, cubicStepFrom, cubicDirectionIncrement, hji]

private theorem finiteBoxGraphLargestComponents_inter_of_good_step_pos
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (i : Fin d)
    (hx : FiniteBoxGraph.IsEpsilonGood p ε (epsilonGoodBlockCenter n x) n
      (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n))
    (hy : FiniteBoxGraph.IsEpsilonGood p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x (i, true))) n
      (finiteBoxOpenGraph d ω
        (epsilonGoodBlockCenter n (cubicStepFrom x (i, true))) n)) :
    ∃ u : Cubic d,
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
          (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n)) ∧
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent
          (epsilonGoodBlockCenter n (cubicStepFrom x (i, true))) n
          (finiteBoxOpenGraph d ω
            (epsilonGoodBlockCenter n (cubicStepFrom x (i, true))) n)) := by
  classical
  let cx := epsilonGoodBlockCenter n x
  let y := cubicStepFrom x (i, true)
  let cy := epsilonGoodBlockCenter n y
  let Gx := finiteBoxOpenGraph d ω cx n
  let Gy := finiteBoxOpenGraph d ω cy n
  let Mx := finiteBoxGraphLargestComponent cx n Gx
  let My := finiteBoxGraphLargestComponent cy n Gy
  change FiniteBoxGraph.IsEpsilonGood p ε cx n Gx at hx
  change FiniteBoxGraph.IsEpsilonGood p ε cy n Gy at hy
  rcases hx with ⟨hxCross, _hxUnique, _hxLarge⟩
  rcases hy with ⟨_hyCross, hyUnique, _hyLarge⟩
  obtain ⟨u, huMx, huFace⟩ := (hxCross i).2
  obtain ⟨v, hvMx, hvFace⟩ := (hxCross i).1
  have huData := huMx
  have hvData := hvMx
  simp only [finiteBoxGraphComponentVertices, Finset.mem_filter] at huData hvData
  obtain ⟨huBox, _huBox', huSupp⟩ := huData
  obtain ⟨hvBox, _hvBox', hvSupp⟩ := hvData
  let uX : {z : Cubic d // z ∈ cubicMetricBox d cx n} := ⟨u, huBox⟩
  let vX : {z : Cubic d // z ∈ cubicMetricBox d cx n} := ⟨v, hvBox⟩
  have huSupp' : uX ∈ Mx.supp := by simpa [uX] using huSupp
  have hvSupp' : vX ∈ Mx.supp := by simpa [vX] using hvSupp
  let wX : Gx.Walk uX vX := (Mx.reachable_of_mem_supp huSupp' hvSupp').some
  let embX := SimpleGraph.Embedding.induce
    (G := cubicOpenGraph d ω) (cubicMetricBox d cx n : Set (Cubic d))
  let w : (cubicOpenGraph d ω).Walk u v := wX.map embX.toHom
  have hOpenLe : cubicOpenGraph d ω ≤ cubicGraph d := by
    intro a b hab
    exact (cubicOpenGraph_adj.mp hab).choose
  have huCoord : u i = cx i + n := by
    simpa [cx] using (mem_cubicBoxFace.mp huFace).1
  have hvCoord : v i = cx i - n := by
    simpa [cx] using (mem_cubicBoxFace.mp hvFace).1
  obtain ⟨z, q, hzCoord, hqSide, hqSub⟩ :=
    exists_cubicWalk_prefix_to_level_of_end_le hOpenLe w i (cx i)
      (by omega) (by omega)
  have hwBox : ∀ a ∈ w.support, a ∈ cubicMetricBox d cx n := by
    intro a ha
    change a ∈ (wX.map embX.toHom).support at ha
    rw [SimpleGraph.Walk.support_map, List.mem_map] at ha
    obtain ⟨aX, _haX, rfl⟩ := ha
    exact aX.property
  have hqBoxY : ∀ a ∈ q.support, a ∈ cubicMetricBox d cy n := by
    intro a ha
    have haX := mem_cubicMetricBox.mp (hwBox a (hqSub a ha))
    rw [mem_cubicMetricBox]
    intro j
    by_cases hji : j = i
    · subst j
      have hside := hqSide a ha
      have hbounds := haX i
      have hcyi : cy i = cx i + n := by
        dsimp [cy, y, cx]
        simpa using epsilonGoodBlockCenter_step_pos_coord (n := n) x i i
      omega
    · have hbounds := haX j
      have hcyj : cy j = cx j := by
        dsimp [cy, y, cx]
        simpa [hji] using epsilonGoodBlockCenter_step_pos_coord (n := n) x i j
      omega
  let qY := q.induce (cubicMetricBox d cy n : Set (Cubic d)) hqBoxY
  let uY : {a : Cubic d // a ∈ cubicMetricBox d cy n} :=
    ⟨u, hqBoxY u q.start_mem_support⟩
  let zY : {a : Cubic d // a ∈ cubicMetricBox d cy n} :=
    ⟨z, hqBoxY z q.end_mem_support⟩
  let D : Gy.ConnectedComponent := Gy.connectedComponentMk uY
  have huD : u ∈ finiteBoxGraphComponentVertices D := by
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
    refine ⟨uY.property, uY.property, ?_⟩
    change uY ∈ D.supp
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hzD : z ∈ finiteBoxGraphComponentVertices D := by
    rw [finiteBoxGraphComponentVertices, Finset.mem_filter]
    refine ⟨zY.property, zY.property, ?_⟩
    change zY ∈ D.supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    apply SimpleGraph.ConnectedComponent.sound
    exact qY.reverse.reachable
  have hdist : n ≤ cubicLInfDist u z := by
    have hcoordLe := cubicLInfDist_coord_le u z i
    have hnatAbs : (z i - u i).natAbs = n := by
      rw [hzCoord, huCoord]
      have hz : cx i - (cx i + (n : ℤ)) = -(n : ℤ) := by omega
      rw [hz, Int.natAbs_neg]
      simp
    omega
  have hdiam : n ≤ finiteBoxGraphComponentDiameter D :=
    hdist.trans (finiteBoxGraphComponentDiameter_ge_pair D huD hzD)
  have hDMy : D = My := hyUnique D hdiam
  refine ⟨u, huMx, ?_⟩
  simpa [hDMy] using huD

set_option maxHeartbeats 800000 in
/-- Largest clusters in two neighboring good coarse boxes have a common vertex.  This is the
deterministic neighboring-block connection statement used in static renormalization. -/
theorem finiteBoxGraphLargestComponents_inter_of_good_step
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (a : CubicDirection d)
    (hx : FiniteBoxGraph.IsEpsilonGood p ε (epsilonGoodBlockCenter n x) n
      (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n))
    (hy : FiniteBoxGraph.IsEpsilonGood p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x a)) n
      (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n (cubicStepFrom x a)) n)) :
    ∃ u : Cubic d,
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
          (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n)) ∧
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent
          (epsilonGoodBlockCenter n (cubicStepFrom x a)) n
          (finiteBoxOpenGraph d ω
            (epsilonGoodBlockCenter n (cubicStepFrom x a)) n)) := by
  rcases a with ⟨i, positive⟩
  cases positive
  · have hback : cubicStepFrom (cubicStepFrom x (i, false)) (i, true) = x :=
      cubicStepFrom_neg_pos x i
    have hx' : FiniteBoxGraph.IsEpsilonGood p ε
        (epsilonGoodBlockCenter n
          (cubicStepFrom (cubicStepFrom x (i, false)) (i, true))) n
        (finiteBoxOpenGraph d ω
          (epsilonGoodBlockCenter n
            (cubicStepFrom (cubicStepFrom x (i, false)) (i, true))) n) := by
      rw [hback]
      exact hx
    have h := finiteBoxGraphLargestComponents_inter_of_good_step_pos p ε ω
      (cubicStepFrom x (i, false)) i hy hx'
    rw [hback] at h
    exact h.imp fun u hu ↦ ⟨hu.2, hu.1⟩
  · exact finiteBoxGraphLargestComponents_inter_of_good_step_pos p ε ω x i hx hy

theorem finiteBoxGraphLargestComponents_inter_of_mem_goodBoxEvents
    {d n : ℕ} (p : I) (ε : ℝ) (ω : EdgeConfiguration d)
    (x : Cubic d) (a : CubicDirection d)
    (hx : ω ∈ epsilonGoodBoxEvent d p ε (epsilonGoodBlockCenter n x) n)
    (hy : ω ∈ epsilonGoodBoxEvent d p ε
      (epsilonGoodBlockCenter n (cubicStepFrom x a)) n) :
    ∃ u : Cubic d,
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent (epsilonGoodBlockCenter n x) n
          (finiteBoxOpenGraph d ω (epsilonGoodBlockCenter n x) n)) ∧
      u ∈ finiteBoxGraphComponentVertices
        (finiteBoxGraphLargestComponent
          (epsilonGoodBlockCenter n (cubicStepFrom x a)) n
          (finiteBoxOpenGraph d ω
            (epsilonGoodBlockCenter n (cubicStepFrom x a)) n)) :=
  finiteBoxGraphLargestComponents_inter_of_good_step p ε ω x a hx hy

end Percolation
