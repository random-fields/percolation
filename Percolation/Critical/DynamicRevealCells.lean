import Percolation.Critical.DynamicRestartPartition

/-!
# Finite reveal-cell indices for the Grimmett--Marstrand construction

An exact dynamic-restart cell records two finite pieces of data: the explored vertex region
inside the restart box and, on every coordinate that the restart can read, the number of earlier
sprinkling increments charged to that edge.  The source overlap bound is `2d+1`, so multiplicity
is stored in `Fin (2d+2)`.  This makes the space of possible reveal cells genuinely finite and
allows later probability arguments to sum over it.
-/

namespace Percolation

open scoped unitInterval

/-- Vertices available to an explored restart region. -/
abbrev RestartBoxVertex (d n : ℕ) :=
  {x : Cubic d // x ∈ cubicMetricBox d cubicOrigin n}

/-- Edge coordinates on which a reference restart can depend. -/
abbrev RestartSupportCoordinate (d : ℕ) (i : Fin d) (m n : ℕ) :=
  {e : CubicEdge d // e ∈ seedConnectionSupport d i m n}

noncomputable instance restartBoxVertexFintype (d n : ℕ) :
    Fintype (RestartBoxVertex d n) :=
  Fintype.ofFinite _

noncomputable instance restartSupportCoordinateFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (RestartSupportCoordinate d i m n) :=
  Fintype.ofFinite _

/-- Finite data selecting one possible random explored region and accumulated threshold profile
for a reference restart in direction `i`. -/
structure RestartRevealCellIndex (d : ℕ) (i : Fin d) (m n : ℕ) where
  region : Finset (RestartBoxVertex d n)
  multiplicity : RestartSupportCoordinate d i m n → Fin (2 * d + 2)

noncomputable instance restartRevealCellIndexDecidableEq
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    DecidableEq (RestartRevealCellIndex d i m n) :=
  Classical.decEq _

/-- A reveal-cell index is just a pair of finite objects; this equivalence supplies the concrete
finiteness instance without postulating finiteness of a structure with a function field. -/
def restartRevealCellIndexEquiv
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    RestartRevealCellIndex d i m n ≃
      Finset (RestartBoxVertex d n) ×
        (RestartSupportCoordinate d i m n → Fin (2 * d + 2)) where
  toFun c := (c.region, c.multiplicity)
  invFun data := ⟨data.1, data.2⟩
  left_inv c := by cases c; rfl
  right_inv data := by cases data; rfl

noncomputable instance restartRevealCellIndexFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (RestartRevealCellIndex d i m n) :=
  Fintype.ofEquiv
    (Finset (RestartBoxVertex d n) ×
      (RestartSupportCoordinate d i m n → Fin (2 * d + 2)))
    (restartRevealCellIndexEquiv d i m n).symm

namespace RestartRevealCellIndex

variable {d m n : ℕ} {i : Fin d}

/-- Ambient cubic vertices of the cell's explored region. -/
noncomputable def regionVertices (c : RestartRevealCellIndex d i m n) :
    Finset (Cubic d) :=
  c.region.map (Function.Embedding.subtype _)

@[simp]
theorem mem_regionVertices_iff (c : RestartRevealCellIndex d i m n) (x : Cubic d) :
    x ∈ c.regionVertices ↔
      ∃ hx : x ∈ cubicMetricBox d cubicOrigin n, (⟨x, hx⟩ : RestartBoxVertex d n) ∈ c.region := by
  classical
  simp [regionVertices]

theorem regionVertices_subset_box (c : RestartRevealCellIndex d i m n) :
    c.regionVertices ⊆ cubicMetricBox d cubicOrigin n := by
  intro x hx
  obtain ⟨hbox, _⟩ := (c.mem_regionVertices_iff x).mp hx
  exact hbox

/-- Multiplicity on every cubic edge, extended by zero away from the finite restart support. -/
noncomputable def edgeMultiplicity
    (c : RestartRevealCellIndex d i m n) (e : CubicEdge d) : ℕ :=
  if he : e ∈ seedConnectionSupport d i m n then c.multiplicity ⟨e, he⟩ else 0

theorem edgeMultiplicity_le (c : RestartRevealCellIndex d i m n) (e : CubicEdge d) :
    c.edgeMultiplicity e ≤ 2 * d + 1 := by
  classical
  unfold edgeMultiplicity
  split
  · have hlt := (c.multiplicity ⟨e, ‹_›⟩).isLt
    omega
  · omega

@[simp]
theorem edgeMultiplicity_of_notMem
    (c : RestartRevealCellIndex d i m n) {e : CubicEdge d}
    (he : e ∉ seedConnectionSupport d i m n) :
    c.edgeMultiplicity e = 0 := by
  simp [edgeMultiplicity, he]

/-- Heterogeneous boundary threshold represented by the reveal cell.  The hypotheses expose the
entire source budget: a nonnegative base density and increment, with `2d+1` increments still at
most one. -/
noncomputable def thresholdProfile
    (c : RestartRevealCellIndex d i m n) (base delta : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) : CubicEdge d → I :=
  fun e =>
    ⟨base + c.edgeMultiplicity e * delta,
      add_nonneg hbase (mul_nonneg (Nat.cast_nonneg _) hdelta),
      (by
        calc
          base + c.edgeMultiplicity e * delta ≤
              base + (2 * d + 1 : ℕ) * delta := by
            gcongr
            exact_mod_cast c.edgeMultiplicity_le e
          _ ≤ 1 := hupper)⟩

@[simp]
theorem coe_thresholdProfile
    (c : RestartRevealCellIndex d i m n) (base delta : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) (e : CubicEdge d) :
    (c.thresholdProfile base delta hbase hdelta hupper e : ℝ) =
      base + c.edgeMultiplicity e * delta :=
  rfl

theorem thresholdProfile_le_globalBudget
    (c : RestartRevealCellIndex d i m n) (base delta budget : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1)
    (hbudget : base + (2 * d + 1 : ℕ) * delta ≤ budget)
    (e : CubicEdge d) :
    (c.thresholdProfile base delta hbase hdelta hupper e : ℝ) ≤ budget := by
  rw [coe_thresholdProfile]
  have hmult : (c.edgeMultiplicity e : ℝ) ≤ (2 * d + 1 : ℕ) := by
    exact_mod_cast c.edgeMultiplicity_le e
  calc
    base + c.edgeMultiplicity e * delta ≤
        base + (2 * d + 1 : ℕ) * delta := by
      gcongr
    _ ≤ budget := hbudget

/-- Source-specialized threshold profile starting at `p_c+η/2` and charging one of at most
`2d+1` increments to every edge. -/
noncomputable def dynamicThresholdProfile
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1) :
    CubicEdge d → I :=
  c.thresholdProfile (dynamicBlockBaseDensity pc eta)
    (dynamicBlockIncrement d eta)
    (by unfold dynamicBlockBaseDensity; positivity)
    (by unfold dynamicBlockIncrement; positivity)
    (by rw [dynamicBlockBaseDensity_add_maxIncrement]; exact htotal)

@[simp]
theorem coe_dynamicThresholdProfile
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1)
    (e : CubicEdge d) :
    (c.dynamicThresholdProfile pc eta hpc heta htotal e : ℝ) =
      dynamicBlockBaseDensity pc eta +
        c.edgeMultiplicity e * dynamicBlockIncrement d eta :=
  rfl

theorem dynamicThresholdProfile_le
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1)
    (e : CubicEdge d) :
    (c.dynamicThresholdProfile pc eta hpc heta htotal e : ℝ) ≤ pc + eta := by
  have hbase : 0 ≤ dynamicBlockBaseDensity pc eta := by
    unfold dynamicBlockBaseDensity
    positivity
  have hdelta : 0 ≤ dynamicBlockIncrement d eta := by
    unfold dynamicBlockIncrement
    positivity
  have hmax : dynamicBlockBaseDensity pc eta +
      (2 * d + 1 : ℕ) * dynamicBlockIncrement d eta ≤ 1 := by
    rw [dynamicBlockBaseDensity_add_maxIncrement]
    exact htotal
  have hbudget : dynamicBlockBaseDensity pc eta +
      (2 * d + 1 : ℕ) * dynamicBlockIncrement d eta ≤ pc + eta := by
    rw [dynamicBlockBaseDensity_add_maxIncrement]
  simpa only [dynamicThresholdProfile] using
    c.thresholdProfile_le_globalBudget
      (dynamicBlockBaseDensity pc eta) (dynamicBlockIncrement d eta) (pc + eta)
      hbase hdelta hmax hbudget e

/-- Source-valid region data: it contains the inlet seed box and avoids the chosen seeded target
quadrant together with its exterior vertex boundary. -/
def IsAdmissible (c : RestartRevealCellIndex d i m n) : Prop :=
  cubicMetricBox d cubicOrigin m ⊆ c.regionVertices ∧
    RegionAvoidsSeededBoundaryQuadrant d i n c.regionVertices

/-- Concrete oriented query carried by a reveal cell. -/
noncomputable def orientedQuery
    (c : RestartRevealCellIndex d i m n)
    (center : Cubic d) (direction : CubicDirection d)
    (base delta : ℝ) (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) :
    OrientedRestartQuery d where
  center := center
  direction := direction
  region := c.regionVertices
  beta := c.thresholdProfile base delta hbase hdelta hupper

end RestartRevealCellIndex

end Percolation
