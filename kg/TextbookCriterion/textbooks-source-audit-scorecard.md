# Percolation Textbooks Source Audit Scorecard

Generated from `kg/TextbookCriterion/autoformalization-source-audit-prompt.md`,
which is the v2 source-audit prompt from
`random-fields/planning@cc685855c952a79af1786abcd85215bfc75f253d`, after reading
the local PDFs in `kg/textbooks/`.

Environment: Lean toolchain `leanprover/lean4:v4.30.0`; Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; percolation repo branch
`codex/percolation-textbook-audit-scorecards` at
`51044cce36626eb5e5928ccf649fd6001128851a`, based on `main`. Tools available
this run: `pdfinfo`, `pdftotext`, `rg` over pinned Mathlib source and this repo.
Tools not used: Lean LSP proof-state inspection, live `#check`, `exact?`,
`apply?`, `leansearch`, `loogle`, and `leanfinder`.

Calibration note: because v2 requires grounded evidence for Mathlib-facing
criteria, this audit treats source-level judgments separately from tool-confirmed
availability. The grounding rows below are shared by the scorecards. Criteria 2,
5, and 6 cite these rows; no Mathlib-facing claim is scored Green merely from
memory.

The official comparator catalog currently contains only:

- `grimmett-percolation-1999`: Geoffrey Grimmett, *Percolation*, 2nd ed., 1999.
- `grimmett-random-cluster-2006`: Geoffrey Grimmett, *The Random-Cluster Model*,
  2006.

Three additional local PDFs were present but untracked at audit time:

- `kg/textbooks/978-1-4899-2730-9.pdf`: Harry Kesten, *Percolation Theory for
  Mathematicians*, 1982.
- `kg/textbooks/2017percolation.pdf`: Hugo Duminil-Copin, *Introduction to
  Bernoulli percolation*, 2018 lecture notes.
- `kg/textbooks/ProbOnGraph.pdf`: Geoffrey Grimmett, *Probability on Graphs:
  Random Processes on Graphs and Lattices*, 2012 notes.

## Shared Grounding Evidence

This table is the v2 grounding evidence for criteria 2, 5, and 6. `rg` references
are against Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` or this repo at
`51044cce36626eb5e5928ccf649fd6001128851a`.

| Row | Object/Lemma | Query | Tool | Result | Axes a/b/c | Location |
|---|---|---|---|---|---|---|
| G1 | simple graphs | `structure SimpleGraph` | `rg .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph` | `SimpleGraph` in `Mathlib/Combinatorics/SimpleGraph/Basic.lean:92` | a yes; b yes; c needs lattice-specific instantiation | Mathlib |
| G2 | graph edge set | `edgeSet` near `SimpleGraph` | `rg .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph` | `SimpleGraph.edgeSet` in `Basic.lean:476` and `mem_edgeSet` in `Basic.lean:479` | a yes; b yes; c directly useful for graph edges | Mathlib |
| G3 | walks, paths, trails, cycles | `inductive Walk`, `IsPath`, `IsTrail`, `IsCycle` | `rg .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph` | `SimpleGraph.Walk` in `Walk/Basic.lean:54`; `Walk.IsTrail`, `Walk.IsPath`, `Walk.IsCircuit`, `Walk.IsCycle` in `Paths.lean:69-84` | a yes; b broad graph API; c bridge needed for lattice path conventions | Mathlib |
| G4 | finite path counting | `Fintype {p : G.Walk u v | p.IsPath ...}` | `rg .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Walk` | finite instances in `Walk/Counting.lean:151-166` | a yes; b finite graph/local-finite settings; c not self-avoiding-walk connective constant | Mathlib |
| G5 | finite sets/types | `structure Finset`, `class Fintype` | `rg .lake/packages/mathlib/Mathlib/Data` | `Finset` in `Data/Finset/Defs.lean:75`; `Fintype` in `Data/Fintype/Defs.lean:57` | a yes; b yes; c directly useful | Mathlib |
| G6 | Bernoulli set product measure | `def setBernoulli`, `setBernoulli_*` | `rg .lake/packages/mathlib/Mathlib/Probability` | `ProbabilityTheory.setBernoulli` in `Probability/Distributions/SetBernoulli.lean:42` plus finite singleton lemmas at lines `102`, `119` | a yes; b set-valued Bernoulli product; c bridge needed for fixed lattice-edge configurations | Mathlib |
| G7 | probability product measure | `ProbabilityMeasure`, `FiniteMeasure.pi`, `Measure.pi` | `rg .lake/packages/mathlib/Mathlib/MeasureTheory` | `IsProbabilityMeasure` in `Measure/Typeclasses/Probability.lean:63`; `ProbabilityMeasure.pi` in `Measure/FiniteMeasurePi.lean:72`; `Measure.pi` in `MeasureTheory/Constructions/Pi.lean:213` | a yes; b general measure API; c setup work needed for percolation events | Mathlib |
| G8 | Bernoulli percolation definitions | `BondConfiguration`, `BernoulliBond`, `CriticalParameter` | `rg Percolation` | scaffolds in `Percolation/Core/Configuration.lean`, `Bernoulli/Basic.lean`, and `Critical/Basic.lean` | a partial; b scaffold only; c production replacement needed | our-repo |
| G9 | planar duality definitions | `PlanarDualPair`, `dual lattice`, `RSW` | `rg Percolation` and `rg Mathlib` | `PlanarDualPair` scaffold in `Percolation/Planar/Basic.lean:14`; no Mathlib percolation-duality API found | a partial; b scaffold only; c major bridge needed | our-repo / nowhere |
| G10 | random-cluster definitions | `RandomClusterModel`, `random-cluster` | `rg Percolation` and `rg Mathlib` | `RandomClusterModel` scaffold in `Percolation/RandomCluster/Basic.lean:21`; no Mathlib random-cluster API found | a partial; b scaffold only; c partition-function/measure layer absent | our-repo / nowhere |
| G11 | FKG/BK/Russo percolation theorems | `FKG`, `BK`, `Russo`, `FourFunctions` | `rg Mathlib` and `rg Percolation` | only a bibliographic FKG mention in `Combinatorics/SetFamily/FourFunctions.lean:56`; project files mark FKG/BK/Russo as targets/scaffolds | a no usable percolation theorem; b no; c absent | nowhere |
| G12 | percolation, connective constants, RSW | `percolation`, `self-avoiding`, `connective constant`, `RSW` | `rg Mathlib` and `rg Percolation` | no Mathlib percolation/connective-constant/RSW APIs found; project docs mark them absent/deep | a no; b no; c absent | nowhere |

Each scorecard below uses the environment above. The `GROUNDING EVIDENCE` line in
each unit lists the relevant shared rows for criteria 2, 5, and 6.

## Criterion 0 - Unit Of Work

The folder is heterogeneous, and no single whole-folder score would be useful.
I split by source and then by proof style:

- Grimmett, *Percolation*: Chapters 1-4 foundational Bernoulli material;
  Chapters 5-8 subcritical/supercritical phase theory; Chapter 11 planar
  two-dimensional theory.
- Grimmett, *The Random-Cluster Model*: Chapters 1-3 finite and monotonic
  random-cluster measures; Chapters 4-6 infinite-volume, phase transition, and
  planar duality.
- Kesten, *Percolation Theory for Mathematicians*: Chapters 2-7 planar periodic
  percolation and RSW/exact-threshold machinery; Chapter 11 random electrical
  networks.
- Duminil-Copin, *Introduction to Bernoulli percolation*: Sections 1-2 basic
  phase transition and standard toolbox; Sections 3-4 non-critical and critical
  two-dimensional theory.
- Grimmett, *Probability on Graphs*: Chapters 3-4 elementary percolation and
  association; Chapters 5 and 8 advanced percolation and random-cluster overview.

These splits are provisional pending the scorecards. The closing re-segmentation
check records that the splits survive, with one important caveat: any target using
Grimmett's planar-circuit sentence should be treated as a separate geometric
subproject.

## Recommended Use

1. Use Grimmett, *Percolation*, Chapters 1-4 as the primary source for the
   current Bernoulli layer, but pair every planar-duality target with an explicit
   discrete frontier/parity statement before launching autonomous proof search.
2. Use Grimmett, *The Random-Cluster Model*, Chapters 1-3 next for finite
   random-cluster measures, stochastic order, positive association, and finite
   couplings.
3. Use Kesten as a rigorous secondary source for two-dimensional planar
   percolation once the repo has a stable planar-duality API.
4. Use Duminil-Copin and *Probability on Graphs* as orientation and target
   selection references, not as stand-alone proof scripts for autonomous Lean
   formalization.

---

SOURCE: `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf` - Geoffrey Grimmett,
*Percolation*, second edition

UNIT OF WORK: Chapters 1-4: bond percolation, critical probability, FKG/BK/Russo,
critical-probability inequalities, and cluster-count preliminaries
FAULT LINE: Chapters 5-8 import much deeper subcritical/supercritical machinery,
and Chapter 11 changes proof style to planar duality; split is PROVISIONAL
pending scores.
SIZE/EFFORT: about 4 chapters; large foundational layer.
GROUNDING EVIDENCE: rows G1-G8, G11-G12.

SCORECARD:
1. Explicit proofs        Yellow - The FKG/BK/Russo and critical-probability material is mostly proved, but the Chapter 1 Theorem 1.10 Peierls step compresses the surrounding closed-dual-circuit implication.
2. Unusual conventions    Yellow - Cubic lattices, bond configurations, open clusters, `theta(p)`, and `p_c` are standard, but rows G8/G12 show only scaffolds or absent Mathlib APIs on this branch.
3. Logical structure      Yellow - The chapter order is clear, but some dependencies are stated informally, especially around planar duality and comparison inequalities.
4. Left-to-reader gaps    Yellow - Exercises and notes are mostly peripheral, but the elementary planar Peierls proof needs an explicit replacement for "there must be a circuit".
5. Mathlib proximity      Red - Rows G1-G7 supply graph/probability infrastructure, but rows G8/G11/G12 show no production percolation, critical-probability, self-avoiding-walk, or planar-duality layer.
6. Definition uniqueness  Yellow - The main Bernoulli objects are canonical mathematically, but rows G8/G12 show the production Lean definitions still need to be fixed.
7. Constructive content   Yellow - Infinite clusters, product measures on countable edge sets, and supremum/infimum critical definitions are classical but standard for Lean.
8. Figure-dependent args  Red - The Chapter 1 Peierls sentence is carried by a planar picture unless supplemented by a formal frontier/parity lemma.
9. Tower structure        Green - Once the planar sentence is isolated, the layer decomposes well into cubic graph, Bernoulli cylinders, path counting, connective constants, and finite planar frontier facts.

VERDICT: DO NOT PROCEED as a stand-alone source for planar targets · effort note: >30 human interventions for this layer until the planar interfaces are supplied - Use it as
the primary source only after adding explicit geometric interfaces; without that
scaffolding the agent will recreate a Jordan-curve-like argument unsafely.

KEY RISKS:
- The planar-circuit implication in Theorem 1.10 is mathematically true but not
  fully textual enough for autonomous formalization.
- The missing Mathlib percolation layer forces local definitions before any
  source proof can be followed line by line.

---

SOURCE: `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf` - Geoffrey Grimmett,
*Percolation*, second edition

UNIT OF WORK: Chapters 5-8: exponential decay, subcritical phase, dynamic/static
renormalization, and supercritical phase
FAULT LINE: Depends on Chapters 1-4 and uses more analytic and renormalization
machinery; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 4 chapters; very large phase-theory layer.
GROUNDING EVIDENCE: rows G1-G8, G11-G12.

SCORECARD:
1. Explicit proofs        Yellow - The chapters contain serious proofs, but the Menshikov/Aizenman-Barsky and renormalization arguments are dense and use background estimates that need unpacking.
2. Unusual conventions    Yellow - Connectivity functions, correlation length, slabs, boxes, and renormalized blocks are standard, but rows G8/G12 show no production Lean API for them.
3. Logical structure      Yellow - The major theorem flow is visible, but the proof dependencies branch through differential inequalities, block events, and finite-volume estimates.
4. Left-to-reader gaps    Yellow - Many "standard" estimates are local but would need named Lean lemmas before autonomous proof search.
5. Mathlib proximity      Red - Rows G1-G7 provide general infrastructure, but rows G8/G12 show no percolation correlation-length, slab, renormalization, or Menshikov/Aizenman-Barsky APIs.
6. Definition uniqueness  Yellow - The central phase-theory quantities have standard textbook definitions, but row G12 shows their Lean formulations are not yet chosen.
7. Constructive content   Yellow - The arguments use classical compactness, monotone limits, and asymptotic estimates.
8. Figure-dependent args  Green - The figures guide intuition; the main proof obligations are primarily algebraic/probabilistic estimates.
9. Tower structure        Yellow - Natural strata exist, but the interfaces between differential inequalities and renormalization need human-chosen statements.

VERDICT: NEEDS SCAFFOLDING · effort note: >30 human interventions expected at current scaffold level - A good long-term source after the Chapter 1-4 layer
is stable, but not a low-intervention starting point.

KEY RISKS:
- Renormalization introduces many finite-volume event definitions that should be
  fixed by a human before proof search.
- The missing lower-level percolation API dominates the cost.

---

SOURCE: `kg/textbooks/Grimmett-Percolation-2ed-1999.pdf` - Geoffrey Grimmett,
*Percolation*, second edition

UNIT OF WORK: Chapter 11: bond percolation in two dimensions, planar duality,
`p_c = 1/2`, tail estimates, annuli, and power-law inequalities
FAULT LINE: Changes proof style to planar topology, crossings, annuli, and exact
threshold arguments; split is PROVISIONAL pending scores.
SIZE/EFFORT: one long chapter; large planar layer.
GROUNDING EVIDENCE: rows G1-G9, G12.

SCORECARD:
1. Explicit proofs        Yellow - The chapter is rigorous at textbook level, but several planar separation and crossing facts are presented in a compressed geometric style.
2. Unusual conventions    Yellow - Square-lattice duality, rectangles, crossings, circuits, and annuli are standard, but row G9 shows only a planar-duality scaffold here.
3. Logical structure      Yellow - The sequence planar duality -> exact threshold -> supercritical tails -> annuli is clear, but crossing lemmas create many implicit geometric side conditions.
4. Left-to-reader gaps    Yellow - The chapter assumes comfort with planar graph separation arguments that are not already present in Mathlib.
5. Mathlib proximity      Red - Rows G9/G12 show no square-lattice percolation, RSW-style crossing theory, or planar dual lattice API in Mathlib or this branch.
6. Definition uniqueness  Yellow - Crossings and annular circuits are canonical mathematically but admit many Lean encodings, especially around boundary conventions.
7. Constructive content   Yellow - Classical probability and limiting arguments are standard, but the formal event boundaries must be chosen carefully.
8. Figure-dependent args  Red - Key intuition about dual crossings, circuits, and annuli is visual unless replaced by discrete parity/frontier statements.
9. Tower structure        Yellow - There is a useful tower, but it depends on a planar-duality foundation that must be built first.

VERDICT: DO NOT PROCEED as a stand-alone autonomous source · effort note: >30 human interventions before the planar-duality API exists - First build a
formal planar-duality toolkit and use this chapter as the theorem-level guide.

KEY RISKS:
- Figure-carried crossing/separation facts can silently change the Lean theorem.
- Boundary conventions for rectangles and annuli can multiply if not centralized.

---

SOURCE: `kg/textbooks/Grimmett-RandomClusterModel-2006.pdf` - Geoffrey Grimmett,
*The Random-Cluster Model*

UNIT OF WORK: Chapters 1-3: finite random-cluster measures, monotonic measures,
positive association, comparison inequalities, and partition functions
FAULT LINE: Chapters 4-6 move to infinite-volume and planar phase-transition
results; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 3 chapters; medium finite-measure layer.
GROUNDING EVIDENCE: rows G1-G7, G10-G11.

SCORECARD:
1. Explicit proofs        Green - The finite-graph model, FK/Potts coupling, stochastic ordering, positive association, and comparison facts are presented as a detailed finite-measure theory.
2. Unusual conventions    Yellow - Edge configurations, cluster counts, finite measures, stochastic order, and increasing events are standard, but row G10 shows the random-cluster Lean layer is only a scaffold.
3. Logical structure      Green - The dependency path finite random-cluster measure -> monotonicity -> association -> finite comparisons is clean.
4. Left-to-reader gaps    Yellow - Some finite combinatorial/probability manipulations are terse, but they are close to Mathlib-style finite-set arguments.
5. Mathlib proximity      Red - Rows G1-G7 provide finite graph/probability infrastructure, but row G10 shows no production random-cluster measure or FK coupling layer.
6. Definition uniqueness  Yellow - The finite random-cluster measure `p^open (1-p)^closed q^k / Z` is canonical, but row G10 shows the Lean definition is not production-ready.
7. Constructive content   Green - This unit is mostly finite and should avoid heavy nonconstructive analysis.
8. Figure-dependent args  Green - Figures are illustrative; the logical content is formula-based.
9. Tower structure        Green - The unit is an excellent tower for `RandomCluster/Basic`, finite measures, and stochastic-order files.

VERDICT: NEEDS SCAFFOLDING · effort note: ~15-30 human interventions after finite graph interfaces are fixed - The exposition is strong, but local random-cluster
definitions and finite graph interfaces must be fixed first.

KEY RISKS:
- The main obstacle is absent project infrastructure, not source quality.
- Boundary-condition choices should be postponed until the finite model is solid.

---

SOURCE: `kg/textbooks/Grimmett-RandomClusterModel-2006.pdf` - Geoffrey Grimmett,
*The Random-Cluster Model*

UNIT OF WORK: Chapters 4-6: infinite-volume measures, phase transition, and
two-dimensional random-cluster duality
FAULT LINE: Depends on Chapters 1-3 and adds weak limits, DLR-style consistency,
boundary conditions, and planar duality; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 3 chapters; large infinite-volume/planar layer.
GROUNDING EVIDENCE: rows G1-G7, G9-G10.

SCORECARD:
1. Explicit proofs        Yellow - The main arguments are documented, but infinite-volume uniqueness, pressure convexity, and planar duality require substantial background infrastructure.
2. Unusual conventions    Yellow - Free/wired boundary conditions and random-cluster infinite-volume measures are standard, but Lean encodings must choose between weak-limit and DLR presentations.
3. Logical structure      Green - The book stages finite measures before infinite-volume limits and then phase transition/planar duality.
4. Left-to-reader gaps    Yellow - Some compactness, weak convergence, and planar-duality steps are compressed relative to Lean's needs.
5. Mathlib proximity      Red - Rows G1-G7 give measure-theoretic ingredients in pieces, but rows G9/G10 show no random-cluster infinite-volume or planar random-cluster API.
6. Definition uniqueness  Yellow - Finite measures are canonical; infinite-volume random-cluster measures have several equivalent formal presentations.
7. Constructive content   Yellow - Weak limits, consistency, and phase-transition definitions use classical compactness and choice.
8. Figure-dependent args  Yellow - Planar duality uses geometric intuition, though less nakedly than introductory percolation proofs.
9. Tower structure        Green - The finite-to-infinite-to-planar sequence gives good module boundaries.

VERDICT: NEEDS SCAFFOLDING · effort note: >30 human interventions until finite random-cluster and boundary-condition APIs exist - Good source after finite random-cluster measures and
boundary-condition APIs exist.

KEY RISKS:
- Choosing the infinite-volume representation too early could make later theorem
  statements awkward.
- Planar random-cluster duality should reuse the Bernoulli planar-duality toolkit.

---

SOURCE: `kg/textbooks/978-1-4899-2730-9.pdf` - Harry Kesten, *Percolation Theory
for Mathematicians*

UNIT OF WORK: Chapters 2-7: periodic graphs, matching pairs, planar separation,
critical regions, increasing events, RSW, and proof of the main planar theorems
FAULT LINE: Chapter 11 on electrical networks uses a different analytic/electrical
interface; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 6 chapters; very large rigorous planar layer.
GROUNDING EVIDENCE: rows G1-G9, G11-G12.

SCORECARD:
1. Explicit proofs        Green - The monograph is explicitly aimed at rigorous proofs and even isolates point-set separation material in Chapter 2.4.
2. Unusual conventions    Yellow - Matching pairs, periodic site/bond setups, and older notation are precise but farther from Mathlib and from the current cubic-lattice project than Grimmett's formulation.
3. Logical structure      Yellow - The theorem dependencies are real and rigorous, but the generality over periodic planar graphs makes the DAG harder to see.
4. Left-to-reader gaps    Yellow - Kesten often supplies the missing hard proofs, but the details are long and "clumsy" by the author's own preface, which means Lean needs intermediate lemmas.
5. Mathlib proximity      Red - Rows G8-G9/G12 show missing or scaffold-only percolation, matching-pair, planar separation, and RSW-specific infrastructure.
6. Definition uniqueness  Yellow - The objects are standard in Kesten's framework, but they are not the project's current canonical cubic-lattice definitions.
7. Constructive content   Yellow - Classical probability, limiting, and planar separation arguments are pervasive.
8. Figure-dependent args  Yellow - Unlike shorter sources, Kesten proves topological/separation ingredients, but planar intuition and diagrams still guide the development.
9. Tower structure        Yellow - There is a tower, but it is a large general planar-periodic tower rather than a minimal square-lattice one.

VERDICT: NEEDS SCAFFOLDING · effort note: >30 human interventions if formalized directly; fewer if used for isolated planar gaps - Excellent rigorous secondary source for planar
percolation, but too general and notation-heavy for a first autonomous run.

KEY RISKS:
- Formalizing Kesten directly may spend most effort on general periodic graph
  infrastructure not needed for the current square-lattice targets.
- It is best used to discharge specific planar/topological gaps in Grimmett.

---

SOURCE: `kg/textbooks/978-1-4899-2730-9.pdf` - Harry Kesten, *Percolation Theory
for Mathematicians*

UNIT OF WORK: Chapter 11: random electrical networks and resistance estimates
FAULT LINE: Uses percolation plus electrical network/flow theory rather than the
planar critical-probability machinery; split is PROVISIONAL pending scores.
SIZE/EFFORT: one chapter; medium but API-heavy electrical-network layer.
GROUNDING EVIDENCE: rows G1-G7 plus absent percolation rows G8-G12.

SCORECARD:
1. Explicit proofs        Yellow - The chapter contains rigorous arguments, but resistance estimates involve several analytic and probabilistic estimates that need decomposition.
2. Unusual conventions    Yellow - Random resistors, passable bonds, and resistance notation are standard for the source but not aligned with a current project API.
3. Logical structure      Yellow - The flow/resistance development is coherent but depends on earlier crossing and percolation facts.
4. Left-to-reader gaps    Yellow - Many estimates would need named finite-network and limiting lemmas before autonomous proving.
5. Mathlib proximity      Red - Rows G1-G7 provide graph/probability foundations, but rows G8-G12 show no ready electrical-network plus random-percolation resistance theory.
6. Definition uniqueness  Yellow - Effective resistance has standard equivalent formulations; the Lean API must choose Dirichlet, flow, or matrix definitions.
7. Constructive content   Yellow - Optimization over flows and limiting random networks use classical existence arguments.
8. Figure-dependent args  Green - The main logic is via formulas and inequalities rather than figures.
9. Tower structure        Yellow - This can be split into finite electrical networks, random subnetwork events, and asymptotic resistance bounds.

VERDICT: NEEDS SCAFFOLDING · effort note: ~15-30 human interventions after percolation and electrical-network APIs exist - A later target after both percolation and finite
electrical-network APIs exist.

KEY RISKS:
- Effective resistance has multiple mathematically equivalent Lean encodings.
- The target is not on the immediate Bernoulli critical-probability path.

---

SOURCE: `kg/textbooks/2017percolation.pdf` - Hugo Duminil-Copin,
*Introduction to Bernoulli percolation*

UNIT OF WORK: Sections 1-2: phase transition in Bernoulli percolation and the
standard toolbox of increasing coupling, Harris-FKG, BK/Reimer, Margulis-Russo,
and ergodicity
FAULT LINE: Sections 3-4 use non-critical/critical phase theory and
two-dimensional results; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 2 short sections; compact toolbox layer.
GROUNDING EVIDENCE: rows G1-G8, G11-G12.

SCORECARD:
1. Explicit proofs        Red - The notes are intentionally exercise-oriented: BK is postponed to an exercise, Reimer is omitted, and the elementary Peierls proof uses a figure-level surrounding-circuit assertion.
2. Unusual conventions    Yellow - The definitions of `Z^d`, Bernoulli configurations, clusters, `theta(p)`, and `p_c` are standard, but row G8 shows only scaffold support here.
3. Logical structure      Green - The sections give a clean pedagogical order from definitions to coupling, FKG, BK/Reimer, Russo, and ergodicity.
4. Left-to-reader gaps    Red - Several important facts are exercises or explicitly omitted, including BK/Reimer details and measurable-event approximation.
5. Mathlib proximity      Red - Rows G8/G11/G12 show the core percolation, toolbox, and planar-duality APIs are missing or only scaffolded.
6. Definition uniqueness  Yellow - The basic Bernoulli definitions are canonical, but row G8 shows the production Lean definitions are not yet settled.
7. Constructive content   Yellow - The notes use standard classical product-measure and ergodic arguments.
8. Figure-dependent args  Red - The proof of `p_c < 1` points to figures for the closed dual circuit surrounding the origin.
9. Tower structure        Green - As an outline, the toolbox is well ordered and useful for planning.

VERDICT: DO NOT PROCEED as a primary autonomous source · effort note: low effort as orientation, high effort as proof source - Excellent orientation,
but the omitted/exercise material is exactly where an agent needs textual proof.

KEY RISKS:
- The notes are designed to make students solve key arguments.
- They are useful for theorem selection and compact statements, not for
  low-intervention Lean proof reconstruction.

---

SOURCE: `kg/textbooks/2017percolation.pdf` - Hugo Duminil-Copin,
*Introduction to Bernoulli percolation*

UNIT OF WORK: Sections 3-4: uniqueness of the infinite cluster, continuity,
exponential decay, Kesten's theorem, RSW, and conformal invariance
FAULT LINE: Depends on Sections 1-2 and shifts from toolbox exposition to major
theorem surveys; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 2 short sections; compact but theorem-heavy survey layer.
GROUNDING EVIDENCE: rows G1-G9, G11-G12.

SCORECARD:
1. Explicit proofs        Red - The sections summarize major results such as Kesten's theorem, RSW, and conformal invariance in lecture-note form rather than proving all prerequisites.
2. Unusual conventions    Yellow - The event notation and square-lattice conventions are standard, but rows G8/G9/G12 show absent or scaffolded Lean support.
3. Logical structure      Yellow - The high-level order is clear, but many theorem dependencies are cited rather than built.
4. Left-to-reader gaps    Red - Large arguments are intentionally delegated to exercises, references, or later literature.
5. Mathlib proximity      Red - Rows G9/G12 show RSW, Kesten's theorem, uniqueness, and conformal-invariance technology are absent from Mathlib and this branch.
6. Definition uniqueness  Yellow - Crossing and critical-event conventions are standard but still need precise boundary choices in Lean.
7. Constructive content   Yellow - Classical limiting and ergodic arguments dominate.
8. Figure-dependent args  Red - Critical two-dimensional arguments rely heavily on geometric crossing pictures unless replaced by formal rectangle/circuit APIs.
9. Tower structure        Yellow - The survey gives a roadmap, not a self-contained theorem tower.

VERDICT: DO NOT PROCEED as a primary autonomous source · effort note: low effort as overview, >30 interventions as a proof source - Use for overview and
target prioritization only.

KEY RISKS:
- The source is too compressed for formal reconstruction of advanced results.
- RSW and conformal-invariance targets need much stronger primary references.

---

SOURCE: `kg/textbooks/ProbOnGraph.pdf` - Geoffrey Grimmett, *Probability on
Graphs: Random Processes on Graphs and Lattices*

UNIT OF WORK: Chapters 3-4: percolation, self-avoiding walk, coupled percolation,
oriented percolation, association, FKG, BK, Hoeffding, influence, Russo, and sharp
thresholds
FAULT LINE: Chapter 5 and Chapter 8 move to advanced percolation and
random-cluster overviews; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 2 chapters; medium lecture-note layer.
GROUNDING EVIDENCE: rows G1-G8, G11-G12.

SCORECARD:
1. Explicit proofs        Yellow - The notes contain many core proofs, but their lecture-note compression and exercise structure leave more reconstruction work than Grimmett's monograph.
2. Unusual conventions    Yellow - The graph/probability notation aligns with rows G1-G7, but percolation-specific definitions remain scaffolded or absent by rows G8/G11/G12.
3. Logical structure      Green - The chapters are staged cleanly from percolation basics to association and influence tools.
4. Left-to-reader gaps    Yellow - Some proofs and applications are intentionally left to exercises or sketched for a course audience.
5. Mathlib proximity      Red - Rows G1-G7 provide graph/probability foundations, but rows G8/G11/G12 show no production percolation, influence, BK, or Russo APIs.
6. Definition uniqueness  Yellow - Basic graph definitions are Mathlib-native by rows G1-G3, but percolation and increasing-event definitions are only scaffolded by row G8.
7. Constructive content   Yellow - Classical product-measure and finite/infinite graph arguments are standard.
8. Figure-dependent args  Green - In these chapters the logical material is mostly textual/formulaic.
9. Tower structure        Green - The lecture order gives useful small formalization targets.

VERDICT: NEEDS SCAFFOLDING · effort note: ~15-30 human interventions for a narrow toolbox cluster - Good compact secondary source for statements and
proof sketches after the primary Grimmett interfaces are fixed.

KEY RISKS:
- The source is broad and terse; agents must be constrained to one theorem cluster.
- Influence/sharp-threshold material should be compared against Mathlib before
  local theorem names are chosen.

---

SOURCE: `kg/textbooks/ProbOnGraph.pdf` - Geoffrey Grimmett, *Probability on
Graphs: Random Processes on Graphs and Lattices*

UNIT OF WORK: Chapters 5 and 8: further percolation, two-dimensional critical
probability/Cardy material, and random-cluster overview
FAULT LINE: Uses the earlier graph/probability chapters but imports advanced
two-dimensional and random-cluster theory; split is PROVISIONAL pending scores.
SIZE/EFFORT: about 2 chapters; medium survey layer.
GROUNDING EVIDENCE: rows G1-G10, G12.

SCORECARD:
1. Explicit proofs        Red - The chapters are survey-like in places: Cardy's formula, SLE, and some random-cluster facts are pointers to a broader literature rather than full formal proof scripts.
2. Unusual conventions    Yellow - The conventions are standard and pedagogically explicit, but rows G8-G10/G12 show the corresponding Lean APIs are absent or scaffolded.
3. Logical structure      Yellow - The topic order is coherent, but advanced results depend on external sources.
4. Left-to-reader gaps    Red - Major proof content is necessarily omitted or assigned as course material.
5. Mathlib proximity      Red - Rows G9/G10/G12 show the required two-dimensional critical percolation, SLE-adjacent, and random-cluster APIs are absent or scaffolded.
6. Definition uniqueness  Yellow - Random-cluster boundary conditions and two-dimensional crossing conventions need precise Lean choices.
7. Constructive content   Yellow - Classical limiting and compactness arguments are routine but numerous.
8. Figure-dependent args  Red - Critical planar material and Cardy/SLE intuition are visual/geometric without a fully formal replacement in the notes.
9. Tower structure        Yellow - The source is better as a map of the field than as a staged proof tower.

VERDICT: DO NOT PROCEED as a primary autonomous source · effort note: low effort as roadmap, >30 interventions as a proof source - Use as a roadmap and
secondary reference, not as the main proof text.

KEY RISKS:
- Advanced targets here should be sourced from fuller monographs or papers.
- Random-cluster content should point back to Grimmett's dedicated book.

## Closing Re-Segmentation Check

The provisional splits survived the scoring. The key refinement is that "planar
duality" is not one homogeneous unit:

- Finite primal/dual crossing bijections, cylinder probabilities, and Peierls
  counting are suitable after scaffolding.
- Surrounding-circuit/separation assertions are stand-alone geometric targets and
  should be formalized using discrete frontier/parity formulations before any
  autonomous proof session tries to use them.
- RSW, exact `p_c = 1/2`, Cardy/SLE, and conformal-invariance material should be
  treated as later projects with separate source audits.

Final recommendation: keep Grimmett's two official books as the catalogued
primary sources, add Kesten as a reviewed secondary source when planar topology
becomes the bottleneck, and use the Duminil-Copin and *Probability on Graphs*
PDFs mainly for orientation, theorem selection, and compact statement comparison.
