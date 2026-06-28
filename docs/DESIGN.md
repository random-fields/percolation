# DESIGN — percolation object hierarchy

Status: initial scaffold for review.

## Principles

- Build on Mathlib for finite sets, graph walks, probability measures, monotone functions,
  finite products, filters, topology, and real analysis.
- Keep finite-volume objects separate from infinite-volume limits.
- Represent boundary conditions explicitly in random-cluster statements.
- Prove on finite graphs first; specialize to lattices only where geometry matters.
- Use comparator cards for every theorem whose statement is sourced from Grimmett.

## Layers

### Core

Graph and configuration vocabulary:

- base graph or Mathlib `SimpleGraph`;
- bond and site configurations;
- open paths, clusters, connected components;
- cylinder events and increasing events;
- finite boxes in `Z^d`;
- lattice translations and graph automorphisms.

The current file `Percolation/Core/Configuration.lean` is only a compile-light scaffold. The first
design task is to decide the production graph carrier.

### Bernoulli

Bernoulli bond/site percolation:

- finite-edge product measures;
- stochastic domination by edge parameter;
- FKG for increasing events;
- BK/Reimer disjoint-occurrence inequality;
- Russo's formula and pivotal edges;
- critical probability `p_c`, percolation probability `θ(p)`, susceptibility.

### Critical

Phase-theory statements:

- existence and monotonicity of `θ(p)`;
- exponential decay in the subcritical phase;
- uniqueness of the infinite cluster in the supercritical phase;
- slab criteria and renormalization interfaces;
- high-dimensional mean-field/lace-expansion statements, likely as conditional interfaces first.

### Planar

Two-dimensional geometry:

- planar dual graph and dual configurations;
- rectangle crossing events;
- square-lattice self-duality;
- `p_c = 1/2` for bond percolation on `Z^2`;
- RSW/Cardy/SLE-related statements as later targets or external interfaces.

### RandomCluster

Random-cluster model:

- finite-volume measure `φ_{p,q,G}` with weight `p^open (1-p)^closed q^clusters`;
- free and wired boundary conditions;
- stochastic ordering and positive association;
- domain Markov property;
- infinite-volume weak limits and DLR measures;
- Edwards-Sokal coupling to Potts/Ising;
- planar random-cluster duality and critical point formula targets.

## Suggested Build Order

1. Finite graph configurations and events.
2. Product Bernoulli measure on finite edge sets.
3. Increasing events and stochastic order.
4. FKG on finite product spaces.
5. Open paths and clusters on finite graphs.
6. Random-cluster finite-volume mass function and partition function.
7. Boundary conditions and comparison inequalities.
8. Critical probability definitions on `Z^d`.
9. Planar duality and square-lattice exact threshold.

## Open Design Questions

- Use Mathlib `SimpleGraph` throughout, or wrap it behind a local `BaseGraph` facade?
- Encode finite edge sets as `Sym2 V`, `SimpleGraph.edgeSet`, or explicit edge types?
- Which `Z^d` representation best matches Mathlib geometry: `Fin d -> ℤ`, Euclidean lattices,
  or a dedicated graph structure?
- Should random-cluster measures be probability measures immediately, or first finite mass functions
  with normalization lemmas?
