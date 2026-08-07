# Selection and stopping-set arguments

Read this only when a proof conditions on a **lowest, highest, leftmost, first, last, or outermost**
object — the `SELECTION_OR_STOPPING` class of
[`PICTORIAL_PROOF_PROTOCOL.md`](PICTORIAL_PROOF_PROTOCOL.md). Otherwise skip it; it will not help.

These arguments look like one informal sentence ("condition on the leftmost crossing") and expand
into the hardest part of the formalization. The material below is what previous attempts on this
repository actually hit.

## The real obstruction: one-sided locality

The picture shows a selected path with fresh randomness on one side of it. Formalizing that needs
a fiber whose *support* stays on the other side.

Generic finite reachability gives dependence on **all edges incident to the reached set** — a
two-sided support. The probability argument needs **one-sided** locality: changing bonds strictly
below the selected boundary must not change the fiber. The two-sided support is far more
convenient and it exposes exactly the extension coordinates the argument needs to be fresh.

This is the generic obstruction, not a quirk of any single proof. Establish one-sidedness before
building anything on top of the selector.

## Selectors that do not work

Each of these was tried and failed. Do not re-derive them.

| Selector | Why it fails |
|---|---|
| An **arbitrary** open crossing | Conditioning on its open bonds gives no disjoint partition of the event. |
| The **lexicographically least** path | Its fiber may query bonds geometrically below the selected path, destroying one-sided freshness. A lexicographic least is not a valid "lowest". |
| A merely **self-avoiding** crossing as a barrier | Not enough. It may revisit a side, so its union with a reflection branches and contains a loop. |
| Partitioning by the **entire trace** of a sub-region crossing | Destroys the left/right symmetry that a symmetric contact estimate depends on. |
| A **boundary-free** crossing event substituted for the source's full crossing event | Different event, different numbers. Check the exact small-scale probabilities before assuming a uniform bound; a plausible one can already be false at scale 2. |

The pattern: every selector that is cheap to define is cheap because it ignores the geometry that
makes the fiber local.

## Normalization

A selected crossing must be normalized before it can serve as a barrier:

- start at the **last** visit to the entry side;
- finish at the **first** subsequent visit to the exit side;
- every intermediate vertex strictly interior in the relevant coordinate.

Prove these as properties of the deterministic selector, not as hypotheses assumed later.

## What actually works

Prefer a **stopped exploration whose reached-face fibers carry the locality**, rather than
inventing a new ordering. A stopped interface obtained by flood fill from one boundary is often
the right canonical object already — under a rotation it *is* the lowest/leftmost crossing of the
argument, and its reachable-face fibers supply the stopping locality.

When that is available, the remaining work is usually much smaller than a new exploration module:
define the contact events around the selected interface, use symmetry on each cover, and glue the
interface to the winning contact.

## Checklist

A selection or stopping argument is complete only when all of these are formalized. Roughly in the
order a real proof discharges them:

1. a finite type or finset of candidate normalized paths, and existence of a candidate on the
   source event;
2. a deterministic selector — an order, a reachable-side region, or an explicit tie-break — with
   existence **and** uniqueness of the selected path;
3. normalization of the selected path (last-entry, first-exit, strict interior) proved;
4. an exact characterization of the fiber `{selected = P}`;
5. a finite support for that fiber event — stated as a **sufficient** support, not as a claim
   about which bonds were queried;
6. **one-sidedness**: the fiber is preserved by changing bonds on the far side;
7. disjointness of the extension event's coordinate support from the fiber support, proved as a
   `Disjoint` statement about explicit finsets;
8. measurability, and the resulting independence or conditional identity;
9. a finite disjoint-union or ratio-free summation over all possible selected paths — ratio-free so
   that empty or null fibers need no special case.

Items 5–7 are where these arguments fail. Reaching item 9 with a two-sided support means the
argument is not finished, however much of it compiles.
