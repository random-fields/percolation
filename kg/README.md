# kg/ — percolation source corpus and target extraction

The source corpus lives in `kg/textbooks/`.

| File | Source |
|---|---|
| `textbooks/Grimmett-Percolation-2ed-1999.pdf` | Geoffrey Grimmett, *Percolation*, 2nd ed., Springer, 1999 |
| `textbooks/Grimmett-RandomClusterModel-2006.pdf` | Geoffrey Grimmett, *The Random-Cluster Model*, Springer, 2006 |
| `textbooks/Bollobas-Riordan-Harris-Kesten-2006.pdf` | Béla Bollobás and Oliver Riordan, “A Short Proof of the Harris–Kesten Theorem,” secondary source for Theorem 11.11 |
| `textbooks/978-1-4899-2730-9.pdf` | Harry Kesten, *Percolation Theory for Mathematicians*, candidate planar-topology source |
| `textbooks/2017percolation.pdf` | Hugo Duminil-Copin, *Introduction to Bernoulli Percolation*, candidate overview source |
| `textbooks/Duminil-Copin-Graphical-Representations-Lattice-Spin-Models-2016.pdf` | Hugo Duminil-Copin, *Graphical Representations of Lattice Spin Models*, source for Proposition 2.14 |
| `textbooks/ProbOnGraph.pdf` | Geoffrey Grimmett, *Probability on Graphs*, candidate overview source |
| `source_catalog.json` | source metadata used by docs and comparator cards |
| `percolation_targets.seed.json` | initial target list; replace/enrich with page-anchored extraction |
| `TextbookCriterion/` | source-material suitability rubric imported from the optimal-transport repo, plus percolation textbook scorecards |

Regenerate derived text locally when needed, but do not commit full extracted book text:

```bash
pdftotext kg/textbooks/Grimmett-Percolation-2ed-1999.pdf kg/derived/percolation.txt
pdftotext kg/textbooks/Grimmett-RandomClusterModel-2006.pdf kg/derived/random-cluster.txt
```

The committed plan is `docs/PLAN.md`.

The textbook audit in `TextbookCriterion/textbooks-source-audit-scorecard.md` scores the three
candidate PDFs. `source_catalog.json` records their hashes and provenance, but their redistribution
status remains unreviewed. Cataloguing a file does not promote it to a primary comparator source;
that decision belongs in the target's source-selection review.
