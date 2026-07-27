# kg/ — percolation source corpus and target extraction

The source corpus lives in `kg/textbooks/`.

| File | Source |
|---|---|
| `textbooks/Grimmett-Percolation-2ed-1999.pdf` | Geoffrey Grimmett, *Percolation*, 2nd ed., Springer, 1999 |
| `textbooks/Grimmett-RandomClusterModel-2006.pdf` | Geoffrey Grimmett, *The Random-Cluster Model*, Springer, 2006 |
| `source_catalog.json` | source metadata used by docs and comparator cards |
| `percolation_targets.seed.json` | initial target list; replace/enrich with page-anchored extraction |
| `TextbookCriterion/` | source-material suitability rubric imported from the optimal-transport repo, plus percolation textbook scorecards |

Regenerate derived text locally when needed, but do not commit full extracted book text:

```bash
pdftotext kg/textbooks/Grimmett-Percolation-2ed-1999.pdf kg/derived/percolation.txt
pdftotext kg/textbooks/Grimmett-RandomClusterModel-2006.pdf kg/derived/random-cluster.txt
```

The committed plan is `docs/PLAN.md`.

The textbook audit in `TextbookCriterion/textbooks-source-audit-scorecard.md`
also scores three local candidate PDFs when present in `kg/textbooks/`. They are
not part of `source_catalog.json` until explicitly promoted to comparator sources.
