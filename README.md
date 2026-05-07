# Permutation-Schedule Dominance for Two-Stage Assembly Flow Shops with Divisible Work

Reproducibility artifact for the manuscript

> Bowman, E. (2026). Permutation-Schedule Dominance for Two-Stage Assembly
> Flow Shops with Divisible Work. *European Journal of Operational
> Research* (under review).

This repository contains:

- The Lean 4 formalization of the main theorem and its supporting lemmas.
- A Scala simulation that exhaustively verifies the structural properties
  on small instances and runs the full computational sweep.
- A claims registry mapping every paper claim to its verification (code
  path, Lean module, or both).
- The manuscript LaTeX source, bibliography, and compiled PDF.

A live web-app demonstration of the dominance principle is hosted
separately at https://ebowman.github.io/prioritizer/ and is not part of
this archive.

## How to cite

If you use this artifact, please cite the paper. A `CITATION.cff` file is
provided so that GitHub's "Cite this repository" button produces correct
metadata. Once the Zenodo DOI is minted, please cite that DOI alongside
the paper.

## Repository layout

```
.
├── README.md
├── LICENSE                 MIT (covers code, Lean, scripts, registry)
├── CITATION.cff            machine-readable citation metadata
├── claims-registry.yaml    paper <-> code <-> Lean traceability
├── paper/
│   ├── LICENSE             CC BY 4.0 (covers .tex, .bib, .pdf)
│   ├── synchronization.tex
│   ├── synchronization.bib
│   └── synchronization.pdf
├── scripts/
│   └── check-claims.sh     verifies registry entries match code + LaTeX
├── lean/                   Lean 4 formalization (zero `sorry` on main theorem)
└── simulation/             Scala cross-build (JVM tests + Scala.js)
```

## Reproducing the verification claims

### 1. Run the claims-registry traceability check

```bash
bash scripts/check-claims.sh
```

This verifies that every claim ID in `claims-registry.yaml` has both
a corresponding LaTeX label in `paper/synchronization.tex` and a
verification path that exists on disk.

### 2. Run the Scala test suite (JVM)

Requires sbt and a recent JDK (Java 17+).

```bash
cd simulation
sbt prioritizerJVM/test
```

This runs all 25 tests, including `ClaimsVerificationSuite`, which
anchors quantitative claims (config counts, exhaustive verification
properties P1a–P4) used in the paper.

### 3. Run the verification sweep

```bash
cd simulation
sbt 'prioritizerJVM/run quick'   # fast pass over the 39-config standard set
sbt 'prioritizerJVM/run full'    # full computational sweep
sbt 'prioritizerJVM/run chain'   # chain-extension verification
```

### 4. Check the Lean 4 formalization

Requires `elan` and a Lean 4 toolchain matching `lean/lean-toolchain`.

```bash
cd lean
lake build
```

A successful build with no `sorry` warnings on the main theorem confirms
the formalization is closed.

### 5. Compile the manuscript

Requires a TeX Live distribution including `biber` and `biblatex-apa`.

```bash
cd paper
pdflatex synchronization.tex
biber synchronization
pdflatex synchronization.tex
pdflatex synchronization.tex
```

## Versioning and DOI

Each tagged release of this repository is automatically deposited on
Zenodo, which mints a DOI for that snapshot. The paper cites the
"all versions" parent DOI so that future revisions remain reachable
from the original citation.

## Licensing

- **Code, Lean, scripts, and the claims registry** are released under
  the MIT License — see `LICENSE`.
- **The manuscript text, bibliography, and compiled PDF** are released
  under Creative Commons Attribution 4.0 International — see
  `paper/LICENSE`.

## Author

Eric Bowman (King, Berlin, Germany) ·
[ORCID 0009-0003-6792-0622](https://orcid.org/0009-0003-6792-0622) ·
eric.bowman@king.com
