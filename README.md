# Formal Verification of "On Perfect Functional Representations"

This project formally verifies the main results from the paper "On Perfect Functional Representations" by Serhat Emre Coban, Yanina Y. Shkel, and Emre Telatar. Website: https://serhatemrecoban.github.io/perfect-functional-representations/

## Paper Overview

The paper characterizes random variables (X, Y) for which there exists a perfect functional representation Z such that:
- Y = g(X, Z) for some deterministic function g
- X is independent of Z
- I(Y; Z) = H(Y | X) (the maximum possible mutual information is achieved)

## Project Structure

- `PerfectFunctionalRepresentations/InfoTheory.lean`: basic information-theoretic objects and placeholder definitions
- `PerfectFunctionalRepresentations/FunctionalRepresentation.lean`: functional representations, canonicality, singularity, and perfect representability
- `PerfectFunctionalRepresentations/Main.lean`: Lemma 1-3 and Theorem 1-2 as Lean statements with `sorry` proofs
- `PerfectFunctionalRepresentations.lean`: top-level library entry point

## Building the Project

```bash
lake build
```

## Website and Dependency Graph

This repository now includes a GitHub Pages scaffold for:
- a project landing page under `home_page/`
- API documentation under `docs/` when the site workflow runs
- a Lean blueprint under `blueprint/`
- a blueprint dependency graph at `blueprint/dep_graph_document.html`

The scaffold is configured for the repository slug `perfect-functional-representations`, which would publish to:

```text
https://serhatemrecoban.github.io/perfect-functional-representations/
```

If you choose a different GitHub repository name, update the GitHub URL in `home_page/index.md` and `blueprint/src/web.tex`.

To publish the site, create the GitHub repository, push this project to its `main` branch, and enable GitHub Pages with source set to `GitHub Actions`.

To build the blueprint locally, install `leanblueprint` and run:

```bash
lake build
leanblueprint web
leanblueprint serve
```

## Progress

- [x] Project initialization and Lake configuration
- [x] Main definitions and theorem statements
- [x] Compileable `sorry`-based scaffold for the paper's core results
- [x] GitHub Pages, API docs, and blueprint website scaffold
- [ ] Fill in formal proofs

## Notes

- Proofs are currently stubbed with `sorry`
- Focus on key lemmas and theorems from the paper
- Information-theoretic privacy and connections to other measures deferred
- The project currently uses a small self-contained scalar model (`Probability := Rat`) so the skeleton compiles without adding mathlib yet
