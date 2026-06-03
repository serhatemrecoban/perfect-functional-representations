---
layout: default
title: Formal Verification of "On Perfect Functional Representations"
---

<section class="hero">
  <p class="eyebrow">Lean 4 formalization</p>
  <h1>On Perfect Functional Representations</h1>
  <p class="lead">
    This site collects the Lean formalization of the paper, generated API documentation,
    and a Blueprint dependency graph for the main definitions, lemmas, and theorems.
  </p>
  <div class="hero-meta">
    <span class="pill">Lean 4.29.1</span>
    <span class="pill">Blueprint dependency graph enabled</span>
    <span class="pill">Main target builds without sorry</span>
    <span class="pill">Theorem 1 forward direction in progress</span>
  </div>
</section>

<section class="section">
  <h2>Explore the formalization</h2>
  <p>
    The published site mirrors the structure used by other public Lean projects: a landing page,
    generated API documentation, a blueprint, and a dependency graph page that shows how the paper's
    central results fit together.
  </p>
  <div class="grid">
    <a class="card" href="./blueprint/">
      <span class="card-kicker">Blueprint</span>
      <h2>Paper roadmap</h2>
      <p>Read the formalization blueprint aligned with the paper's definitions and numbered results.</p>
    </a>
    <a class="card" href="./blueprint/dep_graph_document.html">
      <span class="card-kicker">Dependency graph</span>
      <h2>Result dependencies</h2>
      <p>Inspect the theorem graph generated from the blueprint's \uses annotations.</p>
    </a>
    <a class="card" href="./docs/">
      <span class="card-kicker">API documentation</span>
      <h2>Lean declarations</h2>
      <p>Browse generated documentation for the current Lean modules and theorem declarations.</p>
    </a>
    <a class="card" href="https://github.com/serhatemrecoban/perfect-functional-representations">
      <span class="card-kicker">GitHub</span>
      <h2>Repository</h2>
      <p>Host the project in the matching repository slug to make the site links work without edits.</p>
    </a>
  </div>
</section>

<section class="section">
  <h2>Current status</h2>
  <p>
    The current Lean development has moved beyond a placeholder scaffold. The main target now builds without
    <code>sorry</code>, theorem 1's backward implication is constructive, and the endpoint reduction from the lifted
    matrix to the one-vector matrix is constructive. The remaining gap in theorem 1 is the start-side bridge from a
    raw singular matrix <code>M</code> to the canonical support-restricted recursive state.
  </p>
  <div class="status-grid">
    <div class="status-block">
      <strong>Formal content</strong>
      <span>Finite positive representations, lifted-output machinery, and support-restricted recursion for theorem 1 are implemented in Lean.</span>
    </div>
    <div class="status-block">
      <strong>Documentation</strong>
      <span>GitHub Actions will build the home page, the blueprint, and the generated API docs together.</span>
    </div>
    <div class="status-block">
      <strong>Current blocker</strong>
      <span>The constructive PPS/PPM/VPM bridge from <code>M</code> to <code>supportedSubmatrix M</code> is still the main unfinished theorem-1-forward step.</span>
    </div>
    <div class="status-block">
      <strong>Publishing target</strong>
      <span>Intended Pages URL: serhatemrecoban.github.io/perfect-functional-representations.</span>
    </div>
  </div>
</section>