---
layout: default
title: Formal Verification of "On Perfect Functional Representations"
---

<section class="hero">
  <p class="eyebrow">Lean 4 formalization</p>
  <h1>On Perfect Functional Representations</h1>
  <p class="lead">
    This site collects the Lean scaffold for the paper, the generated API documentation,
    and a Blueprint dependency graph for the main definitions, lemmas, and theorems.
  </p>
  <div class="hero-meta">
    <span class="pill">Lean 4.29.1</span>
    <span class="pill">Blueprint dependency graph enabled</span>
    <span class="pill">Proofs currently tracked with placeholders</span>
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
    The Lean package already compiles with theorem statements and placeholder proofs. The website scaffold now
    exposes the current mathematical structure publicly, while leaving room to tighten the definitions and replace
    each <code>sorry</code> proof incrementally.
  </p>
  <div class="status-grid">
    <div class="status-block">
      <strong>Formal content</strong>
      <span>Main definitions plus Lemma 1-6 and Theorem 1-2 are present as Lean declarations.</span>
    </div>
    <div class="status-block">
      <strong>Documentation</strong>
      <span>GitHub Actions will build the home page, the blueprint, and the generated API docs together.</span>
    </div>
    <div class="status-block">
      <strong>Publishing target</strong>
      <span>Intended Pages URL: serhatemrecoban.github.io/perfect-functional-representations.</span>
    </div>
  </div>
</section>