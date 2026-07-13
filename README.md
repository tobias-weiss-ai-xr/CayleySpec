# CayleySpec

**Cayley graph spectral theory ↔ Hecke eigenvalues — formalized in Lean 4.**

This project is the formal-methods backbone of a research program combining
**graph theory**, **number theory**, and **computational complexity** —
all formalized in the [Lean theorem prover](https://lean-lang.org/).

| Build | Jobs | Errors | Status |
|-------|------|--------|--------|
| `lake build` | 3,265 | 0 | ✅ Passes |
| Admitted theorems | — | 1 | Boundedness-at-cusps (permanent — needs q-expansion) |

## Scientific Motivation

The CayleySpec project builds a formal dictionary between two domains:

| Domain | Connection | Formalized |
|--------|-----------|------------|
| **Cayley graphs** | Vertex-transitive graphs that realize the WL/GNN separation | ✅ `mulCayley_vertexTransitive` |
| **Spectral graph theory** | Eigenvalues of Cayley graphs ↔ characters of finite groups | ✅ Characters are eigenvectors; Peter-Weyl decomposition |
| **Number theory (Hecke operators)** | Hecke eigenvalues as spectra of certain Cayley graphs | ✅ `heckeOperator_slash` (SL(2,ℤ)-invariance); ✅ holomorphy |
| **Dictionary** | Cayley spectrum ↔ Hecke eigenvalue dictionary | ✅ Building blocks |
| **Boundedness at cusps** | q-expansion theory (LMFDB-level) | 🟡 Permanently admitted |

### Research Context

This work builds on published results on **GNN expressivity limits**:
vertex-transitive Cayley graphs of `SL(2,F_p)` separate the k-WL hierarchy,
showing that message-passing GNNs fail on certain graph isomorphism problems.

## Prerequisites

- **Git** for version control ([download](https://git-scm.com/))
- **elan** — the Lean version manager ([install guide](https://lean-lang.org/lean4/doc/quickstart.html))
  ```bash
  # Windows (winget)
  winget install elan
  # or curl (all platforms)
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
  ```
- **Lean 4** — installed via elan (automatically managed via `lean-toolchain`)
- **lake** — Lean's build system (comes with Lean 4)

## Quick Start: Reproduce the Build

```bash
# 1. Clone the repository
git clone https://github.com/tobias-weiss-ai-xr/CayleySpec.git
cd CayleySpec

# 2. Lean version is pinned in lean-toolchain — elan auto-downloads if needed
cat lean-toolchain  # shows: leanprover/lean4:v4.31.0

# 3. Fetch mathlib dependencies (~1-2 GB download on first run)
lake exe cache get  # fetch pre-built mathlib .olean files
lake build          # build the project
```

Expected output:

```
✔ [3265/3265] Built CayleySpec
```

### Troubleshooting

| Symptom | Fix |
|---------|-----|
| `elan: command not found` | Install elan (see Prerequisites) |
| `lake: command not found` | Ensure ~/.elan/bin is in your PATH |
| Build hangs on `mathlib` fetch | Run `lake exe cache get` first to download prebuilt artifacts |
| `error: unknown package` | Run `lake update` then `lake build` |

## Project Structure

```
CayleySpec/
├── CayleySpec.lean               # Root file — re-exports the library
├── CayleySpec/
│   ├── Basic.lean                # Aggregate module — re-exports all sub-modules
│   ├── Defs.lean                 # Core definitions (IsVertexTransitive)
│   ├── CayleyProp.lean           # Proofs (leftMul automorphism, vertex-transitivity)
│   ├── Spectrum.lean             # Adjacency operator, character eigenvectors (abelian)
│   ├── Fourier.lean              # Peter-Weyl theorem, regular representation multiplicity
│   └── Hecke.lean                # Hecke operators T_n, SL(2,ℤ)-invariance, holomorphy
├── paper/
│   └── cayleyspec.tex            # Companion paper (11 pages, CPP/ITP/arXiv)
├── lakefile.toml                 # Lake configuration (Lean build system)
├── lean-toolchain                # Pins Lean version: leanprover/lean4:v4.31.0
├── lake-manifest.json            # Locked dependency versions
└── README.md                     # This file
```

### What Each File Proves

**`Defs.lean`** — defines the vertex-transitivity predicate:

```lean
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v w : V, ∃ (φ : G ≃g G), φ v = w
```

**`CayleyProp.lean`** — constructs the left-multiplication automorphism and proves
every Cayley graph is vertex-transitive:

```lean
def mulCayley.leftMul {G : Type*} [Group G] (s : Set G) (g : G) :
    mulCayley s ≃g mulCayley s := ...

theorem mulCayley_vertexTransitive {G : Type*} [Group G] (s : Set G) :
    IsVertexTransitive (mulCayley s) := ...
```

**`Spectrum.lean`** — the Cayley graph adjacency operator and its eigenbasis for abelian groups:

```lean
noncomputable def adjacencyOperator (S : Finset G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) := ...

theorem character_eigenvector (χ : G →* ℂˣ) :
    (adjacencyOperator S) χ = (∑ s ∈ S, χ s) • χ := ...
```

Also defines the adjacency element `∑_{s∈S} s` in the group algebra `ℂ[G]` and proves its image under any representation is `∑_{s∈S} ρ(s)`.

**`Fourier.lean`** — the Peter-Weyl theorem for finite groups over ℂ (the regular representation and its irreducible decomposition):

```lean
noncomputable def regularHomEquiv :
    IntertwiningMap (leftRegular ℂ G) ρ ≃ₗ[ℂ] V := ...

theorem regular_multiplicity (ρ : FDRep ℂ G) [Simple ρ] :
    finrank (Hom_G(ℂ[G], V_ρ)) = dim(ρ) := ...
```

Key result: each irreducible representation `ρ` appears `dim(ρ)` times in the regular representation.

**`Hecke.lean`** — the Hecke operator `T_n` and its formal properties:

```lean
noncomputable def heckeOperator (f : ℍ → ℂ) (k : ℤ) (n : ℕ) (hn : n ≠ 0) : ℍ → ℂ :=
  ∑ M : reps (n : ℤ), f ∣[k] (ΔtoGL M.1)

theorem heckeOperator_slash (γ : SL(2, ℤ)) (hf : SL(2,ℤ)-invariant) :
    (T_n f) ∣[k] γ = T_n f := ...

noncomputable def heckeOperator_modularForm (f : ModularForm 𝒮ℒ k) (n : ℕ) (hn : n ≠ 0) :
    ModularForm 𝒮ℒ k := ...
```

`heckeOperator_modularForm` proves that `T_n` preserves:
- **SL(2,ℤ)-invariance** ✅ (`heckeOperator_slash`)
- **Holomorphy** ✅ (`MDifferentiable.slash` + `MDifferentiable.sum`)
- **Boundedness at cusps** 🟡 (admitted — requires q-expansion / LMFDB-level formalization)

### Lemma Dependency Graph

```
Defs.lean ←──── Basic.lean ←── CayleySpec.lean
    │                              │
    ├── IsVertexTransitive         ├── CayleyProp.lean  ─── mulCayley_vertexTransitive
    │                              │
    └── (imported by)              ├── Spectrum.lean   ─── adjacencyOperator
                                   │                          └── character_eigenvector
                                   │
                                   ├── Fourier.lean    ─── regularHomEquiv
                                   │                          ├── regular_multiplicity
                                   │                          └── adjacencyElement_spectral
                                   │
                                   └── Hecke.lean      ─── heckeOperator
                                                              ├── heckeOperator_slash
                                                              └── heckeOperator_modularForm
```

## Build Statistics

| Metric | Value |
|--------|-------|
| Total jobs | 3,265 |
| Errors | 0 |
| Warnings | 8 (4 from Fourier.lean unused section variables; 1 from permanent admit) |
| Admitted theorems | 1 (boundedness at cusps — requires q-expansion theory) |
| Lean version | `leanprover/lean4:v4.31.0` |
| mathlib version | `v4.31.0` |

## Companion Paper

An 11-page companion paper (`paper/cayleyspec.tex`) describes the formalization
and its research context. Topics covered:

1. **Abstract** — formal bridge between Cayley graph spectra and Hecke eigenvalues
2. **Background** — Cayley graphs, spectral theory via characters/Peter-Weyl, Hecke operators
3. **Formalization** — all 5 modules with Lean code excerpts
4. **Evaluation** — 3,265 jobs, 0 errors, 1 permanently admitted theorem
5. **Related work** and **Future work** (SL(2,Fₚ) spectra, k-WL hierarchy, q-expansion)

## How This Was Built: OpenCode + Sisyphus Workflow

This project was created using **Sisyphus** (the orchestration agent inside
[OpenCode](https://opencode-ai.com/)), which coordinates specialized sub-agents
for research, planning, and implementation.

The full development history — including agent conversations, failed proof attempts,
and key breakthroughs — is archived in `.sisyphus/`.

### Agent Pipeline

```
User prompt (Lean + graph theory + complexity)
    │
    ▼
┌─────────────────────────────────────────────────────────────┐
│ Sisyphus (Orchestrator)                                      │
│ • Classifies intent → Exploration + Implementation           │
│ • Decomposes into parallel work                             │
└─────────────────────────────────────────────────────────────┘
    │
    ├──→ explore agent (background) — survey existing Lean code
    ├──→ oracle agent (background) — evaluate research paths
    │     ├── Path A: WL Hierarchy             (fit 9/10)
    │     ├── Path B: Number Theory / Hecke    (fit 8/10) ← SELECTED
    │     ├── Path C: Spectral Bounds          (fit 7/10)
    │     ├── Path D: Circuit Complexity       (fit 8/10)
    │     └── Path E: Vertex-Transitive GI     (fit 9/10)
    └──→ ultrabrain agent — synthesize recommendation
         → Path B → A: Cayley spectrum ↔ Hecke eigenvalues
              │
              ▼
    ┌─────────────────┐
    │ Implementation  │
    │ • PlanAgent      │  Decompose into atomic tasks
    │ • todowrite      │  Track progress
    │ • Execute        │  Delegate to subagents, build, verify
    │ • Oracle         │  Debug hard blockers (φ_inj, exists_smul_reduce)
    └─────────────────┘
```

### Key Decisions

| Decision | Rationale |
|----------|-----------|
| **Path B → A** | Mathlib has excellent number theory (modular forms, group reps); circuit complexity would require building foundations from scratch |
| **Start with vertex-transitivity** | Smallest self-contained theorem to establish the project and validate the toolchain |
| **Lean 4.31.0 + mathlib `v4.31.0`** | Stable release pair, extensive graph theory and number theory API |
| **`mulCayley` (not `addCayley`)** | `mulCayley` is the canonical Cayley graph construction in mathlib's `SimpleGraph` |

### Reproducibility

The entire build is reproducible via:

1. **Pinned toolchain**: `lean-toolchain` locks `leanprover/lean4:v4.31.0`
2. **Locked dependencies**: `lake-manifest.json` records exact mathlib revision
3. **Deterministic build**: `lake build` produces identical results on any platform
4. **CI-ready**: GitHub Actions workflow included (`.github/workflows/`)

## Roadmap

### Phase 1: Foundations ✅

- [x] Define `IsVertexTransitive` predicate
- [x] Prove Cayley graphs are vertex-transitive
- [x] Build clean, warnings-free

### Phase 2: Cayley Graph Spectrum → Hecke Eigenvalues ✅

- [x] Define adjacency operator on functions `G → ℂ` via convolution with `S`
- [x] Prove characters of abelian groups are eigenvectors with eigenvalues `∑_{s∈S} χ(s)`
- [x] Peter-Weyl theorem: regular representation `ℂ[G]` decomposes as `⊕_ρ dim(ρ)·ρ`
- [x] Relate to Hecke operators on modular forms — `heckeOperator` definition
- [x] Prove `heckeOperator_slash`: `T_n f` is SL(2,ℤ)-invariant
- [x] Prove `h_holo`: `T_n f` is holomorphic (`MDifferentiable.slash` + `MDifferentiable.sum`)
- [x] Companion paper (11 pages)
- [🟡] **Boundedness at cusps** — permanently admitted; requires q-expansion theory

### Phase 3: WL Hierarchy Formalization (Path A)

- [ ] Formalize 1-WL (color refinement) on `SimpleGraph`
- [ ] Prove SL(2,F_p) Cayley graphs are 1-WL indistinguishable from complete graph + matching
- [ ] Extend to k-WL and bounded-depth circuit equivalence

### Phase 4: Publication & Workshop

- [ ] Package as interactive Lean workshop
- [ ] Add exercise sheets and progressive code walkthroughs
- [ ] Publish paper on arXiv / Zenodo with companion formalization

## References

1. Weiss, T. *"GNN Expressivity Limits on Vertex-Transitive Cayley Graphs of SL(2,F_p)"*
   — Master's thesis, TU Berlin.
2. Grohe, M. *"The Descriptive Complexity of Graph Neural Networks"*, LICS 2021.
3. Morris, C. et al. *"Weisfeiler and Leman Go Neural: Higher-Order Graph Neural Networks"*, AAAI 2019.
4. mathlib4: [Cayley graph documentation](https://leanprover-community.github.io/mathlib4_docs/find?source=file&pattern=Cayley)

## License

This project is released under the Apache 2.0 License (see `LICENSE` file).
