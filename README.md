# CayleySpec

**Cayley graph spectral theory formalized in Lean 4.**

This project is the formal-methods backbone of a research program combining
**graph theory**, **number theory**, and **computational complexity** —
all formalized in the [Lean theorem prover](https://lean-lang.org/).

## Scientific Motivation

The CayleySpec project aims to build a formal bridge between three domains:

| Domain | Connection | Target Theorem |
|--------|-----------|----------------|
| **Cayley graphs** | Vertex-transitive graphs that realize the WL/GNN separation | `mulCayley_vertexTransitive` — every Cayley graph is vertex-transitive |
| **Spectral graph theory** | Eigenvalues of Cayley graphs ↔ characters of finite groups | Plan: formalize the spectrum of SL(2,F_p) Cayley graphs |
| **Number theory (Hecke operators)** | Hecke eigenvalues as spectra of certain Cayley graphs | Plan: Cayley spectrum ↔ Hecke eigenvalue dictionary |

### Research Context

This work builds on published results on **GNN expressivity limits**:
vertex-transitive Cayley graphs of `SL(2,F_p)` separate the k-WL hierarchy,
showing that message-passing GNNs fail on certain graph isomorphism problems.

The long-term goal is **Path B → A** (from our Oracle analysis):

1. **Path B (Number-Theoretic Complexity from Graphs)**: Formalize the dictionary
   between Cayley graph spectra (of SL(2,F_p) and related groups) and Hecke eigenvalues
   of modular forms. This leverages mathlib's strong number theory foundations.
2. **Path A (WL Hierarchy Formalization)**: Pivot to formalizing the GNN expressivity
   hierarchy — the k-WL test, bounded-depth circuit complexity, and the formal proof
   that vertex-transitive Cayley graphs separate WL levels.

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
- **OpenCode** (optional) — for the AI-assisted workflow described below

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

Expected output after a successful build:

```
✔ [751/751] Built CayleySpec
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
│   ├── Basic.lean                # Aggregate module — re-exports Defs + CayleyProp
│   ├── Defs.lean                 # Core definitions (IsVertexTransitive)
│   └── CayleyProp.lean           # Proofs (leftMul automorphism, vertex-transitivity)
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

### Lemma Dependency Graph

```
Defs.lean              CayleyProp.lean
    │                       │
    └─── IsVertexTransitive  ←── mulCayley_vertexTransitive
                                      │
                                      └─── mulCayley.leftMul
```

The proof is short: given vertices `u v: G`, the left-multiplication by
`v * u⁻¹` sends `u` to `v` and preserves adjacency because
`(g*u)⁻¹ * (g*v) = u⁻¹ * g⁻¹ * g * v = u⁻¹ * v`.

## How This Was Built: OpenCode + Sisyphus Workflow

This project was created using **Sisyphus** (the orchestration agent inside
[OpenCode](https://opencode-ai.com/)), which coordinates specialized sub-agents
for research, planning, and implementation.

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
    ├──→ oracle agent (background) — evaluate 5 research paths
    │     ├── Candidate A: WL Hierarchy    (fit 9/10)
    │     ├── Candidate B: Number Theory   (fit 8/10) ← SELECTED
    │     ├── Candidate C: Spectral Bounds (fit 7/10)
    │     ├── Candidate D: Circuit Compl.  (fit 8/10)
    │     └── Candidate E: VT GI           (fit 9/10)
    └──→ ultrabrain agent — synthesize recommendation
         → Path B → A: Cayley spectrum ↔ Hecke eigenvalues
              │
              ▼
    ┌─────────────────┐
    │ Implementation  │
    │ • todowrite      │  Create task list
    │ • Execute        │  Install, init, write code, build
    │ • Verify         │  lsp_diagnostics, lake build
    └─────────────────┘
```

### Key Decisions

| Decision | Rationale |
|----------|-----------|
| **Path B over D** | Mathlib has excellent number theory; circuit complexity would require building foundations from scratch |
| **Start with vertex-transitivity** | Smallest self-contained theorem to establish the project and validate the toolchain |
| **Lean 4.31.0 + mathlib `v4.31.0`** | Stable release pair, extensive graph theory API available |
| **`mulCayley` (not `addCayley`)** | `mulCayley` is the canonical Cayley graph construction in mathlib's `SimpleGraph` |

### Reproducibility

The entire build is reproducible via:

1. **Pinned toolchain**: `lean-toolchain` locks `leanprover/lean4:v4.31.0`
2. **Locked dependencies**: `lake-manifest.json` records exact mathlib revision
3. **Deterministic build**: `lake build` produces identical results on any platform
4. **CI-ready**: GitHub Actions workflow included (`.github/workflows/`)

## Roadmap

### Phase 1: Foundations ✅ (Current State)

- [x] Define `IsVertexTransitive` predicate
- [x] Prove Cayley graphs are vertex-transitive
- [x] Build clean, warnings-free

### Phase 2: Cayley Graph Spectrum → Hecke Eigenvalues (Path B)

- [ ] Define adjacency spectrum of `mulCayley G S` via group characters
- [ ] Prove character formula: spectrum of Cayley graph is given by character sums
- [ ] Relate to Hecke operators on modular forms (for GL(2,Z/qZ))
- [ ] Formalize dictionary: `Hecke eigenvalue` ↔ `Cayley graph eigenvalue`

### Phase 3: WL Hierarchy Formalization (Path A)

- [ ] Formalize 1-WL (color refinement) on `SimpleGraph`
- [ ] Prove SL(2,F_p) Cayley graphs are 1-WL indistinguishable from complete graph + matching
- [ ] Extend to k-WL and bounded-depth circuit equivalence

### Phase 4: Workshop Refinement

- [ ] Package as interactive Lean workshop
- [ ] Add exercise sheets and progressive code walkthroughs
- [ ] Publish paper on Zenodo with companion formalization

## References

1. Weiss, T. *"GNN Expressivity Limits on Vertex-Transitive Cayley Graphs of SL(2,F_p)"*
   — Master's thesis, TU Berlin.
2. Grohe, M. *"The Descriptive Complexity of Graph Neural Networks"*, LICS 2021.
3. Morris, C. et al. *"Weisfeiler and Leman Go Neural: Higher-Order Graph Neural Networks"*, AAAI 2019.
4. mathlib4: [Cayley graph documentation](https://leanprover-community.github.io/mathlib4_docs/find?source=file&pattern=Cayley)

## License

This project is released under the Apache 2.0 License (see `LICENSE` file).
