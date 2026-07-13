/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import CayleySpec.Defs
import CayleySpec.CayleyProp
import CayleySpec.Spectrum
import CayleySpec.Fourier
import CayleySpec.Hecke

/-!
# CayleySpec — Formalizing Cayley Graph Properties in Lean

This project formalizes properties of Cayley graphs using the Lean theorem prover
and mathlib4. The initial focus is on proving that Cayley graphs are vertex-transitive,
with plans to extend to spectral theory and computational complexity.

## Contents

* `CayleySpec.Defs` — basic definitions including `IsVertexTransitive`.
* `CayleySpec.CayleyProp` — proofs that Cayley graphs are vertex-transitive.
* `CayleySpec.Spectrum` — the Cayley graph adjacency operator and its eigenbasis
  (characters of the group, for abelian groups).
-/

