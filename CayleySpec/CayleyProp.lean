/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.Combinatorics.SimpleGraph.Cayley
import CayleySpec.Defs

open SimpleGraph

/-!
# Cayley Graphs are Vertex-Transitive

This file proves that every Cayley graph is vertex-transitive.
The key construction is the left-multiplication automorphism:
for any group element `g`, the map `x ↦ g * x` is a graph isomorphism
of the Cayley graph `mulCayley s`.

## Main definitions

* `SimpleGraph.mulCayley.leftMul g` — the left-multiplication automorphism
  of a Cayley graph by the element `g`.

## Main theorems

* `SimpleGraph.mulCayley_vertexTransitive s` — for any generating set `s`,
  the Cayley graph `mulCayley s` is vertex-transitive.

## TODO

* Add the additive analogue `addCayley` via `to_additive`.
* Prove that the construction yields a group homomorphism `G → Aut(Cay(G, S))`.
* Compute the automorphism group of specific Cayley graphs (e.g. cycles, complete graphs).
-/

namespace SimpleGraph

namespace mulCayley

/--
Left multiplication by a group element `g` is a graph automorphism of the Cayley graph.

Given `g : G`, the map `x ↦ g * x` on vertices is an isomorphism from `mulCayley s`
to itself. This holds because
`(g*u)⁻¹ * (g*v) = u⁻¹ * g⁻¹ * g * v = u⁻¹ * v`,
so adjacency (via `u⁻¹ * v ∈ s`) is preserved and reflected.
-/
def leftMul {G : Type*} [Group G] (s : Set G) (g : G) : mulCayley s ≃g mulCayley s :=
  { toFun := fun x => g * x
    invFun := fun x => g⁻¹ * x
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp
    map_rel_iff' := by
      intro u v
      simp [mulCayley_adj, mul_inv_rev] }

end mulCayley

/--
Every Cayley graph `mulCayley s` is vertex-transitive.

For any two vertices `u v : G`, the left-multiplication by `v * u⁻¹` maps `u` to `v`
and is an automorphism of the Cayley graph (via `leftMul`). Hence the automorphism group
acts transitively on the vertex set.
-/
theorem mulCayley_vertexTransitive {G : Type*} [Group G] (s : Set G) :
    IsVertexTransitive (mulCayley s) := by
  intro u v
  refine ⟨mulCayley.leftMul s (v * u⁻¹), ?_⟩
  simp [mulCayley.leftMul]

end SimpleGraph
