/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

/-!
# Vertex-Transitive Graphs

This file defines the property of a graph being *vertex-transitive*:
a graph `G` is vertex-transitive if for every pair of vertices `v w`,
there exists a graph automorphism `φ : G ≃g G` mapping `v` to `w`.

## Main definitions

* `IsVertexTransitive G` — a `Prop` asserting that `G` is vertex-transitive.

## TODO

* Define the automorphism group `Aut(G)` as a group acting on vertices.
* Show that `IsVertexTransitive G` is equivalent to the action of `Aut(G)` being transitive.
* Show that regular graphs of certain degrees are not vertex-transitive (counterexamples).
-/

/-- A graph `G` is **vertex-transitive** if for every pair of vertices `v w`,
there exists a graph automorphism `φ : G ≃g G` (i.e. an isomorphism from `G` to itself)
that maps `v` to `w`.

Equivalently, the action of the automorphism group `Aut(G)` on the vertex set
is transitive. This definition takes the existential quantifier form for simplicity. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v w : V, ∃ (φ : G ≃g G), φ v = w
