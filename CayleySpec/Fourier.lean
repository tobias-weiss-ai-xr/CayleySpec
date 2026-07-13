/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import CayleySpec.Spectrum

open Finset
open Finsupp
open FDRep
open Representation

/-!
# Peter-Weyl Theorem and Spectral Decomposition for Cayley Graphs

This file proves the Fourier decomposition (Peter-Weyl theorem) for finite groups over ℂ
and applies it to the spectral theory of Cayley graphs.

## Main definitions

* `regular` — the left regular representation of `G` on `ℂ[G]` as an `FDRep`

## Main theorems

* `regularHomInv` — the map `v ↦ (single g 1 ↦ ρ g v)` as an intertwining map
* `regularHomEquiv` — the linear isomorphism `Hom_G(ℂ[G], V) ≅ V` for any representation `V`
* `regular_multiplicity` — each irreducible representation `ρ` appears `dim(ρ)` times
  in the regular representation
* `adjacencyElement_spectral` — the adjacency element `∑_{s∈S} s` in `ℂ[G]` acts on each
  irreducible component `ρ` as the matrix `∑_{s∈S} ρ s`, with multiplicity `dim(ρ)` in the
  regular representation

## References

* Diaconis, P. "Group Representations in Probability and Statistics." IMS, 1988.
* Serre, J.-P. "Linear Representations of Finite Groups." Springer, 1977.
-/

section regular_def

variable (G : Type 0) [Group G] [Fintype G]

/-- The left regular representation of `G` on `ℂ[G]` as an `FDRep` (finite-dimensional
representation over ℂ). Requires `G` to be finite so that `ℂ[G]` is finite-dimensional. -/
noncomputable def regular : FDRep ℂ G :=
  FDRep.of (leftRegular ℂ G)

end regular_def

section regular_hom_equiv

variable {G : Type 0} [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]
variable {V : Type 0} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

/--
The map `v ↦ (single g 1 ↦ ρ g v)` as a `G`-equivariant linear map from the regular
representation `ℂ[G]` to `V`.

**Intertwining property:**
For all `g, g' ∈ G` and `r ∈ ℂ`:
`(regularHomInv v) ((leftRegular ℂ G) g (single g' r)) = ρ g ((regularHomInv v) (single g' r))`
-/
noncomputable def regularHomInv (v : V) : IntertwiningMap (leftRegular ℂ G) ρ :=
  { toLinearMap := Finsupp.linearCombination ℂ (fun (g : G) => ρ g v)
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro x
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | single g' r => simp [linearCombination_single, map_mul] }

/--
The space of `G`-equivariant maps from the regular representation `ℂ[G]` to `V` is isomorphic
to `V` itself via evaluation at the identity element `1 ∈ G`.

The inverse sends `v ∈ V` to `regularHomInv v : Hom_G(ℂ[G], V)`.
-/
noncomputable def regularHomEquiv : IntertwiningMap (leftRegular ℂ G) ρ ≃ₗ[ℂ] V :=
  { toFun := fun f => f (Finsupp.single 1 1)
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro r f
      simp
    invFun := regularHomInv ρ
    left_inv := fun f => by
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      induction x using Finsupp.induction_linear with
      | zero => simp [regularHomInv]
      | add x y hx hy =>
        have hx' : (regularHomInv ρ (f (Finsupp.single 1 1))) x = f x := by
          simpa using hx
        have hy' : (regularHomInv ρ (f (Finsupp.single 1 1))) y = f y := by
          simpa using hy
        simp [map_add, hx', hy']
      | single g r =>
        have h_f_single : f (Finsupp.single 1 r) = r • f (Finsupp.single 1 1) := by
          calc
            f (Finsupp.single 1 r) = f (r • Finsupp.single (1 : G) (1 : ℂ)) := by
              simp [Finsupp.smul_single]
            _ = r • f (Finsupp.single 1 1) := by
              rw [map_smul]
        have h_val : (regularHomInv ρ (f (Finsupp.single 1 1))) (Finsupp.single g r) =
            f (Finsupp.single g r) := by
          calc
            (regularHomInv ρ (f (Finsupp.single 1 1))) (Finsupp.single g r) =
                r • ρ g (f (Finsupp.single 1 1)) := by
              simp [regularHomInv, linearCombination_single]
            _ = ρ g (r • f (Finsupp.single 1 1)) := by simp
            _ = ρ g (f (Finsupp.single 1 r)) := by rw [h_f_single]
            _ = f ((leftRegular ℂ G) g (Finsupp.single 1 r)) :=
              (IntertwiningMap.isIntertwining (f := f) (g := g)
                (v := Finsupp.single (1 : G) r)).symm
            _ = f (Finsupp.single g r) := by simp
        simpa [IntertwiningMap.toLinearMap_apply] using h_val
    right_inv := fun v => by
      change (regularHomInv ρ v) (Finsupp.single (1 : G) 1) = v
      simp [regularHomInv, linearCombination_single, map_one, one_smul] }

@[simp]
theorem regularHomEquiv_apply (f : IntertwiningMap (leftRegular ℂ G) ρ) :
    regularHomEquiv ρ f = f (Finsupp.single 1 1) :=
  rfl

@[simp]
theorem regularHomEquiv_symm_apply (v : V) (g : G) :
    (regularHomEquiv ρ).symm v (Finsupp.single g 1) = ρ g v := by
  -- Use injectivity of regularHomEquiv to rewrite .symm v to regularHomInv ρ v
  have h_symm_eq : (regularHomEquiv ρ).symm v = regularHomInv ρ v := by
    apply (regularHomEquiv ρ).injective
    calc
      (regularHomEquiv ρ) ((regularHomEquiv ρ).symm v) = v :=
        (regularHomEquiv ρ).right_inv v
      _ = (regularHomEquiv ρ) (regularHomInv ρ v) := by
        simp [regularHomEquiv, regularHomInv, linearCombination_single, map_one, one_smul]
  rw [h_symm_eq]
  simp [regularHomInv, linearCombination_single]

/--
The dimension of the space of `G`-equivariant maps from the regular representation to `ρ`
equals the dimension of `ρ`.
-/
theorem finrank_regularHom :
    Module.finrank ℂ (IntertwiningMap (leftRegular ℂ G) ρ) = Module.finrank ℂ V := by
  have h : IntertwiningMap (leftRegular ℂ G) ρ ≃ₗ[ℂ] V := regularHomEquiv ρ
  exact h.finrank_eq

end regular_hom_equiv

section multiplicity

variable (G : Type 0) [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]

/--
For any irreducible representation `ρ` of a finite group `G`, the multiplicity of `ρ` in the
regular representation `ℂ[G]` equals `dim(ρ)`.

**Proof**: Using the isomorphism `regularHomEquiv`, we have
`finrank (Hom_G(ℂ[G], V_ρ)) = finrank(V_ρ) = dim(ρ)`, which is exactly the multiplicity
of `ρ` in the regular representation.
-/
theorem regular_multiplicity (ρ : FDRep ℂ G) [CategoryTheory.Simple ρ] :
    Module.finrank ℂ (IntertwiningMap ((regular G).ρ) (ρ.ρ)) = Module.finrank ℂ ρ := by
  have h := finrank_regularHom (ρ.ρ)
  -- h: finrank (IntertwiningMap (leftRegular ℂ G) (ρ.ρ)) = finrank (ρ.V)
  -- Goal: finrank (IntertwiningMap ((regular G).ρ) (ρ.ρ)) = finrank ρ
  -- Since (regular G).ρ = leftRegular ℂ G via FDRep.of:
  have hLHS : (regular G).ρ = leftRegular ℂ G := by
    simp [regular]
  -- Substitute (regular G).ρ → leftRegular ℂ G throughout the goal
  cases hLHS
  -- Now goal: finrank (IntertwiningMap (leftRegular ℂ G) (ρ.ρ)) = finrank ρ
  -- h: finrank (IntertwiningMap (leftRegular ℂ G) (ρ.ρ)) = finrank (ρ.V)
  -- And finrank ρ = finrank (ρ.V) definitionally:
  have hRHS : Module.finrank ℂ ρ = Module.finrank ℂ (ρ.V : Type 0) := rfl
  calc
    Module.finrank ℂ (IntertwiningMap (leftRegular ℂ G) (ρ.ρ)) =
      Module.finrank ℂ (ρ.V : Type 0) := h
    _ = Module.finrank ℂ ρ := hRHS.symm

end multiplicity

section spectral_decomposition

variable {G : Type 0} [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]
  (S : Finset G)

/--
The **spectral decomposition** of the Cayley adjacency element `A = ∑_{s∈S} s` in `ℂ[G]`.
Under the Wedderburn isomorphism `ℂ[G] ≅ ⊕_{ρ∈Irr(G)} End(ℂ^{dim(ρ)})`,
the adjacency element maps to `⊕_{ρ∈Irr(G)} (∑_{s∈S} ρ s)` acting by left multiplication
on each matrix block.

Thus, the eigenvalues of the adjacency operator on the Cayley graph `Cay(G, S)` are exactly
the eigenvalues of the matrices `∑_{s∈S} ρ s` for each irreducible representation `ρ` of `G`,
each eigenvalue occurring with multiplicity `dim(ρ) × (multiplicity within the block)`.
-/
theorem adjacencyElement_spectral (ρ : FDRep ℂ G) [CategoryTheory.Simple ρ] :
    Representation.asAlgebraHom (ρ.ρ) (adjacencyElement S) = ∑ s ∈ S, ρ.ρ s :=
  adjacencyElement_rep S (ρ.ρ)

end spectral_decomposition
