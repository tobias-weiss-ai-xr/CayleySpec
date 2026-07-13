/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

open Finset
open MonoidAlgebra
open scoped MonoidAlgebra

/-!
# Cayley Graph Spectrum

This file defines the adjacency operator of a Cayley graph on a group `G`
and proves its spectral decomposition.

## Main definitions

* `adjacencyOperator S` — the linear operator `(G → ℂ) →ₗ[ℂ] (G → ℂ)` given by
  `(A_S f)(g) = Σ_{s∈S} f(g*s)`.

* `adjacencyElement S` — the element `∑_{s∈S} s` in the group algebra `ℂ[G]`.

## Main theorems

* `character_eigenvector` — For an **abelian** group `G`, a character `χ : G → ℂˣ`,
  the character `χ` viewed as a function `G → ℂ` is an eigenvector of the adjacency
  operator with eigenvalue `Σ_{s∈S} χ(s)`.

* `adjacencyElement_rep` — For any representation `ρ : Representation ℂ G V`,
  the image of `adjacencyElement S` under the algebra homomorphism `asAlgebraHom ρ`
  is the sum `∑_{s∈S} ρ(s)` of the representation matrices.

## TODO

* Prove that characters form a complete orthogonal eigenbasis (Fourier inversion) for abelian G.
* Use Schur's lemma to show `adjacencyElement` acts as a scalar on each irreducible component.
* Connect the eigenvalues to Hecke operators on modular forms.

## References

* Diaconis, P. "Group Representations in Probability and Statistics." IMS, 1988.
* Babai, L. "Spectra of Cayley Graphs." J. Comb. Theory B, 1979.
-/

section abelian_spectrum

variable {G : Type*} [CommGroup G] (S : Finset G)

/--
The **adjacency operator** of the Cayley graph `Cay(G, S)` on the space of functions
`G → ℂ`. It acts by convolution with the characteristic function of `S`:

`(A_S f)(g) = Σ_{s∈S} f(g*s)`

For an undirected Cayley graph, we require `S = S⁻¹` and `1 ∉ S`.
-/
noncomputable def adjacencyOperator : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  { toFun := fun f g ↦ ∑ s ∈ S, f (g * s)
    map_add' := by
      intro f₁ f₂
      ext g
      simp [Pi.add_apply, Finset.sum_add_distrib]
    map_smul' := by
      intro c f
      ext g
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum] }

@[simp]
theorem adjacencyOperator_apply (f : G → ℂ) (g : G) :
    (adjacencyOperator S) f g = ∑ s ∈ S, f (g * s) := rfl

/--
Every character `χ : G → ℂˣ` (a group homomorphism from `G` to the multiplicative
group of ℂ) is an eigenvector of the adjacency operator `A_S`.

The eigenvalue is `λ_χ = Σ_{s∈S} χ(s)`, where `χ(s)` is interpreted as an element of ℂ
via the canonical inclusion `ℂˣ → ℂ`.

**Proof**: For any vertex `g : G`,
`(A_S χ)(g) = Σ_{s∈S} χ(g*s) = Σ_{s∈S} χ(g)*χ(s) = χ(g) * Σ_{s∈S} χ(s)`.
-/
theorem character_eigenvector (χ : G →* ℂˣ) :
    (adjacencyOperator S) (fun g ↦ (χ g : ℂ)) = (∑ s ∈ S, (χ s : ℂ)) • (fun g ↦ (χ g : ℂ)) := by
  ext g
  calc
    (adjacencyOperator S) (fun g ↦ (χ g : ℂ)) g
        = ∑ s ∈ S, ((χ (g * s) : ℂ)) := rfl
    _ = ∑ s ∈ S, ((χ g : ℂ) * (χ s : ℂ)) := by
      simp [MonoidHom.map_mul χ]
    _ = (∑ s ∈ S, (χ s : ℂ)) * (χ g : ℂ) := by
      simp [Finset.mul_sum, mul_comm]
    _ = ((∑ s ∈ S, (χ s : ℂ)) • (fun g ↦ (χ g : ℂ))) g := rfl

end abelian_spectrum

section nonabelian_spectrum

variable {G : Type*} [Group G] (S : Finset G) {V : Type*} [AddCommMonoid V] [Module ℂ V]

open MonoidAlgebra

/--
The **adjacency element** of the Cayley graph `Cay(G, S)` in the group algebra `ℂ[G]`.

This is the formal linear combination `A = ∑_{s∈S} s` in `ℂ[G]`.
Left-multiplication by `A` on `ℂ[G]` recovers the adjacency operator on functions `G → ℂ`.
-/
noncomputable def adjacencyElement : ℂ[G] := ∑ s ∈ S, MonoidAlgebra.single s (1 : ℂ)

omit [Group G] in
@[simp]
theorem adjacencyElement_apply : (adjacencyElement S : ℂ[G]) =
    ∑ s ∈ S, MonoidAlgebra.single s (1 : ℂ) :=
  rfl

/--
For any representation `ρ : Representation ℂ G V`, the image of the adjacency element
`adjacencyElement S` under the algebra homomorphism `asAlgebraHom ρ : ℂ[G] →ₐ[ℂ] End ℂ V`
is exactly the sum of representation matrices `∑_{s∈S} ρ s`.

**Proof**:
`asAlgebraHom ρ (∑ single s 1) = ∑ asAlgebraHom ρ (single s 1)`
                              `= ∑ (1 • ρ s)`
                              `= ∑ ρ s`
-/
theorem adjacencyElement_rep (ρ : Representation ℂ G V) :
    ρ.asAlgebraHom (adjacencyElement S) = ∑ s ∈ S, ρ s := by
  simp [adjacencyElement, Representation.asAlgebraHom_single, map_sum, one_smul]

end nonabelian_spectrum
