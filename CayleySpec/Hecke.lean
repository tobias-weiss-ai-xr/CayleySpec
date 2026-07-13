/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open Complex UpperHalfPlane Matrix
open FixedDetMatrices ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace HeckeOperator

open FixedDetMatrices
open ModularForm
open SpecialLinearGroup
open ModularGroup

/-!
# Hecke Operators for Level-1 Modular Forms

This file defines Hecke operators `T_n` acting on functions `f : ℍ → ℂ` of weight `k`,
and proves that they preserve the modular form property for SL(2,ℤ).

## Main definitions

* `ΔtoGL hm A`: Embed a `FixedDetMatrix` (integer entries, determinant `m ≠ 0`) into `GL(2,ℝ)`.
* `heckeOperator f k n hn`: The Hecke operator `T_n` applied to `f`, defined as the sum
  `∑_{M ∈ reps n} f ∣[k] ΔtoGL M.1`.

## Main theorems

* `slash_invariant_under_reduce`: If `f` is SL(2,ℤ)-invariant, then
  `f ∣[k] (ΔtoGL hm A) = f ∣[k] (ΔtoGL hm (reduce A))`.
* `heckeOperator_slash`: If `f` is SL(2,ℤ)-invariant, then `(T_n f)` is also SL(2,ℤ)-invariant.
* `heckeOperator_modularForm`: If `f` is a modular form, so is `T_n f`.

## References

* Diamond, F. and Shurman, J. "A First Course in Modular Forms." Springer, 2005.
* Serre, J.-P. "A Course in Arithmetic." Springer, 1973.
-/

/--
Embed a `FixedDetMatrix` (a matrix with fixed determinant `m`) into `GL(2, ℝ)`.
The integer entries are mapped to ℝ via `algebraMap ℤ ℝ`.
-/
noncomputable def ΔtoGL {m : ℤ} (hm : m ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ m) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A.1.map (algebraMap ℤ ℝ)) (by
    have hdet : (A.1.map (algebraMap ℤ ℝ)).det = (m : ℝ) := by
      simpa [A.2] using (RingHom.map_det (algebraMap ℤ ℝ) A.1).symm
    rw [hdet]
    exact_mod_cast hm)

/--
The SMul action of `SL(2,ℤ)` on `FixedDetMatrix` commutes with the embedding `ΔtoGL`:
`ΔtoGL hm (γ • A) = (γ : GL(2,ℝ)) * (ΔtoGL hm A)`.
-/
lemma ΔtoGL_smul {m : ℤ} (hm : m ≠ 0) (γ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ m) :
    ΔtoGL hm (γ • A) = (γ : GL (Fin 2) ℝ) * (ΔtoGL hm A) := by
  ext : 1
  simp only [Units.val_mul, coe_GL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]
  exact Matrix.map_mul (L := γ.1) (M := A.1) (f := algebraMap ℤ ℝ)

/--
Right-multiply a FixedDetMatrix by an SL(2,ℤ) element, producing another FixedDetMatrix.
-/
def mulRight {m : ℤ} (A : FixedDetMatrix (Fin 2) ℤ m) (γ : SL(2, ℤ)) :
    FixedDetMatrix (Fin 2) ℤ m :=
  ⟨A.1 * γ.1, by
    rw [det_mul, A.2, show (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from γ.property, mul_one]⟩

/--
The embedding `ΔtoGL` commutes with right multiplication:
`ΔtoGL hm A * (γ : GL) = ΔtoGL hm (mulRight A γ)`.
-/
lemma ΔtoGL_mul {m : ℤ} (hm : m ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ m) (γ : SL(2, ℤ)) :
    ΔtoGL hm A * (γ : GL (Fin 2) ℝ) = ΔtoGL hm (mulRight A γ) := by
  ext : 1
  simp [ΔtoGL, mulRight]
  -- (A.1.map ...) * (γ.1.map ...) = (A.1 * γ.1).map ...
  simpa using (Matrix.map_mul (L := A.1) (M := γ.1) (f := algebraMap ℤ ℝ)).symm

/--
Every `FixedDetMatrix` `A` (with `m ≠ 0`) is in the SL(2,ℤ)-orbit of its reduction:
there exists `γ ∈ SL(2,ℤ)` such that `γ • (reduce A) = A`.

**Proof outline**: By induction on `reduce_rec`. The base case splits on `A.1 0 0 > 0`:
- If `A.1 0 0 > 0`, use `γ = T^r` with `r = A.1 0 1 / A.1 1 1`; cancel via `T^r • T^(-r) = 1`.
- If `A.1 0 0 ≤ 0`, use `γ = S⁻¹ • S⁻¹ • T^(-p)` where `p = -(-A.1 0 1 / -A.1 1 1)`;
  cancel `T^(-p) * T^p = 1` then `S⁻¹ • S⁻¹ • S • S = 1`.
The step case uses `γ = T^q • S⁻¹ • γ₀` where `q = A.1 0 0 / A.1 1 0` and `γ₀` from the IH,
cancelling `T^q * T^(-q) = 1` after `γ₀` unwraps the `S` and `T^(-q)` layers.

All algebraic simplifications use `h_smul_mul` (interchange of `•` and group multiplication)
and `h_inv_smul` (cancellation of `g⁻¹` with `g`), both proved by `ext : 1` and
`simp [FixedDetMatrices.smul_def, Matrix.mul_assoc]`.
-/
lemma exists_smul_reduce {m : ℤ} (_ : m ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ m) :
    ∃ (γ : SL(2, ℤ)), γ • (FixedDetMatrices.reduce A) = A := by
  have h_smul_mul : ∀ (g h : SL(2,ℤ)) (X : FixedDetMatrix (Fin 2) ℤ m),
      g • (h • X) = (g * h) • X := by
    intro g h X
    ext : 1
    simp [FixedDetMatrices.smul_def, Matrix.mul_assoc]
  have h_inv_smul : ∀ (g : SL(2,ℤ)) (X : FixedDetMatrix (Fin 2) ℤ m), g⁻¹ • (g • X) = X := by
    intro g X
    calc
      g⁻¹ • (g • X) = (g⁻¹ * g) • X := h_smul_mul g⁻¹ g X
      _ = (1 : SL(2,ℤ)) • X := by simp
      _ = X := by simp
  induction A using FixedDetMatrices.reduce_rec with
  | base A hA10 =>
    by_cases hpos : 0 < A.1 0 0
    · rw [FixedDetMatrices.reduce_of_pos hA10 hpos]
      let r := A.1 0 1 / A.1 1 1
      use (T : SL(2,ℤ)) ^ r
      calc
        ((T : SL(2,ℤ)) ^ r) • (((T : SL(2,ℤ)) ^ (-r)) • A)
            = ((T : SL(2,ℤ)) ^ r * (T : SL(2,ℤ)) ^ (-r)) • A := by rw [h_smul_mul]
        _ = ((T : SL(2,ℤ)) ^ (r + (-r : ℤ))) • A := by rw [← zpow_add (T : SL(2,ℤ))]
        _ = ((T : SL(2,ℤ)) ^ (0 : ℤ)) • A := by simp
        _ = (1 : SL(2,ℤ)) • A := by simp
        _ = A := by simp
    · rw [FixedDetMatrices.reduce_of_not_pos hA10 hpos]
      let p : ℤ := -(-A.1 0 1 / -A.1 1 1)
      refine ⟨(S : SL(2,ℤ))⁻¹ * (S : SL(2,ℤ))⁻¹ * (T : SL(2,ℤ)) ^ (-p), ?_⟩
      simp [h_smul_mul, mul_assoc, p]
  | step A hA10nonzero ih =>
    rcases ih with ⟨γ₀, hγ₀⟩
    have h_reduce_reduceStep : FixedDetMatrices.reduce (FixedDetMatrices.reduceStep A) =
      FixedDetMatrices.reduce A :=
      FixedDetMatrices.reduce_reduceStep hA10nonzero
    rw [h_reduce_reduceStep] at hγ₀
    let q : ℤ := A.1 0 0 / A.1 1 0
    have h_redStep : FixedDetMatrices.reduceStep A =
      (S : SL(2,ℤ)) • ((T : SL(2,ℤ)) ^ (-q) • A) := rfl
    rw [h_redStep] at hγ₀
    refine ⟨(T : SL(2,ℤ)) ^ q * ((S : SL(2,ℤ))⁻¹) * γ₀, ?_⟩
    calc
      ((T : SL(2,ℤ)) ^ q * ((S : SL(2,ℤ))⁻¹) * γ₀) • (FixedDetMatrices.reduce A)
          = (T : SL(2,ℤ)) ^ q • (((S : SL(2,ℤ))⁻¹) • (γ₀ • (FixedDetMatrices.reduce A))) := by
        simp [h_smul_mul, mul_assoc]
      _ = (T : SL(2,ℤ)) ^ q • (((S : SL(2,ℤ))⁻¹) •
          ((S : SL(2,ℤ)) • ((T : SL(2,ℤ)) ^ (-q) • A))) := by rw [hγ₀]
      _ = (T : SL(2,ℤ)) ^ q • ((T : SL(2,ℤ)) ^ (-q : ℤ) • A) := by
        rw [h_inv_smul]
      _ = ((T : SL(2,ℤ)) ^ q * (T : SL(2,ℤ)) ^ (-q : ℤ)) • A := by rw [h_smul_mul]
      _ = ((T : SL(2,ℤ)) ^ (q + (-q : ℤ))) • A := by
        rw [← zpow_add (T : SL(2,ℤ)) q (-q)]
      _ = ((T : SL(2,ℤ)) ^ (0 : ℤ)) • A := by
        simp [q]
      _ = (1 : SL(2,ℤ)) • A := by simp
      _ = A := by simp

/-- If a, b, d are integers with 0 ≤ a, b < d, then |a - b| < d. -/
lemma abs_sub_lt_of_nonneg_lt {a b d : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha_d : a < d) (hb_d : b < d) : |a - b| < d := by
  rw [abs_lt]
  constructor
  · -- -(a - b) < d, i.e., b - a < d
    have : b - a ≤ b := by omega
    omega
  · -- a - b < d
    have : a - b ≤ a := by omega
    omega

/-- If A, B ∈ reps m and they are in the same SL(2,ℤ)-coset, then A = B. -/
lemma reps_inj {m : ℤ} (_ : m ≠ 0) (A B : FixedDetMatrix (Fin 2) ℤ m)
    (hA : A ∈ reps m) (hB : B ∈ reps m) (h_coset : ∃ γ : SL(2, ℤ), γ • B = A) : A = B := by
  rcases h_coset with ⟨γ, hγ⟩
  rcases hA with ⟨hA10, hA00pos, hA01_nonneg, hA_abs⟩
  rcases hB with ⟨hB10, hB00pos, hB01_nonneg, hB_abs⟩
  have hAB_pos : 0 ≤ A.1 0 0 := le_of_lt hA00pos
  have hBB_pos : 0 ≤ B.1 0 0 := le_of_lt hB00pos
  have h_mat : γ.1 * B.1 = A.1 := by
    simpa [FixedDetMatrices.smul_def] using congrArg Subtype.val hγ
  -- γ.1 1 0 = 0 (from the (1,0) entry being 0 in both A and B)
  have hγ10 : γ.1 1 0 = 0 := by
    have hprod : γ.1 1 0 * B.1 0 0 = 0 := by
      have h10_entry : (γ.1 * B.1) 1 0 = (0 : ℤ) := by rw [h_mat, hA10]
      simpa [Matrix.mul_apply, hB10] using h10_entry
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with (h | h)
    · exact h
    ·     exfalso; linarith
  -- det(γ) = 1, so over ℤ, γ.1 0 0 * γ.1 1 1 = 1
  have hdet_prod : γ.1 0 0 * γ.1 1 1 = 1 := by
    have hdet_val : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.property
    rw [Matrix.det_fin_two, hγ10] at hdet_val
    omega
  have hγ00_one : γ.1 0 0 = 1 := by
    by_contra! h_not_one
    -- γ.1 0 0 must be -1 (since it's a unit in ℤ dividing 1)
    have hγ00_neg_one : γ.1 0 0 = -1 := by
      have h_dvd : γ.1 0 0 ∣ (1 : ℤ) := ⟨γ.1 1 1, hdet_prod.symm⟩
      have hunit : IsUnit (γ.1 0 0) := isUnit_of_dvd_one h_dvd
      rcases (Int.isUnit_iff.mp hunit) with (h | h)
      · exfalso; exact h_not_one h
      · exact h
    -- Then A.1 0 0 = -B.1 0 0, contradicting positivity
    have h00_entry : γ.1 0 0 * B.1 0 0 = A.1 0 0 := by
      calc
        γ.1 0 0 * B.1 0 0 = (γ.1 * B.1) 0 0 := by
          simp [Matrix.mul_apply, hB10]
        _ = A.1 0 0 := by rw [h_mat]
    rw [hγ00_neg_one] at h00_entry
    have : A.1 0 0 = -B.1 0 0 := by omega
    omega
  have hγ11_one : γ.1 1 1 = 1 := by
    rw [hγ00_one] at hdet_prod
    omega
  -- Now A.1 0 0 = B.1 0 0, A.1 1 1 = B.1 1 1
  have hA00_eq_B00 : A.1 0 0 = B.1 0 0 := by
    have h00_entry : γ.1 0 0 * B.1 0 0 = A.1 0 0 := by
      calc
        γ.1 0 0 * B.1 0 0 = (γ.1 * B.1) 0 0 := by
          simp [Matrix.mul_apply, hB10]
        _ = A.1 0 0 := by rw [h_mat]
    rw [hγ00_one] at h00_entry; omega
  have hA11_eq_B11 : A.1 1 1 = B.1 1 1 := by
    have h11_entry : γ.1 1 1 * B.1 1 1 = A.1 1 1 := by
      calc
        γ.1 1 1 * B.1 1 1 = (γ.1 * B.1) 1 1 := by
          simp [Matrix.mul_apply, hγ10]
        _ = A.1 1 1 := by rw [h_mat]
    rw [hγ11_one] at h11_entry; omega
  have hA01_lt : A.1 0 1 < |A.1 1 1| := by
    have : |A.1 0 1| < |A.1 1 1| := hA_abs
    have : |A.1 0 1| = A.1 0 1 := abs_of_nonneg hA01_nonneg
    omega
  have hB01_lt : B.1 0 1 < |B.1 1 1| := by
    have : |B.1 0 1| < |B.1 1 1| := hB_abs
    have : |B.1 0 1| = B.1 0 1 := abs_of_nonneg hB01_nonneg
    omega
  -- Relate A.1 0 1 to B.1 0 1
  have h01_relation : A.1 0 1 = B.1 0 1 + γ.1 0 1 * B.1 1 1 := by
    have h01_entry : γ.1 0 0 * B.1 0 1 + γ.1 0 1 * B.1 1 1 = A.1 0 1 := by
      calc
        γ.1 0 0 * B.1 0 1 + γ.1 0 1 * B.1 1 1 = (γ.1 * B.1) 0 1 := by
          simp [Matrix.mul_apply]
        _ = A.1 0 1 := by rw [h_mat]
    rw [hγ00_one] at h01_entry; omega
  -- Show γ.1 0 1 = 0 by using the bounds
  have hγ01_zero : γ.1 0 1 = 0 := by
    by_contra! h_ne_zero
    have hA11_ne_zero : A.1 1 1 ≠ 0 := by
      intro hzero
      have h_abs_lt_zero : |A.1 0 1| < 0 := by
        simpa [hzero] using hA_abs
      have h_nonneg : 0 ≤ |A.1 0 1| := abs_nonneg _
      linarith
    have h_pos_abs : 0 < |B.1 1 1| := by
      rw [← hA11_eq_B11]
      exact abs_pos.mpr hA11_ne_zero
    have hA01_lt' : A.1 0 1 < |B.1 1 1| := by
      simpa [hA11_eq_B11] using hA01_lt
    have h_diff_abs_lt : |A.1 0 1 - B.1 0 1| < |B.1 1 1| :=
      abs_sub_lt_of_nonneg_lt hA01_nonneg hB01_nonneg hA01_lt' hB01_lt
    have h_diff_eq : A.1 0 1 - B.1 0 1 = γ.1 0 1 * B.1 1 1 := by
      omega
    have h_abs_mul_lt : |γ.1 0 1| * |B.1 1 1| < |B.1 1 1| := by
      calc
        |γ.1 0 1| * |B.1 1 1| = |γ.1 0 1 * B.1 1 1| := by rw [abs_mul]
        _ = |A.1 0 1 - B.1 0 1| := by rw [h_diff_eq]
        _ < |B.1 1 1| := h_diff_abs_lt
    have h_nonneg_abs : 0 ≤ |γ.1 0 1| := abs_nonneg _
    have hγ01_abs_lt_one : |γ.1 0 1| < 1 := by
      nlinarith
    have h_abs_zero : |γ.1 0 1| = 0 := by omega
    have : γ.1 0 1 = 0 := abs_eq_zero.mp h_abs_zero
    exact h_ne_zero this
  have hA01_eq_B01 : A.1 0 1 = B.1 0 1 := by
    rw [hγ01_zero] at h01_relation; omega
  -- All four entries match
  apply FixedDetMatrices.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hA00_eq_B00, hA01_eq_B01, hA10, hB10, hA11_eq_B11]

/-- For any γ ∈ SL(2,ℤ), reducing γ • A gives the same result as reducing A. -/
lemma reduce_smul {m : ℤ} (hm : m ≠ 0) (γ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ m) :
    FixedDetMatrices.reduce (γ • A) = FixedDetMatrices.reduce A := by
  apply reps_inj hm (FixedDetMatrices.reduce (γ • A)) (FixedDetMatrices.reduce A)
  · exact reduce_mem_reps hm (γ • A)
  · exact reduce_mem_reps hm A
  · rcases exists_smul_reduce hm (γ • A) with ⟨γ₁, hγ₁⟩
    rcases exists_smul_reduce hm A with ⟨γ₂, hγ₂⟩
    refine ⟨γ₁⁻¹ * γ * γ₂, ?_⟩
    calc
      (γ₁⁻¹ * γ * γ₂) • (FixedDetMatrices.reduce A) =
          γ₁⁻¹ • (γ • (γ₂ • FixedDetMatrices.reduce A)) := by
        simp [FixedDetMatrices.smul_def, mul_assoc]
      _ = γ₁⁻¹ • (γ • A) := by rw [hγ₂]
      _ = γ₁⁻¹ • (γ₁ • (FixedDetMatrices.reduce (γ • A))) := by rw [hγ₁]
      _ = FixedDetMatrices.reduce (γ • A) := by rw [inv_smul_smul]

/-- If A ∈ reps m, then `reduce A = A`. -/
lemma reduce_of_reps {m : ℤ} (_ : m ≠ 0) {A : FixedDetMatrix (Fin 2) ℤ m} (hA : A ∈ reps m) :
    FixedDetMatrices.reduce A = A := by
  rcases hA with ⟨hA10, hA00pos, hA01_nonneg, hA_abs⟩
  rw [FixedDetMatrices.reduce_of_pos hA10 hA00pos]
  have h_div : A.1 0 1 / A.1 1 1 = 0 :=
    Int.ediv_eq_zero_of_lt_abs hA01_nonneg (by
      simpa [abs_of_nonneg hA01_nonneg] using hA_abs)
  simp [h_div]

variable (f : ℍ → ℂ) (k : ℤ)

/--
If `f` is SL(2,ℤ)-invariant of weight `k`, then for any `FixedDetMatrix` `A` (with `m ≠ 0`), we have
`f ∣[k] (ΔtoGL hm A) = f ∣[k] (ΔtoGL hm (reduce A))`.
-/
theorem slash_invariant_under_reduce {m : ℤ} (hm : m ≠ 0)
    (hf : ∀ (γ : SL(2, ℤ)), f ∣[k] (γ : GL (Fin 2) ℝ) = f) (A : FixedDetMatrix (Fin 2) ℤ m) :
    f ∣[k] (ΔtoGL hm A) = f ∣[k] (ΔtoGL hm (FixedDetMatrices.reduce A)) := by
  rcases exists_smul_reduce hm A with ⟨γ, hγ⟩
  calc
    f ∣[k] (ΔtoGL hm A) = f ∣[k] (ΔtoGL hm (γ • (FixedDetMatrices.reduce A))) := by rw [hγ]
    _ = f ∣[k] ((γ : GL (Fin 2) ℝ) * (ΔtoGL hm (FixedDetMatrices.reduce A))) := by
      rw [ΔtoGL_smul hm γ (FixedDetMatrices.reduce A)]
    _ = (f ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (ΔtoGL hm (FixedDetMatrices.reduce A)) := by
      rw [SlashAction.slash_mul]
    _ = f ∣[k] (ΔtoGL hm (FixedDetMatrices.reduce A)) := by rw [hf γ]

/--
The **Hecke operator** `T_n` on functions `f : ℍ → ℂ` of weight `k`,
for `n` a positive integer.
`T_n(f)` is defined as `∑_{M ∈ reps n} f ∣[k] ΔtoGL M.1`.
-/
noncomputable def heckeOperator (f : ℍ → ℂ) (k : ℤ) (n : ℕ) (hn : n ≠ 0) : ℍ → ℂ :=
  ∑ M : reps (n : ℤ), f ∣[k] (ΔtoGL (by exact_mod_cast hn) M.1)

/-- The map `M ↦ ⟨reduce(mulRight M.1 γ), reduce_mem_reps⟩` is injective on `reps m`.

If `φ(M₁) = φ(M₂)`, then `reduce(A₁) = reduce(A₂)` where `Aᵢ = mulRight Mᵢ.1 γ`.
By `exists_smul_reduce`, `αᵢ • reduce(Aᵢ) = Aᵢ`, so `M₁.1 * M₂.1⁻¹ = (α₁ * α₂⁻¹).1`,
hence `δ • M₂ = M₁` with `δ = α₁ * α₂⁻¹`. By `reps_inj`, `M₁ = M₂`. -/
lemma φ_inj {m : ℤ} (hm : m ≠ 0) (γ : SL(2, ℤ)) (M₁ M₂ : reps m)
    (h_eq : reduce (mulRight M₁.1 γ) = reduce (mulRight M₂.1 γ)) : M₁ = M₂ := by
  have h₁ : ∃ α₁ : SL(2, ℤ),
      α₁ • reduce (mulRight M₁.1 γ) = mulRight M₁.1 γ :=
    exists_smul_reduce hm (mulRight M₁.1 γ)
  obtain ⟨α₁, hα₁⟩ := h₁
  have h₂ : ∃ α₂ : SL(2, ℤ),
      α₂ • reduce (mulRight M₂.1 γ) = mulRight M₂.1 γ :=
    exists_smul_reduce hm (mulRight M₂.1 γ)
  obtain ⟨α₂, hα₂⟩ := h₂
  have h_eq₁ : (α₁.1 : Matrix (Fin 2) (Fin 2) ℤ) * (reduce (mulRight M₁.1 γ)).1 =
      (mulRight M₁.1 γ).1 :=
    by simpa [FixedDetMatrices.smul_def, mulRight] using congrArg Subtype.val hα₁
  have h_eq₂ : (α₂.1 : Matrix (Fin 2) (Fin 2) ℤ) * (reduce (mulRight M₂.1 γ)).1 =
      (mulRight M₂.1 γ).1 :=
    by simpa [FixedDetMatrices.smul_def, mulRight] using congrArg Subtype.val hα₂
  rw [h_eq] at hα₁
  have h_coset : ∃ δ : SL(2, ℤ), δ • M₂.1 = M₁.1 := by
    -- Lemmas needed for the proof
    have h_smul_mulRight (δ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ m) (γ' : SL(2, ℤ)) :
        δ • mulRight A γ' = mulRight (δ • A) γ' := by
      ext : 1
      simp [FixedDetMatrices.smul_def, mulRight, Matrix.mul_assoc]
    have h_mulRight_inj (A B : FixedDetMatrix (Fin 2) ℤ m)
        (h : mulRight A γ = mulRight B γ) : A = B := by
      apply Subtype.ext
      have h_val : (A.1 : Matrix (Fin 2) (Fin 2) ℤ) * (γ.1 : Matrix (Fin 2) (Fin 2) ℤ) =
                   (B.1 : Matrix (Fin 2) (Fin 2) ℤ) * (γ.1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        simpa [mulRight] using congrArg (·.1) h
      have h_inv : (γ.1 : Matrix (Fin 2) (Fin 2) ℤ) *
          ((γ⁻¹ : SL(2,ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
        calc
          (γ.1 : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2,ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ)
              = (γ * (γ⁻¹ : SL(2,ℤ))).1 := rfl
          _ = (1 : SL(2,ℤ)).1 := by rw [mul_inv_cancel γ]
          _ = (1 : Matrix (Fin 2) (Fin 2) ℤ) := rfl
      calc
        (A.1 : Matrix (Fin 2) (Fin 2) ℤ) = (A.1 : _) * 1 := by simp
        _ = (A.1 : _) * ((γ.1 : _) * ((γ⁻¹ : SL(2,ℤ)).1 : _)) := by rw [h_inv]
        _ = ((A.1 : _) * (γ.1 : _)) * ((γ⁻¹ : SL(2,ℤ)).1 : _) := by simp [Matrix.mul_assoc]
        _ = ((B.1 : _) * (γ.1 : _)) * ((γ⁻¹ : SL(2,ℤ)).1 : _) := by rw [h_val]
        _ = (B.1 : _) * ((γ.1 : _) * ((γ⁻¹ : SL(2,ℤ)).1 : _)) := by simp [Matrix.mul_assoc]
        _ = (B.1 : _) * 1 := by rw [h_inv]
        _ = (B.1 : Matrix (Fin 2) (Fin 2) ℤ) := by simp
    -- hα₁: α₁ • R = mulRight M₁.1 γ   (R = reduce(mulRight M₂.1 γ))
    -- hα₂: α₂ • R = mulRight M₂.1 γ
    -- Step 1: chain to get (α₁*α₂⁻¹) • mulRight M₂.1 γ = mulRight M₁.1 γ
    have h_step : (α₁ * (α₂⁻¹ : SL(2, ℤ))) • mulRight M₂.1 γ = mulRight M₁.1 γ := by
      have h_assoc (X : FixedDetMatrix (Fin 2) ℤ m) :
          (α₁ * α₂⁻¹) • X = α₁ • (α₂⁻¹ • X) := by
        ext : 1
        simp [FixedDetMatrices.smul_def, Matrix.mul_assoc]
      have h_inner : (α₂⁻¹ : SL(2, ℤ)) • mulRight M₂.1 γ = reduce (mulRight M₂.1 γ) := by
        calc
          (α₂⁻¹ : SL(2, ℤ)) • mulRight M₂.1 γ
              = (α₂⁻¹ : SL(2, ℤ)) • (α₂ • reduce (mulRight M₂.1 γ)) := by
                conv => lhs; rw [hα₂.symm]
          _ = reduce (mulRight M₂.1 γ) := by rw [inv_smul_smul]
      calc
        (α₁ * α₂⁻¹) • mulRight M₂.1 γ
            = α₁ • ((α₂⁻¹ : SL(2, ℤ)) • mulRight M₂.1 γ) := by rw [h_assoc]
        _ = α₁ • reduce (mulRight M₂.1 γ) := by rw [h_inner]
        _ = mulRight M₁.1 γ := hα₁
    -- Step 2: apply smul_mulRight and mulRight_inj
    have h_cancel : (α₁ * (α₂⁻¹ : SL(2, ℤ))) • M₂.1 = M₁.1 := by
      apply h_mulRight_inj _ _ ?_
      calc
        mulRight ((α₁ * (α₂⁻¹ : SL(2, ℤ))) • M₂.1) γ
            = (α₁ * (α₂⁻¹ : SL(2, ℤ))) • mulRight M₂.1 γ := by
              symm; exact h_smul_mulRight (α₁ * α₂⁻¹) M₂.1 γ
        _ = mulRight M₁.1 γ := h_step
    exact ⟨α₁ * (α₂⁻¹ : SL(2, ℤ)), h_cancel⟩
  exact Subtype.ext (reps_inj hm M₁.1 M₂.1 M₁.2 M₂.2 h_coset)

/-- The map `M ↦ ⟨reduce(mulRight M.1 γ), reduce_mem_reps⟩` is a bijection on `reps m`.

Injectivity via `φ_inj`. Surjectivity from finiteness: injective on a finite type is bijective. -/
lemma φ_bij {m : ℤ} (hm : m ≠ 0) (γ : SL(2, ℤ)) :
    Function.Bijective (fun M : reps m =>
      Subtype.mk (reduce (mulRight M.1 γ))
        (reduce_mem_reps hm (mulRight M.1 γ))) :=
  ⟨fun M₁ M₂ h_eq => φ_inj hm γ M₁ M₂ (congrArg Subtype.val h_eq),
    Finite.surjective_of_injective (fun M₁ M₂ h => φ_inj hm γ M₁ M₂ (congrArg Subtype.val h))⟩

/--
If `f` is SL(2,ℤ)-invariant of weight `k`, then `T_n(f)` is also SL(2,ℤ)-invariant.
-/
theorem heckeOperator_slash (γ : SL(2, ℤ)) (n : ℕ) (hn : n ≠ 0)
    (hf : ∀ (γ : SL(2, ℤ)), f ∣[k] (γ : GL (Fin 2) ℝ) = f) :
    (heckeOperator f k n hn) ∣[k] (γ : GL (Fin 2) ℝ) = heckeOperator f k n hn := by
  let hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simp only [heckeOperator]
  rw [SlashAction.sum_slash]
  -- Goal: ∑ M, (f∣[k]ΔtoGL hnz M.1)∣[k]γ = ∑ M, f∣[k]ΔtoGL hnz M.1
  have h_step (M : reps (n : ℤ)) :
      (f ∣[k] ΔtoGL hnz M.1) ∣[k] (γ : GL (Fin 2) ℝ) =
      f ∣[k] ΔtoGL hnz (reduce (mulRight M.1 γ)) := by
    rw [← SlashAction.slash_mul, ΔtoGL_mul hnz M.1 γ,
        slash_invariant_under_reduce f k hnz hf]
  -- Define the bijection φ explicitly
  set_option linter.unusedVariables false in
  let φ (M : reps (n : ℤ)) : reps (n : ℤ) :=
    ⟨reduce (mulRight M.1 γ), reduce_mem_reps hnz (mulRight M.1 γ)⟩
  have hφ : Function.Bijective φ := φ_bij hnz γ
  -- Per-summand rewrite: (f∣[k]ΔtoGL hnz M.1)∣[k]γ = f∣[k]ΔtoGL hnz (φ M).1
  have h_each : ∀ M : reps (n : ℤ),
      (f ∣[k] ΔtoGL hnz M.1) ∣[k] (γ : GL (Fin 2) ℝ) =
      f ∣[k] ΔtoGL hnz (φ M).1 := h_step
  -- Chain: rewrite each summand via h_step, then reindex via Bijective.sum_comp
  calc
    @Finset.sum (reps (n : ℤ)) (ℍ → ℂ) _ Finset.univ
        (fun M : reps (n : ℤ) =>
        (f ∣[k] ΔtoGL hnz M.1) ∣[k] (γ : GL (Fin 2) ℝ)) =
      @Finset.sum (reps (n : ℤ)) (ℍ → ℂ) _ Finset.univ
        (fun M : reps (n : ℤ) => f ∣[k] ΔtoGL hnz (φ M).1) := by
      congr 1; funext M; exact h_step M
    _ = @Finset.sum (reps (n : ℤ)) (ℍ → ℂ) _ Finset.univ
        (fun M : reps (n : ℤ) => f ∣[k] ΔtoGL hnz M.1) :=
      Function.Bijective.sum_comp hφ fun N : reps (n : ℤ) => f ∣[k] ΔtoGL hnz N.1

/--
If `f` is a modular form of weight `k` for SL(2,ℤ), then `T_n(f)` is also a modular form
of weight `k` for SL(2,ℤ).

The proof uses `heckeOperator_slash` for SL(2,ℤ)-invariance, `MDifferentiable.slash` for
holomorphy, and admits the boundedness-at-cusps condition (which requires q-expansion
theory, a research-level formalization problem).
-/
noncomputable def heckeOperator_modularForm (f : ModularForm 𝒮ℒ k) (n : ℕ) (hn : n ≠ 0) :
    ModularForm 𝒮ℒ k :=
  let hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  let F : ℍ → ℂ := heckeOperator (f : ℍ → ℂ) k n hn
  -- Show that f is SL(2,ℤ)-invariant (as a function ℍ → ℂ)
  have h_slash_f : ∀ (γ : SL(2, ℤ)), (f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = (f : ℍ → ℂ) := by
    intro γ
    have hg : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := by
      exact MonoidHom.mem_range.mpr ⟨γ, rfl⟩
    exact f.slash_action_eq' (γ : GL (Fin 2) ℝ) hg
  -- Show that F is 𝒮ℒ-invariant
  have hF_slash_inv : ∀ g ∈ 𝒮ℒ, F ∣[k] (g : GL (Fin 2) ℝ) = F := by
    intro g hg
    rcases MonoidHom.mem_range.mp hg with ⟨γ, hγ⟩
    have hF_slash_sl := heckeOperator_slash (f : ℍ → ℂ) k γ n hn h_slash_f
    have : (γ : GL (Fin 2) ℝ) = g := hγ
    rw [this] at hF_slash_sl
    exact hF_slash_sl
  -- Holomorphy: each summand f ∣[k] ΔtoGL hnz M.1 is holomorphic by MDifferentiable.slash.
  -- A finite sum of holomorphic functions is holomorphic: MDifferentiable.sum.
  -- Note: ∑ M : reps (n : ℤ), ... desugars to Finset.sum Finset.univ ..., so
  -- MDifferentiable.sum applies directly.
  have h_holo : MDiff F := by
    dsimp [F, heckeOperator]
    apply MDifferentiable.sum
    intro M hM
    exact MDifferentiable.slash f.holo' k (ΔtoGL hnz M.1)
  -- Boundedness at cusps (TODO: requires q-expansion theory)
  have h_bdd : ∀ {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ), c.IsBoundedAt F k := by sorry
  { toSlashInvariantForm := ⟨F, hF_slash_inv⟩
    holo' := h_holo
    bdd_at_cusps' := h_bdd }

end HeckeOperator
