module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFrame

@[expose] public section


/-!
# The Atkin–Lehner conjugation permutes the Hecke cosets of `Γ₁'(3)`

Let `alHom : GL₂(ℚ) → GL₂(ℚ)` be `x ↦ δ x^{-T} δ⁻¹`, `δ = diag(1, 3)`.  It is a homomorphism and an
involution, and `alHom ι(γ) = ι(α γ)` for the cusp-exchanging involution `α` of `Γ₁'(3)`.  On the
Hecke representatives `α_j = [[1, j], [0, p]]`, `α_∞ = ε_p [[p, 0], [0, 1]]`:

* `alHom α_j = (ε_p / p) · α_∞ · ι(lower(-j))` for `j ∈ {0, …, p - 1}` (with `lower(-j) = [[1, 0],
  [-3j, 1]] ∈ Γ₁'(3)`), because `δ [[1, j], [0, p]]^{-T} δ⁻¹ = p⁻¹ [[p, 0], [-3j, 1]]`;
* `alHom α_∞ = (ε_p / p) · α_0`.

Here `ε_p = ±1` is the sign `≡ p mod 3`, and `(ε_p/p)` is the central scalar `zP`.  Combined with
the right coset transitions `α_∞ ι(g) = ι(δ) α_k` (`levelDelta_spec`) this exhibits `alHom` as a
permutation of the right cosets up to elements of `Γ₁'(3)` and the central scalar.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
  (integralEmbed integralEmbed_val)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del del_val del_inv_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

/-! ### The inverse transpose and the conjugation `alHom` -/

/-- The inverse transpose `x ↦ (x⁻¹)ᵀ` of `GL₂(ℚ)`. -/
def invTQ : GL (Fin 2) ℚ →* GL (Fin 2) ℚ where
  toFun x := ⟨((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ,
    (x : Matrix (Fin 2) (Fin 2) ℚ)ᵀ, by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    change (((x * y)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ =
      ((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ *
        ((y⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem invTQ_val (x : GL (Fin 2) ℚ) :
    ((invTQ x : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ := rfl

/-- The inverse transpose is an involution. -/
theorem invTQ_invTQ (x : GL (Fin 2) ℚ) : invTQ (invTQ x) = x := by
  apply Units.ext
  change (((invTQ x)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ = _
  have : (((invTQ x)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (x : Matrix (Fin 2) (Fin 2) ℚ)ᵀ := rfl
  rw [this, Matrix.transpose_transpose]

/-- The inverse transpose of `δ = diag(1, 3)` is `δ⁻¹`. -/
theorem invTQ_del : invTQ del = del⁻¹ := by
  apply Units.ext
  rw [invTQ_val, del_inv_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.transpose_apply]

/-- **The conjugation `x ↦ δ x^{-T} δ⁻¹`.** -/
def alHom : GL (Fin 2) ℚ →* GL (Fin 2) ℚ := (MulAut.conj del).toMonoidHom.comp invTQ

theorem alHom_apply (x : GL (Fin 2) ℚ) : alHom x = del * invTQ x * del⁻¹ := rfl

/-- `alHom` is an involution. -/
theorem alHom_alHom (x : GL (Fin 2) ℚ) : alHom (alHom x) = x := by
  rw [alHom_apply, alHom_apply, map_mul, map_mul, map_inv, invTQ_invTQ, invTQ_del, inv_inv]
  group

/-! ### Scalars -/

theorem signP_sq_rat (p : Nat.Primes) : ((signP p : ℤ) : ℚ) * ((signP p : ℤ) : ℚ) = 1 := by
  exact_mod_cast signP_mul_self p

/-- The central scalar `ε_p / p`. -/
def zUnit (p : Nat.Primes) : ℚˣ :=
  Units.mk0 (((signP p : ℤ) : ℚ) / (p.val : ℚ)) (by
    have h1 : ((signP p : ℤ) : ℚ) ≠ 0 := by
      have := signP_sq_rat p
      intro h
      rw [h] at this
      simp at this
    have h2 : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    exact div_ne_zero h1 h2)

/-- The scalar matrix `(ε_p / p) · 1`. -/
def zP (p : Nat.Primes) : GL (Fin 2) ℚ := GeneralLinearGroup.scalar (Fin 2) (zUnit p)

theorem zP_val (p : Nat.Primes) :
    ((zP p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.scalar (Fin 2) (((signP p : ℤ) : ℚ) / (p.val : ℚ)) := rfl

/-- The scalar matrices are central. -/
theorem zP_central (p : Nat.Primes) (x : GL (Fin 2) ℚ) : zP p * x = x * zP p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zP_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

/-! ### The inverse of a matrix with a known right inverse -/

theorem inv_val_of_mul (x : GL (Fin 2) ℚ) (N : Matrix (Fin 2) (Fin 2) ℚ)
    (h : (x : Matrix (Fin 2) (Fin 2) ℚ) * N = 1) :
    ((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = N := by
  calc ((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = ((x⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        ((x : Matrix (Fin 2) (Fin 2) ℚ) * N) := by
        rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]

/-! ### The action on the Hecke representatives -/

/-- The matrix of the embedded lower unipotent element. -/
theorem levelEmbed_lower_val (k : ℤ) :
    ((levelEmbed (lower k) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![1, 0; 3 * (k : ℚ), 1] := by
  rw [levelEmbed_apply, integralEmbed_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lower]

section Reps

variable (p : Nat.Primes)

/-- **`alHom` on the finite representatives**:
`alHom α_j = (ε_p / p) · α_∞ · ι(lower(-j))`. -/
theorem alHom_heckeRep_some (i : Fin p.val) :
    alHom (heckeRep p (some i)) =
      zP p * (heckeRep p none * levelEmbed (lower (-(i.val : ℤ)))) := by
  have hp0 : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hε := signP_sq_rat p
  have hinv : ((heckeRep p (some i))⁻¹ : GL (Fin 2) ℚ).val =
      !![1, -(i.val : ℚ) / p.val; 0, 1 / p.val] := by
    apply inv_val_of_mul
    rw [heckeRep_some]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  have hinvT : (((heckeRep p (some i))⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ =
      !![1, 0; -(i.val : ℚ) / p.val, 1 / p.val] := by
    rw [hinv]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  apply Units.ext
  simp only [alHom_apply, Units.val_mul, invTQ_val, hinvT, del_val, del_inv_val, zP_val,
    heckeRep_none, levelEmbed_lower_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [div_mul_eq_mul_div, eq_div_iff hp0]
    linear_combination (-(p.val : ℚ)) * hε
  · linear_combination (3 * (i.val : ℚ) / (p.val : ℚ)) * hε
  · linear_combination (-((p.val : ℚ)⁻¹)) * hε

/-- The index `0` of the finite cosets. -/
def zeroIdx : Fin p.val := ⟨0, p.property.pos⟩

/-- **`alHom` on the infinite representative**: `alHom α_∞ = (ε_p / p) · α_0`. -/
theorem alHom_heckeRep_none :
    alHom (heckeRep p none) = zP p * (levelEmbed 1 * heckeRep p (some (zeroIdx p))) := by
  have hp0 : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hε := signP_sq_rat p
  have hinv : ((heckeRep p none)⁻¹ : GL (Fin 2) ℚ).val =
      !![((signP p : ℤ) : ℚ) / p.val, 0; 0, ((signP p : ℤ) : ℚ)] := by
    apply inv_val_of_mul
    rw [heckeRep_none]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
      linear_combination hε
    · linear_combination hε
  have hinvT : (((heckeRep p none)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)ᵀ =
      !![((signP p : ℤ) : ℚ) / p.val, 0; 0, ((signP p : ℤ) : ℚ)] := by
    rw [hinv]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  apply Units.ext
  simp only [alHom_apply, Units.val_mul, invTQ_val, hinvT, del_val, del_inv_val, zP_val,
    map_one, Units.val_one]
  rw [heckeRep_some]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, zeroIdx]
  field_simp

/-- **`alHom` permutes the cosets up to central scalars and level elements.** -/
theorem alHom_heckeRep_exists (hp3 : p.val ≠ 3) (j : Option (Fin p.val)) :
    ∃ (k : Option (Fin p.val)) (u : binaryArithmeticLevel),
      alHom (heckeRep p j) = zP p * (levelEmbed u * heckeRep p k) := by
  cases j with
  | none => exact ⟨some (zeroIdx p), 1, by rw [alHom_heckeRep_none]⟩
  | some i =>
    refine ⟨levelNext p hp3 (lower (-(i.val : ℤ))) none,
      levelDelta p hp3 (lower (-(i.val : ℤ))) none, ?_⟩
    rw [alHom_heckeRep_some]
    congr 1
    have h := (levelCosets p hp3).delta_spec (lower (-(i.val : ℤ))) none
    change levelEmbed (levelDelta p hp3 (lower (-(i.val : ℤ))) none) =
      heckeRep p none * levelEmbed (lower (-(i.val : ℤ))) *
        (heckeRep p (levelNext p hp3 (lower (-(i.val : ℤ))) none))⁻¹ at h
    rw [h]
    group

end Reps

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
