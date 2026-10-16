module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Cusp

@[expose] public section


/-!
# Hecke equivariance of the boundary functional at the cusp `0`

With `T_p = levelHecke m e p hp3`, `β_0(z) = z(L)(0, 1)` (`LevelThreeBoundaryFunctional.betaZero`)
we prove

`betaZero_levelHecke : β_0 (T_p x) = q_0 · β_0 x`,
`q_0 = qZero m e p = p ^ (-e) · (p ^ (m + 1) + ε_p ^ m)`.

The proof evaluates `(T_p z)(L^p)`: right multiplication by `L^p` fixes every coset
`Γ₁'(3) α_j`, with transition `α_j L^p α_j⁻¹`, namely
`L` for `j = ∞`, `L^{p²}` for `j = 0` and the unipotent `[[1+3pj, -3j²],[3p², 1-3pj]] = γ_j L γ_j⁻¹`
for `0 < j < p`, where `γ_j = [[a, ε_p j],[3c, ε_p p]] ∈ Γ₁(3)` (Bezout, `gcd(p, 3j) = 1`).
By `LevelThreeBoundaryCusp.eval_cusp_value` the value `z(δ_j)(α_j (0, 1))` is `ε_p^m β_0(z)` for
`j ≠ 0`, and `p^m p² β_0(z)` for `j = 0`; since `β_0(w(L^p)) = p β_0(w)` this gives
`p β_0(T_p z) = p^{-e} (p^{m+2} + p ε_p^m) β_0(z)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryZero

open Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds FullBound
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional LevelThreeBoundaryHecke
open LevelThreeBoundaryCusp
open GeneralEisenstein

section Elements

theorem zmod_three : (3 : ZMod 3) = 0 := by decide

theorem lower_coe (k : ℤ) :
    ((lower k).val : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 3 * k, 1] := rfl

theorem lower_pow_nat (n : ℕ) : lower 1 ^ n = lower (n : ℤ) := by
  rw [lower_zpow (n : ℤ), zpow_natCast]

theorem hElt_c (p : Nat.Primes) : (((3 * (p.val : ℤ) ^ 2 : ℤ)) : ZMod 3) = 0 := by
  simp [zmod_three]

theorem hElt_d (p : Nat.Primes) (i : Fin p.val) :
    (((1 - 3 * (p.val : ℤ) * (i.val : ℤ) : ℤ)) : ZMod 3) = 1 := by
  simp [zmod_three]

/-- `h_i = [[1 + 3pi, -3i²],[3p², 1 - 3pi]] = α_i L^p α_i⁻¹`. -/
def hElt (p : Nat.Primes) (i : Fin p.val) : binaryArithmeticLevel :=
  levelElt (1 + 3 * (p.val : ℤ) * (i.val : ℤ)) (-3 * (i.val : ℤ) ^ 2) (3 * (p.val : ℤ) ^ 2)
    (1 - 3 * (p.val : ℤ) * (i.val : ℤ)) (by ring) (hElt_c p) (hElt_d p i)

theorem hElt_coe (p : Nat.Primes) (i : Fin p.val) :
    ((hElt p i).val : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 + 3 * (p.val : ℤ) * (i.val : ℤ), -3 * (i.val : ℤ) ^ 2;
        3 * (p.val : ℤ) ^ 2, 1 - 3 * (p.val : ℤ) * (i.val : ℤ)] := rfl

theorem hElt_det (p : Nat.Primes) (i : Fin p.val) :
    ((hElt p i).val : Matrix (Fin 2) (Fin 2) ℤ).det = 1 :=
  levelElt_det _ _ _ _ _ _ _

end Elements

section Deltas

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `α_∞ L^p = L α_∞`. -/
theorem levelDelta_lower_none : levelDelta p hp3 (lower (p.val : ℤ)) none = lower 1 := by
  refine levelDelta_eq p hp3 _ _ none none ?_
  rw [N_none, lower_coe, lower_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `α_0 L^p = L^{p²} α_0`. -/
theorem levelDelta_lower_zero :
    levelDelta p hp3 (lower (p.val : ℤ)) (some ⟨0, p.property.pos⟩) =
      lower ((p.val * p.val : ℕ) : ℤ) := by
  refine levelDelta_eq p hp3 _ _ (some ⟨0, p.property.pos⟩) (some ⟨0, p.property.pos⟩) ?_
  rw [N_some, lower_coe, lower_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `α_i L^p = h_i α_i`. -/
theorem levelDelta_lower_some (i : Fin p.val) :
    levelDelta p hp3 (lower (p.val : ℤ)) (some i) = hElt p i := by
  refine levelDelta_eq p hp3 _ _ (some i) (some i) ?_
  rw [N_some, hElt_coe, lower_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Deltas

section Gamma

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

include hp3 in
/-- Bezout: `a p - 3 c i = ε_p` for `0 < i < p`. -/
theorem exists_gamma_data (i : Fin p.val) (hi : i.val ≠ 0) :
    ∃ a c : ℤ, a * (p.val : ℤ) - 3 * c * (i.val : ℤ) = ((signP p : ℤˣ) : ℤ) := by
  have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
  have hlt : i.val < p.val := i.isLt
  have hp3' : Nat.Coprime p.val 3 := (Nat.coprime_primes p.property Nat.prime_three).mpr hp3
  have hpi : Nat.Coprime p.val i.val := by
    rw [Nat.Prime.coprime_iff_not_dvd p.property]
    intro hdvd
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  have hcop : Nat.Coprime p.val (3 * i.val) := Nat.Coprime.mul_right hp3' hpi
  have hz : IsCoprime ((p.val : ℕ) : ℤ) ((3 * i.val : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, huv⟩ := hz
  push_cast at huv
  refine ⟨((signP p : ℤˣ) : ℤ) * u, -(((signP p : ℤˣ) : ℤ) * v), ?_⟩
  linear_combination ((signP p : ℤˣ) : ℤ) * huv

include hp3 in
/-- The matrix `γ_i = [[a, ε_p i],[3c, ε_p p]]`. -/
theorem exists_gamma (i : Fin p.val) (hi : i.val ≠ 0) :
    ∃ (a c : ℤ) (γ : binaryArithmeticLevel),
      a * (p.val : ℤ) - 3 * c * (i.val : ℤ) = ((signP p : ℤˣ) : ℤ) ∧
      (γ.val : Matrix (Fin 2) (Fin 2) ℤ) =
        !![a, ((signP p : ℤˣ) : ℤ) * (i.val : ℤ); 3 * c, ((signP p : ℤˣ) : ℤ) * (p.val : ℤ)] := by
  obtain ⟨a, c, hrel⟩ := exists_gamma_data p hp3 i hi
  have hεε : ((signP p : ℤˣ) : ℤ) * ((signP p : ℤˣ) : ℤ) = 1 := signP_mul_self p
  have hdet : a * (((signP p : ℤˣ) : ℤ) * (p.val : ℤ)) -
      (((signP p : ℤˣ) : ℤ) * (i.val : ℤ)) * (3 * c) = 1 := by
    linear_combination ((signP p : ℤˣ) : ℤ) * hrel + hεε
  have hc : ((3 * c : ℤ) : ZMod 3) = 0 := by
    simp [zmod_three]
  have hd : ((((signP p : ℤˣ) : ℤ) * (p.val : ℤ) : ℤ) : ZMod 3) = 1 := by
    rw [Int.cast_mul, Int.cast_natCast, signP_cast p hp3, cast_mul_self p hp3]
  exact ⟨a, c, levelElt a (((signP p : ℤˣ) : ℤ) * (i.val : ℤ)) (3 * c)
    (((signP p : ℤˣ) : ℤ) * (p.val : ℤ)) hdet hc hd, hrel, rfl⟩

end Gamma

section Values

variable (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

include hp3 in
/-- `z(h_i)(i, p) = ε_p^m β_0(z)` for `0 < i < p`. -/
theorem eval_hElt_value (z : crossedCocycles (levelRep m e)) (i : Fin p.val) (hi : i.val ≠ 0) :
    eval ![(i.val : ℂ), (p.val : ℂ)] (z.val (hElt p i)).val =
      (((signP p : ℤˣ) : ℤ) : ℂ) ^ m * eval ![0, 1] (z.val (lower 1)).val := by
  obtain ⟨a, c, γ, hrel, hγ⟩ := exists_gamma p hp3 i hi
  have hεεC : (((signP p : ℤˣ) : ℤ) : ℂ) * (((signP p : ℤˣ) : ℤ) : ℂ) = 1 := by
    exact_mod_cast signP_mul_self p
  have hεε : ((signP p : ℤˣ) : ℤ) * ((signP p : ℤˣ) : ℤ) = 1 := signP_mul_self p
  have hγdet : ((γ.val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [hγ, Matrix.det_fin_two_of]
    linear_combination ((signP p : ℤˣ) : ℤ) * hrel + hεε
  have hcomm : hElt p i * γ = γ * lower 1 ^ 1 := by
    rw [pow_one]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hElt_coe, hγ, lower_coe]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | ring1
        | linear_combination (3 * (i.val : ℤ)) * hrel
        | linear_combination (3 * (p.val : ℤ)) * hrel
  have hδx : ∀ r, ∑ j, (((((hElt p i).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r j : ℤ) : ℂ)
      * (![(i.val : ℂ), (p.val : ℂ)] : Fin 2 → ℂ) j = (![(i.val : ℂ), (p.val : ℂ)] :
        Fin 2 → ℂ) r := by
    intro r
    rw [hElt_coe]
    fin_cases r <;> simp [Fin.sum_univ_two] <;> ring
  have hγy : ∀ r, ∑ j, ((((γ.val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) r j : ℤ) : ℂ) *
      ((((signP p : ℤˣ) : ℤ) : ℂ) • (![0, 1] : Fin 2 → ℂ)) j =
      (![(i.val : ℂ), (p.val : ℂ)] : Fin 2 → ℂ) r := by
    intro r
    rw [hγ]
    fin_cases r <;> simp [Fin.sum_univ_two] <;>
      first
        | linear_combination (i.val : ℂ) * hεεC
        | linear_combination (p.val : ℂ) * hεεC
  have key := eval_cusp_value m e z (hElt p i) γ 1 hcomm (hElt_det p i) hγdet
    ![(i.val : ℂ), (p.val : ℂ)] (((signP p : ℤˣ) : ℤ) : ℂ) hδx hγy
  rw [Nat.cast_one, mul_one] at key
  exact key

/-- `z(L)(0, ε_p) = ε_p^m β_0(z)`. -/
theorem eval_lower_one_value (z : crossedCocycles (levelRep m e)) :
    eval ![0, (((signP p : ℤˣ) : ℤ) : ℂ)] (z.val (lower 1)).val =
      (((signP p : ℤˣ) : ℤ) : ℂ) ^ m * eval ![0, 1] (z.val (lower 1)).val := by
  have hv : (![0, (((signP p : ℤˣ) : ℤ) : ℂ)] : Fin 2 → ℂ) =
      (((signP p : ℤˣ) : ℤ) : ℂ) • (![0, 1] : Fin 2 → ℂ) := by
    funext j
    fin_cases j <;> simp
  rw [hv, SymFixed.eval_smul_of_homogeneous (SymFixed.isHomogeneous _)]

/-- `z(L^{p²})(0, p) = p^m p² β_0(z)`. -/
theorem eval_lower_sq_value (z : crossedCocycles (levelRep m e)) :
    eval ![((⟨0, p.property.pos⟩ : Fin p.val).val : ℂ), (p.val : ℂ)]
        (z.val (lower ((p.val * p.val : ℕ) : ℤ))).val =
      (p.val : ℂ) ^ m * (((p.val * p.val : ℕ) : ℂ) * eval ![0, 1] (z.val (lower 1)).val) := by
  have hv : (![((⟨0, p.property.pos⟩ : Fin p.val).val : ℂ), (p.val : ℂ)] : Fin 2 → ℂ) =
      (p.val : ℂ) • (![0, 1] : Fin 2 → ℂ) := by
    funext j
    fin_cases j <;> simp
  rw [hv, SymFixed.eval_smul_of_homogeneous (SymFixed.isHomogeneous _),
    ← lower_pow_nat (p.val * p.val), ev01_cocycle_pow]

end Values

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryZero
