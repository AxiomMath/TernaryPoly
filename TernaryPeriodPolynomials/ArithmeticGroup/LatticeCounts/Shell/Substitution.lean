module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IntegralSubstitution

@[expose] public section


/-!
# The finite factor and the packaged shell substitution

Formalized by Claude Haiku 5.5.
Paper: (`L(s,t) k₀ = [[A_Λ, *],[0, p^{-r}]]`).

Proved here:
* `finite_factor`: if `det A = p^r` then `|det A|_p^{k/2} = p^{-rk/2}` (real exponent `k/2`).
* `shell_substitution_packaged`: the substitution `k₀` of `IntegralSubstitution.exists_substitution_matrix`
  together with the plane transformation law, giving the finite factor `p^{-rk/2}` times `v_h|A`.

Hypothesis:
* `SeedTransform k V W`: the plane transformation law eq:seed-transform,
  `g^* ω_h = ρ(g) ω_{δ^{k/2}(h|_k A)}`, in the form used by the paper: the plane value `V A`
  equals `|det A|_p^{k/2} · W A`, where `W A` is `v_h|A`. Its proof is the Eichler-Shimura plane
  computation and the product formula; it is supplied by the plane-cohomology tree, not here.

NOT in this file: the shell sum and the measure. The measure of the shell is
`ShellHaar.shell_measure_finitePlace` (`p^{2r} - p^{2r-2}`); it is not bundled here because the
shell contribution also needs the cyclic-lattice identity eq:cyclic-hecke (owned by S5).
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

variable {p : ℕ} [Fact p.Prime]

/-- **Finite factor.** If `det A = p^r`, then `|det A|_p^{k/2} = p^{-rk/2}`, where the exponent
`k/2` is real and `|·|_p` is the `p`-adic absolute value. -/
theorem finite_factor {A : Matrix (Fin 2) (Fin 2) (Padic p)} {r : ℕ} (k : ℤ)
    (hdet : A.det = (p : Padic p) ^ r) :
    ‖A.det‖ ^ ((k : ℝ) / 2) = (p : ℝ) ^ (-(r : ℝ) * ((k : ℝ) / 2)) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have e : ((p : ℝ) ^ r)⁻¹ = (p : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg hp, Real.rpow_natCast]
  rw [hdet, norm_p_pow_nat, e, ← Real.rpow_mul hp]

/-- **Hypothesis: the plane transformation law (eq:seed-transform).** For a family of
plane values `V A` (the pullback of `ω_h` at `A`) and the adelic values `W A = v_h|A`, the law says
`V A = |det A|_p^{k/2} · W A` for every nonsingular `A`. Stated as a hypothesis; not derived here. -/
def SeedTransform (k : ℤ) (p : ℕ) [Fact p.Prime]
    (V W : Matrix (Fin 2) (Fin 2) (Padic p) → ℂ) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) (Padic p), A.det ≠ 0 →
    V A = (((‖A.det‖ ^ ((k : ℝ) / 2) : ℝ)) : ℂ) * W A

/-- **Packaged shell substitution.** Given the columns of `A` in `Λ_{s,t}`, `det A = p^r`,
`max(‖s‖,‖t‖) = p^r`, and the plane transformation law `SeedTransform`:
* the substitution `k₀` is `p`-integral with `det k₀ = 1` and `L(s,t) k₀ = [[A, *],[0, p^{-r}]]`;
* the plane value is `p^{-rk/2}` times `v_h|A`. -/
theorem shell_substitution_packaged (k : ℤ) {V W : Matrix (Fin 2) (Fin 2) (Padic p) → ℂ}
    (hSeed : SeedTransform k p V W) {r : ℕ} {s t : Padic p}
    (hmax : max ‖s‖ ‖t‖ = (p : ℝ) ^ r)
    {A : Matrix (Fin 2) (Fin 2) (Padic p)}
    (hA : ∀ j : Fin 2, (A 0 j, A 1 j) ∈ latSubst s t)
    (hdet : A.det = (p : Padic p) ^ r) :
    (∃ w₀ x y : Padic p, (∀ i j : Fin 3, ‖substK s t A w₀ x y i j‖ ≤ 1) ∧
      (substK s t A w₀ x y).det = 1 ∧
      substL s t * substK s t A w₀ x y =
        !![A 0 0, A 0 1, x; A 1 0, A 1 1, y; 0, 0, ((p : Padic p) ^ r)⁻¹]) ∧
    V A = (((p : ℝ) ^ (-(r : ℝ) * ((k : ℝ) / 2)) : ℝ) : ℂ) * W A := by
  refine ⟨exists_substitution_matrix hA hdet hmax, ?_⟩
  have hne : A.det ≠ 0 := by
    rw [hdet]
    exact padic_p_pow_ne_zero r
  rw [hSeed A hne, finite_factor k hdet]

end TernaryPeriodPolynomials.Argument.LatticeCounts
