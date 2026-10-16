module

public import TernaryPeriodPolynomials.Polynomial.Corollaries.Lemma21Parts

@[expose] public section


/-! Generalizing `Solution.symmPart`/`Solution.altPart` (from `Lemma21Parts.lean`, there stated only
for `[Field F]`) to any `[Algebra ℚ R]`, using an explicit witness inverse of `(2:R)` rather than
`Field`-division. This is what lets the fourth linear factor's argument
(`UniversalDivisorFourth.lean`, already `[Algebra ℚ R]`-generic) be applied to a solution's sector
decomposition over `A := TFHull R` in `UniversalDivisorTorsionFree.lean`, where `A` need not be a
field. -/


open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

section Half

/-- An explicit witness inverse of `(2 : R)`, valid in any `[Algebra ℚ R]` (not just a field):
`ℚ` already contains the true inverse of `2`, and the algebra map carries the defining identity
across. -/
noncomputable def half (R : Type*) [CommRing R] [Algebra ℚ R] : R := algebraMap ℚ R (2⁻¹ : ℚ)

theorem two_mul_half (R : Type*) [CommRing R] [Algebra ℚ R] : (2 : R) * half R = 1 := by
  show (2 : R) * algebraMap ℚ R (2⁻¹ : ℚ) = 1
  rw [show (2 : R) = algebraMap ℚ R (2 : ℚ) from (map_ofNat (algebraMap ℚ R) 2).symm, ← map_mul,
    show (2 : ℚ) * 2⁻¹ = 1 from by norm_num, map_one]

theorem half_add_half (R : Type*) [CommRing R] [Algebra ℚ R] : half R + half R = (1 : R) := by
  have h := two_mul_half R
  rwa [two_mul] at h

end Half

section SwapInvolution

variable {R : Type*} [CommRing R]

/-- The variable swap `(x,y,z) ↦ (y,x,z)` is an involution, over every commutative ring. -/
theorem swap01_swap01_tf (f : Ternary R) :
    bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)
      (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) = f := by
  have h : (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)).comp
      (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)) = AlgHom.id R (Ternary R) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun h f

end SwapInvolution

section Sectors

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem half_smul_two_mul (x : Ternary R) : half R • (x + x) = x := by
  rw [smul_add, ← add_smul, half_add_half, one_smul]

/-- The symmetric-sector combination `half R • (f + swap f)` is fixed by the swap. -/
theorem swap01_symmPart (f : Ternary R) :
    bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)
        (half R • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f))
      = half R • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) := by
  rw [map_smul, map_add, swap01_swap01_tf]
  congr 1
  ring

/-- The alternating-sector combination `half R • (f - swap f)` is negated by the swap. -/
theorem swap01_altPart (f : Ternary R) :
    bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)
        (half R • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f))
      = -(half R • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f)) := by
  rw [map_smul, map_sub, swap01_swap01_tf, ← smul_neg]
  congr 1
  ring

/-- The two sector pieces reassemble to `f`. -/
theorem symmPart_add_altPart (f : Ternary R) :
    half R • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) +
        half R • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) = f := by
  rw [← smul_add]
  have hsum : (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) +
      (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f) = f + f := by ring
  rw [hsum]
  exact half_smul_two_mul f

/-- The symmetric sector of a solution, generalized from `Solution.symmPart`'s `[Field F]` to any
`[Algebra ℚ R]`: identical proof, with `half R` standing in for `(2:F)⁻¹`. -/
theorem Solution.symmPart' {f : Ternary R} (hf : Solution f) :
    Solution (half R • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f)) :=
  (solutions R).smul_mem _ ((solutions R).add_mem hf (Solution.swap01 hf))

/-- The alternating sector of a solution, generalized from `Solution.altPart`'s `[Field F]` to any
`[Algebra ℚ R]`: identical proof, with `half R` standing in for `(2:F)⁻¹`. -/
theorem Solution.altPart' {f : Ternary R} (hf : Solution f) :
    Solution (half R • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f)) :=
  (solutions R).smul_mem _ ((solutions R).sub_mem hf (Solution.swap01 hf))

end Sectors

end TernaryPeriodPolynomials.Argument
