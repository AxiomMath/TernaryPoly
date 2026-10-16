module

public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorEasy
public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorFourth
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Lemma21Parts
public import TernaryPeriodPolynomials.Polynomial.Classification.Restriction
public import TernaryPeriodPolynomials.Polynomial.Divisibility

@[expose] public section


/-! Assembly of the four linear factors of `universalDivisor` into
`universalDivisor F ∣ f` for any solution `f` over a field `F` of characteristic zero
(Corollary 1.5, part (a)). Strategy: split `f` into its symmetric and alternating parts under
the swap `S : (x,y,z) ↦ (y,z,x)` (`Solution.symmPart`/`Solution.altPart` from
`Lemma21Parts.lean`), apply the three "easy" factors (`UniversalDivisorEasy.lean`) plus the
sector-specific fourth factor (`UniversalDivisorFourth.lean`) to each part separately, using
`TernaryPoly.mul_linear_factor_dvd_of_substitution_zero` to chain the four linear factors into one
product-divisibility fact (deriving each step's vanishing hypothesis directly from the previous
step's own divisibility fact, so no coprimality/UFD machinery is needed to combine independent
linear factors), then recombine via `f = fs + fa` and `dvd_add`. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials.Argument

variable {F : Type*} [Field F]

/-- The swap `S : (x,y,z) ↦ (y,z,x)` is an involution. -/
theorem swap01_swap01 (p : Ternary F) :
    bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F)
      (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) p) = p := by
  rw [bind₁_bind₁]
  have hv : (fun i : Fin 3 => bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F)
      ((![X 1, X 0, X 2] : Fin 3 → Ternary F) i)) = (X : Fin 3 → Ternary F) := by
    funext i; fin_cases i <;> simp [bind₁_X_right]
  rw [hv]
  simp [bind₁_X_left]

/-- Assembling the three "easy" factors and a sector-specific fourth factor into one
divisibility by `universalDivisor`. -/
private theorem universalDivisor_dvd_of_four {g : Ternary F} (hg : Solution g)
    (hCL : g = cyclicLift (restriction g)) (hPR : PeriodRelations (restriction g))
    (hd4 : (X 0 + X 1 + X 2 : Ternary F) ∣ g) :
    universalDivisor F ∣ g := by
  have hd1 : (X 0 + X 1 : Ternary F) ∣ g := dvd_X0_add_X1 hCL hPR
  have hd2 : (X 1 + X 2 : Ternary F) ∣ g := dvd_X1_add_X2 hg hCL hPR
  have hd3 : (X 2 + X 0 : Ternary F) ∣ g := dvd_X2_add_X0 hg hCL hPR
  have v2 : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary F) g = 0 := by
    obtain ⟨r, hr⟩ := hd2
    have hz : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary F) (X 1 + X 2) = 0 := by
      simp
    rw [hr, map_mul, hz, zero_mul]
  have hX0X1_ne : (X 0 + X 1 : Ternary F) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) h
    simp at this
  have hkeep2 : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary F) (X 0 + X 1) ≠ 0 := by
    have e : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary F) (X 0 + X 1) = X 0 + X 1 := by
      simp
    rwa [e]
  have D2 : (X 0 + X 1) * (X 1 + X 2) ∣ g := by
    have h := mul_linear_factor_dvd_of_substitution_zero g (X 0 + X 1) 2 (-X 1) hd1 v2 hkeep2
    have e : (X 0 + X 1 : Ternary F) * (X 2 - (-X 1)) = (X 0 + X 1) * (X 1 + X 2) := by ring
    rwa [e] at h
  have v3 : bind₁ (Function.update X 0 (-X 2) : Fin 3 → Ternary F) g = 0 := by
    obtain ⟨r, hr⟩ := hd3
    have hz : bind₁ (Function.update X 0 (-X 2) : Fin 3 → Ternary F) (X 2 + X 0) = 0 := by
      simp
    rw [hr, map_mul, hz, zero_mul]
  have hX1subX2_ne : (X 1 - X 2 : Ternary F) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) h
    simp at this
  have hX1X2_ne : (X 1 + X 2 : Ternary F) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) h
    simp at this
  have hkeep3 : bind₁ (Function.update X 0 (-X 2) : Fin 3 → Ternary F)
      ((X 0 + X 1) * (X 1 + X 2)) ≠ 0 := by
    have e1 : bind₁ (Function.update X 0 (-X 2) : Fin 3 → Ternary F) (X 0 + X 1) =
        X 1 - X 2 := by simp; ring
    have e2 : bind₁ (Function.update X 0 (-X 2) : Fin 3 → Ternary F) (X 1 + X 2) =
        X 1 + X 2 := by simp
    rw [map_mul, e1, e2]
    exact mul_ne_zero hX1subX2_ne hX1X2_ne
  have D3 : (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) ∣ g := by
    have h := mul_linear_factor_dvd_of_substitution_zero g ((X 0 + X 1) * (X 1 + X 2)) 0 (-X 2)
      D2 v3 hkeep3
    have e : (X 0 + X 1) * (X 1 + X 2) * (X 0 - (-X 2) : Ternary F) =
        (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) := by ring
    rwa [e] at h
  have v4 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F) g = 0 := by
    obtain ⟨r, hr⟩ := hd4
    have hz : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F)
        (X 0 + X 1 + X 2) = 0 := by simp
    rw [hr, map_mul, hz, zero_mul]
  have hX0_ne : (X 0 : Ternary F) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (![1, 0, 0] : Fin 3 → F)) h
    simp at this
  have hX1_ne : (X 1 : Ternary F) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → F)) h
    simp at this
  have hkeep4 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F)
      ((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)) ≠ 0 := by
    have e1 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F) (X 0 + X 1) =
        X 0 + X 1 := by simp
    have e2 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F) (X 1 + X 2) =
        -X 0 := by simp
    have e3 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary F) (X 2 + X 0) =
        -X 1 := by simp; ring
    rw [map_mul, map_mul, e1, e2, e3]
    have e4 : (X 0 + X 1) * (-X 0) * (-X 1 : Ternary F) = (X 0 + X 1) * X 0 * X 1 := by ring
    rw [e4]
    exact mul_ne_zero (mul_ne_zero hX0X1_ne hX0_ne) hX1_ne
  have D4 : (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) * (X 0 + X 1 + X 2) ∣ g := by
    have h := mul_linear_factor_dvd_of_substitution_zero g
      ((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)) 2 (-X 0 - X 1) D3 v4 hkeep4
    have e : (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) * (X 2 - (-X 0 - X 1) : Ternary F) =
        (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) * (X 0 + X 1 + X 2) := by ring
    rwa [e] at h
  have heq : (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) * (X 0 + X 1 + X 2 : Ternary F) =
      universalDivisor F := by
    simp only [universalDivisor]; ring
  rwa [heq] at D4

variable [CharZero F]

/-- Corollary 1.5, part (a): `universalDivisor F` divides every solution. -/
theorem universalDivisor_dvd_of_solution {f : Ternary F} (hf : Solution f) :
    universalDivisor F ∣ f := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hfs : Solution ((2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f)) :=
    Solution.symmPart hf
  have hfa : Solution ((2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f)) :=
    Solution.altPart hf
  have hsum : (2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) +
      (2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) = f := by
    have e : (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) +
        (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) = (2 : F) • f := by
      rw [two_smul]; ring
    rw [← smul_add, e, inv_smul_smul₀ h2]
  have hSfs : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F)
      ((2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f)) =
      (2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) := by
    rw [map_smul, map_add, swap01_swap01 f,
      add_comm (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) f]
  have hSfa : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F)
      ((2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f)) =
      -((2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f)) := by
    rw [map_smul, map_sub, swap01_swap01 f]
    rw [show (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f - f) =
        -(f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) from by ring]
    rw [smul_neg]
  have hCLfs : (2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) =
      cyclicLift (restriction ((2 : F)⁻¹ •
        (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f))) :=
    (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hfs).symm
  have hPRfs : PeriodRelations (restriction
      ((2 : F)⁻¹ • (f + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f))) :=
    TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hfs
  have hCLfa : (2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f) =
      cyclicLift (restriction ((2 : F)⁻¹ •
        (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f))) :=
    (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hfa).symm
  have hPRfa : PeriodRelations (restriction
      ((2 : F)⁻¹ • (f - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary F) f))) :=
    TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hfa
  have hd4s := dvd_X0_add_X1_add_X2_of_symmetric hfs hCLfs hPRfs hSfs
  have hd4a := dvd_X0_add_X1_add_X2_of_alternating hfa hCLfa hPRfa hSfa
  have hUfs := universalDivisor_dvd_of_four hfs hCLfs hPRfs hd4s
  have hUfa := universalDivisor_dvd_of_four hfa hCLfa hPRfa hd4a
  rw [← hsum]
  exact dvd_add hUfs hUfa

end TernaryPeriodPolynomials.Argument
