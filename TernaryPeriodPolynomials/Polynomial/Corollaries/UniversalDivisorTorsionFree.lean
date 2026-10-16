module

public import TernaryPeriodPolynomials.Polynomial.Corollaries.TorsionFreeDescent
public import TernaryPeriodPolynomials.Polynomial.Corollaries.TorsionFreeSectors
public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorFourth
public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorEasy
public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorRegularity

@[expose] public section


/-! The fifth and final conjunct of `torsion_free_descent`: `universalDivisor R ∣ f`, for any
`[CommRing R] [IsAddTorsionFree R]` and any solution `f`. The three "easy" factors
(`UniversalDivisorEasy.lean`) are already valid directly over `R`. The fourth factor
(`UniversalDivisorFourth.lean`) is `[Algebra ℚ _]`-generic but `R` itself need not carry
`[Algebra ℚ R]`; it is obtained by lifting to `A := TFHull R` (which does carry `[Algebra ℚ A]`),
splitting the lifted solution into symmetric/alternating sectors there
(`TorsionFreeSectors.lean`), applying the fourth-factor lemmas to each sector over `A`, and
descending the resulting vanishing fact back down along the injective embedding. All four
single-factor facts are then combined into the literal product `universalDivisor R` using the
domain-free combinator `mul_linear_factor_dvd_of_substitution_zero'`
(`UniversalDivisorRegularity.lean`), which needs no `[IsDomain R]`. Finally this is assembled with
`torsionFree_assembled_main`'s four conjuncts into the full statement of `torsion_free_descent`. -/


open MvPolynomial TernaryPoly TernaryPoly.Paper
open TernaryPeriodPolynomials.Argument.Classification

namespace TernaryPeriodPolynomials.Argument

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

section FourthFactorTorsionFree

/-- `-X0-X1` is unaffected by updating coordinate 2, over any `CommRing R`: it does not involve
`X 2`. -/
private theorem update2_fixes_negsum {A : Type*} [CommRing A] :
    bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary A) (-X 0 - X 1) = -X 0 - X 1 := by
  have hvec : (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary A) = ![X 0, X 1, -X 0 - X 1] := by
    funext i; fin_cases i <;> simp
  rw [hvec]
  simp [bind₁_X_right]

omit [IsAddTorsionFree R] in
/-- Naturality of the "F4" coordinate substitution (`X2 ↦ -X0-X1`) under a coefficient ring hom:
needed to pull the fourth factor's vanishing fact back down from `TFHull R` to `R`. Re-derives the
vector pushforward inline rather than reusing `TorsionFreeDescent.lean`'s `map_vec3_apply`, which
is `private` to that file and so not visible here. -/
private theorem map_update2_negsum {A : Type*} [CommRing A] (φ : R →+* A) (f : Ternary R) :
    map φ (bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) f) =
      bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary A) (map φ f) := by
  have hvecR : (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) = ![X 0, X 1, -X 0 - X 1] := by
    funext i; fin_cases i <;> simp
  have hvecA : (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary A) = ![X 0, X 1, -X 0 - X 1] := by
    funext i; fin_cases i <;> simp
  have hpush : (fun i : Fin 3 => MvPolynomial.map φ ((![X 0, X 1, -X 0 - X 1] : Fin 3 → Ternary R) i)) =
      (![X 0, X 1, -X 0 - X 1] : Fin 3 → Ternary A) := by
    funext i; fin_cases i <;> simp
  rw [hvecR, hvecA, map_bind₁, hpush]

/-- The fourth linear factor `X0+X1+X2` divides any solution over a merely torsion-free `R` (no
`[Algebra ℚ R]` needed on `R` itself): lift to `A := TFHull R`, split into symmetric and
alternating sectors there (each individually divisible by the fourth factor, by
`UniversalDivisorFourth.lean`), recombine, and push the resulting vanishing fact back down the
injective embedding. -/
theorem dvd_X0_add_X1_add_X2_torsionFree {f : Ternary R} (hf : Solution f) :
    (X 0 + X 1 + X 2 : Ternary R) ∣ f := by
  set φ : R →+* TFHull R := algebraMap R (TFHull R) with hφdef
  have hφ : Function.Injective φ := TFHull.algebraMap_injective
  have hφmap : Function.Injective (MvPolynomial.map φ : Ternary R →+* Ternary (TFHull R)) :=
    MvPolynomial.map_injective φ hφ
  set F : Ternary (TFHull R) := map φ f with hFdef
  have hF : Solution F := Solution.map hf φ
  set g1 : Ternary (TFHull R) :=
    half (TFHull R) • (F + bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary (TFHull R)) F) with hg1def
  set g2 : Ternary (TFHull R) :=
    half (TFHull R) • (F - bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary (TFHull R)) F) with hg2def
  have hg1 : Solution g1 := Solution.symmPart' hF
  have hg2 : Solution g2 := Solution.altPart' hF
  have hSym : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary (TFHull R)) g1 = g1 := swap01_symmPart F
  have hAlt : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary (TFHull R)) g2 = -g2 := swap01_altPart F
  have hCL1 : g1 = cyclicLift (restriction g1) := (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hg1).symm
  have hPR1 : PeriodRelations (restriction g1) := TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hg1
  have hCL2 : g2 = cyclicLift (restriction g2) := (TernaryPeriodPolynomials.Argument.Classification.cyclicLift_restriction hg2).symm
  have hPR2 : PeriodRelations (restriction g2) := TernaryPeriodPolynomials.Argument.Classification.restriction_periodRelations hg2
  have hdvd1 : (X 0 + X 1 + X 2 : Ternary (TFHull R)) ∣ g1 :=
    dvd_X0_add_X1_add_X2_of_symmetric hg1 hCL1 hPR1 hSym
  have hdvd2 : (X 0 + X 1 + X 2 : Ternary (TFHull R)) ∣ g2 :=
    dvd_X0_add_X1_add_X2_of_alternating hg2 hCL2 hPR2 hAlt
  have hsum : g1 + g2 = F := symmPart_add_altPart F
  have hdvdF : (X 0 + X 1 + X 2 : Ternary (TFHull R)) ∣ F := by
    rw [← hsum]; exact dvd_add hdvd1 hdvd2
  have hdvdF' : (X 2 - (-X 0 - X 1) : Ternary (TFHull R)) ∣ F := by
    have heq : (X 2 - (-X 0 - X 1) : Ternary (TFHull R)) = X 0 + X 1 + X 2 := by ring
    rw [heq]; exact hdvdF
  have hzeroA : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary (TFHull R)) F = 0 :=
    substitution_zero_of_dvd F 2 (-X 0 - X 1) update2_fixes_negsum hdvdF'
  have hzeroR : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) f = 0 :=
    hφmap (by rw [map_update2_negsum, hzeroA, map_zero])
  have hdvd := TernaryPoly.linear_factor_dvd_of_substitution_zero f 2 (-X 0 - X 1) hzeroR
  have heq : (X 0 + X 1 + X 2 : Ternary R) = X 2 - (-X 0 - X 1) := by ring
  rw [heq]; exact hdvd

end FourthFactorTorsionFree

section Combine

omit [IsAddTorsionFree R] in
/-- `X0` and `X1` are non-zero-divisors in `Ternary R`, for any `CommRing R`: a bare polynomial
variable is always regular (`MvPolynomial.isRegular_X`), no domain needed. -/
private theorem X0_mem_nonZeroDivisors : (X 0 : Ternary R) ∈ nonZeroDivisors (Ternary R) :=
  MvPolynomial.isRegular_X.mem_nonZeroDivisors

omit [IsAddTorsionFree R] in
private theorem X1_mem_nonZeroDivisors : (X 1 : Ternary R) ∈ nonZeroDivisors (Ternary R) :=
  MvPolynomial.isRegular_X.mem_nonZeroDivisors

omit [IsAddTorsionFree R] in
private theorem update1_fixes_negX0 :
    bind₁ (Function.update X 1 (-X 0) : Fin 3 → Ternary R) (-X 0) = -X 0 := by
  simp [bind₁_X_right]

omit [IsAddTorsionFree R] in
private theorem update2_fixes_negX1 :
    bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary R) (-X 1) = -X 1 := by
  simp [bind₁_X_right]

/-- `universalDivisor R` divides any solution over a merely torsion-free `R`: the fifth and final
conjunct of `torsion_free_descent`. Peels the three "easy" factors and the fourth factor onto a
running divisor one at a time (order F3, F1, F2, F4), each time checking that the running
divisor's image under the next substitution is a non-zero-divisor (never needing
`[IsDomain R]`). -/
theorem universalDivisor_dvd_torsionFree {f : Ternary R} (hf : Solution f)
    (hCL : f = cyclicLift (restriction f)) (hPR : PeriodRelations (restriction f)) :
    universalDivisor R ∣ f := by
  have d3 : (X 2 + X 0 : Ternary R) ∣ f := dvd_X2_add_X0 hf hCL hPR
  have d1 : (X 0 + X 1 : Ternary R) ∣ f := dvd_X0_add_X1 hCL hPR
  have d2 : (X 1 + X 2 : Ternary R) ∣ f := dvd_X1_add_X2 hf hCL hPR
  have d4 : (X 0 + X 1 + X 2 : Ternary R) ∣ f := dvd_X0_add_X1_add_X2_torsionFree hf
  -- Step 1: peel F1 (index 1, value -X0) onto D0 := F3 = X2+X0.
  have hvanish1 : bind₁ (Function.update X 1 (-X 0) : Fin 3 → Ternary R) f = 0 := by
    apply substitution_zero_of_dvd f 1 (-X 0) update1_fixes_negX0
    have heq : (X 1 - (-X 0) : Ternary R) = X 0 + X 1 := by ring
    rw [heq]; exact d1
  have hkeep1 : bind₁ (Function.update X 1 (-X 0) : Fin 3 → Ternary R) (X 2 + X 0) ∈
      nonZeroDivisors (Ternary R) := by
    have heval : bind₁ (Function.update X 1 (-X 0) : Fin 3 → Ternary R) (X 2 + X 0) = X 0 + X 2 := by
      simp [bind₁_X_right]; ring
    rw [heval]
    exact X0_add_X2_mem_nonZeroDivisors
  have hD1 : (X 2 + X 0) * (X 1 - (-X 0)) ∣ f :=
    mul_linear_factor_dvd_of_substitution_zero' f (X 2 + X 0) 1 (-X 0) d3 hvanish1 hkeep1
  -- Step 2: peel F2 (index 2, value -X1) onto D1 := (X2+X0)*(X0+X1).
  have hvanish2 : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary R) f = 0 := by
    apply substitution_zero_of_dvd f 2 (-X 1) update2_fixes_negX1
    have heq : (X 2 - (-X 1) : Ternary R) = X 1 + X 2 := by ring
    rw [heq]; exact d2
  have hkeep2 : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary R)
      ((X 2 + X 0) * (X 1 - (-X 0))) ∈ nonZeroDivisors (Ternary R) := by
    have heval : bind₁ (Function.update X 2 (-X 1) : Fin 3 → Ternary R)
        ((X 2 + X 0) * (X 1 - (-X 0))) = (X 0 - X 1) * (X 0 + X 1) := by
      simp [bind₁_X_right]; ring
    rw [heval]
    exact mul_mem X0_sub_X1_mem_nonZeroDivisors X0_add_X1_mem_nonZeroDivisors
  have hD2 : (X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1)) ∣ f :=
    mul_linear_factor_dvd_of_substitution_zero' f ((X 2 + X 0) * (X 1 - (-X 0))) 2 (-X 1)
      hD1 hvanish2 hkeep2
  -- Step 3: peel F4 (index 2, value -X0-X1) onto D2 := (X2+X0)*(X0+X1)*(X1+X2).
  have hvanish4 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R) f = 0 := by
    apply substitution_zero_of_dvd f 2 (-X 0 - X 1) update2_fixes_negsum
    have heq : (X 2 - (-X 0 - X 1) : Ternary R) = X 0 + X 1 + X 2 := by ring
    rw [heq]; exact d4
  have hkeep4 : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R)
      ((X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1))) ∈ nonZeroDivisors (Ternary R) := by
    have heval : bind₁ (Function.update X 2 (-X 0 - X 1) : Fin 3 → Ternary R)
        ((X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1))) = (-X 1) * (X 0 + X 1) * (-X 0) := by
      simp [bind₁_X_right]; ring
    rw [heval]
    exact mul_mem (mul_mem (neg_mem_nonZeroDivisors X1_mem_nonZeroDivisors)
      X0_add_X1_mem_nonZeroDivisors) (neg_mem_nonZeroDivisors X0_mem_nonZeroDivisors)
  have hD3 : (X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1)) * (X 2 - (-X 0 - X 1)) ∣ f :=
    mul_linear_factor_dvd_of_substitution_zero' f
      ((X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1))) 2 (-X 0 - X 1) hD2 hvanish4 hkeep4
  have heqfinal :
      (X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1)) * (X 2 - (-X 0 - X 1)) = universalDivisor R := by
    show (X 2 + X 0) * (X 1 - (-X 0)) * (X 2 - (-X 1)) * (X 2 - (-X 0 - X 1)) =
      (X 0 + X 1 + X 2) * (X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)
    ring
  rw [heqfinal] at hD3
  exact hD3

end Combine

section Assembled

/-- The full five-conjunct statement of `torsion_free_descent`, assembled from
`torsionFree_assembled_main` (the first four conjuncts) and `universalDivisor_dvd_torsionFree`
(the fifth). -/
theorem torsion_free_descent_assembled {f : Ternary R} (hf : Solution f) :
    Pairwise f ∧ (∀ n : ℕ, Odd n → homogeneousComponent n f = 0) ∧
      PeriodRelations (restriction f) ∧ f = cyclicLift (restriction f) ∧
      universalDivisor R ∣ f := by
  obtain ⟨hP, hOdd, hPR, hCL⟩ := torsionFree_assembled_main hf
  exact ⟨hP, hOdd, hPR, hCL, universalDivisor_dvd_torsionFree hf hCL hPR⟩

end Assembled

end TernaryPeriodPolynomials.Argument
