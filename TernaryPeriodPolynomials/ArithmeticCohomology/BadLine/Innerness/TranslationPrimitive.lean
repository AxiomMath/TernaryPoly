module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.OddCusp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem X_two_dvd_sub_upperCusp (p : Poly) : X 2 ∣ p-upperCuspSubstitution p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [upperCuspSubstitution]
  | add p q hp hq =>
    rw [map_add]
    convert dvd_add hp hq using 1
    ring
  | mul_X p i hp =>
    fin_cases i
    · simpa [upperCuspSubstitution,sub_mul] using
        dvd_mul_of_dvd_left hp (X 0)
    · simpa [upperCuspSubstitution,sub_mul] using dvd_mul_of_dvd_left hp (X 1)
    · simp [upperCuspSubstitution]

theorem bernoulliEnd_translationEnd_commute (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0) :
    Commute (bernoulliEnd n positive t linear) (translationEnd n positive t linear) := by
  apply Commute.sum_right
  intro k _
  exact ((derivative_bernoulliEnd_commute n positive t t linear linear independent independent).symm.pow_right k).smul_right _

theorem difference_bernoulliEnd (n : ℕ) (positive : 0 < n)
    (t : Poly) (linear : t.IsHomogeneous 1) (independent : pderiv 0 t = 0)
    (p : HomogeneousPoly n) :
    (bernoulliEnd n positive t linear p).val -
      bind₁ ![X 0-t,X 1,X 2] (bernoulliEnd n positive t linear p).val =
      t * pderiv 0 p.val := by
  have commutes := congrArg (fun L : Module.End ℂ (HomogeneousPoly n) => (L p).val)
    (bernoulliEnd_translationEnd_commute n positive t linear independent).eq
  simp only [Module.End.mul_apply] at commutes
  rw [← translationEnd_apply n positive t linear independent,← commutes,
    ← Submodule.coe_sub,← map_sub,bernoulliEnd_apply n positive t linear independent]
  rw [Submodule.coe_sub,translationEnd_apply n positive t linear independent]
  exact bernoulliOperator_coboundary n positive t linear independent p

theorem first_difference_primitive (n : ℕ) (positive : 0 < n)
    (p : HomogeneousPoly n) (divisible : X 2 ∣ p.val) :
    ∃ q : HomogeneousPoly n, p.val = q.val-bind₁ ![X 0-X 2,X 1,X 2] q.val := by
  obtain ⟨h,factorization⟩ := divisible
  have hh : h.IsHomogeneous (n-1) :=
    homogeneous_of_X_mul h 2 (factorization ▸ p.property)
  let primitive : HomogeneousPoly n := ⟨firstAntiderivative h,by
    change (firstAntiderivative h).IsHomogeneous n
    simpa only [Nat.sub_add_cancel positive] using firstAntiderivative_homogeneous h hh⟩
  refine ⟨bernoulliEnd n positive (X 2) (isHomogeneous_X ℂ 2) primitive,?_⟩
  rw [difference_bernoulliEnd n positive (X 2) (isHomogeneous_X ℂ 2) (by simp)]
  exact factorization.trans (congrArg (fun h => X 2*h) (firstAntiderivative_pderiv h).symm)

def swapXY : Poly →ₐ[ℂ] Poly := bind₁ ![X 1,X 0,X 2]

theorem swapXY_twice (p : Poly) : swapXY (swapXY p) = p := by
  have hom_eq : swapXY.comp swapXY = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [swapXY]
  exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p) hom_eq

theorem swapXY_homogeneous {n : ℕ} (p : HomogeneousPoly n) :
    (swapXY p.val).IsHomogeneous n := by
  have homogeneous_images (i : Fin 3) : (![X 1,X 0,X 2] i : Poly).IsHomogeneous 1 := by
    fin_cases i <;> exact isHomogeneous_X ℂ _
  simpa only [swapXY,aeval_eq_bind₁,one_mul] using
    p.property.aeval ![X 1,X 0,X 2] homogeneous_images

theorem swapXY_first_translation (p : Poly) :
    swapXY (bind₁ ![X 0-X 2,X 1,X 2] p) = upperTranslationSubstitution (swapXY p) := by
  have hom_eq : swapXY.comp (bind₁ ![X 0-X 2,X 1,X 2]) =
      upperTranslationSubstitution.comp swapXY := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [swapXY,upperTranslationSubstitution]
  exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p) hom_eq

theorem removeFirstVariable_upperTranslation (p : Poly) :
    removeFirstVariable (upperTranslationSubstitution p) =
      upperTranslationSubstitution (removeFirstVariable p) := by
  have hom_eq : removeFirstVariable.comp upperTranslationSubstitution =
      upperTranslationSubstitution.comp removeFirstVariable := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [removeFirstVariable,upperTranslationSubstitution]
  exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p) hom_eq

theorem upper_translation_primitive (m : ℕ) (positive : 0 < m)
    (p : HomogeneousPoly m) (independent : pderiv 0 p.val = 0)
    (cusp_zero : upperCuspSubstitution p.val = 0) :
    ∃ q : HomogeneousPoly m, pderiv 0 q.val = 0 ∧
      p.val = q.val-upperTranslationSubstitution q.val := by
  have divisible : X 2 ∣ p.val := by
    simpa only [cusp_zero,sub_zero] using X_two_dvd_sub_upperCusp p.val
  have swapped_divisible : X 2 ∣ swapXY p.val := by
    obtain ⟨h,hh⟩ := divisible
    exact ⟨swapXY h,by simp [hh,swapXY]⟩
  obtain ⟨q,hq⟩ := first_difference_primitive m positive ⟨swapXY p.val,swapXY_homogeneous p⟩
    swapped_divisible
  have difference := congrArg swapXY hq
  rw [swapXY_twice,map_sub,swapXY_first_translation] at difference
  let projected := independentPart m ⟨swapXY q.val,swapXY_homogeneous q⟩
  refine ⟨projected,removeFirstVariable_pderiv _,?_⟩
  have result := congrArg removeFirstVariable difference
  rw [removeFirstVariable_eq_of_pderiv_zero p.val independent,map_sub,
    removeFirstVariable_upperTranslation] at result
  exact result

theorem normalizedBadLine_upper_coordinate_primitive (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∃ q : HomogeneousPoly (n+1), pderiv 0 q.val = 0 ∧
      mixedBernoulliCoordinate c upperTranslation = q.val-upperTranslationSubstitution q.val := by
  have homogeneous : (mixedBernoulliCoordinate c upperTranslation).IsHomogeneous (n+1) := by
    rw [mixedBernoulliCoordinate_eq_pair]
    exact radicalPairCoordinate_homogeneous n positive _ _
  exact upper_translation_primitive (n+1) (Nat.succ_pos n) ⟨_,homogeneous⟩
    (mixedBernoulliCoordinate_pderiv_zero n positive c normalized.1
      ⟨upperTranslation,upperTranslation_mem⟩ upperTranslation_normalizes)
    (normalizedBadLine_upper_cusp_zero n positive f solution c normalized)

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
