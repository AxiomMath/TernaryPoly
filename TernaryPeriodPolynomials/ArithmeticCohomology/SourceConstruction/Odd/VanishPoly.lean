module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Basic

@[expose] public section


/-!
# Polynomial and character facts for the odd-character vanishing

* evaluation of a linear substitution (`eval_substitute`);
* degree-zero homogeneous polynomials are constants (`homogeneousPoly_zero_eq_C`);
* in degree zero, for an odd character, the twisted coefficient action of every rational matrix of
  determinant `±1` is trivial (`rho_chi_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix

namespace TernaryPeriodPolynomials.SourceConstruction

/-- Evaluation after a substitution by forms. -/
theorem eval_bind₁_forms (forms : Fin 3 → Poly) (x : Fin 3 → ℂ) (f : Poly) :
    MvPolynomial.eval x (bind₁ forms f) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (forms i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, bind₁_X_right, eval_X]

/-- Evaluation after a linear substitution. -/
theorem eval_substitute3 (M : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 → ℂ) (f : Poly) :
    MvPolynomial.eval x (substitute M f) =
      MvPolynomial.eval (fun i => ∑ j, M i j * x j) f := by
  have forms : (fun i => MvPolynomial.eval x (linearForm M i)) = fun i => ∑ j, M i j * x j := by
    funext i
    simp [linearForm]
  rw [substitute, eval_bind₁_forms, forms]

/-- A homogeneous polynomial of degree zero is a constant. -/
theorem homogeneousPoly_zero_eq_C (v : HomogeneousPoly 0) :
    v.val = C (v.val.coeff 0) := by
  ext m
  rw [MvPolynomial.coeff_C]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hzero : v.val.coeff m = 0 := by
      by_contra hne
      have h3 := Spectral.GoodLineRestriction.deg3 0 v hne
      apply hm
      ext i
      fin_cases i <;> simp <;> omega
    rw [hzero, ite_eq_right (Ne.symm hm)]

/-- **The trivial-character coefficient action in degree zero** is the inverse determinant. -/
theorem rho_trivial_zero (g : RationalGL3) (v : HomogeneousPoly 0) :
    rationalCoefficientComponent 0 trivialCharacter g v = ((g.val.det : ℚ) : ℂ)⁻¹ • v := by
  apply Subtype.ext
  have hcoe := Spectral.IdentityPlaneCoordinate.rho_coe 0 g v
  have hdet : determinantCharacter (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) g) =
      (algebraMap ℚ ℂ g.val.det)⁻¹ := by
    change (((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℂ) g) : ℂˣ) : ℂ)) ^
      (-1 : ℤ) = _
    rw [_root_.zpow_neg_one, GeneralLinearGroup.val_det_apply]
    congr 1
    have h1 : (g.val.map (algebraMap ℚ ℂ)).det = algebraMap ℚ ℂ (g.val.det) :=
      (RingHom.map_det _ _).symm
    exact h1
  have hconst : substitute ((GeneralLinearGroup.map (algebraMap ℚ ℂ) g)⁻¹ : GL3).val v.val =
      v.val := by
    rw [homogeneousPoly_zero_eq_C v]
    exact MvPolynomial.bind₁_C_right _ _
  change (rationalCoefficientComponent 0 trivialCharacter g v).val = ((g.val.det : ℚ) : ℂ)⁻¹ • v.val
  rw [hcoe, action_apply, hconst, hdet]
  rfl

/-- **Degree zero, odd character.** The twisted coefficient action of a rational matrix of
determinant `±1` on degree-zero polynomials is trivial. -/
theorem rho_chi_zero {χ : RankOneCharacter}
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (g : RationalGL3)
    (hg : g.val.det = 1 ∨ g.val.det = -1) (v : HomogeneousPoly 0) :
    rationalCoefficientComponent 0 χ g v = v := by
  rw [Twisted.rho_apply_eq_detSign_smul, Twisted.detSign_odd hodd,
    rho_trivial_zero]
  have hpos : (0 : ℚ) < 1 := one_pos
  have hneg : ¬ (0 : ℚ) < -1 := by norm_num
  rcases hg with h | h
  · rw [h, ite_eq_left hpos]
    simp
  · rw [h, ite_eq_right hneg]
    simp [smul_smul]

end TernaryPeriodPolynomials.SourceConstruction
