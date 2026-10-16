module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.ParabolicMatrix

@[expose] public section


open Matrix MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueParabolic
open PolynomialGLAction SinglePoleCoordinate

/-- Literal binary substitution by the displayed two by two matrix. -/
def binarySubstitute (M : Matrix (Fin 2) (Fin 2) ℚ) : Binary →ₐ[ℚ] Binary :=
  bind₁ (fun i => ∑ j, MvPolynomial.C (M i j) * X j)

theorem binarySubstitute_homogeneous (M : Matrix (Fin 2) (Fin 2) ℚ)
    {n : ℕ} {q : Binary} (hq : q.IsHomogeneous n) : (binarySubstitute M q).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hq
  intro i
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

def homogeneousBinarySubstitute (n : ℕ) (M : Matrix (Fin 2) (Fin 2) ℚ) :
    BinaryV n →ₗ[ℚ] BinaryV n where
  toFun q := ⟨binarySubstitute M q.val,binarySubstitute_homogeneous M q.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext ((binarySubstitute M).toLinearMap.map_smul _ _)

/-- The actual inverse substitution has precisely the normal scaling lambda inverse. -/
theorem substitute_inverse_X_zero (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) :
    substitute (g⁻¹ : GL3) (X 0) = MvPolynomial.C ((lam : ℚ)⁻¹) * X 0 := by
  rw [substitute_X]
  simp [linearForm,Fin.sum_univ_three,inverse_first_row g lam u C hg]

theorem substitute_X_zero (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) :
    substitute (g : Mat3) (X 0) = MvPolynomial.C (lam : ℚ) * X 0 := by
  rw [substitute_X]
  simp [linearForm,Fin.sum_univ_three,hg,blockMatrix]

/-- Restriction erases all lower-left inverse entries since their terms are multiples of a. -/
theorem restrict_substitute_inverse (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (p : SinglePole.Poly) :
    restrict 0 (substitute (g⁻¹ : GL3) p) = binarySubstitute (C⁻¹).val (restrict 0 p) := by
  have hb (i j : Fin 2) : (g.val⁻¹) i.succ j.succ = (C.val⁻¹) i j := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M i j) (inverse_lowerBlock g lam u C hg)
    simpa [lowerBlock] using h
  have he : (restrict 0).comp (substitute (g⁻¹ : GL3)) =
      (binarySubstitute (C⁻¹).val).comp (restrict 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · have hz := congrArg (restrict 0) (substitute_inverse_X_zero g lam u C hg)
      simpa [restrict,restrictionVariables] using hz
    · simp [AlgHom.comp_apply,substitute_X,linearForm,Fin.sum_univ_three,
        restrict,restrictionVariables,binarySubstitute,Fin.sum_univ_two]
      exact congrArg₂ (fun a b : ℚ => MvPolynomial.C a * X 0 + MvPolynomial.C b * X 1)
        (hb 0 0) (hb 0 1)
    · simp [AlgHom.comp_apply,substitute_X,linearForm,Fin.sum_univ_three,
        restrict,restrictionVariables,binarySubstitute,Fin.sum_univ_two]
      exact congrArg₂ (fun a b : ℚ => MvPolynomial.C a * X 0 + MvPolynomial.C b * X 1)
        (hb 1 0) (hb 1 1)
  exact AlgHom.congr_fun he p

/-- The chosen primitive denominator is carried to the same primitive denominator with exact scaling. -/
theorem substitute_inverse_denominator (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) :
    substitute (g⁻¹ : GL3) (SinglePole.denominator (OrdinaryResidueSupport.axis 0)) =
      MvPolynomial.C ((lam : ℚ)⁻¹) * SinglePole.denominator (OrdinaryResidueSupport.axis 0) := by
  rw [denominator_axis,map_mul,substitute_inverse_X_zero g lam u C hg]
  simp only [substitute,bind₁_C_right]
  ring

end TernaryPoly.OrdinaryResidueParabolic
