module

public import TernaryPeriodPolynomials.Analysis.Scalar.EisensteinLevelThreeEichlerGeometry
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Hom
public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Projection

@[expose] public section
noncomputable section
open MvPolynomial Matrix

namespace TernaryPoly.BinaryCuspSymbol

abbrev GL2 := BinaryModularSymbol.GL2
abbrev Poly := MvPolynomial (Fin 2) ℂ
abbrev Functions := Coordinates → ℂ

/-- Actual rational matrices acting on complex coordinates through coefficient extension. -/
def complexify : GL2 →* GeneralLinearGroup (Fin 2) ℂ :=
  GeneralLinearGroup.map (algebraMap ℚ ℂ)

/-- Literal complex linear coordinate form of a matrix row. -/
def linearForm (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) : Poly :=
  ∑ j, MvPolynomial.C (M i j)*X j

/-- Literal substitution by a complex matrix. -/
def substitute (M : Matrix (Fin 2) (Fin 2) ℂ) : Poly →ₐ[ℂ] Poly := bind₁ (linearForm M)

theorem substitute_linearForm (M N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    substitute M (linearForm N i) = linearForm (N*M) i := by
  simp only [linearForm, substitute, map_sum, map_mul, bind₁_C_right, bind₁_X_right,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem substitute_X (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    substitute M (X i) = linearForm M i := by simp [substitute]

theorem substitute_comp (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (substitute M).comp (substitute N) = substitute (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitute_X]
  exact substitute_linearForm M N i

theorem substitute_one : substitute (1 : Matrix (Fin 2) (Fin 2) ℂ) = AlgHom.id ℂ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitute, linearForm, Matrix.one_apply]

/-- Actual inverse polynomial substitution as a rational representation on complex polynomials. -/
def polynomialUntwisted : Representation ℚ GL2 Poly where
  toFun g := (substitute ((complexify g)⁻¹ : GeneralLinearGroup (Fin 2) ℂ)).toLinearMap.restrictScalars ℚ
  map_one' := by
    simp only [map_one, inv_one, GeneralLinearGroup.coe_one, substitute_one]
    rfl
  map_mul' g h := by
    simp only [map_mul, _root_.mul_inv_rev, GeneralLinearGroup.coe_mul]
    exact congrArg (fun q : Poly →ₐ[ℂ] Poly => q.toLinearMap.restrictScalars ℚ)
      (substitute_comp ((complexify g)⁻¹ : GeneralLinearGroup (Fin 2) ℂ)
        ((complexify h)⁻¹ : GeneralLinearGroup (Fin 2) ℂ)).symm

/-- The exact determinant-inverse left action, on genuine complex coefficients. -/
def polynomialAction : Representation ℚ GL2 Poly where
  toFun g := BinaryModularSymbolCoefficients.determinantCharacter (-1) g • polynomialUntwisted g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    change BinaryModularSymbolCoefficients.determinantCharacter (-1) (g*h) • polynomialUntwisted (g*h) P =
      BinaryModularSymbolCoefficients.determinantCharacter (-1) g • polynomialUntwisted g
        (BinaryModularSymbolCoefficients.determinantCharacter (-1) h • polynomialUntwisted h P)
    rw [map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- Actual inverse coordinate substitution on all complex-valued functions. -/
def functionUntwisted : Representation ℚ GL2 Functions where
  toFun g :=
    { toFun := fun F v => F (((complexify g)⁻¹).val.mulVec v)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext F v
    simp
  map_mul' g h := by
    ext F v
    change F (((complexify (g*h))⁻¹).val.mulVec v) =
      F (((complexify h)⁻¹).val.mulVec (((complexify g)⁻¹).val.mulVec v))
    rw [map_mul, _root_.mul_inv_rev, GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

/-- The same determinant-inverse action on scalar-valued functions of complex coordinates. -/
def functionAction : Representation ℚ GL2 Functions where
  toFun g := BinaryModularSymbolCoefficients.determinantCharacter (-1) g • functionUntwisted g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    change BinaryModularSymbolCoefficients.determinantCharacter (-1) (g*h) • functionUntwisted (g*h) F =
      BinaryModularSymbolCoefficients.determinantCharacter (-1) g • functionUntwisted g
        (BinaryModularSymbolCoefficients.determinantCharacter (-1) h • functionUntwisted h F)
    rw [map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]

/-- Evaluation embeds actual complex polynomials into scalar functions. -/
def evaluate : Poly →ₗ[ℚ] Functions where
  toFun P v := eval v P
  map_add' P Q := by funext v; exact map_add (eval v) P Q
  map_smul' c P := by funext v; exact map_rat_smul (eval v) c P

theorem evaluate_injective : Function.Injective evaluate := by
  intro P Q h
  exact MvPolynomial.funext (congrFun h)

theorem eval_linearForm (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Coordinates) (i : Fin 2) :
    eval v (linearForm M i) = (M.mulVec v) i := by
  simp [linearForm, Matrix.mulVec, dotProduct]

theorem eval_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Poly) (v : Coordinates) :
    eval v (substitute M P) = eval (M.mulVec v) P := by
  change eval₂Hom (RingHom.id ℂ) v (bind₁ (linearForm M) P) = _
  rw [eval₂Hom_bind₁]
  have he : (fun i => eval₂Hom (RingHom.id ℂ) v (linearForm M i)) = M.mulVec v :=
    funext (eval_linearForm M v)
  rw [he]
  rfl

/-- Evaluation intertwines the exact coefficient actions, with no normalization adjustment. -/
theorem evaluate_equivariant (g : GL2) (P : Poly) :
    evaluate (polynomialAction g P) = functionAction g (evaluate P) := by
  funext v
  change eval v (BinaryModularSymbolCoefficients.determinantCharacter (-1) g •
    substitute ((complexify g)⁻¹ : GeneralLinearGroup (Fin 2) ℂ) P) = _
  rw [map_rat_smul, eval_substitute]
  rfl

abbrev PolynomialHom := BinaryModularSymbol.Hom polynomialAction
abbrev FunctionHom := BinaryModularSymbol.Hom functionAction

end TernaryPoly.BinaryCuspSymbol
