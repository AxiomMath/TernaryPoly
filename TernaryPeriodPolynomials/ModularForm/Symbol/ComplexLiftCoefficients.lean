module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Coefficients
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Formula

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspSymbol
open MvPolynomial BinaryModularSymbol BinaryModularSymbolCoefficients BinaryRationalHeckePrime

/-- The actual complex-valued evaluation of a rational polynomial. -/
def rationalEvaluate : BinaryModularSymbolCoefficients.Poly →ₗ[ℚ] Functions where
  toFun q v := eval₂ (algebraMap ℚ ℂ) v q
  map_add' q r := by funext v; exact map_add (eval₂Hom (algebraMap ℚ ℂ) v) q r
  map_smul' a q := by funext v; exact map_rat_smul (eval₂Hom (algebraMap ℚ ℂ) v) a q

theorem rationalEvaluate_map (q : BinaryModularSymbolCoefficients.Poly) :
    rationalEvaluate q=evaluate (map (algebraMap ℚ ℂ) q) := by
  funext v
  exact (eval₂_map (algebraMap ℚ ℂ) v (RingHom.id ℂ) q).symm

theorem rationalEvaluate_linearForm (M : Matrix (Fin 2) (Fin 2) ℚ) (v : Coordinates) (i : Fin 2) :
    rationalEvaluate (BinaryModularSymbolCoefficients.linearForm M i) v=
      ((M.map (algebraMap ℚ ℂ)).mulVec v) i := by
  simp [rationalEvaluate,BinaryModularSymbolCoefficients.linearForm,Matrix.mulVec,dotProduct]

/-- Coefficient extension and evaluation intertwine the genuine determinant-inverse actions. -/
theorem rationalEvaluate_equivariant (g : GL2) (q : BinaryModularSymbolCoefficients.Poly) :
    rationalEvaluate (BinaryModularSymbolCoefficients.action (-1) g q)=functionAction g (rationalEvaluate q) := by
  funext v
  change eval₂Hom (algebraMap ℚ ℂ) v (determinantCharacter (-1) g •
    bind₁ (BinaryModularSymbolCoefficients.linearForm (g⁻¹).val) q)=
      determinantCharacter (-1) g • eval₂Hom (algebraMap ℚ ℂ) (((complexify g)⁻¹).val.mulVec v) q
  rw [map_rat_smul,eval₂Hom_bind₁]
  congr 3
  funext i
  change rationalEvaluate (BinaryModularSymbolCoefficients.linearForm (g⁻¹).val i) v=_
  rw [rationalEvaluate_linearForm,←map_inv]
  rfl

/-- Complex scalars commute with the actual rational function-coefficient action. -/
theorem functionAction_complex_smul (g : GL2) (a : ℂ) (F : Functions) :
    functionAction g (a • F)=a • functionAction g F := by
  funext v
  change determinantCharacter (-1) g • (a • F (((complexify g)⁻¹).val.mulVec v))=
    a • (determinantCharacter (-1) g • F (((complexify g)⁻¹).val.mulVec v))
  exact smul_comm _ _ _

/-- Complex scaling preserves actual integral equivariance. -/
def scaleFunctionHom (a : ℂ) (F : FunctionHom) : FunctionHom :=
  ⟨a • F.val,by
    intro g c
    change a • F.val (BinaryModularSymbol.action (integral g) c)=functionAction (integral g) (a • F.val c)
    rw [hom_equivariant,functionAction_complex_smul]⟩

@[simp] theorem scaleFunctionHom_apply (a : ℂ) (F : FunctionHom) (c : St) :
    (scaleFunctionHom a F).val c=a • F.val c := rfl

theorem evaluate_complex_smul (a : ℂ) (q : BinaryCuspSymbol.Poly) :
    evaluate (a • q)=a • evaluate q := by
  funext v
  exact map_smul (aeval v) a q

/-- Actual rational homogeneous symbol maps acquire complex-valued function coefficients. -/
def rationalFunctionHom (d : ℕ) (F : PeriodHom d) : FunctionHom :=
  ⟨(rationalEvaluate.comp (homogeneousSubmodule (Fin 2) ℚ d).subtype).comp F.val,by
    intro g c
    change rationalEvaluate (F.val (BinaryModularSymbol.action (integral g) c)).val=
      functionAction (integral g) (rationalEvaluate (F.val c).val)
    rw [hom_equivariant]
    exact rationalEvaluate_equivariant _ _⟩

@[simp] theorem rationalFunctionHom_apply (d : ℕ) (F : PeriodHom d) (c : St) :
    (rationalFunctionHom d F).val c=rationalEvaluate (F.val c).val := rfl

/-- The genuine prime transfer commutes with actual coefficient extension and evaluation. -/
theorem rationalFunctionHom_hecke (d p : ℕ) [Fact p.Prime] (F : PeriodHom d) :
    BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction (rationalFunctionHom d F)=
      rationalFunctionHom d (BinaryRationalHecke.rationalHecke (primeDiagonal p) (homogeneousAction d (-1)) F) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  have hleft := congrArg (fun T : St →ₗ[ℚ] Functions => T c)
    (rationalHecke_prime p functionAction (rationalFunctionHom d F))
  have hright := congrArg (fun T : St →ₗ[ℚ] HomogeneousPoly d => T c)
    (rationalHecke_prime p (homogeneousAction d (-1)) F)
  simp only [LinearMap.sum_apply,homAction_apply] at hleft hright
  rw [hleft,rationalFunctionHom_apply,hright]
  simp only [Submodule.coe_sum,map_sum,rationalFunctionHom_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (rationalEvaluate_equivariant _ _).symm

/-- Prime transfer is also complex-linear on the actual function-valued Hom space. -/
theorem scaleFunctionHom_hecke (p : ℕ) [Fact p.Prime] (a : ℂ) (F : FunctionHom) :
    BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction (scaleFunctionHom a F)=
      scaleFunctionHom a (BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction F) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  have h (G : FunctionHom) := congrArg (fun T : St →ₗ[ℚ] Functions => T c)
    (rationalHecke_prime p functionAction G)
  simp only [LinearMap.sum_apply,homAction_apply] at h
  rw [h,scaleFunctionHom_apply,h,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => functionAction_complex_smul _ _ _)

end TernaryPoly.BinaryCuspSymbol
