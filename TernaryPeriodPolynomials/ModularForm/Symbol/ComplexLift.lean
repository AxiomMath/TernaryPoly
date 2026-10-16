module

public import TernaryPeriodPolynomials.ModularForm.Symbol.ComplexLiftCoefficients
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodTensorHecke

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspSymbol
open BinaryModularSymbol BinaryComplexPeriod BinaryRationalHeckePrime

/-- The actual rational symbol map, faithfully evaluated in complex coordinates. -/
def rationalPeriodFunction (d : ℕ) (q : space ℚ d) : FunctionHom :=
  rationalFunctionHom d ((periodEquiv d).symm ((rationalEquiv d).symm q))

@[simp] theorem rationalPeriodFunction_reference (d : ℕ) (q : space ℚ d) :
    (rationalPeriodFunction d q).val reference=evaluate (extend (algebraMap ℚ ℂ) d q).val := by
  rw [rationalPeriodFunction,rationalFunctionHom_apply,periodEquiv_symm_reference]
  exact rationalEvaluate_map q.val

theorem rationalPeriodFunction_hecke (d p : ℕ) (q : space ℚ d) [Fact p.Prime] :
    BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction (rationalPeriodFunction d q)=
      rationalPeriodFunction d (rationalSymbolHecke d (primeDiagonal p) q) := by
  unfold rationalPeriodFunction
  rw [rationalFunctionHom_hecke]
  congr 1
  apply (periodEquiv d).injective
  rw [←BinaryRationalHecke.periodHecke_evaluation]
  simp [rationalSymbolHecke]

/-- Rational spanning constructs an actual complex-valued modular symbol for every complex
period, with exactly the scalar-extended prime Hecke value. -/
theorem exists_functionHom_hecke (d p : ℕ) [Fact p.Prime] (q : space ℂ d) :
    ∃ F : FunctionHom,F.val reference=evaluate q.val ∧
      (BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction F).val reference=
        evaluate (complexHecke d (primeDiagonal p) q).val := by
  have hq : q ∈ Submodule.span ℂ (Set.range (extend (algebraMap ℚ ℂ) d)) := by
    rw [span_extend_eq_top]
    trivial
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨r,rfl⟩ := hq
    refine ⟨rationalPeriodFunction d r,rationalPeriodFunction_reference d r,?_⟩
    rw [rationalPeriodFunction_hecke,rationalPeriodFunction_reference,complexHecke_extend]
  | zero =>
    refine ⟨0,?_,?_⟩ <;> simp
  | add q r _ _ hq hr =>
    obtain ⟨F,hF,hTF⟩ := hq
    obtain ⟨G,hG,hTG⟩ := hr
    refine ⟨F+G,?_,?_⟩
    · change F.val reference+G.val reference=evaluate (q.val+r.val)
      rw [map_add,hF,hG]
    · rw [map_add]
      change _+_=evaluate (complexHecke d (primeDiagonal p) (q+r)).val
      rw [hTF,hTG,map_add,Submodule.coe_add,map_add]
  | smul a q _ hq =>
    obtain ⟨F,hF,hTF⟩ := hq
    refine ⟨scaleFunctionHom a F,?_,?_⟩
    · rw [scaleFunctionHom_apply,hF]
      exact (evaluate_complex_smul a q.val).symm
    · rw [scaleFunctionHom_hecke,scaleFunctionHom_apply,hTF,map_smul]
      exact (evaluate_complex_smul a (complexHecke d (primeDiagonal p) q).val).symm

/-- Reference evaluation is faithful, so every actual symbol with the prescribed complex period
has precisely the genuine complex Hecke value. -/
theorem functionHom_hecke_reference (d p : ℕ) [Fact p.Prime]
    (F : FunctionHom) (q : space ℂ d) (hF : F.val reference=evaluate q.val) :
    (BinaryRationalHecke.rationalHecke (primeDiagonal p) functionAction F).val reference=
      evaluate (complexHecke d (primeDiagonal p) q).val := by
  obtain ⟨G,hG,hTG⟩ := exists_functionHom_hecke d p q
  have he : F=G := evaluation_injective functionAction (hF.trans hG.symm)
  rw [he]
  exact hTG

end TernaryPoly.BinaryCuspSymbol
