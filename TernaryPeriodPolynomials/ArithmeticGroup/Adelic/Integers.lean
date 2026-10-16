module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Finite

@[expose] public section




/-! The actual product of all local integer rings and its finite-adele embedding. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open IsDedekindDomain

abbrev IntegralAdeles := ∀ v : FinitePlace, v.adicCompletionIntegers ℚ

def integralEmbedding : IntegralAdeles →+* FiniteAdeles where
  toFun x := ⟨fun v => x v, Filter.Eventually.of_forall (fun v => (x v).property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem integralEmbedding_at (x : IntegralAdeles) (v : FinitePlace) :
    finiteEvaluation v (integralEmbedding x) = (x v).val := rfl

theorem integralEmbedding_injective : Function.Injective integralEmbedding := by
  intro x y h
  funext v
  exact Subtype.ext (congrArg (finiteEvaluation v) h)

@[simp] theorem integralEmbedding_int (z : ℤ) :
    integralEmbedding (z : IntegralAdeles) = (z : FiniteAdeles) :=
  map_intCast integralEmbedding z

end GeneralEisenstein.Adelic

end
