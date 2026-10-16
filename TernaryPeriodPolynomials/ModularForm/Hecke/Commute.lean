module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Coefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryCuspPeriod

/-- Genuine prime Hecke endomorphisms of actual full-level cusp forms commute pairwise. -/
theorem T_commute (d p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Commute (T d p) (T d q) := by
  apply LinearMap.ext
  intro f
  apply coefficients_injective d
  simp only [Module.End.mul_apply,coefficients_T_function]
  exact coefficientOperator_commute d p q Fact.out Fact.out (coefficients f)

/-- The commuting operators act equally on every actual cusp form. -/
theorem T_commute_apply (d p q : ℕ) [Fact p.Prime] [Fact q.Prime] (f : Forms d) :
    T d p (T d q f) = T d q (T d p f) := LinearMap.congr_fun (T_commute d p q) f

end TernaryPoly.BinaryCuspHeckeEndomorphism
