module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.GLTransfer

@[expose] public section


/-!
# `QGL` is a transitive `gammaNGL N`-set with stabilizer `gammaNGL M`; transport of the induced and restricted modules

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

variable {N M : ℕ}

/-- The base coset. -/
def base (N M : ℕ) : QGL N M := ((1 : Gamma N) : Gamma N ⧸ subM N M)

/-- A lift of a coset to `gammaNGL N`. -/
def uLift [hN : Fact (3 ≤ N)] (x : QGL N M) : gammaNGL N := gammaEquiv hN.out (Quotient.out x)

theorem uLift_base [hN : Fact (3 ≤ N)] (x : QGL N M) : uLift x • base N M = x := by
  rw [QGL_smul, uLift, MulEquiv.symm_apply_apply]
  change (QuotientGroup.mk (Quotient.out x * 1) : Gamma N ⧸ subM N M) = x
  rw [mul_one]
  exact Quotient.out_eq' x

theorem smul_base_iff [hN : Fact (3 ≤ N)] (g : gammaNGL N) :
    g • base N M = base N M ↔ (g : IntegralGL) ∈ gammaNGL M := by
  rw [QGL_smul]
  change (QuotientGroup.mk ((gammaEquiv hN.out).symm g * 1) : Gamma N ⧸ subM N M) = QuotientGroup.mk 1 ↔ _
  rw [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf]
  have hmem : ((gammaEquiv hN.out).symm g : Gamma N).1 ∈ Gamma M ↔
      Matrix.SpecialLinearGroup.toGL ((gammaEquiv hN.out).symm g : Gamma N).1 ∈ gammaNGL M :=
    toGL_mem_gammaNGL.symm
  have hg : Matrix.SpecialLinearGroup.toGL ((gammaEquiv hN.out).symm g : Gamma N).1 = (g : IntegralGL) := by
    have := congrArg (fun x : gammaNGL N => (x : IntegralGL)) ((gammaEquiv hN.out).apply_symm_apply g)
    exact this
  rw [hmem, hg]

end TernaryPeriodPolynomials.Argument.CuspidalInduction
