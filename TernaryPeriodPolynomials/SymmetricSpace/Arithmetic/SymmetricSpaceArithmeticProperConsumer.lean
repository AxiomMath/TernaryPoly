module

public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperFinite
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper
open Matrix SymmetricSpacePositive IntegralGL3Congruence

/-- A principal-six matrix fixing any point of the actual symmetric-space model is identity.
Only ordinary finite-order torsion-freeness is used, after proving the actual stabilizer finite. -/
theorem principalSix_fixed_eq_one (g : IntegralGL) (hg : g ∈ principalSix) (S : Space)
    (hfix : act (realIntegral g) S = S) : g = 1 :=
  principalSix_finiteOrder_eq_one g hg (integral_fixed_isOfFinOrder g S hfix)

/-- Freeness stated intrinsically in the actual principal-six subgroup. -/
theorem principalSix_subgroup_fixed_eq_one (g : principalSix) (S : Space)
    (hfix : act (realIntegral g.val) S = S) : g = 1 := by
  apply Subtype.ext
  exact principalSix_fixed_eq_one g.val g.property S hfix

/-- Every principal-six orbit map in the actual trace-normalized model is injective. -/
theorem principalSix_orbit_injective (S : Space) :
    Function.Injective (fun g : principalSix => act (realIntegral g.val) S) := by
  intro g h heq
  change act (realIntegral g.val) S = act (realIntegral h.val) S at heq
  have hfix : act (realIntegral (h.val⁻¹*g.val)) S = S := by
    rw [map_mul,map_inv,act_mul,heq,←act_mul,inv_mul_cancel,act_one]
  have hmem : h.val⁻¹*g.val ∈ principalSix :=
    principalSix.mul_mem (principalSix.inv_mem h.property) g.property
  have hid := principalSix_fixed_eq_one _ hmem S hfix
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hid).symm

/-- The actual principal-six kernel inside the sum-covector fixer also acts freely. -/
theorem principalSixInK_fixed_eq_one (g : ModThreeGoodAction.K) (hg : g ∈ principalSixInK)
    (S : Space) (hfix : act (realIntegral g.val) S = S) : g = 1 := by
  apply Subtype.ext
  exact principalSix_fixed_eq_one g.val ((mem_principalSixInK g).mp hg) S hfix

end TernaryPoly.SymmetricSpaceArithmeticProper
