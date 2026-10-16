module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberActions

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed ReferenceCoefficientMatrices

/-- The actual reference matrix acts by A2, as dictated by inverse substitution. -/
theorem fractionEquiv_a (x : Frac) : SinglePole.fractionEquiv (rational a) x=fracA2 x := by
  have he : (SinglePole.fractionEquiv (rational a)).toRingHom=fracA2.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    intro p
    change SinglePole.fractionEquiv (rational a) (embed p)=fracA2 (embed p)
    rw [SinglePole.fractionEquiv_embed,fracA2_embed,substitute_a_inverse]
  exact DFunLike.congr_fun he x

theorem fractionEquiv_c (x : Frac) : SinglePole.fractionEquiv (rational c) x=fracC x := by
  have he : (SinglePole.fractionEquiv (rational c)).toRingHom=fracC.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    intro p
    change SinglePole.fractionEquiv (rational c) (embed p)=fracC (embed p)
    rw [SinglePole.fractionEquiv_embed,fracC_embed,substitute_c_inverse]
  exact DFunLike.congr_fun he x

theorem fractionEquiv_s (x : Frac) : SinglePole.fractionEquiv (rational s) x=fracS x := by
  have he : (SinglePole.fractionEquiv (rational s)).toRingHom=fracS.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    intro p
    change SinglePole.fractionEquiv (rational s) (embed p)=fracS (embed p)
    rw [SinglePole.fractionEquiv_embed,fracS_embed,substitute_s_inverse]
  exact DFunLike.congr_fun he x

/-- Two applications of the reference norm matrix give the literal A action. -/
theorem fractionEquiv_a_a (x : Frac) :
    SinglePole.fractionEquiv (rational a) (SinglePole.fractionEquiv (rational a) x)=fracA x := by
  rw [fractionEquiv_a,fractionEquiv_a]
  change fracA (fracA (fracA (fracA x)))=fracA x
  rw [fracA_cube]

end TernaryPoly.OrdinaryRationalFiber
