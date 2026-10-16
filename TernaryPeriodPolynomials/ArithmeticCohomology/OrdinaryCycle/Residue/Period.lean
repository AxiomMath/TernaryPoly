module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Parabolic

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePole SinglePoleCoordinate OrdinaryFullCoefficient OrdinaryHomHecke
open OrdinaryResidueParabolic PolynomialGLAction

/-- The binary coordinate of the genuine rational correspondence is literally the transported operator. -/
theorem periodHecke_coordinate (n : ℕ) (g : OrdinaryFullAction.GL3) (q : periodSpace (n+1)) :
    (periodHecke n g q).val =
      coordinatePeriod n 0 (rationalHecke g (residueAction n (-1)) ((periodEquiv n).symm q)) := rfl

/-- The full residue functional inverse and the actual parabolic coefficient action use the same literal binary coordinate. -/
theorem inverse_reference_parabolic (n : ℕ) (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (q : periodSpace (n+1)) :
    coordinateTuple n (residueAction n (-1) g
      (reference (residueAction n (-1)) ((periodEquiv n).symm q))) 0 =
      C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val q.val := by
  rw [coordinateTuple_action n g lam u C hg]
  congr 2
  change (periodEquiv n ((periodEquiv n).symm q)).val = q.val
  rw [LinearEquiv.apply_symm_apply]

/-- Every genuine rational Hecke translate of an actual liftable period satisfies the extreme obstruction. -/
theorem periodHecke_liftable_extreme (n : ℕ) (g : OrdinaryFullAction.GL3) (q : periodSpace (n+1))
    (hq : q ∈ liftable n) (m : Fin 1 →₀ ℕ) :
    (periodHecke n g q).val.val.coeff (Finsupp.cons 1 m) = 0 :=
  liftable_extreme n (periodHecke n g q) (liftable_stable n g q hq) m

end TernaryPoly.OrdinaryResiduePeriod
