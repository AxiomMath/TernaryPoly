module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodEquiv
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hom.HeckeAll

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePole SinglePoleCoordinate OrdinaryFullCoefficient OrdinaryHomHecke

/-- The genuine rational Hecke correspondence transported through the literal period-coordinate equivalence. -/
def periodHecke (n : ℕ) (g : OrdinaryFullAction.GL3) : Module.End ℚ (periodSpace (n+1)) :=
  (periodEquiv n).toLinearMap.comp
    ((rationalHecke g (residueAction n (-1))).comp (periodEquiv n).symm.toLinearMap)

/-- The transported operator is exactly the coordinate of the genuine residue Hom correspondence. -/
theorem periodHecke_equiv (n : ℕ) (g : OrdinaryFullAction.GL3) (F : ResidueHom n (-1)) :
    periodHecke n g (periodEquiv n F) = periodEquiv n (rationalHecke g (residueAction n (-1)) F) := by
  change periodEquiv n (rationalHecke g (residueAction n (-1)) ((periodEquiv n).symm (periodEquiv n F))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual liftable-period subspace inside the homogeneous binary period space. -/
def liftable (n : ℕ) : Submodule ℚ (periodSpace (n+1)) :=
  (liftableResidueHoms n (-1)).map (periodEquiv n).toLinearMap

/-- This subspace is precisely the defined literal liftablePeriods, with its proved period codomain. -/
theorem mem_liftable (n : ℕ) (q : periodSpace (n+1)) :
    q ∈ liftable n ↔ q.val ∈ liftablePeriods n := by
  constructor
  · rintro ⟨F,hF,hq⟩
    exact ⟨F,hF,congrArg Subtype.val hq⟩
  · rintro ⟨F,hF,hq⟩
    exact ⟨F,hF,Subtype.ext hq⟩

theorem liftable_eq_comap (n : ℕ) :
    liftable n = (liftablePeriods n).comap (periodSpace (n+1)).subtype := by
  ext q
  exact mem_liftable n q

/-- Every prior literal liftable period satisfies the full homogeneous binary period equations. -/
theorem liftablePeriods_mem_periodSpace (n : ℕ) (q : BinaryV (n+1)) (hq : q ∈ liftablePeriods n) :
    q ∈ periodSpace (n+1) := by
  obtain ⟨F,_hF,rfl⟩ := hq
  exact coordinatePeriod_mem n F

/-- Actual liftable binary periods are stable under the transported genuine rational Hecke operators. -/
theorem liftable_stable (n : ℕ) (g : OrdinaryFullAction.GL3) (q : periodSpace (n+1))
    (hq : q ∈ liftable n) : periodHecke n g q ∈ liftable n := by
  obtain ⟨F,hF,rfl⟩ := hq
  change periodHecke n g (periodEquiv n F) ∈ liftable n
  rw [periodHecke_equiv]
  exact ⟨rationalHecke g (residueAction n (-1)) F,
    liftableResidueHoms_rational_stable g n (-1) F hF,rfl⟩

/-- The exact extreme-coordinate obstruction holds on the transported actual liftable subspace. -/
theorem liftable_extreme (n : ℕ) (q : periodSpace (n+1)) (hq : q ∈ liftable n) (m : Fin 1 →₀ ℕ) :
    q.val.val.coeff (Finsupp.cons 1 m) = 0 :=
  liftablePeriods_extreme n q.val ((mem_liftable n q).mp hq) m

end TernaryPoly.OrdinaryResiduePeriod
