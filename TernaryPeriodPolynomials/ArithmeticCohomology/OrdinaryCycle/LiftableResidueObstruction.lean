module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ResidueObstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalCoordinate

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open SinglePoleCoordinate SinglePoleSupport OrdinaryResidueGeneral OrdinaryResidueSupport

/-- The actual literal binary period coordinate of an ordinary residue functional. -/
def coordinatePeriod (n : ℕ) (i : Fin 3) : ResidueHom n (-1) →ₗ[ℚ] BinaryV (n+1) :=
  (literalFiberMap n i).comp ((SinglePoleSupport.component n (axis i)).comp
    (reference (SinglePole.residueAction n (-1))))

@[simp] theorem coordinatePeriod_residueHom (n : ℕ) (i : Fin 3) (Φ : SinglePoleHom n (-1)) :
    coordinatePeriod n i (residueHom n (-1) Φ)=
      coordinateResidue n i (reference (SinglePole.singlePoleAction n (-1)) Φ) := rfl

/-- Every extreme coefficient vanishes on the actual liftable subspace in its literal coordinate. -/
theorem liftable_coordinate_extreme (n : ℕ) (Φ : ResidueHom n (-1))
    (hΦ : Φ ∈ liftableResidueHoms n (-1)) (i : Fin 3) (m : Fin 1 →₀ ℕ) :
    (coordinatePeriod n i Φ).val.coeff (Finsupp.cons 1 m)=0 := by
  obtain ⟨Ψ,rfl⟩ := hΦ
  rw [coordinatePeriod_residueHom]
  let x := reference (SinglePole.singlePoleAction n (-1)) Ψ
  have hx : Relations (SinglePole.singlePoleAction n (-1)) x := hom_relations _ Ψ
  apply actual_coordinate_extreme n (-1) x _ _ hx.norm i m
  · exact symmetry_of_relations _ x hx
  · intro s
    rw [odd_scalar_neg_one,one_smul]
    exact sign_invariant_of_relations _ x hx s

/-- The literal binary periods carried by actual liftable residue functionals form a linear subspace. -/
def liftablePeriods (n : ℕ) : Submodule ℚ (BinaryV (n+1)) :=
  (liftableResidueHoms n (-1)).map (coordinatePeriod n 0)

/-- The specified extreme-coefficient functional vanishes on that entire actual period subspace. -/
theorem liftablePeriods_extreme (n : ℕ) (q : BinaryV (n+1)) (hq : q ∈ liftablePeriods n)
    (m : Fin 1 →₀ ℕ) : q.val.coeff (Finsupp.cons 1 m)=0 := by
  obtain ⟨Φ,hΦ,rfl⟩ := hq
  exact liftable_coordinate_extreme n Φ hΦ 0 m

end TernaryPoly.OrdinaryFullCoefficient
