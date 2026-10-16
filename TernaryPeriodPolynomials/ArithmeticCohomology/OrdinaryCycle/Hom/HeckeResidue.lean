module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hom.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientResidue

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHomHecke
open OrdinaryFullAction OrdinaryFullCoefficient OrdinaryHeckeArithmetic OrdinaryHeckeTransfer SinglePole

variable (g : OrdinaryFullAction.GL3) [(intersection Gamma g).FiniteIndex]

/-- The actual residue morphism commutes with the genuine full-level Hecke correspondence. -/
theorem residue_heckeHom (n : ℕ) (e : ℤ) (f : SinglePoleHom n e) :
    residueHom n e (heckeHom g (singlePoleAction n e) f) =
      heckeHom g (residueAction n e) (residueHom n e f) :=
  heckeHom_natural g (singlePoleAction n e) (residueAction n e) (residue n)
    (fun h x => (residue_equivariant n e h x).symm) f

/-- An actual lift is carried to an actual lift by the conjugation-transfer operator. -/
theorem hecke_lift_witness (n : ℕ) (e : ℤ) (r : ResidueHom n e) (f : SinglePoleHom n e)
    (hf : residueHom n e f = r) :
    residueHom n e (heckeHom g (singlePoleAction n e) f) =
      heckeHom g (residueAction n e) r := by
  rw [residue_heckeHom,hf]

/-- The genuine image of the actual residue map on ordinary Hom is Hecke stable. -/
theorem liftableResidueHoms_stable (n : ℕ) (e : ℤ) (r : ResidueHom n e)
    (hr : r ∈ liftableResidueHoms n e) :
    heckeHom g (residueAction n e) r ∈ liftableResidueHoms n e := by
  obtain ⟨f,hf⟩ := hr
  exact ⟨heckeHom g (singlePoleAction n e) f,hecke_lift_witness g n e r f hf⟩

/-- Submodule form of actual liftable-residue Hecke stability. -/
theorem liftableResidueHoms_le_comap (n : ℕ) (e : ℤ) :
    liftableResidueHoms n e ≤
      (liftableResidueHoms n e).comap (heckeHom g (residueAction n e)) :=
  fun r hr => liftableResidueHoms_stable g n e r hr

end TernaryPoly.OrdinaryHomHecke
