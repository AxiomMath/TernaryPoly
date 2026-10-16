module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hom.HeckeResidue
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.ArithmeticFiniteIndex

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHomHecke
open OrdinaryFullAction OrdinaryFullCoefficient OrdinaryHeckeArithmetic OrdinaryHeckeTransfer SinglePole

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Actual ordinary Hecke operators exist for every rational invertible matrix, by the proved finite index. -/
def rationalHecke (g : OrdinaryFullAction.GL3) (ρ : Representation ℚ OrdinaryFullAction.GL3 E) :
    Module.End ℚ (Hom ρ) := by
  letI := intersection_finiteIndex g
  exact heckeHom g ρ

@[simp] theorem rationalHecke_eq (g : OrdinaryFullAction.GL3) [(intersection Gamma g).FiniteIndex]
    (ρ : Representation ℚ OrdinaryFullAction.GL3 E) : rationalHecke g ρ = heckeHom g ρ := rfl

/-- Every actual coefficient intertwiner commutes with every rational Hecke correspondence. -/
theorem rationalHecke_natural {F : Type*} [AddCommGroup F] [Module ℚ F]
    (g : OrdinaryFullAction.GL3) (ρ : Representation ℚ OrdinaryFullAction.GL3 E)
    (τ : Representation ℚ OrdinaryFullAction.GL3 F) (T : E →ₗ[ℚ] F)
    (hT : ∀ h x, T (ρ h x) = τ h (T x)) (f : Hom ρ) :
    homMap ρ τ T hT (rationalHecke g ρ f) = rationalHecke g τ (homMap ρ τ T hT f) := by
  let := intersection_finiteIndex g
  exact heckeHom_natural g ρ τ T hT f

/-- The actual residue map commutes with all rational Hecke operators, with no index hypothesis. -/
theorem residue_rationalHecke (g : OrdinaryFullAction.GL3) (n : ℕ) (e : ℤ) (f : SinglePoleHom n e) :
    residueHom n e (rationalHecke g (singlePoleAction n e) f) =
      rationalHecke g (residueAction n e) (residueHom n e f) := by
  let := intersection_finiteIndex g
  exact residue_heckeHom g n e f

/-- The concrete transformed lift witnesses actual residue liftability for every rational correspondence. -/
theorem rationalHecke_lift_witness (g : OrdinaryFullAction.GL3) (n : ℕ) (e : ℤ)
    (r : ResidueHom n e) (f : SinglePoleHom n e) (hf : residueHom n e f = r) :
    residueHom n e (rationalHecke g (singlePoleAction n e) f) =
      rationalHecke g (residueAction n e) r := by
  rw [residue_rationalHecke,hf]

/-- Actual liftable residues form a Hecke-stable subspace for all rational invertible matrices. -/
theorem liftableResidueHoms_rational_stable (g : OrdinaryFullAction.GL3) (n : ℕ) (e : ℤ)
    (r : ResidueHom n e) (hr : r ∈ liftableResidueHoms n e) :
    rationalHecke g (residueAction n e) r ∈ liftableResidueHoms n e := by
  obtain ⟨f,hf⟩ := hr
  exact ⟨rationalHecke g (singlePoleAction n e) f,rationalHecke_lift_witness g n e r f hf⟩

end TernaryPoly.OrdinaryHomHecke
