module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Reflected
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Modularity
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Holomorphy

@[expose] public section


/-!
# G5 at level one, with the hypotheses on the scalar functions derived from the inducing data

Formalized by Claude Sonnet 5.5.

`g5_levelOne_of_eichler`: for an inducing datum `D` and an `EichlerInput` `I` of its cuspidal representation (the Eichler vector of the model's
scalar `F = cuspScalarWeightedRealization D.cusp I.halfWeight I.vector`), the holomorphy (`scalar_holomorphic_allBases`), the Levi modularity
(`hmod_H`, `hmod_H'`) and the moment primitives (`exists_moment_primitives`) of `H = F(1·b_F(1))` and `H' = F(J·b_F(1))` are PROVED, so `g5_levelOne`
applies to the model's actual identity-plane cochain without separate hypotheses.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
  TernaryPeriodPolynomials.Argument GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction
  TernaryPeriodPolynomials.Argument.LevelTransfer

open TernaryPeriodPolynomials.EdgeControl (spherical_fixed)
open TernaryPeriodPolynomials.SphericalDetection.Helpers TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.CuspidalSpan

/-- The hypotheses of the seed class of `Γ_P = Γ(N) ∩ P(ℤ)` on a scalar function `H` with moment primitives `Gm`. -/
structure SeedHyp (N n : ℕ) (H : ℂ → ℂ) (Gm : ℕ → ℂ → ℂ) : Prop where
  hh : DifferentiableOn ℂ H Psi.upperSet
  hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (H z * z ^ j) z
  hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
    H (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * H z

/-- The conclusion of `g5_levelOne` (cochain identity and class identity). -/
def LevelOneConclusion (N n : ℕ) [NeZero N] (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (Gm Gm' : ℕ → ℂ → ℂ)
    (s : SeedHyp N n (F (1 * bF (1 : AdelicGL))) Gm) (s' : SeedHyp N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm') :
    Prop :=
  (∀ (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ), cOmegaCoeff n D F y 1 κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D 1) *
        ((((gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm s.hh s.hG s.hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' s'.hh s'.hG s'.hmod).val.val y :
            HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ)) ∧
    (groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (Submodule.Quotient.mk (gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm s.hh s.hG s.hmod)
              (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' s'.hh s'.hG s'.hmod))) =
      complexifyG N n ((gammaNPlaneData N).seedClass (F (1 * bF (1 : AdelicGL))) n Gm s.hh s.hG s.hmod) +
        (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
          (complexifyG N n ((gammaNPlaneData N).seedClass (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) n Gm'
            s'.hh s'.hG s'.hmod))

theorem g5_levelOne_of_eichler (N n : ℕ) [NeZero N] (h3 : 3 ∣ N) (D : InducingData n) (I : EichlerInput D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hF : F = cuspScalarWeightedRealization D.cusp I.halfWeight I.vector) :
    ∃ (Gm Gm' : ℕ → ℂ → ℂ) (s : SeedHyp N n (F (1 * bF (1 : AdelicGL))) Gm)
      (s' : SeedHyp N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm'),
      LevelOneConclusion N n D F Gm Gm' s s' := by
  subst hF
  have hfix := spherical_fixed D.cusp I.vector.val I.vector_spherical
  have hh : DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp I.halfWeight I.vector (1 * bF (1 : AdelicGL))) Psi.upperSet :=
    scalar_holomorphic_allBases I D.cohomological _
  have hh' : DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp I.halfWeight I.vector
      (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Psi.upperSet :=
    scalar_holomorphic_allBases I D.cohomological _
  obtain ⟨Gm, -, hG⟩ := exists_moment_primitives _ hh
  obtain ⟨Gm', -, hG'⟩ := exists_moment_primitives _ hh'
  have hmod := fun g z hz => hmod_H D.cusp n I.halfWeight I.weight I.vector I.rotation hfix N h3 g z hz
  have hmod' := fun g z hz => hmod_H' D.cusp n I.halfWeight I.weight I.vector I.rotation hfix N h3 g z hz
  exact ⟨Gm, Gm', ⟨hh, hG, hmod⟩, ⟨hh', hG', hmod'⟩, g5_levelOne N n D _ Gm Gm' hh hG hmod hh' hG' hmod'⟩

end TernaryPeriodPolynomials.Argument.FormSeedBridge
