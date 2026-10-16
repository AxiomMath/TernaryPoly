module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.OtherCuspsTransport
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.OtherCuspsCochain
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.OtherCuspsBase

@[expose] public section


/-!
# `g5_levelOne` at the other plane cusps

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (`ar:lem:seed`) at the plane cusps `h⁻¹ P h`.

`g5_levelOne_cusp`: for an inducing datum `D` with an `EichlerInput` `I`, `3 ∣ N`, and any adelic `g` with `g_∞ = mapGL σ` (`σ ∈ SL₃(ℤ)`) and integral `b_F g`
(e.g. the diagonal image of an integral matrix, `bF_rational_integral`), the scalar functions `H_g = F(1·b_F g)`, `H'_g = F(J·b_F g)` have all the seed hypotheses of `Γ_P` (proved: holomorphy, moment primitives,
Levi modularity), and
(1) the model's plane integral cochain at `g` is `K_g` times the coefficient of `ρ(σ⁻¹) C(σ y)`, `C = c_{H_g} + ε`-transport of `c_{H'_g}` (a cocycle of `realLevel Γ_{σ⁻¹Pσ}`);
(2) the class of that conjugate cocycle in `H²(Γ_{σ⁻¹Pσ}, E_n)` is the conjugation transport (`conjP N σ`, `ρ(σ⁻¹)`) of `[seed H_g] + ε_*[seed H'_g]`.
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
  TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.EdgeControl (spherical_fixed)
open TernaryPeriodPolynomials.SphericalDetection.Helpers TernaryPeriodPolynomials.Argument.CuspidalSpan

theorem g5_levelOne_cusp (N n : ℕ) [NeZero N] (h3 : 3 ∣ N) (D : InducingData n) (I : EichlerInput D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hF : F = cuspScalarWeightedRealization D.cusp I.halfWeight I.vector)
    (σ : SL(3, ℤ)) (G : AdelicGL) (hσ : realGroup G = Matrix.SpecialLinearGroup.mapGL ℝ σ)
    (hB : ∃ B : GeneralLinearGroup (Fin 2) IntegralAdeles,
      bF G = atFinite (GeneralLinearGroup.map integralEmbedding B)) :
    ∃ (Gm Gm' : ℕ → ℂ → ℂ) (s : SeedHyp N n (F (1 * bF G)) Gm)
      (s' : SeedHyp N n (F (atInfinity UpperHalfPlane.J * bF G)) Gm'),
      (∀ (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ), cOmegaCoeff n D F y G κ =
        (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D G) *
          ((realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
            ((gramCocycleW (seedCone N n (F (1 * bF G)) Gm s.hh s.hG s.hmod) (rhoR_gammaNP N n) +
              reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF G)) Gm' s'.hh s'.hG s'.hmod).val.val
                (fun i => Matrix.SpecialLinearGroup.mapGL ℝ σ * y i) : HomogeneousPoly n) :
                  MvPolynomial (Fin 3) ℂ).coeff κ)) ∧
      (groupCohomology.map (realLevelHom (gammaNPAt N σ)) (repMorAt n (gammaNPAt N σ)) 2).hom
          (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNPAt N σ))
            (Submodule.Quotient.mk (cuspCocycle N n σ
              (gramCocycleW (seedCone N n (F (1 * bF G)) Gm s.hh s.hG s.hmod) (rhoR_gammaNP N n) +
                reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF G)) Gm' s'.hh s'.hG s'.hmod)))) =
        (groupCohomology.map (conjP N σ).toMonoidHom (faceMor N n σ) 2).hom
          (complexifyG N n ((gammaNPlaneData N).seedClass (F (1 * bF G)) n Gm s.hh s.hG s.hmod) +
            (groupCohomology.map (epsHom N) (epsRep N n) 2).hom
              (complexifyG N n ((gammaNPlaneData N).seedClass (F (atInfinity UpperHalfPlane.J * bF G)) n Gm'
                s'.hh s'.hG s'.hmod))) := by
  subst hF
  have hfix := spherical_fixed D.cusp I.vector.val I.vector_spherical
  have hh : DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp I.halfWeight I.vector (1 * bF G)) Psi.upperSet :=
    scalar_holomorphic_allBases I D.cohomological _
  have hh' : DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp I.halfWeight I.vector
      (atInfinity UpperHalfPlane.J * bF G)) Psi.upperSet :=
    scalar_holomorphic_allBases I D.cohomological _
  obtain ⟨Gm, -, hG⟩ := exists_moment_primitives _ hh
  obtain ⟨Gm', -, hG'⟩ := exists_moment_primitives _ hh'
  have hmod := fun g z hz => hmod_H_of_bF D.cusp n I.halfWeight I.weight I.vector I.rotation hfix N h3 G hB g z hz
  have hmod' := fun g z hz => hmod_H'_of_bF D.cusp n I.halfWeight I.weight I.vector I.rotation hfix N h3 G hB g z hz
  refine ⟨Gm, Gm', ⟨hh, hG, hmod⟩, ⟨hh', hG', hmod'⟩, ?_, ?_⟩
  · intro y κ
    have := cOmegaCoeff_eq_cocycle N n D _ G Gm Gm' hh hG hmod hh' hG' hmod' y κ
    rw [hσ] at this
    exact this
  · rw [class_transport_cusp N n σ, Submodule.Quotient.mk_add, map_add, map_add, map_add, map_add,
      bridge_gramCocycleW_seed, bridge_reflCocycle]

end TernaryPeriodPolynomials.Argument.FormSeedBridge
