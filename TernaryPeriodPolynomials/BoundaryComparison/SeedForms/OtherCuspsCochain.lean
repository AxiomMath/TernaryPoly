module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.AntiHolomorphic

@[expose] public section


/-!
# `g5_levelOne` at the other plane cusps: the cochain identity at an arbitrary adelic matrix

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (`ar:lem:seed`) at the plane cusps `h⁻¹ P h` ("rationally conjugate the other plane cusps to `P`").

* `cOmegaCoeff_eq_cocycle`: for `g : AdelicGL` and scalar functions `H_g = F(1·b_F g)`, `H'_g = F(J·b_F g)` with the seed hypotheses of `Γ_P`, the model's plane integral cochain is
  `K_g · coeff_κ (ρ(g_∞⁻¹) C(g_∞ y))` with `C = c_{H_g} + ε-transport c_{H'_g}` (cocycle of `realLevel Γ_P`).
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument
  TernaryPeriodPolynomials.Argument.LevelTransfer GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction

variable (N n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)

/-- **R1c at an arbitrary adelic matrix `g`** (cochain level): the model's plane integral cochain at `g` is `K_g` times the coefficient of
`ρ(g_∞⁻¹) C(g_∞ y)`, `C = c_{H_g} + ε-transport c_{H'_g}`, `H_g = F(1·b_F g)`, `H'_g = F(J·b_F g)`, for scalar functions with the seed hypotheses of `Γ_P`. -/
theorem cOmegaCoeff_eq_cocycle (Gm Gm' : ℕ → ℂ → ℂ)
    (hh : DifferentiableOn ℂ (F (1 * bF g)) Psi.upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (F (1 * bF g) z * z ^ j) z)
    (hmod : ∀ γ : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (1 * bF g) (mob ((gammaNPlaneData N).lam γ) z) =
        dnm ((gammaNPlaneData N).lam γ) z ^ (n + 3) * F (1 * bF g) z)
    (hh' : DifferentiableOn ℂ (F (atInfinity UpperHalfPlane.J * bF g)) Psi.upperSet)
    (hG' : ∀ j z, 0 < z.im → HasDerivAt (Gm' j) (F (atInfinity UpperHalfPlane.J * bF g) z * z ^ j) z)
    (hmod' : ∀ γ : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (atInfinity UpperHalfPlane.J * bF g) (mob ((gammaNPlaneData N).lam γ) z) =
        dnm ((gammaNPlaneData N).lam γ) z ^ (n + 3) * F (atInfinity UpperHalfPlane.J * bF g) z)
    (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeff n D F y g κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D g) *
        ((realCoefficient n (realGroup g)⁻¹
          ((gramCocycleW (seedCone N n (F (1 * bF g)) Gm hh hG hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF g)) Gm' hh' hG' hmod').val.val
              (fun i => realGroup g * y i) : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ).coeff κ) := by
  rw [cOmegaCoeff_eq]
  congr 1
  have e1 := coeff_rho_gramCochainW_seed N n (F (1 * bF g)) Gm hh hG hmod (realGroup g) y κ
  have e2 := coeff_rho_gramCochainW_seed N n (F (atInfinity UpperHalfPlane.J * bF g)) Gm' hh' hG' hmod'
    (epsJ * realGroup g) y κ
  rw [← e1]
  have e3 : planeIntG n (F (atInfinity UpperHalfPlane.J * bF g)) (epsJ.val * (realGroup g).val)
      (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ =
      planeIntG n (F (atInfinity UpperHalfPlane.J * bF g)) (epsJ * realGroup g).val
        (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ := by rw [Units.val_mul]
  rw [e3, ← e2]
  have e4 := reflCocycle_apply' N n (F (atInfinity UpperHalfPlane.J * bF g)) Gm' hh' hG' hmod' (fun i => realGroup g * y i)
  obtain ⟨S1, hS1⟩ : ∃ S1 : HomogeneousPoly n, S1 = gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
      (seedCone N n (F (1 * bF g)) Gm hh hG hmod) (fun i => realGroup g * y i) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2 : HomogeneousPoly n, S2 = (reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF g)) Gm' hh' hG' hmod').val.val
        (fun i => realGroup g * y i) := ⟨_, rfl⟩
  have hsum : ((gramCocycleW (seedCone N n (F (1 * bF g)) Gm hh hG hmod) (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF g)) Gm' hh' hG' hmod').val.val
              (fun i => realGroup g * y i) : HomogeneousPoly n) = S1 + S2 := by
    rw [hS1, hS2]; rfl
  rw [hsum, map_add, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  have hfun : (fun i => epsJ * realGroup g * y i) = (fun i => epsJ * (realGroup g * y i)) :=
    funext fun i => mul_assoc _ _ _
  rw [hS1, hS2, e4, hfun, _root_.mul_inv_rev, map_mul]
  rfl

end TernaryPeriodPolynomials.Argument.FormSeedBridge
