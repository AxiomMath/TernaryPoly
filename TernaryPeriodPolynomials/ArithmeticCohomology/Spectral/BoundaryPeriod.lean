module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryFunctional

@[expose] public section


/-!
# The boundary functional kills level-one cusp-form period classes

The boundary functional `β : H¹(SL₂(ℤ), Sym^d ⊗ det^τ) → ℂ`, `[z] ↦ ℓ(z(T))`, vanishes on the
class of the parity-projected Eichler–Shimura period cocycle of every level-one cusp form, for
every twist and either parity. The cusp-normalized classical cocycle vanishes at `T`, the parity
projection preserves this, and the period cocycle differs from the projection by a coboundary,
on which `ℓ ∘ ev_T` vanishes by `T`-invariance of `ℓ`. The same holds for the restriction to
`SL₂(ℤ)` of the `GL₂(ℤ)` period class, with source and target twists independent.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional

namespace TernaryPeriodPolynomials.Spectral.BoundaryPeriod

/-- **`ℓ` vanishes on the value at `T` of the parity-projected period cocycle**, for every twist
and both parities. -/
theorem ell_modularPeriod_T (d : ℕ) (τ : ℤ) (h : ℤ) (weight_eq : -2 * h = (d : ℤ) + 2)
    (parity : Fin 2) (f : CuspForm levelOne (-2 * h)) :
    ellRep d τ (modularPeriod d τ h weight_eq parity f ModularGroup.T) = 0 := by
  set z := cuspNormalizedBinaryCocycle f d weight_eq τ with hz
  have hT : z ModularGroup.T = 0 := by
    apply cuspNormalizedBinaryCocycle_T
    rw [weight_eq]
    omega
  have hpar : modularCocycleParity d τ parity.val z ModularGroup.T = 0 :=
    modularCocycleParity_T _ _ _ z hT
  have hdecomp : modularPeriod d τ h weight_eq parity f =
      modularCocycleParity d τ parity.val z -
        oneBoundaryCycle (modularBinaryRep d τ)
          (binaryParityComponent d parity.val (classicalBinaryCuspConstant f d)) := by
    rw [modularPeriod_eq, hz, cuspNormalizedBinaryCocycle, map_add, modularCocycleParity_boundary]
    abel
  rw [hdecomp]
  change ellRep d τ (modularCocycleParity d τ parity.val z ModularGroup.T -
    oneBoundaryCycle (modularBinaryRep d τ)
      (binaryParityComponent d parity.val (classicalBinaryCuspConstant f d)) ModularGroup.T) = 0
  have key : ∀ v : modularBinaryRep d τ,
      ellRep d τ (oneBoundaryCycle (modularBinaryRep d τ) v ModularGroup.T) = 0 := fun v => by
    rw [oneBoundaryCycle_apply, map_sub, ell_rho_T, sub_self]
  rw [hpar, zero_sub, map_neg, neg_eq_zero]
  exact key _

/-- **The boundary functional vanishes on every parity-projected period class of `SL₂(ℤ)`.** -/
theorem beta_modularPeriod (d : ℕ) (τ : ℤ) (h : ℤ) (weight_eq : -2 * h = (d : ℤ) + 2)
    (parity : Fin 2) (f : CuspForm levelOne (-2 * h)) :
    beta d τ (groupCohomology.H1π _ (modularPeriod d τ h weight_eq parity f)) = 0 := by
  rw [beta_H1π]
  exact ell_modularPeriod_T d τ h weight_eq parity f

/-- **The boundary functional of target twist `τ` kills the restriction to `SL₂(ℤ)` of the
`GL₂(ℤ)` level-one period class of source twist `σ`.** -/
theorem beta_restriction_levelOnePeriodMap (d : ℕ) (σ τ : ℤ) (h : ℤ)
    (weight_eq : -2 * h = (d : ℤ) + 2) (even : Even d) (parity : Fin 2)
    (sign : (-1 : ℂ) ^ σ = (-1 : ℂ) ^ parity.val) (f : CuspForm levelOne (-2 * h)) :
    beta d τ (restriction d σ τ
      (LevelOneEichlerShimura.levelOnePeriodMap h d weight_eq even σ parity sign f)) = 0 := by
  rw [levelOnePeriodMap_apply, restriction_apply, beta_H1π]
  have hval : (oneCocyclePullback (arithmeticBinaryRep d σ) (modularBinaryRep d τ)
      SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines d σ τ)
      (classicalArithmeticCocycle f d weight_eq even σ parity.val sign)) ModularGroup.T =
      modularPeriod d σ h weight_eq parity f ModularGroup.T :=
    arithmeticParityCocycle_specialLinear d σ even parity.val sign
      (classicalBinaryCocycle f d weight_eq σ) ModularGroup.T
  change ell d ((oneCocyclePullback (arithmeticBinaryRep d σ) (modularBinaryRep d τ)
      SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines d σ τ)
      (classicalArithmeticCocycle f d weight_eq even σ parity.val sign)) ModularGroup.T) = 0
  rw [hval]
  exact ell_modularPeriod_T d σ h weight_eq parity f

end TernaryPeriodPolynomials.Spectral.BoundaryPeriod
