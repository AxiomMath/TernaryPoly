module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneESDimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodHeckeKernel

@[expose] public section


/-!
# Hecke operators on `H¹(GL₂(ℤ), Sym^d ⊗ det^τ)` and Hecke-equivariance of the period map

`arithmeticHecke d τ p` is the Hecke operator of `GL₂(ℤ) diag(p,1) GL₂(ℤ)` on
`H¹(GL₂(ℤ), Sym^d ⊗ det^τ)` (the generic coset formula `HeckeH1.heckeH1` with the `p + 1` cosets of
`LevelOneCosets`), and `modularHecke d τ p` the one of `SL₂(ℤ)`. Restriction to `SL₂(ℤ)` intertwines
them (`restriction_arithmeticHecke`). The classical Hecke operator on level-one cusp forms and the
cohomological one correspond under the parity-projected Eichler–Shimura period map:
`levelOnePeriodMap (T_p f) = p^τ • arithmeticHecke p (levelOnePeriodMap f)`
(`levelOnePeriodMap_hecke`). The analytic input is the Sol port's comparison of the Hecke trace of
the period primitive (`classicalHeckeParityPrimitive_comparison`); the trace is a primitive of the
cohomological Hecke cocycle by `HeckeH1.heckeFun_primitive`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension

namespace TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1

variable (d : ℕ) (τ : ℤ) (p : Nat.Primes)

/-- The coefficient representation of `GL₂(ℚ)` on the carrier of `arithmeticBinaryRep d τ`. -/
abbrev rationalRho : Representation ℂ (GL (Fin 2) ℚ) (arithmeticBinaryRep d τ) :=
  (rationalBinaryRep d τ).ρ

/-- The same representation on the carrier of `modularBinaryRep d τ`. -/
abbrev modularRho : Representation ℂ (GL (Fin 2) ℚ) (modularBinaryRep d τ) :=
  (rationalBinaryRep d τ).ρ

theorem arithmetic_compat (g : GL (Fin 2) ℤ) :
    (arithmeticBinaryRep d τ).ρ g = rationalRho d τ (integralEmbed g) := by
  apply LinearMap.ext
  intro P
  exact (rationalBinaryRep_integral d τ g P).symm

theorem modular_compat (σ : SL(2, ℤ)) :
    (modularBinaryRep d τ).ρ σ = modularRho d τ (modularEmbed σ) :=
  arithmetic_compat d τ (SpecialLinearGroup.toGL σ)

/-- **The Hecke operator `T_p` on `H¹(GL₂(ℤ), Sym^d ⊗ det^τ)`.** -/
def arithmeticHecke : Module.End ℂ (groupCohomology.H1 (arithmeticBinaryRep d τ)) :=
  heckeH1 (arithmeticCosets p) (arithmeticBinaryRep d τ) (rationalRho d τ) (arithmetic_compat d τ)
    integralEmbed_injective

/-- The Hecke operator `T_p` on `H¹(SL₂(ℤ), Sym^d ⊗ det^τ)`. -/
def modularHecke : Module.End ℂ (groupCohomology.H1 (modularBinaryRep d τ)) :=
  heckeH1 (modularCosets p) (modularBinaryRep d τ) (modularRho d τ) (modular_compat d τ)
    modularEmbed_injective

/-- The cocycle restriction `GL₂(ℤ) → SL₂(ℤ)`. -/
abbrev restrictCocycle :
    groupCohomology.cocycles₁ (arithmeticBinaryRep d τ) →ₗ[ℂ]
      groupCohomology.cocycles₁ (modularBinaryRep d τ) :=
  oneCocyclePullback (arithmeticBinaryRep d τ) (modularBinaryRep d τ) SpecialLinearGroup.toGL
    LinearMap.id (restriction_intertwines d τ τ)

theorem restrictCocycle_hecke (z : groupCohomology.cocycles₁ (arithmeticBinaryRep d τ)) :
    restrictCocycle d τ (heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep d τ) (rationalRho d τ)
        (arithmetic_compat d τ) integralEmbed_injective z) =
      heckeCocycle (modularCosets p) (modularBinaryRep d τ) (modularRho d τ) (modular_compat d τ)
        modularEmbed_injective (restrictCocycle d τ z) := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  change ∑ j, rationalRho d τ (binaryHeckeRepresentative p j)⁻¹
      (z (arithmeticDelta p (SpecialLinearGroup.toGL σ) j)) =
    ∑ j, modularRho d τ (binaryHeckeRepresentative p j)⁻¹
      (z (SpecialLinearGroup.toGL (modularDelta p σ j)))
  simp only [toGL_modularDelta]
  rfl

/-- **Restriction to `SL₂(ℤ)` intertwines the Hecke operators.** -/
theorem restriction_arithmeticHecke (x : groupCohomology.H1 (arithmeticBinaryRep d τ)) :
    restriction d τ τ (arithmeticHecke d τ p x) = modularHecke d τ p (restriction d τ τ x) := by
  obtain ⟨z, rfl⟩ := H1π_surjective (arithmeticBinaryRep d τ) x
  have h1 := heckeH1_H1π (arithmeticCosets p) (arithmeticBinaryRep d τ) (rationalRho d τ)
    (arithmetic_compat d τ) integralEmbed_injective z
  have h2 := heckeH1_H1π (modularCosets p) (modularBinaryRep d τ) (modularRho d τ)
    (modular_compat d τ) modularEmbed_injective (restrictCocycle d τ z)
  have h3 := restriction_apply d τ τ z
  have h4 := restriction_apply d τ τ (heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep d τ)
    (rationalRho d τ) (arithmetic_compat d τ) integralEmbed_injective z)
  change restriction d τ τ (heckeH1 (arithmeticCosets p) (arithmeticBinaryRep d τ) (rationalRho d τ)
    (arithmetic_compat d τ) integralEmbed_injective _) = heckeH1 (modularCosets p) (modularBinaryRep d τ)
      (modularRho d τ) (modular_compat d τ) modularEmbed_injective _
  rw [h1, h4, h3, h2, restrictCocycle_hecke]

section Period

variable (h : ℤ) (weight_eq : -2 * h = (d : ℤ) + 2) (even : Even d) (parity : Fin 2)
  (sign : (-1 : ℂ) ^ τ = (-1 : ℂ) ^ parity.val)

/-- The parity-projected period cocycle map on `SL₂(ℤ)`. -/
def modularPeriodMap :
    CuspForm levelOne (-2 * h) →ₗ[ℂ] groupCohomology.cocycles₁ (modularBinaryRep d τ) :=
  (modularCocycleParity d τ parity.val).comp (classicalBinaryCocycleMap (-2 * h) d weight_eq τ)

/-- The parity-projected period cocycle on `SL₂(ℤ)`. -/
abbrev modularPeriod (f : CuspForm levelOne (-2 * h)) :
    groupCohomology.cocycles₁ (modularBinaryRep d τ) :=
  modularPeriodMap d τ h weight_eq parity f

theorem modularPeriod_eq (f : CuspForm levelOne (-2 * h)) :
    modularPeriod d τ h weight_eq parity f =
      modularCocycleParity d τ parity.val (classicalBinaryCocycle f d weight_eq τ) := rfl

/-- A polynomial as a vector of `modularBinaryRep d τ`. -/
abbrev toModular (P : Binary.HomogeneousPoly d) : modularBinaryRep d τ := P

theorem toModular_zero : toModular d τ 0 = 0 := rfl

theorem real_map_modularEmbed (σ : SL(2, ℤ)) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (modularEmbed σ) = SpecialLinearGroup.mapGL ℝ σ :=
  map_toGL_eq_mapGL σ

/-- The parity primitive is a primitive of the parity-projected period cocycle. -/
theorem modularPeriod_primitive (f : CuspForm levelOne (-2 * h)) (σ : SL(2, ℤ)) (z : ℍ) :
    modularPeriod d τ h weight_eq parity f σ =
      toModular d τ (classicalParityPrimitive f d parity.val
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (modularEmbed σ) • z : ℍ) : ℂ)) -
        (modularBinaryRep d τ).ρ σ (toModular d τ (classicalParityPrimitive f d parity.val z)) := by
  rw [real_map_modularEmbed, modularPeriod_eq]
  have hmod := classicalParityPrimitive_modular f d weight_eq τ parity.val σ z
  have hcoc := classicalParityPrimitive_cocycle f d weight_eq τ parity.val σ
  rw [hcoc] at hmod
  rw [← hmod]
  exact (sub_sub_cancel _ _).symm

theorem coe_I : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := rfl

include even in
/-- **Hecke-equivariance of the period map on `SL₂(ℤ)`**, at the level of classes. -/
theorem modularHecke_period (f target : CuspForm levelOne (-2 * h))
    (transformed : (target : ℍ → ℂ) = scalarPrimeHecke h p f) :
    modularHecke d τ p (groupCohomology.H1π _ (modularPeriod d τ h weight_eq parity f)) =
      ((p.val : ℂ) ^ (-h - 1 - τ)) •
        groupCohomology.H1π _ (modularPeriod d τ h weight_eq parity target) := by
  rw [modularHecke, heckeH1_H1π, ← map_smul]
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  let F : ℍ → modularBinaryRep d τ := fun z => toModular d τ (classicalParityPrimitive f d parity.val z)
  let C : modularBinaryRep d τ :=
    toModular d τ (classicalHeckeParityPrimitive f d τ parity.val p Complex.I)
  have hprim := heckeFun_primitive (modularCosets p) (modularBinaryRep d τ) (modularRho d τ)
    (modular_compat d τ) (GeneralLinearGroup.map (algebraMap ℚ ℝ))
    (modularPeriod d τ h weight_eq parity f) F (modularPeriod_primitive d τ h weight_eq parity f)
  have htrace : ∀ z : ℍ, traceFunction (modularCosets p) (modularBinaryRep d τ) (modularRho d τ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ)) F z =
        ((p.val : ℂ) ^ (-h - 1 - τ)) • toModular d τ (classicalParityPrimitive target d parity.val z) +
          C := by
    intro z
    have hcomp := classicalHeckeParityPrimitive_comparison h f target d weight_eq even τ parity.val p
      transformed z z.im_pos
    have heq := classicalHeckeParityPrimitive_eq_trace f d τ parity.val p z
    exact heq.symm.trans (sub_eq_iff_eq_add.mp hcomp)
  refine ⟨-C, ?_⟩
  funext σ
  rw [groupCohomology.d₀₁_hom_apply]
  change _ = heckeFun (modularCosets p) (modularBinaryRep d τ) (modularRho d τ)
      (modularPeriod d τ h weight_eq parity f) σ -
    ((p.val : ℂ) ^ (-h - 1 - τ)) • modularPeriod d τ h weight_eq parity target σ
  rw [hprim σ UpperHalfPlane.I, htrace, htrace, real_map_modularEmbed, modularPeriod_eq,
    ← classicalParityPrimitive_cocycle target d weight_eq τ parity.val σ, coe_I,
    classicalParityPrimitive_basepoint, toModular_zero, smul_zero, zero_add, map_neg]
  abel

/-- The restriction of the `GL₂(ℤ)` period class is the `SL₂(ℤ)` period class. -/
theorem restriction_levelOnePeriodMap (f : CuspForm levelOne (-2 * h)) :
    restriction d τ τ (levelOnePeriodMap h d weight_eq even τ parity sign f) =
      groupCohomology.H1π _ (modularPeriod d τ h weight_eq parity f) := by
  rw [levelOnePeriodMap_apply, restriction_apply]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep d τ) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro σ
  change (classicalArithmeticCocycle f d weight_eq even τ parity.val sign)
      (SpecialLinearGroup.toGL σ) =
    modularCocycleParity d τ parity.val (classicalBinaryCocycle f d weight_eq τ) σ
  exact arithmeticParityCocycle_specialLinear d τ even parity.val sign _ σ

theorem modularPeriod_smul (a : ℂ) (f : CuspForm levelOne (-2 * h)) :
    modularPeriod d τ h weight_eq parity (a • f) = a • modularPeriod d τ h weight_eq parity f :=
  map_smul _ a f

/-- **Hecke-equivariance of the level-one Eichler–Shimura period map.** -/
theorem levelOnePeriodMap_hecke (f : CuspForm levelOne (-2 * h)) :
    levelOnePeriodMap h d weight_eq even τ parity sign (levelOneHecke (-2 * h) p f) =
      ((p.val : ℂ) ^ τ) • arithmeticHecke d τ p (levelOnePeriodMap h d weight_eq even τ parity sign f) := by
  apply restriction_injective d τ τ
  rw [map_smul, restriction_arithmeticHecke, restriction_levelOnePeriodMap,
    restriction_levelOnePeriodMap,
    modularHecke_period d τ p h weight_eq even parity f (((p.val : ℂ) ^ (h + 1)) • levelOneHecke (-2 * h) p f)
      (by rw [FunLike.coe_smul]; exact (scalarPrimeHecke_eq h p f).symm),
    modularPeriod_smul, map_smul, smul_smul, smul_smul]
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [← zpow_add₀ hp, ← zpow_add₀ hp, show τ + (-h - 1 - τ) + (h + 1) = 0 by ring, zpow_zero,
    one_smul]

end Period

end TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
