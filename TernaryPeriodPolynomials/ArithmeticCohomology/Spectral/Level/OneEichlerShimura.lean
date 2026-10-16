module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodHeckeKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CocycleLinearity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CommonEigenvector

@[expose] public section


/-!
# Eichler–Shimura at level one: injectivity of the period map on ALL cusp forms

For even `degree` and weight `degree + 2`, the parity-projected period map
`S_{degree+2}(SL₂(ℤ)) → H¹(GL₂(ℤ), Sym^degree ⊗ det^twist)` (the project's
`classicalArithmeticCocycle`, followed by the class map) is injective on Mathlib's whole space of
level-one cusp forms (`levelOnePeriodMap_injective`). The kernel is stable under the Hecke
operators `levelOneHecke` (Sol's `classicalParityPeriod_hecke_kernel`), the Hecke operators commute
(`levelOneHecke_comm`), so a nonzero kernel would contain a common eigenform, whose period is nonzero
(Sol's `classicalArithmeticCocycle_H1_ne_zero`, via the nonvanishing of the Hecke `L`-series).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura

open LevelOneHecke

theorem cuspForm_finiteDimensional_nat (k : ℕ) (hk : Even k) :
    FiniteDimensional ℂ (CuspForm levelOne (k : ℤ)) := by
  have hrank := ModularForm.dimension_level_one k hk
  have hlt : Module.rank ℂ (ModularForm levelOne (k : ℤ)) < Cardinal.aleph0 := by
    rw [hrank]
    exact Cardinal.natCast_lt_aleph0
  have : Module.Finite ℂ (ModularForm levelOne (k : ℤ)) := Module.rank_lt_aleph0_iff.mp hlt
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

theorem cuspForm_finiteDimensional {h : ℤ} {degree : ℕ} (weight_eq : -2 * h = (degree : ℤ) + 2)
    (even : Even degree) : FiniteDimensional ℂ (CuspForm levelOne (-2 * h)) := by
  have hw : -2 * h = ((degree + 2 : ℕ) : ℤ) := by push_cast; exact weight_eq
  rw [hw]
  exact cuspForm_finiteDimensional_nat (degree + 2) (even.add even_two)

variable (h : ℤ) (degree : ℕ) (weight_eq : -2 * h = (degree : ℤ) + 2) (even : Even degree)
  (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val)

/-- The parity-projected Eichler–Shimura period map on level-one cusp forms. -/
def levelOnePeriodMap :
    CuspForm levelOne (-2 * h) →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep degree twist) :=
  (groupCohomology.H1π (arithmeticBinaryRep degree twist)).hom.comp
    (classicalArithmeticCocycleMap (-2 * h) degree weight_eq even twist parity.val sign)

theorem levelOnePeriodMap_apply (f : CuspForm levelOne (-2 * h)) :
    levelOnePeriodMap h degree weight_eq even twist parity sign f =
      groupCohomology.H1π (arithmeticBinaryRep degree twist)
        (classicalArithmeticCocycle f degree weight_eq even twist parity.val sign) := rfl

/-- The Hecke sum is a multiple of the project's `scalarPrimeHecke`. -/
theorem scalarPrimeHecke_eq (p : Nat.Primes) (f : CuspForm levelOne (-2 * h)) :
    scalarPrimeHecke h p f = ((p.val : ℂ) ^ (h + 1) • levelOneHecke (-2 * h) p f : ℍ → ℂ) := by
  funext τ
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  change _ = (p.val : ℂ) ^ (h + 1) * heckeFun (-2 * h) p f τ
  rw [heckeFun_apply]
  simp only [scalarPrimeHecke, LinearMap.coe_mk, AddHom.coe_mk]
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hp, ← _root_.zpow_neg_one,
    ← zpow_add₀ hp, show h + 1 + (-2 * h - 1) = -h by ring, show h + 1 + -1 = h by ring]

/-- The kernel of the period map is stable under every Hecke operator. -/
theorem levelOnePeriodMap_hecke_kernel (p : Nat.Primes) (f : CuspForm levelOne (-2 * h))
    (zero : levelOnePeriodMap h degree weight_eq even twist parity sign f = 0) :
    levelOnePeriodMap h degree weight_eq even twist parity sign (levelOneHecke (-2 * h) p f) = 0 := by
  have hp : (p.val : ℂ) ^ (h + 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  let target : CuspForm levelOne (-2 * h) := (p.val : ℂ) ^ (h + 1) • levelOneHecke (-2 * h) p f
  have htarget : levelOnePeriodMap h degree weight_eq even twist parity sign target = 0 := by
    rw [levelOnePeriodMap_apply, classicalArithmeticCocycle,
      arithmeticParityCocycle_H1_zero_iff] at zero ⊢
    exact classicalParityPeriod_hecke_kernel h f target degree weight_eq even twist parity.val p
      (scalarPrimeHecke_eq h p f).symm zero
  have hlin : levelOnePeriodMap h degree weight_eq even twist parity sign target =
      (p.val : ℂ) ^ (h + 1) •
        levelOnePeriodMap h degree weight_eq even twist parity sign (levelOneHecke (-2 * h) p f) :=
    map_smul _ _ _
  rw [hlin] at htarget
  exact (smul_eq_zero.mp htarget).resolve_left hp

/-- **Eichler–Shimura injectivity at level one.** The parity-projected period map is injective on
the whole space of level-one cusp forms of weight `degree + 2`. -/
theorem levelOnePeriodMap_injective :
    Function.Injective (levelOnePeriodMap h degree weight_eq even twist parity sign) := by
  have := cuspForm_finiteDimensional weight_eq even
  apply LinearMap.ker_eq_bot.mp
  by_contra hne
  set K := LinearMap.ker (levelOnePeriodMap h degree weight_eq even twist parity sign) with hK
  have hstable : ∀ (p : Nat.Primes) (f : CuspForm levelOne (-2 * h)), f ∈ K →
      levelOneHecke (-2 * h) p f ∈ K := fun p f hf =>
    levelOnePeriodMap_hecke_kernel h degree weight_eq even twist parity sign p f hf
  have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hne
  let operators : Nat.Primes → Module.End ℂ K := fun p =>
    (levelOneHecke (-2 * h) p).restrict (hstable p)
  have hcomm : ∀ p q, Commute (operators p) (operators q) := by
    intro p q
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact levelOneHecke_comm (-2 * h) p q f.val
  obtain ⟨v, eigenvalues, hv0, hv⟩ := commuting_family_exists_eigenvector operators hcomm
  have hv0' : v.val ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have heigen : ∀ p, levelOneHecke (-2 * h) p v.val = eigenvalues p • v.val := fun p =>
    congrArg Subtype.val (hv p)
  have relations : HasPrimeHeckeRelations (-2 * h) v.val eigenvalues := by
    intro p τ
    have hτ := congrArg (fun g : CuspForm levelOne (-2 * h) => g τ) (heigen p)
    change heckeFun (-2 * h) p v.val τ = eigenvalues p * v.val τ at hτ
    rw [heckeFun_apply] at hτ
    exact hτ.symm
  exact classicalArithmeticCocycle_H1_ne_zero v.val hv0' eigenvalues relations degree weight_eq even
    twist parity sign v.property

end TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
