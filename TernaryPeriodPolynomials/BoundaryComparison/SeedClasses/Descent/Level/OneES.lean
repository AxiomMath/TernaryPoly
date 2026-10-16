module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryPeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleReflection

@[expose] public section


/-!
# Eichler--Shimura spanning at level one for `H¹(SL₂(ℤ), Sym^d ⊗ det⁻¹)`

Paper: Lemma C.3
(`ar:lem:seed`), spanning clause, level one.

The library proves the level-one Eichler--Shimura statement as a dimension count
(`ParabolicES`): the classes of `H¹(SL₂(ℤ), Sym^{2r})` killed by the boundary functional `β` are
exactly the sum of the two restricted `GL₂(ℤ)` period images. Here this is turned into the
statement used by the seed lemma: every class of `H¹(SL₂(ℤ), Sym^d ⊗ det⁻¹)` with a
representative that is a coboundary at `T` is a combination of the classes of the classical
period cocycles `c_f` and of their reflections `R c_f` (`es_levelOne_modular`), and for odd `d`
the whole group vanishes (`modularH1_eq_zero_of_odd`). Nothing is assumed: the proof is the
library's, with the dimension identity `dim H¹ = 2 dim S + 1` from Mathlib's level-one dimension
formula.

Formalized by Claude Sonnet 5.5.
-/

open scoped ModularForm MatrixGroups
open GeneralEisenstein Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.BoundaryPeriod
open TernaryPeriodPolynomials.Spectral.IdentityPlaneEven

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section Generic

variable {C X₀ X₁ Y : Type*} [AddCommGroup C] [Module ℂ C] [AddCommGroup X₀] [Module ℂ X₀]
  [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup Y] [Module ℂ Y]

/-- **The kernel of a nonzero functional is the sum of two embedded period images** when the
dimensions match. -/
theorem mem_range_pair_of_finrank [FiniteDimensional ℂ C] [FiniteDimensional ℂ Y]
    (r₀ : X₀ →ₗ[ℂ] Y) (r₁ : X₁ →ₗ[ℂ] Y) (hinj : Function.Injective (r₀.coprod r₁))
    (β : Y →ₗ[ℂ] ℂ) (hβ : β ≠ 0) (per₀ : C →ₗ[ℂ] X₀) (per₁ : C →ₗ[ℂ] X₁)
    (inj₀ : Function.Injective per₀) (inj₁ : Function.Injective per₁)
    (hY : Module.finrank ℂ Y = 2 * Module.finrank ℂ C + 1)
    (hv₀ : ∀ f, β (r₀ (per₀ f)) = 0) (hv₁ : ∀ f, β (r₁ (per₁ f)) = 0) (y : Y) (hy : β y = 0) :
    ∃ f g : C, y = r₀ (per₀ f) + r₁ (per₁ g) := by
  have hsurj : LinearMap.range β = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, β y ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (LinearMap.ext h)
    apply eq_top_iff.mpr
    intro z _
    exact ⟨(z / β y) • y, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]⟩
  have hker : Module.finrank ℂ (LinearMap.ker β) = 2 * Module.finrank ℂ C := by
    have h := LinearMap.finrank_range_add_finrank_ker β
    rw [hsurj, finrank_top, Module.finrank_self, hY] at h
    omega
  let Φ : C × C →ₗ[ℂ] Y := (r₀ ∘ₗ per₀).coprod (r₁ ∘ₗ per₁)
  have hΦ : ∀ v, Φ v ∈ LinearMap.ker β := by
    rintro ⟨f, g⟩
    simp only [Φ, LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.mem_ker, map_add]
    rw [hv₀ f, hv₁ g, add_zero]
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    have h' : (r₀.coprod r₁) (per₀ v.1, per₁ v.2) = (r₀.coprod r₁) (per₀ w.1, per₁ w.2) := by
      simpa [Φ] using hvw
    have := hinj h'
    exact Prod.ext (inj₀ (congrArg Prod.fst this)) (inj₁ (congrArg Prod.snd this))
  have hrange : LinearMap.range Φ ≤ LinearMap.ker β := by
    rintro _ ⟨v, rfl⟩
    exact hΦ v
  have hfin : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ (LinearMap.ker β) := by
    rw [LinearMap.finrank_range_of_inj hΦinj, Module.finrank_prod, hker]
    ring
  have heq := Submodule.eq_of_le_of_finrank_eq hrange hfin
  have hy' : y ∈ LinearMap.range Φ := by
    rw [heq]; exact hy
  obtain ⟨⟨f, g⟩, hfg⟩ := hy'
  refine ⟨f, g, ?_⟩
  simp only [Φ, LinearMap.coprod_apply, LinearMap.comp_apply] at hfg
  exact hfg.symm

end Generic

section LevelOne

/-- The restriction to `SL₂(ℤ)` of the `GL₂(ℤ)` period class, for independent source and target
twists, is the parity projection of the classical cocycle. -/
theorem restriction_levelOnePeriodMap_mixed (d : ℕ) (σ τ : ℤ) (h : ℤ)
    (weight_eq : -2 * h = (d : ℤ) + 2) (even : Even d) (parity : Fin 2)
    (sign : (-1 : ℂ) ^ σ = (-1 : ℂ) ^ parity.val) (f : CuspForm levelOne (-2 * h)) :
    restriction d σ τ (levelOnePeriodMap h d weight_eq even σ parity sign f) =
      groupCohomology.H1π (modularBinaryRep d τ)
        ((2 : ℂ)⁻¹ • (classicalBinaryCocycle f d weight_eq τ +
          (-1 : ℂ) ^ parity.val • modularCocycleReflection d τ
            (classicalBinaryCocycle f d weight_eq τ))) := by
  rw [levelOnePeriodMap_apply, restriction_apply]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep d τ) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro m
  have h1 := arithmeticParityCocycle_specialLinear d σ even parity.val sign
    (classicalBinaryCocycle f d weight_eq σ) m
  exact h1

/-- **Eichler–Shimura spanning at level one, in the library's coordinates.** For even `d > 0`, every
class of `H¹(SL₂(ℤ), Sym^d ⊗ det⁻¹)` with a representative that is a coboundary at `T` is a
combination of the classes of the classical period cocycles `c_f` and their reflections `R c_f`
of level-one cusp forms of weight `d + 2`. -/
theorem es_levelOne_modular (d : ℕ) (hd : Even d) (hpos : 0 < d) (k : ℤ)
    (hk : k = (d : ℤ) + 2) (z : groupCohomology.cocycles₁ (modularBinaryRep d (-1)))
    (hz : ∃ u : modularBinaryRep d (-1),
      z ModularGroup.T = (modularBinaryRep d (-1)).ρ ModularGroup.T u - u) :
    groupCohomology.H1π (modularBinaryRep d (-1)) z ∈ Submodule.span ℂ
      (Set.range (fun f : CuspForm levelOne k =>
          groupCohomology.H1π (modularBinaryRep d (-1)) (classicalBinaryCocycle f d hk (-1))) ∪
        Set.range (fun f : CuspForm levelOne k =>
          groupCohomology.H1π (modularBinaryRep d (-1))
            (modularCocycleReflection d (-1) (classicalBinaryCocycle f d hk (-1))))) := by
  obtain ⟨r, rfl⟩ := hd.two_dvd
  have hr : 0 < r := by omega
  obtain rfl : k = -2 * hw r := hk.trans (weight_eq_r r).symm
  have := modularH1_finiteDimensional (2 * r) (-1)
  have hβ : beta (2 * r) (-1) ≠ 0 := beta_ne_zero (2 * r) (-1) (by omega) (even_two_mul r)
  have hzb : beta (2 * r) (-1) (groupCohomology.H1π (modularBinaryRep (2 * r) (-1)) z) = 0 := by
    obtain ⟨u, hu⟩ := hz
    rw [beta_H1π]
    change ellRep (2 * r) (-1) (z ModularGroup.T) = 0
    rw [hu, map_sub, ell_rho_T, sub_self]
  obtain ⟨f, g, hfg⟩ := mem_range_pair_of_finrank (restriction (2 * r) (-1) (-1))
    (restriction (2 * r) (-1 + 1) (-1)) (restriction_pair_injective (2 * r) (-1))
    (beta (2 * r) (-1)) hβ (per r (-1)) (per r (-1 + 1)) (per_injective r (-1))
    (per_injective r (-1 + 1)) (finrank_modularH1 r hr (-1))
    (fun f => beta_restriction_levelOnePeriodMap (2 * r) (-1) (-1) (hw r) (weight_eq_r r)
      (even_two_mul r) (parityOf (-1)) (parityOf_sign (-1)) f)
    (fun f => beta_restriction_levelOnePeriodMap (2 * r) (-1 + 1) (-1) (hw r) (weight_eq_r r)
      (even_two_mul r) (parityOf (-1 + 1)) (parityOf_sign (-1 + 1)) f) _ hzb
  have hexp : ∀ (c : groupCohomology.cocycles₁ (modularBinaryRep (2 * r) (-1))) (a : ℂ),
      groupCohomology.H1π (modularBinaryRep (2 * r) (-1))
          ((2 : ℂ)⁻¹ • (c + a • modularCocycleReflection (2 * r) (-1) c)) =
        (2 : ℂ)⁻¹ • (groupCohomology.H1π (modularBinaryRep (2 * r) (-1)) c +
          a • groupCohomology.H1π (modularBinaryRep (2 * r) (-1))
            (modularCocycleReflection (2 * r) (-1) c)) := by
    intro c a
    rw [_root_.map_smul, map_add, _root_.map_smul]
  rw [hfg, restriction_levelOnePeriodMap_mixed (2 * r) (-1) (-1) (hw r) (weight_eq_r r)
      (even_two_mul r) (parityOf (-1)) (parityOf_sign (-1)) f,
    restriction_levelOnePeriodMap_mixed (2 * r) (-1 + 1) (-1) (hw r) (weight_eq_r r)
      (even_two_mul r) (parityOf (-1 + 1)) (parityOf_sign (-1 + 1)) g, hexp, hexp]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.subset_span (Or.inl ⟨f, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨f, rfl⟩)))))
    (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨g, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨g, rfl⟩)))))

/-- `H¹(SL₂(ℤ), Sym^d ⊗ det^τ) = 0` for odd `d`: the central element `-1` acts by `-1`. -/
theorem modularH1_eq_zero_of_odd (d : ℕ) (hd : Odd d) (τ : ℤ)
    (x : groupCohomology.H1 (modularBinaryRep d τ)) : x = 0 := by
  have hscalar : SpecialLinearGroup.toGL (-1 : SL(2, ℤ)) =
      GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.coe_scalar]
  refine H1_eq_zero_of_central_neg _ (-1 : SL(2, ℤ)) (fun g => ?_) (fun w => ?_) x
  · ext i j
    simp
  · change (arithmeticBinaryRep d τ).ρ (SpecialLinearGroup.toGL (-1 : SL(2, ℤ))) w = -w
    rw [hscalar]
    exact scalar_neg_one_negates hd τ w

end LevelOne

end TernaryPeriodPolynomials.Argument.SeedC3S4c
