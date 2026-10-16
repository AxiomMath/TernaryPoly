module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.EvenInjectivity
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.EvenPeriodMembership
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.ParabolicIndependence
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.ParabolicSubspace
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.SymmetricDimension
public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodSmul
public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Linear
public import TernaryPeriodPolynomials.Polynomial.RestrictionEquiv

@[expose] public section


/-!
# Corollary 1.4, first conjunct, alternating half: the even-period bijection

For even `n > 0`, `h ↦ normalizedEvenPeriodPart n h` is a linear map from `Forms n` into
`evenPeriodSpace ℂ n` (additivity is proved here from the additivity of the Mellin period
polynomial; homogeneity is `normalizedEvenPeriodPart_smul`). It is injective
(`normalizedEvenPeriodPart_injective`), and `evenPeriodSpace ℂ n` is finite dimensional of
dimension at most `d = dim S_{n+2}`, because the period-class map embeds it into the subspace
`ker β ⊓ E₊` of `H¹(SL₂(ℤ), Sym^n)` (`finrank_ker_beta_inf_eigenspace_one_le`). Hence the map is
bijective, and composing with the alternating restriction equivalence gives the isomorphism with
`alternatingSolutionSpace ℂ n`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TernaryPoly.Paper TernaryPoly.BinaryCuspPeriod

namespace TernaryPeriodPolynomials.Argument.Corollary14

open TernaryPeriodPolynomials.Argument.RouteIndependent

open TernaryPeriodPolynomials.Argument.CuspForms
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.ModularH1
open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem evenPeriod_add' {d : ℕ} (f g : Forms d) :
    evenPeriod (f + g) = evenPeriod f + evenPeriod g := by
  simp only [evenPeriod, period_add, map_add, smul_add]
  module

theorem evenPeriodPart_add {d : ℕ} (f g : Forms d) :
    TernaryPeriodPolynomials.Argument.evenPeriodPart d (f + g) =
      TernaryPeriodPolynomials.Argument.evenPeriodPart d f +
        TernaryPeriodPolynomials.Argument.evenPeriodPart d g := by
  rw [← evenPeriod_eq_evenPeriodPart, ← evenPeriod_eq_evenPeriodPart,
    ← evenPeriod_eq_evenPeriodPart, evenPeriod_add']

theorem normalizedEvenPeriodPart_add {d : ℕ} (f g : Forms d) :
    TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart d (f + g) =
      TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart d f +
        TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart d g := by
  simp only [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart, evenPeriodPart_add,
    map_add]
  ring

/-- The normalized even period map as a linear map into `evenPeriodSpace ℂ n`. -/
noncomputable def evenMap (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Forms n →ₗ[ℂ] evenPeriodSpace ℂ n where
  toFun f := ⟨TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f,
    normalizedEvenPeriodPart_mem_evenPeriodSpace hn0 hn f⟩
  map_add' f g := Subtype.ext (normalizedEvenPeriodPart_add f g)
  map_smul' c f := Subtype.ext (by
    show TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n (c • f) =
      c • TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f
    rw [normalizedEvenPeriodPart_smul, MvPolynomial.smul_eq_C_mul])

theorem evenMap_injective (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Function.Injective (evenMap n hn0 hn) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  exact normalizedEvenPeriodPart_injective hn0 hn f (by
    have := congrArg Subtype.val hf
    simpa [evenMap] using this)

/-- The period-class map restricted to the even period space. -/
noncomputable def evenClassMap (n : ℕ) (hn : Even n) :
    evenPeriodSpace ℂ n →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep n 0) :=
  periodCocycleMap 0 hn ∘ₗ Submodule.inclusion (inf_le_left : evenPeriodSpace ℂ n ≤ periodSpace ℂ n)

theorem evenClassMap_injective (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Function.Injective (evenClassMap n hn) :=
  (periodCocycleMap_injective 0 hn0 hn).comp (Submodule.inclusion_injective _)

theorem range_evenClassMap_le (n : ℕ) (hn : Even n) :
    LinearMap.range (evenClassMap n hn) ≤
      LinearMap.ker (beta n 0) ⊓ Module.End.eigenspace (reflectionH1 n 0) (1 : ℂ) := by
  rintro _ ⟨q, rfl⟩
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact periodCocycleMap_mem_ker_beta 0 hn _
  · rw [Module.End.mem_eigenspace_iff, one_smul]
    have hq : bind₁ (![-X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) ℂ) q.1 - q.1 = 0 := q.2.2
    exact reflectionH1_periodClass 0 hn
      (P := periodSpaceToHomogeneous q.2.1)
      (periodSpaceToHomogeneous_periodRelations q.2.1) (sub_eq_zero.mp hq)

theorem evenPeriodSpace_finiteDimensional (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    FiniteDimensional ℂ (evenPeriodSpace ℂ n) :=
  have := modularH1_finiteDimensional n 0
  Module.Finite.of_injective (evenClassMap n hn) (evenClassMap_injective n hn0 hn)

theorem finrank_evenPeriodSpace_le (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Module.finrank ℂ (evenPeriodSpace ℂ n) ≤ Module.finrank ℂ (Forms n) := by
  have := modularH1_finiteDimensional n 0
  calc Module.finrank ℂ (evenPeriodSpace ℂ n)
      = Module.finrank ℂ (LinearMap.range (evenClassMap n hn)) :=
        (LinearMap.finrank_range_of_inj (evenClassMap_injective n hn0 hn)).symm
    _ ≤ Module.finrank ℂ ↥(LinearMap.ker (beta n 0) ⊓
          Module.End.eigenspace (reflectionH1 n 0) (1 : ℂ)) :=
        Submodule.finrank_mono (range_evenClassMap_le n hn)
    _ ≤ Module.finrank ℂ (Forms n) :=
        finrank_ker_beta_inf_eigenspace_one_le 0 hn0 hn (by simp)

theorem evenMap_bijective (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Function.Bijective (evenMap n hn0 hn) := by
  have := evenPeriodSpace_finiteDimensional n hn0 hn
  have : FiniteDimensional ℂ (Forms n) := inferInstance
  have hle := finrank_evenPeriodSpace_le n hn0 hn
  have hge : Module.finrank ℂ (Forms n) ≤ Module.finrank ℂ (evenPeriodSpace ℂ n) :=
    LinearMap.finrank_le_finrank_of_injective (evenMap_injective n hn0 hn)
  exact ⟨evenMap_injective n hn0 hn,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hge hle)).mp
      (evenMap_injective n hn0 hn)⟩

/-- **Corollary 1.4, first conjunct, alternating half.** -/
noncomputable def evenBijection (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    Forms n ≃ₗ[ℂ] alternatingSolutionSpace ℂ n :=
  (LinearEquiv.ofBijective (evenMap n hn0 hn) (evenMap_bijective n hn0 hn)).trans
    (TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv ℂ n).symm

theorem evenBijection_coe (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) (f : Forms n) :
    ((evenBijection n hn0 hn f : alternatingSolutionSpace ℂ n) : MvPolynomial (Fin 3) ℂ) =
      cyclicLift (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n f) := by
  show (((TernaryPeriodPolynomials.Argument.RouteIndependent.alternatingRestrictionEquiv ℂ n).symm
    (LinearEquiv.ofBijective (evenMap n hn0 hn) (evenMap_bijective n hn0 hn) f) :
      alternatingSolutionSpace ℂ n) : MvPolynomial (Fin 3) ℂ) = _
  rw [alternatingRestrictionEquiv_new_symm_apply]
  rfl

/-- The alternating half of the dimension formula over `ℂ` (all `n`). -/
theorem alternatingSolution_finrank_complex (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    Module.finrank ℂ (alternatingSolutionSpace ℂ n) = Module.finrank ℂ (Forms n) :=
  (evenBijection n hn0 hn).symm.finrank_eq

end TernaryPeriodPolynomials.Argument.Corollary14
