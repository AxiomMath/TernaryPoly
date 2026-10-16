module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteAverageCommutation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalPrimeHecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (first second : Nat.Primes) :
    Commute (cuspClassicalPrimeHecke cusp central_positive halfWeight first)
      (cuspClassicalPrimeHecke cusp central_positive halfWeight second) := by
  change _ = _
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  exact cuspPrimeHeckeSum_commute cusp first second vector.val vector.property.1

theorem cuspClassicalSubmodule_exists_eigenform (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (space : Submodule ℂ (cuspClassicalVectors cusp halfWeight))
    (nonzero : space ≠ ⊥)
    (stable : ∀ (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight), vector ∈ space →
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector ∈ space) :
    ∃ (vector : cuspClassicalVectors cusp halfWeight)
      (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
      (eigenvalues : Nat.Primes → ℂ),
      vector ∈ space ∧ vector.val ≠ 0 ∧ form ≠ 0 ∧
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 vector.val ∧
      HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues ∧
      ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector.val =
        ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector.val := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  let : Nontrivial space := Submodule.nontrivial_iff_ne_bot.mpr nonzero
  let operators (prime : Nat.Primes) : Module.End ℂ space :=
    (cuspClassicalPrimeHecke cusp central_positive halfWeight prime).restrict (stable prime)
  have commutes (first second : Nat.Primes) : Commute (operators first) (operators second) := by
    change _ = _
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    exact DFunLike.congr_fun (cuspClassicalPrimeHecke_commute cusp central_positive halfWeight first second).eq vector.val
  obtain ⟨eigenvector, eigenvalues, vector_nonzero, action⟩ :=
    commuting_family_exists_eigenvector (V := space) (ι := Nat.Primes) operators commutes
  have eigen (prime : Nat.Primes) : cuspPrimeHeckeSum cusp prime eigenvector.val.val =
      eigenvalues prime • eigenvector.val.val := congrArg (fun vector : space => vector.val.val) (action prime)
  let function : cuspClassicalScalarImage cusp halfWeight :=
    ⟨cuspScalarWeightedLinear cusp halfWeight 1 eigenvector.val.val,
      (cuspClassicalScalarImage_mem cusp halfWeight _).mpr ⟨_, eigenvector.val.property, rfl⟩⟩
  let form := cuspScalarImageForm cusp halfWeight negative function
  have form_eq : (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear cusp halfWeight 1 eigenvector.val.val :=
    cuspScalarImageForm_coe cusp halfWeight negative function
  have relations : HasPrimeHeckeRelations (-2 * halfWeight) form
      (fun prime => (prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalues prime) := by
    rw [form_eq]
    apply scalarPrimeHecke_eigen_relations
    intro prime
    rw [← cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight prime _ eigenvector.val.property.2.1,
      eigen, map_smul]
  refine ⟨eigenvector.val, form, _, eigenvector.property,
    (fun zero => vector_nonzero (Subtype.ext (Subtype.ext zero))), ?_, form_eq, relations, ?_⟩
  · intro zero
    apply vector_nonzero
    apply Subtype.ext
    apply cuspClassicalScalarMap_injective cusp central_positive halfWeight
    change cuspScalarWeightedLinear cusp halfWeight 1 eigenvector.val.val =
      cuspScalarWeightedLinear cusp halfWeight 1 0
    rw [← form_eq, zero, map_zero]
    rfl
  · intro prime
    apply cuspClassicalVector_hecke_eigen cusp central_positive halfWeight _ eigenvector.val.property
    rwa [← form_eq]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
