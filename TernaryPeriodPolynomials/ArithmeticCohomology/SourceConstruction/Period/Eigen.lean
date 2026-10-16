module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.SubmoduleEigenvector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.ImageEigenform

@[expose] public section


/-!
# A holomorphic Hecke eigenvector as an Eichler input

A cohomological spherical cuspidal representation carries a spherical holomorphic lowest-weight
vector, and the prime Hecke operators preserve the Hilbert-holomorphic spherical weight vectors
(they are finite sums of finite translates, and finite translation preserves holomorphy of the orbit).
Running the simultaneous eigenvector extraction inside this Hecke-stable subspace gives a simultaneous
eigenvector which is again an input of the Eichler construction.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Holomorphy of the weighted affine orbit of a Hilbert vector. -/
abbrev HolomorphicOrbit (σ : CuspidalRepresentation) (halfWeight : ℤ) (x : σ.H) : Prop :=
  DifferentiableOn ℂ (cuspWeightedAffineOrbit σ halfWeight x) UpperHalfPlane.upperHalfPlaneSet

theorem period_real_smul_comm {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (r : ℝ) (c : ℂ) (x : E) : r • c • x = c • r • x := by
  rw [real_smul_eq_coe, real_smul_eq_coe]
  exact smul_comm _ _ _

section Orbit

variable (σ : CuspidalRepresentation) (halfWeight : ℤ)

theorem holomorphicOrbit_zero : HolomorphicOrbit σ halfWeight 0 := by
  have orbit : cuspWeightedAffineOrbit σ halfWeight (0 : σ.H) = fun _ => 0 := by
    funext z
    simp [cuspWeightedAffineOrbit, cuspAffineOrbitVector]
  unfold HolomorphicOrbit
  rw [orbit]
  exact differentiableOn_const _

theorem holomorphicOrbit_add {x y : σ.H} (hx : HolomorphicOrbit σ halfWeight x)
    (hy : HolomorphicOrbit σ halfWeight y) : HolomorphicOrbit σ halfWeight (x + y) := by
  have orbit : cuspWeightedAffineOrbit σ halfWeight (x + y) = fun z =>
      cuspWeightedAffineOrbit σ halfWeight x z + cuspWeightedAffineOrbit σ halfWeight y z := by
    funext z
    simp only [cuspWeightedAffineOrbit, cuspAffineOrbitVector, map_add, smul_add]
  unfold HolomorphicOrbit
  rw [orbit]
  exact DifferentiableOn.add hx hy

theorem holomorphicOrbit_smul (c : ℂ) {x : σ.H} (hx : HolomorphicOrbit σ halfWeight x) :
    HolomorphicOrbit σ halfWeight (c • x) := by
  have orbit : cuspWeightedAffineOrbit σ halfWeight (c • x) = fun z =>
      c • cuspWeightedAffineOrbit σ halfWeight x z := by
    funext z
    simp only [cuspWeightedAffineOrbit, cuspAffineOrbitVector, map_smul]
    exact period_real_smul_comm _ _ _
  unfold HolomorphicOrbit
  rw [orbit]
  exact DifferentiableOn.const_smul hx c

theorem holomorphicOrbit_sum {ι : Type*} (s : Finset ι) (x : ι → σ.H)
    (hx : ∀ i ∈ s, HolomorphicOrbit σ halfWeight (x i)) :
    HolomorphicOrbit σ halfWeight (∑ i ∈ s, x i) := by
  have orbit : cuspWeightedAffineOrbit σ halfWeight (∑ i ∈ s, x i) = fun z =>
      ∑ i ∈ s, cuspWeightedAffineOrbit σ halfWeight (x i) z := by
    funext z
    simp only [cuspWeightedAffineOrbit, cuspAffineOrbitVector, map_sum, Finset.smul_sum]
  unfold HolomorphicOrbit
  rw [orbit]
  exact DifferentiableOn.fun_sum hx

/-- Finite translation preserves holomorphy of the orbit. -/
theorem holomorphicOrbit_slash (m : BinaryRationalGL) (u : σ.smooth)
    (hu : HolomorphicOrbit σ halfWeight u.val) :
    HolomorphicOrbit σ halfWeight (cuspFiniteRationalSlash σ m u).val :=
  cuspWeightedAffineOrbit_finite_holomorphic σ halfWeight u.val
    (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) m⁻¹) hu

/-- The classical vectors whose Hilbert-valued weighted orbit is holomorphic. -/
def holomorphicClassicalSpace : Submodule ℂ (cuspClassicalVectors σ halfWeight) where
  carrier := {v | HolomorphicOrbit σ halfWeight v.val.val}
  zero_mem' := by
    show HolomorphicOrbit σ halfWeight (0 : σ.H)
    exact holomorphicOrbit_zero σ halfWeight
  add_mem' := by
    intro x y hx hy
    show HolomorphicOrbit σ halfWeight (x.val.val + y.val.val)
    exact holomorphicOrbit_add σ halfWeight hx hy
  smul_mem' := by
    intro c x hx
    show HolomorphicOrbit σ halfWeight (c • x.val.val)
    exact holomorphicOrbit_smul σ halfWeight c hx

/-- The prime Hecke operators preserve the holomorphic classical vectors. -/
theorem holomorphicClassicalSpace_stable
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (prime : Nat.Primes) (v : cuspClassicalVectors σ halfWeight)
    (hv : v ∈ holomorphicClassicalSpace σ halfWeight) :
    cuspClassicalPrimeHecke σ central_positive halfWeight prime v ∈
      holomorphicClassicalSpace σ halfWeight := by
  have hu : HolomorphicOrbit σ halfWeight v.val.val := hv
  show HolomorphicOrbit σ halfWeight ((cuspPrimeHeckeSum σ prime v.val).val)
  rw [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
    Submodule.coe_sum]
  exact holomorphicOrbit_add σ halfWeight (holomorphicOrbit_slash σ halfWeight _ v.val hu)
    (holomorphicOrbit_sum σ halfWeight _ _ fun _ _ => holomorphicOrbit_slash σ halfWeight _ v.val hu)

end Orbit

/-- **A Hecke eigenform among the Eichler inputs.**  A spherical cuspidal representation with a
nonzero cohomology class of odd degree has an Eichler input whose scalar weighted realization is a
nonzero level one cusp form with prime Hecke eigenrelations. -/
theorem exists_eichlerInput_eigenform (σ : CuspidalRepresentation) (spherical : SphericalCusp σ)
    {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n) :
    ∃ (I : EichlerInput σ n)
      (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
        (-2 * I.halfWeight))
      (eigenvalues : Nat.Primes → ℂ),
      form ≠ 0 ∧
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector ∧
      HasPrimeHeckeRelations (-2 * I.halfWeight) form eigenvalues := by
  obtain ⟨halfWeight, vector, weight, nonzero, fixed, rotation, _, holomorphic⟩ :=
    cohomological_exists_spherical_holomorphic σ spherical odd cohomological
  have central_positive := cohomological_centralCharacter_positive σ cohomological
  have negative : halfWeight < 0 := by omega
  have scalar_holomorphic := cuspScalarWeightedRealization_holomorphic σ halfWeight vector fixed
    rotation holomorphic 1
  have classical : vector ∈ cuspClassicalVectors σ halfWeight :=
    cuspClassicalVectors_mem_of_holomorphic σ halfWeight vector fixed rotation scalar_holomorphic
  have nonzero_space : holomorphicClassicalSpace σ halfWeight ≠ ⊥ := by
    intro bottom
    have member : (⟨vector, classical⟩ : cuspClassicalVectors σ halfWeight) ∈
        holomorphicClassicalSpace σ halfWeight := holomorphic
    rw [bottom, Submodule.mem_bot] at member
    exact nonzero (congrArg Subtype.val member)
  obtain ⟨eigenvector, form, eigenvalues, member, eigen_ne, form_ne, form_eq, relations, _⟩ :=
    cuspClassicalSubmodule_exists_eigenform σ central_positive halfWeight negative
      (holomorphicClassicalSpace σ halfWeight) nonzero_space
      (fun prime u member =>
        holomorphicClassicalSpace_stable σ halfWeight central_positive prime u member)
  exact ⟨{ central_positive := central_positive
           halfWeight := halfWeight
           weight := weight
           vector := eigenvector.val
           vector_ne := eigen_ne
           vector_spherical := eigenvector.property.1
           rotation := eigenvector.property.2.1
           holomorphic := member }, form, eigenvalues, form_ne, form_eq, relations⟩

end TernaryPeriodPolynomials.SourceConstruction

end
