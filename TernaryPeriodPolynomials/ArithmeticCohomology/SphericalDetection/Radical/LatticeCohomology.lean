module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticePairs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem exp_boundary_iff_inst_irrel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i₁ i₂ : Module ℚ (Module.End ℂ V)) (g h : Module.End ℂ V) (c₁ c₂ : V) (R : Prop)
    (iff : (∃ potential : V, c₁ = (@IsNilpotent.exp _ _ i₁ g - 1) potential ∧
      c₂ = (@IsNilpotent.exp _ _ i₁ h - 1) potential) ↔ R) :
    (∃ potential : V, c₁ = (@IsNilpotent.exp _ _ i₂ g - 1) potential ∧
      c₂ = (@IsNilpotent.exp _ _ i₂ h - 1) potential) ↔ R := by
  cases Subsingleton.elim i₁ i₂
  exact iff

theorem commonScalar_boundary_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (first second : Module.End ℂ V) (scalar : ℂ) (nonzero : scalar ≠ 0) (alpha beta : V) :
    (∃ potential : V, alpha = (scalar • first) potential ∧ beta = (scalar • second) potential) ↔
      ∃ potential : V, alpha = first potential ∧ beta = second potential := by
  constructor
  · rintro ⟨potential, first_eq, second_eq⟩
    refine ⟨scalar • potential, ?_, ?_⟩
    · rw [map_smul]
      exact first_eq
    · rw [map_smul]
      exact second_eq
  · rintro ⟨potential, first_eq, second_eq⟩
    refine ⟨scalar⁻¹ • potential, ?_, ?_⟩
    · rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ nonzero, one_smul]
      exact first_eq
    · rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ nonzero, one_smul]
      exact second_eq

theorem upperRadicalCocycle_H1_zero_iff_generators {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    groupCohomology.H1π (upperRadicalLatticeRep degree) cycle = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        upperRadicalCocyclePair degree cycle 0 = upperRadicalGenerator degree 0 potential ∧
        upperRadicalCocyclePair degree cycle 1 = upperRadicalGenerator degree 1 potential := by
  rw [oneCocycle_H1_zero_iff_generator_boundaries (upperRadicalLatticeRep degree) cycle
    radicalLatticeFirst radicalLatticeSecond radicalLattice_generated,
    upperRadicalLatticeRep_first, upperRadicalLatticeRep_second]
  have first := upperRadicalCocyclePair_average cycle (0 : Fin 2)
  have second := upperRadicalCocyclePair_average cycle (1 : Fin 2)
  change _ = cycle radicalLatticeFirst at first
  change _ = cycle radicalLatticeSecond at second
  rw [← first, ← second]
  exact exp_boundary_iff_inst_irrel _ _ _ _ _ _ _ (nilpotent_difference_pair_boundary_iff _ _ degree degree
    (upperRadicalGenerator_power_zero degree 0) (upperRadicalGenerator_power_zero degree 1) _ _)

theorem lowerRadicalCocycle_H1_zero_iff_generators {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    groupCohomology.H1π (lowerRadicalLatticeRep degree) cycle = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        lowerRadicalCocyclePair degree cycle 0 = lowerRadicalGenerator degree 0 potential ∧
        lowerRadicalCocyclePair degree cycle 1 = lowerRadicalGenerator degree 1 potential := by
  rw [oneCocycle_H1_zero_iff_generator_boundaries (lowerRadicalLatticeRep degree) cycle
    radicalLatticeFirst radicalLatticeSecond radicalLattice_generated,
    lowerRadicalLatticeRep_first, lowerRadicalLatticeRep_second]
  have first := lowerRadicalCocyclePair_average cycle (0 : Fin 2)
  have second := lowerRadicalCocyclePair_average cycle (1 : Fin 2)
  change _ = cycle radicalLatticeFirst at first
  change _ = cycle radicalLatticeSecond at second
  rw [← first, ← second]
  exact exp_boundary_iff_inst_irrel _ _ _ _ _ _ _ (nilpotent_difference_pair_boundary_iff _ _ degree degree
    (lowerRadicalGenerator_power_zero degree 0) (lowerRadicalGenerator_power_zero degree 1) _ _)

theorem upperRadicalCocycle_H1_zero_iff_polynomial_boundary {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    groupCohomology.H1π (upperRadicalLatticeRep degree) cycle = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        (upperRadicalCocyclePair degree cycle 0).val = X 2 * pderiv 0 potential.val ∧
        (upperRadicalCocyclePair degree cycle 1).val = X 2 * pderiv 1 potential.val := by
  rw [upperRadicalCocycle_H1_zero_iff_generators]
  change (∃ potential : HomogeneousPoly degree,
    upperRadicalCocyclePair degree cycle 0 = ((-1 : ℂ) • homogeneousShearDerivation degree 0 2) potential ∧
    upperRadicalCocyclePair degree cycle 1 = ((-1 : ℂ) • homogeneousShearDerivation degree 1 2) potential) ↔ _
  rw [commonScalar_boundary_iff _ _ (-1) (by norm_num)]
  constructor
  · rintro ⟨potential, first_eq, second_eq⟩
    exact ⟨potential, congrArg Subtype.val first_eq, congrArg Subtype.val second_eq⟩
  · rintro ⟨potential, first_eq, second_eq⟩
    exact ⟨potential, Subtype.ext first_eq, Subtype.ext second_eq⟩

theorem lowerRadicalCocycle_H1_zero_iff_polynomial_boundary {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    groupCohomology.H1π (lowerRadicalLatticeRep degree) cycle = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        (lowerRadicalCocyclePair degree cycle 0).val = X 0 * pderiv 2 potential.val ∧
        (lowerRadicalCocyclePair degree cycle 1).val = X 1 * pderiv 2 potential.val := by
  rw [lowerRadicalCocycle_H1_zero_iff_generators]
  change (∃ potential : HomogeneousPoly degree,
    lowerRadicalCocyclePair degree cycle 0 = ((-3 : ℂ) • homogeneousShearDerivation degree 2 0) potential ∧
    lowerRadicalCocyclePair degree cycle 1 = ((-3 : ℂ) • homogeneousShearDerivation degree 2 1) potential) ↔ _
  rw [commonScalar_boundary_iff _ _ (-3) (by norm_num)]
  constructor
  · rintro ⟨potential, first_eq, second_eq⟩
    exact ⟨potential, congrArg Subtype.val first_eq, congrArg Subtype.val second_eq⟩
  · rintro ⟨potential, first_eq, second_eq⟩
    exact ⟨potential, Subtype.ext first_eq, Subtype.ext second_eq⟩

def upperRadicalCocycleCoordinate (degree : ℕ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (planeRadicalCycleCoordinate degree).comp (upperRadicalCocycleToInfinitesimal degree)

def lowerRadicalCocycleCoordinate (degree : ℕ) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (lowerRadicalCycleCoordinate degree).comp (lowerRadicalCocycleToInfinitesimal degree)

theorem upperRadicalCocycleCoordinate_zero_iff {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalCocycleCoordinate degree cycle = 0 ↔
      groupCohomology.H1π (upperRadicalLatticeRep degree) cycle = 0 := by
  rw [upperRadicalCocycle_H1_zero_iff_polynomial_boundary]
  exact planeRadicalCycleCoordinate_kernel (upperRadicalCocycleToInfinitesimal degree cycle)

theorem lowerRadicalCocycleCoordinate_zero_iff {degree : ℕ} (positive : 0 < degree)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocycleCoordinate degree cycle = 0 ↔
      groupCohomology.H1π (lowerRadicalLatticeRep degree) cycle = 0 := by
  rw [lowerRadicalCocycle_H1_zero_iff_polynomial_boundary]
  exact lowerRadicalCycleCoordinate_kernel positive (lowerRadicalCocycleToInfinitesimal degree cycle)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
