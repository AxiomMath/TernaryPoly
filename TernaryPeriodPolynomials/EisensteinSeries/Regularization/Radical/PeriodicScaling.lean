module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.LatticeAutomorphisms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem radical_periodic_integral_automorphism
    (function : Adeles × Adeles → ℂ)
    (periodic : ∀ rational : ℚ × ℚ, ∀ point,
      function (rationalAdele rational.1 + point.1, rationalAdele rational.2 + point.2) = function point)
    (equivalence : (Adeles × Adeles) ≃ₜ+ (Adeles × Adeles))
    (stable : ∀ point ∈ rationalLattice.prod rationalLattice,
      equivalence point ∈ rationalLattice.prod rationalLattice)
    (inverse_stable : ∀ point ∈ rationalLattice.prod rationalLattice,
      equivalence.symm point ∈ rationalLattice.prod rationalLattice) :
    (∫ point, function (equivalence point) ∂planeDomainMeasure) =
      ∫ point, function point ∂planeDomainMeasure := by
  have lattice_periodic (point : rationalLattice.prod rationalLattice) (argument : Adeles × Adeles) :
      function (point +ᵥ argument) = function argument := by
    obtain ⟨first, first_eq⟩ := point.property.1
    obtain ⟨second, second_eq⟩ := point.property.2
    change function (point.val.1 + argument.1, point.val.2 + argument.2) = function argument
    rw [← first_eq, ← second_eq]
    exact periodic (first, second) argument
  rw [planeDomainMeasure_eq]
  calc
    _ = ∫ point in equivalence '' (additiveDomain ×ˢ additiveDomain), function point ∂radicalMeasure :=
      ((radical_lattice_automorphism_measurePreserving equivalence stable inverse_stable).setIntegral_image_emb
        equivalence.toHomeomorph.toMeasurableEquiv.measurableEmbedding function _).symm
    _ = _ := (radicalDomain_image_isFundamental equivalence stable inverse_stable).setIntegral_eq
      radicalDomain_isFundamental lattice_periodic

noncomputable def rationalRadicalScaling (scalar : ℚˣ) : (Adeles × Adeles) ≃ₜ+ (Adeles × Adeles) where
  toFun point := (rationalAdele scalar.val * point.1, rationalAdele scalar.val * point.2)
  invFun point := (rationalAdele scalar.inv * point.1, rationalAdele scalar.inv * point.2)
  left_inv point := by simp only [← mul_assoc, ← map_mul, scalar.inv_val, map_one, one_mul]
  right_inv point := by simp only [← mul_assoc, ← map_mul, scalar.val_inv, map_one, one_mul]
  map_add' first second := by ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add]
  continuous_toFun := (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
  continuous_invFun := (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)

theorem rationalRadicalScaling_lattice (scalar : ℚˣ) (point : Adeles × Adeles)
    (member : point ∈ rationalLattice.prod rationalLattice) :
    rationalRadicalScaling scalar point ∈ rationalLattice.prod rationalLattice := by
  obtain ⟨first, first_eq⟩ := member.1
  obtain ⟨second, second_eq⟩ := member.2
  change rationalAdele first = point.1 at first_eq
  change rationalAdele second = point.2 at second_eq
  constructor
  · exact ⟨scalar.val * first, by change rationalAdele (scalar.val * first) = _; rw [map_mul, first_eq]; rfl⟩
  · exact ⟨scalar.val * second, by change rationalAdele (scalar.val * second) = _; rw [map_mul, second_eq]; rfl⟩

theorem radical_periodic_integral_rational_scaling
    (function : Adeles × Adeles → ℂ)
    (periodic : ∀ rational : ℚ × ℚ, ∀ point,
      function (rationalAdele rational.1 + point.1, rationalAdele rational.2 + point.2) = function point)
    (scalar : ℚˣ) :
    (∫ point : Adeles × Adeles,
      function (rationalAdele scalar.val * point.1, rationalAdele scalar.val * point.2) ∂planeDomainMeasure) =
      ∫ point, function point ∂planeDomainMeasure := by
  apply radical_periodic_integral_automorphism function periodic (rationalRadicalScaling scalar)
  · exact rationalRadicalScaling_lattice scalar
  · exact rationalRadicalScaling_lattice scalar⁻¹

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
