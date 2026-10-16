module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirScalar

@[expose] public section


open GeneralEisenstein
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def BinaryDegreeMonomial (degree : ℕ) :=
  {monomial : Fin 2 →₀ ℕ // Finsupp.degree monomial = degree}

noncomputable instance binaryDegreeMonomialFintype (degree : ℕ) : Fintype (BinaryDegreeMonomial degree) :=
  (Finsupp.finite_of_degree_eq degree).fintype

noncomputable def binaryHomogeneousMonomial {degree : ℕ} (monomial : BinaryDegreeMonomial degree) :
    Binary.HomogeneousPoly degree :=
  ⟨MvPolynomial.monomial monomial.val 1, MvPolynomial.isHomogeneous_monomial 1 monomial.property⟩

def binaryHomogeneousCoordinates (degree : ℕ) :
    Binary.HomogeneousPoly degree →ₗ[ℂ] (BinaryDegreeMonomial degree → ℂ) where
  toFun polynomial monomial := polynomial.val.coeff monomial.val
  map_add' _ _ := by ext monomial; simp only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' _ _ := by ext monomial; simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, Pi.smul_apply, RingHom.id_apply]

noncomputable def binaryHomogeneousReconstruct (degree : ℕ) :
    (BinaryDegreeMonomial degree → ℂ) →ₗ[ℂ] Binary.HomogeneousPoly degree where
  toFun coordinates := ∑ monomial, coordinates monomial • binaryHomogeneousMonomial monomial
  map_add' first second := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar coordinates := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

theorem binaryHomogeneousCoordinates_injective (degree : ℕ) :
    Function.Injective (binaryHomogeneousCoordinates degree) := by
  intro first second equality
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  by_cases matching : Finsupp.degree monomial = degree
  · exact congrFun equality ⟨monomial, matching⟩
  · rw [first.property.coeff_eq_zero matching, second.property.coeff_eq_zero matching]

theorem binaryHomogeneousCoordinates_reconstruct (degree : ℕ)
    (coordinates : BinaryDegreeMonomial degree → ℂ) :
    binaryHomogeneousCoordinates degree (binaryHomogeneousReconstruct degree coordinates) = coordinates := by
  classical
  funext monomial
  have equal (other : BinaryDegreeMonomial degree) : other.val = monomial.val ↔ other = monomial :=
    ⟨Subtype.ext, congrArg Subtype.val⟩
  change (∑ other : BinaryDegreeMonomial degree, coordinates other • binaryHomogeneousMonomial other).val.coeff monomial.val = coordinates monomial
  simp only [Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.coeff_sum, binaryHomogeneousMonomial,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
  simp [equal]

theorem binaryHomogeneousReconstruct_coordinates (degree : ℕ) (polynomial : Binary.HomogeneousPoly degree) :
    binaryHomogeneousReconstruct degree (binaryHomogeneousCoordinates degree polynomial) = polynomial := by
  apply binaryHomogeneousCoordinates_injective degree
  exact binaryHomogeneousCoordinates_reconstruct degree _

noncomputable def binaryHomogeneousCoordinateEquiv (degree : ℕ) :
    Binary.HomogeneousPoly degree ≃ₗ[ℂ] (BinaryDegreeMonomial degree → ℂ) :=
  LinearEquiv.ofBijective (binaryHomogeneousCoordinates degree)
    ⟨binaryHomogeneousCoordinates_injective degree,
      fun coordinates => ⟨binaryHomogeneousReconstruct degree coordinates, binaryHomogeneousCoordinates_reconstruct degree coordinates⟩⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
