module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodPolynomial

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Literal substitution `(X,Y) ↦ (X,-Y)` on homogeneous binary polynomials. -/
def binaryParityReflection (degree : ℕ) : Module.End ℂ (Binary.HomogeneousPoly degree) where
  toFun polynomial := ⟨Binary.substitute !![1,0;0,-1] polynomial.val,
    Binary.substitute_homogeneous _ polynomial.property⟩
  map_add' first second := Subtype.ext (map_add (Binary.substitute !![1,0;0,-1]) first.val second.val)
  map_smul' scalar polynomial := Subtype.ext (map_smul (Binary.substitute !![1,0;0,-1]) scalar polynomial.val)

theorem binaryParityReflection_standardBasis (degree : ℕ) (position : Fin (degree + 1)) :
    binaryParityReflection degree (binaryStandardBasis degree position) =
      (-1 : ℂ) ^ (degree - position.val) • binaryStandardBasis degree position := by
  apply Subtype.ext
  change Binary.substitute !![1,0;0,-1] (binaryStandardBasis degree position).val = _
  simp only [binaryStandardBasis_coe, Submodule.coe_smul, Binary.substitute, map_mul, map_pow,
    bind₁_X_right, Binary.linearForm, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero,
    map_neg, one_mul, zero_mul, add_zero, zero_add, neg_one_mul, Algebra.smul_def, algebraMap_eq, map_pow]
  ring

theorem binaryParityReflection_coord (degree : ℕ) (polynomial : Binary.HomogeneousPoly degree)
    (position : Fin (degree + 1)) :
    (binaryStandardBasis degree).coord position (binaryParityReflection degree polynomial) =
      (-1 : ℂ) ^ (degree - position.val) * (binaryStandardBasis degree).coord position polynomial := by
  conv_lhs => rw [← (binaryStandardBasis degree).sum_repr polynomial]
  simp only [map_sum, map_smul, binaryParityReflection_standardBasis, Module.Basis.coord_apply]
  simp [Finsupp.single_apply, mul_comm]

/-- Parity zero is the even part and parity one is the odd part. -/
def binaryParityComponent (degree parity : ℕ) : Module.End ℂ (Binary.HomogeneousPoly degree) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ) ^ parity • binaryParityReflection degree)

theorem binaryParityComponent_coord (degree parity : ℕ) (polynomial : Binary.HomogeneousPoly degree)
    (position : Fin (degree + 1)) :
    (binaryStandardBasis degree).coord position (binaryParityComponent degree parity polynomial) =
      (2 : ℂ)⁻¹ * (1 + (-1 : ℂ) ^ (parity + degree - position.val)) *
        (binaryStandardBasis degree).coord position polynomial := by
  change (binaryStandardBasis degree).coord position
    ((2 : ℂ)⁻¹ • (polynomial + (-1 : ℂ) ^ parity • binaryParityReflection degree polynomial)) = _
  rw [map_smul, map_add, map_smul, binaryParityReflection_coord]
  simp only [smul_eq_mul]
  rw [show parity + degree - position.val = parity + (degree - position.val) by omega, pow_add]
  ring

theorem binaryParityComponent_coord_preserved (degree parity : ℕ) (polynomial : Binary.HomogeneousPoly degree)
    (position : Fin (degree + 1)) (same_parity : Even (parity + degree - position.val)) :
    (binaryStandardBasis degree).coord position (binaryParityComponent degree parity polynomial) =
      (binaryStandardBasis degree).coord position polynomial := by
  rw [binaryParityComponent_coord, same_parity.neg_one_pow]
  norm_num

def binaryEndpointPolynomialSpan (degree : ℕ) : Submodule ℂ (Binary.HomogeneousPoly degree) :=
  Submodule.span ℂ {binaryStandardBasis degree 0, binaryStandardBasis degree (Fin.last degree)}

theorem binaryEndpointPolynomialSpan_coord_zero (degree : ℕ)
    (polynomial : Binary.HomogeneousPoly degree) (member : polynomial ∈ binaryEndpointPolynomialSpan degree)
    (position : Fin (degree + 1)) (left : position ≠ 0) (right : position ≠ Fin.last degree) :
    (binaryStandardBasis degree).coord position polynomial = 0 := by
  have inclusion : binaryEndpointPolynomialSpan degree ≤
      LinearMap.ker ((binaryStandardBasis degree).coord position) := by
    apply Submodule.span_le.mpr
    intro generator member
    rcases Set.mem_insert_iff.mp member with rfl | member
    · simp [LinearMap.mem_ker, Module.Basis.coord_apply, left]
    · have equal : generator = binaryStandardBasis degree (Fin.last degree) := Set.mem_singleton_iff.mp member
      subst generator
      simp [LinearMap.mem_ker, Module.Basis.coord_apply, right]
  exact inclusion member

end TernaryPeriodPolynomials.SphericalDetection.Helpers
