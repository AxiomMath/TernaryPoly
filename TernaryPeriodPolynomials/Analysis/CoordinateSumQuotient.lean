module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodLift
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodPrimitive
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.Topology.HomogeneousQuotient

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The coordinate sum is a nonzero homogeneous linear polynomial. -/
theorem coordinate_sum_ne_zero : (X 0+X 1+X 2 : TernaryPolynomial) ≠ 0 := by
  intro h
  have h' := congrArg (bind₁ (![1,0,0] : Fin 3 → TernaryPolynomial)) h
  simp at h'

theorem coordinate_sum_isHomogeneous :
    (X 0+X 1+X 2 : TernaryPolynomial).IsHomogeneous 1 :=
  ((isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 1)).add (isHomogeneous_X ℚ 2)

/-- Powers of the coordinate sum can be cancelled from cyclic symmetry. -/
theorem cyclic_of_coordinate_sum_pow_mul {f : TernaryPolynomial} (r : ℕ)
    (hc : C ((X 0+X 1+X 2)^r*f) = (X 0+X 1+X 2)^r*f) : C f = f := by
  apply mul_left_cancel₀ (pow_ne_zero r coordinate_sum_ne_zero)
  have hw : C (X 0+X 1+X 2) = (X 0+X 1+X 2 : TernaryPolynomial) := by
    simp [C]; ring
  simpa only [map_mul, map_pow, hw] using hc

/-- Powers of the coordinate sum can be cancelled from alternating symmetry. -/
theorem alternating_of_coordinate_sum_pow_mul {f : TernaryPolynomial} (r : ℕ)
    (hs : S ((X 0+X 1+X 2)^r*f) = -((X 0+X 1+X 2)^r*f)) : S f = -f := by
  apply mul_left_cancel₀ (pow_ne_zero r coordinate_sum_ne_zero)
  have hw : S (X 0+X 1+X 2) = (X 0+X 1+X 2 : TernaryPolynomial) := by
    simp [S]; ring
  simpa only [map_mul, map_pow, hw, mul_neg] using hs

/-- The literal cyclic lift is cyclic. -/
theorem binaryPeriodLift_cyclic (q : MvPolynomial (Fin 2) ℚ) :
    C (binaryPeriodLift q) = binaryPeriodLift q := by
  change substitute3 (binaryPeriodLift q) (X 1) (X 2) (X 0) = _
  rw [binaryPeriodLift_substitute3, binaryPeriodLift]
  abel

/-- An alternating binary polynomial has an alternating cyclic lift. -/
theorem binaryPeriodLift_alternating {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) : S (binaryPeriodLift q) = -binaryPeriodLift q := by
  change substitute3 (binaryPeriodLift q) (X 1) (X 0) (X 2) = _
  rw [binaryPeriodLift_substitute3, binaryPeriodLift]
  rw [binaryLiftEval_swap hq (X 0) (X 1), binaryLiftEval_swap hq (X 2) (X 0),
    binaryLiftEval_swap hq (X 1) (X 2)]
  abel

/-- The cyclic lift preserves homogeneous degree. -/
theorem binaryPeriodLift_isHomogeneous {q : MvPolynomial (Fin 2) ℚ} {n : ℕ}
    (hq : q.IsHomogeneous n) : (binaryPeriodLift q).IsHomogeneous n := by
  have he (i j : Fin 3) : (binaryLiftEval q (X i) (X j)).IsHomogeneous n := by
    apply isHomogeneous_bind₁_linear hq
    intro k
    fin_cases k <;> exact isHomogeneous_X ℚ _
  exact ((he 0 1).add (he 1 2)).add (he 2 0)

/-- Binary period extraction raises homogeneous degree by one. -/
theorem binaryPeriodPrimitive_isHomogeneous {p : MvPolynomial (Fin 2) ℚ} {n : ℕ}
    (hp : p.IsHomogeneous n) : (binaryPeriodPrimitive n p).IsHomogeneous (n+1) := by
  have hr : (binaryRotation p).IsHomogeneous n := by
    apply isHomogeneous_bind₁_linear hp
    intro i
    fin_cases i
    · exact isHomogeneous_X ℚ 1
    · exact (isHomogeneous_X ℚ 0).neg
  have h := ((isHomogeneous_X ℚ 0).mul hr).add ((isHomogeneous_X ℚ 1).mul hp)
  have hh := (homogeneousSubmodule (Fin 2) ℚ (1+n)).smul_mem (-(1/((n:ℚ)+1))) h
  simpa only [mem_homogeneousSubmodule, binaryPeriodPrimitive, Nat.add_comm] using hh

end TernaryPoly
