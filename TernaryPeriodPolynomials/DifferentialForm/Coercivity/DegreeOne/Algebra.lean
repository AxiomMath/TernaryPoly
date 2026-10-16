module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HodgeMetric

@[expose] public section



/-! # Degree-one algebraic Hodge operator

Exterior-degree-one analogue of `TernaryPoly.SL3PolynomialCoercivity.algebraicHodgeTwo`, one
step down in the complex.
-/

noncomputable section
open TernaryPoly.SL3PolynomialCoercivity MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CoercivityOne

/-- The degree-0-to-1 exterior derivative in algebraic coordinates: `(d p)_i = X_i p`. -/
def exteriorZero (p : Poly) : OneCoordinates := fun i => infinitesimal (tangentFrame i) p

/-- The degree-1-to-0 contraction (divergence) in algebraic coordinates. -/
def contractionOne (a : OneCoordinates) : Poly :=
  ∑ j : Fin 5, tangentWeight j • infinitesimal (tangentFrame j) (a j)

/-- The algebraic Hodge operator in exterior degree one: `d∘δ + δ∘d` one level below
`algebraicHodgeTwo`. -/
def algebraicHodgeOne (a : OneCoordinates) : OneCoordinates :=
  exteriorZero (contractionOne a) + contractionTwo (exteriorOne a)

theorem algebraicHodgeOne_expansion (a : OneCoordinates) (i : Fin 5) :
    algebraicHodgeOne a i = ∑ k : Fin 5, tangentWeight k •
      (infinitesimal (tangentFrame k) (infinitesimal (tangentFrame k) (a i)) +
        infinitesimal (tangentFrame i * tangentFrame k - tangentFrame k * tangentFrame i)
          (a k)) := by
  simp only [algebraicHodgeOne, exteriorZero, contractionOne, contractionTwo, exteriorOne,
    Pi.add_apply, map_sum, Derivation.map_smul, infinitesimal_commutator, Derivation.commutator_apply,
    map_sub, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  module

/-- Homogeneous degree-`n` elements of `OneCoordinates`: no alternation condition is needed
at this bottom level. -/
def homogeneousOneForms (n : ℕ) : Submodule ℝ OneCoordinates where
  carrier := {a | ∀ i, (a i).IsHomogeneous n}
  zero_mem' := fun _i => isHomogeneous_zero (Fin 3) ℝ n
  add_mem' := fun ha hb i => (homogeneousSubmodule (Fin 3) ℝ n).add_mem (ha i) (hb i)
  smul_mem' := fun c _ ha i => (homogeneousSubmodule (Fin 3) ℝ n).smul_mem c (ha i)

theorem algebraicHodgeOne_preserves_degree {n : ℕ} (a : OneCoordinates)
    (ha : ∀ i, (a i).IsHomogeneous n) :
    ∀ i, (algebraicHodgeOne a i).IsHomogeneous n := by
  intro i
  rw [algebraicHodgeOne_expansion]
  apply IsHomogeneous.sum
  intro k _
  apply (homogeneousSubmodule (Fin 3) ℝ n).smul_mem
  exact (infinitesimal_preserves_degree _ (infinitesimal_preserves_degree _ (ha i))).add
    (infinitesimal_preserves_degree _ (ha k))

theorem algebraicHodgeOne_mem {n : ℕ} (a : OneCoordinates) (ha : a ∈ homogeneousOneForms n) :
    algebraicHodgeOne a ∈ homogeneousOneForms n :=
  algebraicHodgeOne_preserves_degree a ha

theorem onePairing_symmetric (a b : OneCoordinates) : onePairing a b = onePairing b a := by
  simp only [onePairing, factorialPairing_symmetric]

theorem onePairing_add_left (a b c : OneCoordinates) :
    onePairing (a + b) c = onePairing a c + onePairing b c := by
  simp [onePairing, mul_add, Finset.sum_add_distrib]

/-- Unconditional adjunction between `exteriorZero` and `contractionOne`: unlike
`exteriorOne_contractionTwo_adjoint`, no alternation hypothesis is needed since there is
nothing to alternate at this bottom level. -/
theorem exteriorZero_contractionOne_adjoint (p : Poly) (a : OneCoordinates) :
    onePairing (exteriorZero p) a = factorialPairing p (contractionOne a) := by
  simp only [onePairing, exteriorZero, contractionOne, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem i).1]

/-- The energy identity for the degree-one algebraic Hodge operator, reusing the existing
(degree-general) adjunction `exteriorOne_contractionTwo_adjoint` for the second summand. -/
theorem algebraicHodgeOne_energy (a : OneCoordinates) :
    onePairing (algebraicHodgeOne a) a =
      factorialPairing (contractionOne a) (contractionOne a) +
        twoPairing (exteriorOne a) (exteriorOne a) := by
  rw [algebraicHodgeOne, onePairing_add_left, exteriorZero_contractionOne_adjoint,
    onePairing_symmetric]
  rw [← exteriorOne_contractionTwo_adjoint _ _ (exteriorOne_alternating a)]

theorem algebraicHodgeOne_nonneg (a : OneCoordinates) :
    0 ≤ onePairing (algebraicHodgeOne a) a := by
  rw [algebraicHodgeOne_energy]
  exact add_nonneg (factorialPairing_self_nonneg _) (twoPairing_self_nonneg _)

end TernaryPeriodPolynomials.Argument.CoercivityOne
