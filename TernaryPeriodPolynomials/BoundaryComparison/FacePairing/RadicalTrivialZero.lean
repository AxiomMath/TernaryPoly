module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.CrossedEquiv

@[expose] public section


/-!
# The discrete radical acts trivially on `HomogeneousPoly 0` (face pairing, bad line, `n = 0`)

At degree `0`, `HomogeneousPoly 0` is the space of constant polynomials, and `substitute M`
(any matrix `M`) fixes every constant: `substitute M (C c) = C c` since `substitute M = bind₁
(linearForm M)` is a `ℂ`-algebra homomorphism, hence fixes `C c = algebraMap ℂ Poly c`. Combined
with the already degree-generic formula `rationalCoefficientComponent_lineUnipotent` (which
reduces `rationalCoefficientComponent degree trivialCharacter (lineUnipotent a b)` to exactly
such a `bind₁`-substitution, since `trivialCharacter`'s determinant-character scalar is `1`
unconditionally and `lineUnipotent a b` has determinant `1`), this gives: for **every** matrix of
the form `lineUnipotent a b` (`a b : ℚ`), the rational coefficient-component representation at
degree `0` is the identity.

The discrete radical subgroup embeds via `integralBadLineRadicalEmbedding coordinates =
lineUnipotent coordinates.toAdd.1 coordinates.toAdd.2` **for every** `coordinates`, not only at
the two generators (this is immediate from that definition's `toFun`, exactly mirroring the proof
already given for `integralRadicalRationalHom_generator` at the two generators, dropped here to an
arbitrary group element). Hence `radicalRepresentation 0` is the trivial representation on *all*
of `Multiplicative (ℤ × ℤ)`, not merely at the two generators. Both companion facts needed for the
degree-`0` replacement of the radical identification follow immediately:

* `discreteRadicalCycles 0 = ⊤` (both `radicalDifference 0 index` vanish, so
  `discreteRadicalDifferentialOne 0 = 0`);
* `radicalCrossedBoundaries 0 = ⊥` (`crossedBoundary (radicalRepresentation 0) = 0` outright, since
  `radicalRepresentation 0 coordinates value = value` for every group element `coordinates`, not
  only at generators).
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- Every degree-`0` homogeneous polynomial is the constant polynomial on its own constant
coefficient. -/
theorem homogeneousPoly_zero_eq_C (f : HomogeneousPoly 0) :
    f.val = C (f.val.coeff 0) := by
  have h1 : MvPolynomial.homogeneousComponent 0 f.val = f.val := by
    have h := MvPolynomial.homogeneousComponent_of_mem (n := 0) (m := 0) f.2
    simpa using h
  rw [MvPolynomial.homogeneousComponent_zero] at h1
  exact h1.symm

/-- Any coordinate substitution fixes a degree-`0` homogeneous polynomial. -/
theorem substitute_homogeneousPoly_zero (M : Matrix (Fin 3) (Fin 3) ℂ) (f : HomogeneousPoly 0) :
    substitute M f.val = f.val := by
  show bind₁ (linearForm M) f.val = f.val
  rw [homogeneousPoly_zero_eq_C f]
  exact bind₁_C_right _ _

/-- At degree `0`, the rational coefficient-component representation is the identity at every
`lineUnipotent a b`, not only at the two radical generators. -/
theorem rationalCoefficientComponent_lineUnipotent_zero (first second : ℚ)
    (f : HomogeneousPoly 0) :
    rationalCoefficientComponent 0 trivialCharacter (lineUnipotent first second) f = f := by
  apply Subtype.ext
  rw [rationalCoefficientComponent_lineUnipotent, homogeneousPoly_zero_eq_C f]
  exact bind₁_C_right _ _

/-- The discrete radical embeds via `lineUnipotent` at **every** group element, not only at the
two generators (immediate unfolding of `integralBadLineRadicalEmbedding`'s definition, dropping
the restriction to generators present in `integralRadicalRationalHom_generator`). -/
theorem integralRadicalRationalHom_eq (coordinates : Multiplicative (ℤ × ℤ)) :
    integralRadicalRationalHom coordinates =
      lineUnipotent (coordinates.toAdd.1 : ℚ) (coordinates.toAdd.2 : ℚ) := by
  change GeneralLinearGroup.map (Int.castRingHom ℚ)
    (lineUnipotent coordinates.toAdd.1 coordinates.toAdd.2) = _
  rw [map_lineUnipotent]
  norm_cast

/-- **The discrete radical acts trivially on `HomogeneousPoly 0`, at every group element.** -/
theorem radicalRepresentation_zero_eq_one (coordinates : Multiplicative (ℤ × ℤ))
    (f : HomogeneousPoly 0) :
    radicalRepresentation 0 coordinates f = f := by
  change rationalCoefficientComponent 0 trivialCharacter
    (integralRadicalRationalHom coordinates) f = f
  rw [integralRadicalRationalHom_eq]
  exact rationalCoefficientComponent_lineUnipotent_zero _ _ f

/-- Both radical differences vanish at degree `0`. -/
theorem radicalDifference_zero_eq_zero (index : Fin 2) :
    radicalDifference 0 index = 0 := by
  apply LinearMap.ext
  intro f
  show rationalCoefficientComponent 0 trivialCharacter (radicalGenerator index) f - f = 0
  rw [← radicalRepresentation_generator]
  rw [radicalRepresentation_zero_eq_one]
  abel

/-- **The discrete radical cycles are everything at degree `0`.** -/
theorem discreteRadicalCycles_zero_eq_top :
    discreteRadicalCycles 0 = ⊤ := by
  show (discreteRadicalDifferentialOne 0).ker = ⊤
  have hz : discreteRadicalDifferentialOne 0 = 0 := by
    show ((radicalDifference 0 0).comp (LinearMap.snd ℂ _ _)) -
        ((radicalDifference 0 1).comp (LinearMap.fst ℂ _ _)) = 0
    rw [radicalDifference_zero_eq_zero 0, radicalDifference_zero_eq_zero 1]
    simp
  rw [hz]
  exact LinearMap.ker_zero

/-- **The radical crossed-cocycle boundaries vanish at degree `0`.** -/
theorem radicalCrossedBoundaries_zero_eq_bot :
    radicalCrossedBoundaries 0 = ⊥ := by
  show (crossedBoundary (radicalRepresentation 0)).range = ⊥
  have hz : crossedBoundary (radicalRepresentation 0) = 0 := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    funext coordinates
    show radicalRepresentation 0 coordinates value - value = 0
    rw [radicalRepresentation_zero_eq_one]
    abel
  rw [hz]
  exact LinearMap.range_zero

end TernaryPeriodPolynomials.Argument.FacePairing
