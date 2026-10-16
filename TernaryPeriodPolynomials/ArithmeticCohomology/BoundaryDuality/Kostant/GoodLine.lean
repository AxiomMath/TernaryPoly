module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Form
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.H1Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula

@[expose] public section


/-!
# The Kostant pairing at the good line

The radical `U` of the stabilizer of the good line `⟨e₃⟩` is the lattice `ℤ²` of the matrices
`I + 3 r E₃₁ + 3 s E₃₂` (`lowerRadicalLattice`).  It acts on the ternary forms `V = V_n` of degree
`n` by the shear `X₂ ↦ X₂ − 3 (r X₀ + s X₁)`, and `H¹(U, V) ≅ Sym^{n+1}` (`lowerRadicalH1Coordinate`).
The level involution `φ(g) = a (g⁻¹)ᵀ a⁻¹`, `a = diag(1, 1, 3)`, carries `U` onto the radical
`I + r E₁₃ + s E₂₃` of the identity plane (`dualInvolution_lowerRadicalLattice_mul`), and the
coefficient pairing `dualPairing` is adjoint for the lower and the upper radical actions
(`isAdjointAt_lower_upper`).  The Kostant pairing

  `K(z, w) = ⟨z(e₁), w(e₂)⟩ − ⟨z(e₂), w(e₁)⟩`,   `z ∈ Z¹(U, V)`, `w ∈ Z¹(U^φ, V)`,

(the cup product evaluated on the fundamental class of `U`) is computed in the binary coordinates:
**`K(z, w) = ⟨ coord z, coord w ⟩_apolar`** (`kostantValue_eq`), the apolar pairing of the two
elements of `Sym^{n+1}` given by `lowerRadicalH1Coordinate` and `upperRadicalH1Coordinate`.  The
proof computes `K` on the cocycles with values in the invariants `ℂ[X₀, X₁]_n` (every class has one,
`exists_invariant_pair`) and removes the coboundary by `kostantValue_boundary_left`.  Hence the pairing
`goodLineKostant` on `H¹(U, V) × H¹(U^φ, V)` is perfect (`goodLineKostant_left_eq_zero`,
`goodLineKostant_right_eq_zero`).  The unipotent lattices see only the determinant-one part of the
coefficient system, so nothing here depends on the character of the coefficients.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-! ### The level involution on the radical lattices -/

/-- The level involution carries the good-line radical `I + 3x E₃₁ + 3y E₃₂` to the identity-plane
radical `I − x E₁₃ − y E₂₃`. -/
theorem dualInvolution_lowerPlaneUnipotent (x y : ℚ) :
    dualInvolution (lowerPlaneUnipotent (3 * x) (3 * y) : RationalGL3) =
      planeUnipotent (-x) (-y) := by
  have hL : ((levelScale : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 3] := rfl
  have hLi : (((levelScale⁻¹ : RationalGL3)) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 1 / 3] := rfl
  have hT : ((inverseTranspose (lowerPlaneUnipotent (3 * x) (3 * y) : RationalGL3) :
      RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) = !![1, 0, -(3 * x); 0, 1, -(3 * y); 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  apply Units.ext
  rw [dualInvolution_apply, Units.val_mul, Units.val_mul, hL, hLi, hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, planeUnipotent] <;> ring

/-- `φ (lower u) · upper u = 1`: the level involution of the good-line radical element is the
inverse of the identity-plane radical element with the same coordinates. -/
theorem dualInvolution_lowerRadicalLattice_mul (u : RadicalLattice) :
    dualInvolution (lowerRadicalLattice u) * upperRadicalLattice u = 1 := by
  have h : lowerRadicalLattice u =
      lowerPlaneUnipotent (3 * (u.toAdd.1 : ℚ)) (3 * (u.toAdd.2 : ℚ)) := rfl
  have h2 : upperRadicalLattice u = planeUnipotent (u.toAdd.1 : ℚ) (u.toAdd.2 : ℚ) := rfl
  rw [h, h2, dualInvolution_lowerPlaneUnipotent, ← GeneralEisenstein.Adelic.planeUnipotent_add,
    neg_add_cancel, neg_add_cancel]
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [planeUnipotent]

/-- **Adjointness.**  The coefficient pairing `dualPairing` is adjoint for the good-line radical
action on the first slot and the identity-plane radical action on the second slot:
`⟨u·v, w⟩ = ⟨v, u·w⟩` for the lattice elements `u` of the two radicals with the same coordinates. -/
theorem isAdjointAt_lower_upper (n : ℕ) (u : RadicalLattice) :
    IsAdjointAt (lowerRadicalLatticeRep n).ρ (upperRadicalLatticeRep n).ρ (dualPairing n) u := by
  intro v w
  have key := dualPairing_invariant n trivialCharacter (lowerRadicalLattice u) v
    (rationalCoefficientComponent n trivialCharacter (upperRadicalLattice u) w)
  have hmul : ∀ w' : HomogeneousPoly n, (rationalCoefficientComponent n trivialCharacter
      (dualInvolution (lowerRadicalLattice u)))
        ((rationalCoefficientComponent n trivialCharacter (upperRadicalLattice u)) w') = w' := by
    intro w'
    rw [← Module.End.mul_apply, ← map_mul, dualInvolution_lowerRadicalLattice_mul, map_one,
      Module.End.one_apply]
  rw [hmul w] at key
  rw [lowerRadicalLatticeRep_rho, upperRadicalLatticeRep_rho]
  exact key

/-! ### Cocycles with values in the invariants -/

/-- The average of the exponential acts as the identity on the kernel of the nilpotent operator. -/
theorem nilpotentExponentialAverage_apply_of_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N : Module.End ℂ V) (cutoff : ℕ) (v : V) (hv : N v = 0) :
    nilpotentExponentialAverage N (cutoff + 1) v = v := by
  have hcomm : Commute N (∑ index ∈ Finset.range cutoff,
      ((index + 2).factorial : ℚ)⁻¹ • N ^ index) := by
    apply Commute.sum_right
    intro index _
    exact (Commute.refl N).pow_right index |>.smul_right _
  have h := nilpotentExponentialAverage_remainder N cutoff
  have h2 : (nilpotentExponentialAverage N (cutoff + 1) - 1) v = 0 := by
    rw [h, hcomm.eq, Module.End.mul_apply, hv, map_zero]
  exact sub_eq_zero.mp (show nilpotentExponentialAverage N (cutoff + 1) v - v = 0 from h2)

/-- The lower-radical generators kill the forms free of `X₂`. -/
theorem lowerRadicalGenerator_of_pderiv_third_zero (n : ℕ) (i : Fin 2) (P : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) : lowerRadicalGenerator n i P = 0 := by
  apply Subtype.ext
  change (-3 : ℂ) • (X i.castSucc * pderiv 2 P.val) = 0
  rw [hP, mul_zero, smul_zero]

/-- The closedness condition `(ρ₁ − 1) Q = (ρ₂ − 1) P` holds for forms free of `X₂`. -/
theorem lower_closed_of_pderiv_third_zero (n : ℕ) (P Q : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) (hQ : pderiv 2 Q.val = 0) :
    ((lowerRadicalLatticeRep n).ρ radicalLatticeFirst - 1) Q =
      ((lowerRadicalLatticeRep n).ρ radicalLatticeSecond - 1) P := by
  have h1 : ((lowerRadicalLatticeRep n).ρ radicalLatticeFirst - 1) Q = 0 := by
    rw [lowerRadicalLatticeRep_first, exp_inst_irrel _ Algebra.toModule]
    exact (nilpotent_difference_kernel (lowerRadicalGenerator n 0) n
      (lowerRadicalGenerator_power_zero n 0) Q).mpr
      (lowerRadicalGenerator_of_pderiv_third_zero n 0 Q hQ)
  have h2 : ((lowerRadicalLatticeRep n).ρ radicalLatticeSecond - 1) P = 0 := by
    rw [lowerRadicalLatticeRep_second, exp_inst_irrel _ Algebra.toModule]
    exact (nilpotent_difference_kernel (lowerRadicalGenerator n 1) n
      (lowerRadicalGenerator_power_zero n 1) P).mpr
      (lowerRadicalGenerator_of_pderiv_third_zero n 1 P hP)
  rw [h1, h2]

/-- The 1-cocycle of the good-line radical with prescribed values `P, Q` on the two generators,
for `P, Q` free of `X₂` (so that they lie in the invariants and the cocycle is a homomorphism). -/
def specialCocycle (n : ℕ) (P Q : HomogeneousPoly n) (hP : pderiv 2 P.val = 0)
    (hQ : pderiv 2 Q.val = 0) : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  latticeCocycleOfClosedPair (lowerRadicalLatticeRep n) P Q
    (lower_closed_of_pderiv_third_zero n P Q hP hQ)

/-- The special cocycle takes the value `P` on the first generator. -/
theorem specialCocycle_first (n : ℕ) (P Q : HomogeneousPoly n) (hP : pderiv 2 P.val = 0)
    (hQ : pderiv 2 Q.val = 0) : specialCocycle n P Q hP hQ radicalLatticeFirst = P :=
  latticeCocycleOfClosedPair_first _ _ _ _

/-- The special cocycle takes the value `Q` on the second generator. -/
theorem specialCocycle_second (n : ℕ) (P Q : HomogeneousPoly n) (hP : pderiv 2 P.val = 0)
    (hQ : pderiv 2 Q.val = 0) : specialCocycle n P Q hP hQ radicalLatticeSecond = Q :=
  latticeCocycleOfClosedPair_second _ _ _ _

/-- The infinitesimal first component of the special cocycle is `P`. -/
theorem lowerRadicalCocyclePair_special_first (n : ℕ) (P Q : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) (hQ : pderiv 2 Q.val = 0) :
    lowerRadicalCocyclePair n (specialCocycle n P Q hP hQ) 0 = P := by
  change (lowerRadicalAverageEquiv n 0).symm
    (specialCocycle n P Q hP hQ (radicalLatticeGenerator 0)) = P
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change specialCocycle n P Q hP hQ (radicalLatticeGenerator 0) =
    nilpotentExponentialAverage (lowerRadicalGenerator n 0) (n + 1) P
  rw [nilpotentExponentialAverage_apply_of_kernel _ _ _
    (lowerRadicalGenerator_of_pderiv_third_zero n 0 P hP)]
  exact specialCocycle_first n P Q hP hQ

/-- The infinitesimal second component of the special cocycle is `Q`. -/
theorem lowerRadicalCocyclePair_special_second (n : ℕ) (P Q : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) (hQ : pderiv 2 Q.val = 0) :
    lowerRadicalCocyclePair n (specialCocycle n P Q hP hQ) 1 = Q := by
  change (lowerRadicalAverageEquiv n 1).symm
    (specialCocycle n P Q hP hQ (radicalLatticeGenerator 1)) = Q
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change specialCocycle n P Q hP hQ (radicalLatticeGenerator 1) =
    nilpotentExponentialAverage (lowerRadicalGenerator n 1) (n + 1) Q
  rw [nilpotentExponentialAverage_apply_of_kernel _ _ _
    (lowerRadicalGenerator_of_pderiv_third_zero n 1 Q hQ)]
  exact specialCocycle_second n P Q hP hQ

/-- The lift of the binary coordinate of a lower-radical cocycle is the contraction of its
infinitesimal pair. -/
theorem lift_lowerCoordinate (n : ℕ) (z : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    binaryPolynomialLift (lowerRadicalCocycleCoordinate n z).val =
      lowerRadicalContraction (lowerRadicalCocyclePair n z 0).val
        (lowerRadicalCocyclePair n z 1).val :=
  lowerRadicalCycleCoordinate_lift (lowerRadicalCocycleToInfinitesimal n z)

/-- The binary coordinate of the special cocycle is the contraction of its two values. -/
theorem lift_lowerCoordinate_special (n : ℕ) (P Q : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) (hQ : pderiv 2 Q.val = 0) :
    binaryPolynomialLift (lowerRadicalCocycleCoordinate n (specialCocycle n P Q hP hQ)).val =
      lowerRadicalContraction P.val Q.val := by
  rw [lift_lowerCoordinate, lowerRadicalCocyclePair_special_first n P Q hP hQ,
    lowerRadicalCocyclePair_special_second n P Q hP hQ]

/-- Every binary form of degree `n + 1` is the contraction `X₁ P − X₀ Q` of two forms of degree
`n` free of `X₂`. -/
theorem exists_invariant_pair {n : ℕ} (W : Binary.HomogeneousPoly (n + 1)) :
    ∃ P Q : HomogeneousPoly n, pderiv 2 P.val = 0 ∧ pderiv 2 Q.val = 0 ∧
      lowerRadicalContraction P.val Q.val = (binaryHomogeneousLift (n + 1) W).val := by
  let polynomial := (binaryHomogeneousLift (n + 1) W).val
  let scalar : ℂ := (n + 1 : ℂ)⁻¹
  have homogeneous : polynomial.IsHomogeneous (n + 1) :=
    (binaryHomogeneousLift (n + 1) W).property
  have independent : pderiv (2 : Fin 3) polynomial = 0 :=
    binaryPolynomialLift_pderiv_third W.val
  have P_degree : (scalar • pderiv (1 : Fin 3) polynomial).IsHomogeneous n := by
    rw [Algebra.smul_def]
    have derivative_degree : (pderiv (1 : Fin 3) polynomial).IsHomogeneous n := by
      simpa using homogeneous.pderiv (i := (1 : Fin 3))
    exact derivative_degree.C_mul scalar
  have Q_degree : (-(scalar • pderiv (0 : Fin 3) polynomial)).IsHomogeneous n := by
    apply IsHomogeneous.neg
    rw [Algebra.smul_def]
    have derivative_degree : (pderiv (0 : Fin 3) polynomial).IsHomogeneous n := by
      simpa using homogeneous.pderiv (i := (0 : Fin 3))
    exact derivative_degree.C_mul scalar
  refine ⟨⟨scalar • pderiv 1 polynomial, P_degree⟩, ⟨-(scalar • pderiv 0 polynomial), Q_degree⟩,
    ?_, ?_, ?_⟩
  · change pderiv 2 (scalar • pderiv 1 polynomial) = 0
    rw [Derivation.map_smul, pderiv_commute 2 1, independent, map_zero, smul_zero]
  · change pderiv 2 (-(scalar • pderiv 0 polynomial)) = 0
    rw [map_neg, Derivation.map_smul, pderiv_commute 2 0, independent, map_zero, smul_zero,
      neg_zero]
  · change lowerRadicalContraction (scalar • pderiv 1 polynomial)
        (-(scalar • pderiv 0 polynomial)) = polynomial
    have contraction : lowerRadicalContraction (scalar • pderiv 1 polynomial)
        (-(scalar • pderiv 0 polynomial)) =
        scalar • (X 0 * pderiv 0 polynomial + X 1 * pderiv 1 polynomial) := by
      simp only [lowerRadicalContraction, Algebra.smul_def]
      ring
    have euler := homogeneous.sum_X_mul_pderiv
    simp only [Fin.sum_univ_three, independent, mul_zero, add_zero] at euler
    rw [contraction, euler, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have nonzero : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    dsimp only [scalar]
    rw [Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ nonzero, one_smul]

/-! ### The restriction of identity-plane cocycles -/

/-- The restriction to `X₂ = 0` of the first value of an identity-plane cocycle is `∂₀` of its
binary coordinate. -/
theorem restrict_upper_first (n : ℕ) (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    binaryPolynomialRestrict (w radicalLatticeFirst).val =
      pderiv 0 (upperRadicalCocycleCoordinate n w).val := by
  obtain ⟨potential, h0, _⟩ := planeRadicalCoordinate_has_normal
    (⟨upperRadicalCocyclePair n w, upperRadicalCocyclePair_closed w⟩ : planeRadicalCycles n)
  have h0' : (upperRadicalCocyclePair n w 0).val =
      pderiv 0 (binaryPolynomialLift (upperRadicalCocycleCoordinate n w).val) +
        X 2 * pderiv 0 potential.val := h0
  have hr := congrArg Subtype.val (upperRadicalCocyclePair_restrict w 0)
  change binaryPolynomialRestrict (upperRadicalCocyclePair n w 0).val =
    binaryPolynomialRestrict (w radicalLatticeFirst).val at hr
  rw [← hr, h0', binaryPolynomialRestrict_plane_first]

/-- The restriction to `X₂ = 0` of the second value of an identity-plane cocycle is `∂₁` of its
binary coordinate. -/
theorem restrict_upper_second (n : ℕ) (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    binaryPolynomialRestrict (w radicalLatticeSecond).val =
      pderiv 1 (upperRadicalCocycleCoordinate n w).val := by
  obtain ⟨potential, _, h1⟩ := planeRadicalCoordinate_has_normal
    (⟨upperRadicalCocyclePair n w, upperRadicalCocyclePair_closed w⟩ : planeRadicalCycles n)
  have h1' : (upperRadicalCocyclePair n w 1).val =
      pderiv 1 (binaryPolynomialLift (upperRadicalCocycleCoordinate n w).val) +
        X 2 * pderiv 1 potential.val := h1
  have hr := congrArg Subtype.val (upperRadicalCocyclePair_restrict w 1)
  change binaryPolynomialRestrict (upperRadicalCocyclePair n w 1).val =
    binaryPolynomialRestrict (w radicalLatticeSecond).val at hr
  rw [← hr, h1', binaryPolynomialRestrict_plane_second]

/-! ### The Kostant pairing in binary coordinates -/

/-- `∂₀` commutes with the lift of binary forms. -/
theorem pderiv_lift_zero (F : Binary.Poly) :
    pderiv 0 (binaryPolynomialLift F) = binaryPolynomialLift (pderiv 0 F) :=
  lift_pderiv_castSucc 0 F

/-- `∂₁` commutes with the lift of binary forms. -/
theorem pderiv_lift_one (F : Binary.Poly) :
    pderiv 1 (binaryPolynomialLift F) = binaryPolynomialLift (pderiv 1 F) :=
  lift_pderiv_castSucc 1 F

/-- **The Kostant pairing of a cocycle with values in the invariants.**  If `P, Q` are free of `X₂`
and the restrictions of `wα, wβ` to `X₂ = 0` are `∂₀ F, ∂₁ F`, then
`⟨P, wβ⟩ − ⟨Q, wα⟩ = ⟨X₁ P − X₀ Q, F⟩_apolar`. -/
theorem kostantValue_special (n : ℕ) (P Q : HomogeneousPoly n) (hP : pderiv 2 P.val = 0)
    (hQ : pderiv 2 Q.val = 0) (F : Binary.HomogeneousPoly (n + 1)) (wα wβ : HomogeneousPoly n)
    (h0 : binaryPolynomialRestrict wα.val = pderiv 0 F.val)
    (h1 : binaryPolynomialRestrict wβ.val = pderiv 1 F.val) :
    kostantValue (dualPairing n) P Q wα wβ =
      apolarPoly (lowerRadicalContraction P.val Q.val) (binaryPolynomialLift F.val) := by
  unfold kostantValue
  rw [dualPairing_eq_of_pderiv_third_zero n P wβ hP, dualPairing_eq_of_pderiv_third_zero n Q wα hQ,
    h0, h1, ← pderiv_lift_one, ← pderiv_lift_zero, ← apolarPoly_X_mul, ← apolarPoly_X_mul,
    lowerRadicalContraction, map_sub, LinearMap.sub_apply]

/-- **The Kostant pairing in binary coordinates.**  For `z` a cocycle of the good-line radical and
`w` a cocycle of the identity-plane radical, the cup-product value
`⟨z(e₁), w(e₂)⟩ − ⟨z(e₂), w(e₁)⟩` is the apolar pairing of their binary coordinates in
`Sym^{n+1}`. -/
theorem kostantValue_eq (n : ℕ) (positive : 0 < n)
    (z : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n))
    (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    kostantValue (dualPairing n) (z radicalLatticeFirst) (z radicalLatticeSecond)
        (w radicalLatticeFirst) (w radicalLatticeSecond) =
      binApolar (n + 1) (lowerRadicalCocycleCoordinate n z) (upperRadicalCocycleCoordinate n w) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_invariant_pair (lowerRadicalCocycleCoordinate n z)
  -- the special cocycle with the same coordinate as `z`
  have hcoord : lowerRadicalCocycleCoordinate n (specialCocycle n P Q hP hQ) =
      lowerRadicalCocycleCoordinate n z := by
    apply Subtype.ext
    apply binaryPolynomialLift_injective
    rw [lift_lowerCoordinate_special n P Q hP hQ, hPQ]
    rfl
  obtain ⟨s, hs1, hs2, hsc⟩ : ∃ s : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n),
      s radicalLatticeFirst = P ∧ s radicalLatticeSecond = Q ∧
        lowerRadicalCocycleCoordinate n s = lowerRadicalCocycleCoordinate n z :=
    ⟨specialCocycle n P Q hP hQ, specialCocycle_first n P Q hP hQ,
      specialCocycle_second n P Q hP hQ, hcoord⟩
  -- the difference is a coboundary
  have hzero : lowerRadicalCocycleCoordinate n (z - s) = 0 := by
    rw [map_sub, hsc, sub_self]
  have hH1 := (lowerRadicalCocycleCoordinate_zero_iff positive (z - s)).mp hzero
  obtain ⟨potential, hfirst, hsecond⟩ :=
    (oneCocycle_H1_zero_iff_generator_boundaries (lowerRadicalLatticeRep n) (z - s)
      radicalLatticeFirst radicalLatticeSecond radicalLattice_generated).mp hH1
  have hz1 : z radicalLatticeFirst = s radicalLatticeFirst + (((lowerRadicalLatticeRep n).ρ radicalLatticeFirst)
      potential - potential) := by
    have h := hfirst
    change z radicalLatticeFirst - s radicalLatticeFirst = _ at h
    exact sub_eq_iff_eq_add'.mp h
  have hz2 : z radicalLatticeSecond = s radicalLatticeSecond + (((lowerRadicalLatticeRep n).ρ radicalLatticeSecond)
      potential - potential) := by
    have h := hsecond
    change z radicalLatticeSecond - s radicalLatticeSecond = _ at h
    exact sub_eq_iff_eq_add'.mp h
  -- the closedness of `w`
  have hw := oneCocycle_generator_closed (upperRadicalLatticeRep n) w radicalLatticeFirst
    radicalLatticeSecond (Commute.all _ _)
  have hwc : ((upperRadicalLatticeRep n).ρ radicalLatticeFirst) (w radicalLatticeSecond) -
      w radicalLatticeSecond = ((upperRadicalLatticeRep n).ρ radicalLatticeSecond)
        (w radicalLatticeFirst) - w radicalLatticeFirst := hw
  have hbd : kostantValue (dualPairing n)
      (((lowerRadicalLatticeRep n).ρ radicalLatticeFirst) potential - potential)
      (((lowerRadicalLatticeRep n).ρ radicalLatticeSecond) potential - potential)
      (w radicalLatticeFirst) (w radicalLatticeSecond) = 0 :=
    kostantValue_boundary_left (lowerRadicalLatticeRep n).ρ (upperRadicalLatticeRep n).ρ
      (dualPairing n) radicalLatticeFirst radicalLatticeSecond
      (isAdjointAt_lower_upper n radicalLatticeFirst)
      (isAdjointAt_lower_upper n radicalLatticeSecond) potential _ _ hwc
  have hK : kostantValue (dualPairing n) (z radicalLatticeFirst) (z radicalLatticeSecond)
        (w radicalLatticeFirst) (w radicalLatticeSecond) =
      kostantValue (dualPairing n) P Q (w radicalLatticeFirst) (w radicalLatticeSecond) := by
    have h2 := congrArg₂ (fun x y => kostantValue (dualPairing n) x y (w radicalLatticeFirst)
      (w radicalLatticeSecond)) hz1 hz2
    have h1 := kostantValue_add_left (dualPairing n) (s radicalLatticeFirst)
      (s radicalLatticeSecond)
      (((lowerRadicalLatticeRep n).ρ radicalLatticeFirst) potential - potential)
      (((lowerRadicalLatticeRep n).ρ radicalLatticeSecond) potential - potential)
      (w radicalLatticeFirst) (w radicalLatticeSecond)
    have h3 := congrArg₂ (fun x y => kostantValue (dualPairing n) x y (w radicalLatticeFirst)
      (w radicalLatticeSecond)) hs1 hs2
    refine h2.trans (h1.trans ?_)
    refine Eq.trans (congrArg (fun t => kostantValue (dualPairing n) (s radicalLatticeFirst)
      (s radicalLatticeSecond) (w radicalLatticeFirst) (w radicalLatticeSecond) + t) hbd) ?_
    exact (add_zero _).trans h3
  have hF : kostantValue (dualPairing n) P Q (w radicalLatticeFirst) (w radicalLatticeSecond) =
      binApolar (n + 1) (lowerRadicalCocycleCoordinate n z) (upperRadicalCocycleCoordinate n w) := by
    rw [kostantValue_special n P Q hP hQ (upperRadicalCocycleCoordinate n w)
      (w radicalLatticeFirst) (w radicalLatticeSecond) (restrict_upper_first n w)
      (restrict_upper_second n w), hPQ]
    exact (binApolar_apply _ _ _).symm
  exact hK.trans hF

/-! ### The pairing on cohomology -/

/-- **The Kostant pairing of the good line.**  The cup product pairing
`H¹(U, V) × H¹(U^φ, V) → H²(U) = ℂ` of the good-line radical lattice `U` with the identity-plane
radical lattice `U^φ = φ(U)` (with the coefficient pairing `dualPairing`), expressed in the binary
coordinates: the apolar pairing of `Sym^{n+1}`. -/
def goodLineKostant (n : ℕ) (positive : 0 < n) :
    groupCohomology.H1 (lowerRadicalLatticeRep n) →ₗ[ℂ]
      groupCohomology.H1 (upperRadicalLatticeRep n) →ₗ[ℂ] ℂ :=
  (binApolar (n + 1)).compl₁₂ (lowerRadicalH1Coordinate n positive).toLinearMap
    (upperRadicalH1Coordinate n).toLinearMap

/-- The pairing of two classes is the apolar pairing of their binary coordinates. -/
theorem goodLineKostant_apply (n : ℕ) (positive : 0 < n)
    (c : groupCohomology.H1 (lowerRadicalLatticeRep n))
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    goodLineKostant n positive c c' =
      binApolar (n + 1) (lowerRadicalH1Coordinate n positive c) (upperRadicalH1Coordinate n c') :=
  rfl

/-- **Evaluation on cocycles.**  On the classes of cocycles the Kostant pairing is the cup-product
value `⟨z(e₁), w(e₂)⟩ − ⟨z(e₂), w(e₁)⟩`. -/
theorem goodLineKostant_H1π (n : ℕ) (positive : 0 < n)
    (z : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n))
    (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    goodLineKostant n positive (groupCohomology.H1π (lowerRadicalLatticeRep n) z)
        (groupCohomology.H1π (upperRadicalLatticeRep n) w) =
      kostantValue (dualPairing n) (z radicalLatticeFirst) (z radicalLatticeSecond)
        (w radicalLatticeFirst) (w radicalLatticeSecond) := by
  rw [kostantValue_eq n positive z w, goodLineKostant_apply, lowerRadicalH1Coordinate_apply,
    upperRadicalH1Coordinate_apply]

/-- **Perfectness, left.**  A class of `H¹(U, V)` pairing to zero with every class of `H¹(U^φ, V)`
is zero. -/
theorem goodLineKostant_left_eq_zero (n : ℕ) (positive : 0 < n)
    {c : groupCohomology.H1 (lowerRadicalLatticeRep n)}
    (h : ∀ c' : groupCohomology.H1 (upperRadicalLatticeRep n),
      goodLineKostant n positive c c' = 0) : c = 0 := by
  have h' : lowerRadicalH1Coordinate n positive c = 0 := by
    apply binApolar_left_eq_zero
    intro g
    have h1 := h ((upperRadicalH1Coordinate n).symm g)
    rw [goodLineKostant_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1
  exact (LinearEquiv.map_eq_zero_iff _).mp h'

/-- **Perfectness, right.**  A class of `H¹(U^φ, V)` pairing to zero with every class of `H¹(U, V)`
is zero. -/
theorem goodLineKostant_right_eq_zero (n : ℕ) (positive : 0 < n)
    {c' : groupCohomology.H1 (upperRadicalLatticeRep n)}
    (h : ∀ c : groupCohomology.H1 (lowerRadicalLatticeRep n),
      goodLineKostant n positive c c' = 0) : c' = 0 := by
  have h' : upperRadicalH1Coordinate n c' = 0 := by
    apply binApolar_right_eq_zero
    intro f
    have h1 := h ((lowerRadicalH1Coordinate n positive).symm f)
    rw [goodLineKostant_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1
  exact (LinearEquiv.map_eq_zero_iff _).mp h'

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
