module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BadDual
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Swap

@[expose] public section


/-!
# The Kostant pairing at the bad line

The radical `U = {I + a E₁₂ + b E₁₃}` of the bad line acts on the ternary forms `V = V_n` by the shear
`X₀ ↦ X₀ − a X₁ − b X₂`, and `H¹(U, V) ≅ Sym^{n+1}` (`explicitRadicalBinaryEquiv`, every class is
a homomorphism into the invariants `ℂ[X₁, X₂]_n`).  Its dual factor is `H¹(φ(U), V)` for the
first-column plane radical `φ(U) = {I − a E₂₁ − 3 b E₃₁}`.  In the frame `badFrame` this radical is
the standard upper plane radical `{I + b E₁₃ + a E₂₃}` with the two lattice directions exchanged, so
the dual factor is identified with `H¹(upperRadicalLatticeRep n)` (the radical of the good plane in
its standard frame); a class `w` of the latter corresponds to the cocycle `x ↦ ρ(badFrame) w(swap x)`
of `φ(U)`.

The Kostant pairing (the cup product on the fundamental class of `U`) is

  `K(z, w) = ⟨z(e₁), w(e₁)⟩_bad − ⟨z(e₂), w(e₂)⟩_bad`,   `⟨v, w⟩_bad = ⟨v, ρ(badFrame) w⟩` (`badDualForm`),

and it is computed in the binary coordinates (`badLineKostantValue_eq`):

  `K(z, w) = 1/3 · ⟨σ (coord z), coord w⟩_apolar`,

where `σ` exchanges the two binary variables, `coord z` is the bad-line coordinate in `Sym^{n+1}` and
`coord w` the upper-radical coordinate.  Hence the pairing `badLineKostant` on
`H¹(U, V) × H¹(upper radical)` is perfect and is `(n+1)!/3` times the classical invariant pairing of
`σ (coord z)` against the rotated `coord w` (`badLineKostant_eq_binaryPairing`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-! ### The exchange of the two binary variables -/

/-- The exchange of the two binary variables as an element of `GL₂(ℂ)`. -/
def swapUnit : Binary.GL2 :=
  ⟨swap01, swap01, by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap01, Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap01, Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The exchange `g(x, y) ↦ g(y, x)` of the two variables of a binary form of degree `N`. -/
def binarySwapVar (N : ℕ) : Module.End ℂ (Binary.HomogeneousPoly N) :=
  Binary.homogeneousAction N 0 swapUnit

/-- The underlying polynomial of the exchange. -/
theorem binarySwapVar_val (N : ℕ) (f : Binary.HomogeneousPoly N) :
    ((binarySwapVar N f : Binary.HomogeneousPoly N) : Binary.Poly) =
      Binary.substitute swap01 f.val :=
  binaryUntwistedHomogeneous_val N swapUnit f

theorem swapUnit_mul_self : swapUnit * swapUnit = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapUnit, swap01, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exchange is an involution. -/
theorem binarySwapVar_involutive (N : ℕ) (f : Binary.HomogeneousPoly N) :
    binarySwapVar N (binarySwapVar N f) = f := by
  unfold binarySwapVar
  rw [← Module.End.mul_apply, ← map_mul, swapUnit_mul_self, map_one, Module.End.one_apply]

/-- The exchange as a linear equivalence. -/
def binarySwapVarEquiv (N : ℕ) :
    Binary.HomogeneousPoly N ≃ₗ[ℂ] Binary.HomogeneousPoly N :=
  LinearEquiv.ofLinearMap (binarySwapVar N) (binarySwapVar N)
    (LinearMap.ext fun f => binarySwapVar_involutive N f)
    (LinearMap.ext fun f => binarySwapVar_involutive N f)

/-- The exchange intertwines the actions of `γ` and of its conjugate `σ γ σ⁻¹`. -/
theorem binarySwapVar_action (N : ℕ) (γ : Binary.GL2) (f : Binary.HomogeneousPoly N) :
    binarySwapVar N (Binary.homogeneousAction N 0 γ f) =
      Binary.homogeneousAction N 0 (swapUnit * γ * swapUnit⁻¹) (binarySwapVar N f) := by
  have h : (swapUnit * γ * swapUnit⁻¹) * swapUnit = swapUnit * γ := by group
  unfold binarySwapVar
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h]

/-- The exchange of the variables of a wedge `x q − y p` is `y σq − x σp`. -/
theorem binarySwapVar_wedge_val (n : ℕ)
    (pair : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) :
    ((binarySwapVar (n + 1) (binaryPairWedge n pair) : Binary.HomogeneousPoly (n + 1)) :
        Binary.Poly) =
      X 1 * Binary.substitute swap01 pair.2.val - X 0 * Binary.substitute swap01 pair.1.val := by
  rw [binarySwapVar_val]
  change Binary.substitute swap01 (X 0 * pair.2.val - X 1 * pair.1.val) = _
  rw [map_sub, map_mul, map_mul, Binary.substitute_X, Binary.substitute_X, linearForm_swap01_zero,
    linearForm_swap01_one]

/-! ### Generators -/

theorem radicalGenerator_zero : radicalGenerator 0 = lineUnipotent 1 0 := by
  simp [radicalGenerator]

theorem radicalGenerator_one : radicalGenerator 1 = lineUnipotent 0 1 := by
  simp [radicalGenerator]

/-- The radical representation of the semidirect model on a generator. -/
theorem rho_s_generator (n : ℕ) (i : Fin 2) (v : HomogeneousPoly n) :
    ((standardBadLineRepresentation n).comp SemidirectProduct.inl) (integralRadicalGenerator i) v =
      rationalCoefficientComponent n trivialCharacter (radicalGenerator i) v := by
  rw [standardBadLineRepresentation_radical n, radicalRepresentation_generator]

theorem upperRep_first (n : ℕ) :
    (upperRadicalLatticeRep n).ρ radicalLatticeFirst =
      rationalCoefficientComponent n trivialCharacter (planeUnipotent 1 0) := by
  rw [upperRadicalLatticeRep_rho]
  have h : upperRadicalLattice radicalLatticeFirst = planeUnipotent (1 : ℚ) 0 := by
    change planeUnipotent (((1 : ℤ)) : ℚ) (((0 : ℤ)) : ℚ) = _
    simp
  rw [h]

theorem upperRep_second (n : ℕ) :
    (upperRadicalLatticeRep n).ρ radicalLatticeSecond =
      rationalCoefficientComponent n trivialCharacter (planeUnipotent 0 1) := by
  rw [upperRadicalLatticeRep_rho]
  have h : upperRadicalLattice radicalLatticeSecond = planeUnipotent (0 : ℚ) 1 := by
    change planeUnipotent (((0 : ℤ)) : ℚ) (((1 : ℤ)) : ℚ) = _
    simp
  rw [h]

/-- Adjointness at the first generator of the bad-line radical. -/
theorem bad_adjoint_first (n : ℕ) (v w : HomogeneousPoly n) :
    badDualForm n (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) v) w =
      badDualForm n v (rationalCoefficientComponent n trivialCharacter (planeUnipotent 0 1) w) := by
  rw [radicalGenerator_zero]
  exact badDualForm_adjoint n 1 0 v w

/-- Adjointness at the second generator of the bad-line radical. -/
theorem bad_adjoint_second (n : ℕ) (v w : HomogeneousPoly n) :
    badDualForm n (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) v) w =
      badDualForm n v (rationalCoefficientComponent n trivialCharacter (planeUnipotent 1 0) w) := by
  rw [radicalGenerator_one]
  exact badDualForm_adjoint n 0 1 v w

/-! ### The Kostant pairing in binary coordinates -/

/-- The first-row radical `H¹` of the bad line, in the crossed-homomorphism model. -/
abbrev BadH1 (n : ℕ) :=
  CrossedH1 ((standardBadLineRepresentation n).comp SemidirectProduct.inl)

/-- **The Kostant pairing of the bad line in binary coordinates.**  For `z` a crossed cocycle of the
bad-line radical and `w` a cocycle of the upper plane radical,
`⟨z(e₁), w(e₁)⟩_bad − ⟨z(e₂), w(e₂)⟩_bad = 1/3 · ⟨σ (coord z), coord w⟩_apolar`. -/
theorem badLineKostantValue_eq (n : ℕ) (positive : 0 < n)
    (z : crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl))
    (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    kostantValue (badDualForm n) (z.val (integralRadicalGenerator 0))
        (z.val (integralRadicalGenerator 1)) (w radicalLatticeSecond) (w radicalLatticeFirst) =
      (1 / 3 : ℂ) * binApolar (n + 1)
        (binarySwapVar (n + 1) (explicitRadicalBinaryEquiv n positive
          ((crossedBoundaries ((standardBadLineRepresentation n).comp
            SemidirectProduct.inl)).mkQ z)))
        (upperRadicalCocycleCoordinate n w) := by
  obtain ⟨pair, hpair⟩ := standardRadicalH1_binaryPair_representative n positive
    ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ z)
  have hdiff : explicitBinaryPairCocycle n pair - z ∈
      crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl) := by
    rw [← Submodule.Quotient.eq]
    exact hpair
  obtain ⟨v, hv⟩ := hdiff
  -- the generator values of `z`
  have hz : ∀ i : Fin 2, z.val (integralRadicalGenerator i) =
      binaryHomogeneousEmbedding n (if i = 0 then pair.1 else pair.2) +
        (rationalCoefficientComponent n trivialCharacter (radicalGenerator i) (-v) - (-v)) := by
    intro i
    have h1 := congrArg (fun c => c.val (integralRadicalGenerator i)) hv
    change ((standardBadLineRepresentation n).comp SemidirectProduct.inl)
        (integralRadicalGenerator i) v - v =
      (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) -
        z.val (integralRadicalGenerator i) at h1
    rw [rho_s_generator] at h1
    have h2 : z.val (integralRadicalGenerator i) =
        (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) -
          (rationalCoefficientComponent n trivialCharacter (radicalGenerator i) v - v) := by
      rw [h1]
      abel
    have hE : (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) =
        binaryHomogeneousEmbedding n (if i = 0 then pair.1 else pair.2) :=
      binaryPairRadicalCocycle_generator n pair i
    rw [h2, hE, map_neg]
    abel
  have hw := (oneCocycle_generator_closed (upperRadicalLatticeRep n) w radicalLatticeFirst
    radicalLatticeSecond (Commute.all _ _)).symm
  rw [upperRep_first, upperRep_second] at hw
  have hbd : kostantValue (badDualForm n)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) (-v) - (-v))
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) (-v) - (-v))
      (w radicalLatticeSecond) (w radicalLatticeFirst) = 0 :=
    kostantValue_boundary_left_end (badDualForm n)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0))
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1))
      (rationalCoefficientComponent n trivialCharacter (planeUnipotent 0 1))
      (rationalCoefficientComponent n trivialCharacter (planeUnipotent 1 0))
      (bad_adjoint_first n) (bad_adjoint_second n) (-v) _ _ hw
  have hcoord : explicitRadicalBinaryEquiv n positive
      ((crossedBoundaries ((standardBadLineRepresentation n).comp
        SemidirectProduct.inl)).mkQ z) = binaryPairWedge n pair := by
    rw [← hpair]
    exact explicitBinaryPairCocycle_coordinate n positive pair
  rw [hcoord]
  have hsum := kostantValue_add_left (badDualForm n)
    (binaryHomogeneousEmbedding n (if (0 : Fin 2) = 0 then pair.1 else pair.2))
    (binaryHomogeneousEmbedding n (if (1 : Fin 2) = 0 then pair.1 else pair.2))
    (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) (-v) - (-v))
    (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) (-v) - (-v))
    (w radicalLatticeSecond) (w radicalLatticeFirst)
  have hrewrite := congrArg₂ (fun x y => kostantValue (badDualForm n) x y
    (w radicalLatticeSecond) (w radicalLatticeFirst)) (hz 0) (hz 1)
  refine hrewrite.trans (hsum.trans ?_)
  refine Eq.trans (congrArg (fun t => kostantValue (badDualForm n)
    (binaryHomogeneousEmbedding n (if (0 : Fin 2) = 0 then pair.1 else pair.2))
    (binaryHomogeneousEmbedding n (if (1 : Fin 2) = 0 then pair.1 else pair.2))
    (w radicalLatticeSecond) (w radicalLatticeFirst) + t) hbd) ?_
  refine (add_zero _).trans ?_
  have e0 : (if (0 : Fin 2) = 0 then pair.1 else pair.2) = pair.1 := ite_eq_left rfl
  have e1 : (if (1 : Fin 2) = 0 then pair.1 else pair.2) = pair.2 := ite_eq_right (by decide)
  have hl0 : binaryPolynomialLift (X (0 : Fin 2)) = (X (0 : Fin 3) : Poly) := by
    simp [binaryPolynomialLift]
  have hl1 : binaryPolynomialLift (X (1 : Fin 2)) = (X (1 : Fin 3) : Poly) := by
    simp [binaryPolynomialLift]
  rw [e0, e1]
  unfold kostantValue
  have key : ∀ w1 w2 : HomogeneousPoly n,
      binaryPolynomialRestrict w1.val = pderiv 0 (upperRadicalCocycleCoordinate n w).val →
      binaryPolynomialRestrict w2.val = pderiv 1 (upperRadicalCocycleCoordinate n w).val →
      badDualForm n (binaryHomogeneousEmbedding n pair.1) w1 -
          badDualForm n (binaryHomogeneousEmbedding n pair.2) w2 =
        (1 / 3 : ℂ) * binApolar (n + 1) (binarySwapVar (n + 1) (binaryPairWedge n pair))
          (upperRadicalCocycleCoordinate n w) := by
    intro w1 w2 r1 r2
    rw [badDualForm_embedding, badDualForm_embedding, r1, r2, ← pderiv_lift_zero,
      ← pderiv_lift_one, ← apolarPoly_X_mul, ← apolarPoly_X_mul, binApolar_apply,
      binarySwapVar_wedge_val, map_sub binaryPolynomialLift, map_mul binaryPolynomialLift,
      map_mul binaryPolynomialLift, hl1, hl0, map_sub apolarPoly, LinearMap.sub_apply]
    ring
  exact key _ _ (restrict_upper_first n w) (restrict_upper_second n w)

/-! ### The pairing on cohomology -/

/-- **The Kostant pairing of the bad line**: the cup-product pairing of the first-row radical lattice
`U` with the dual plane radical lattice, in binary coordinates,
`K(c, c') = 1/3 · ⟨σ (coord c), coord c'⟩_apolar`. -/
def badLineKostant (n : ℕ) (positive : 0 < n) :
    BadH1 n →ₗ[ℂ] groupCohomology.H1 (upperRadicalLatticeRep n) →ₗ[ℂ] ℂ :=
  ((1 / 3 : ℂ) • binApolar (n + 1)).compl₁₂
    ((binarySwapVar (n + 1)).comp (explicitRadicalBinaryEquiv n positive).toLinearMap)
    (upperRadicalH1Coordinate n).toLinearMap

/-- The pairing of two classes is `1/3` of the apolar pairing of their coordinates. -/
theorem badLineKostant_apply (n : ℕ) (positive : 0 < n) (c : BadH1 n)
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    badLineKostant n positive c c' =
      (1 / 3 : ℂ) * binApolar (n + 1)
        (binarySwapVar (n + 1) (explicitRadicalBinaryEquiv n positive c))
        (upperRadicalH1Coordinate n c') := rfl

/-- **Evaluation on cocycles**: on the class of a crossed cocycle `z` and a cocycle `w`, the
pairing is `⟨z(e₁), w(e₁)⟩_bad − ⟨z(e₂), w(e₂)⟩_bad`. -/
theorem badLineKostant_mkQ_H1π (n : ℕ) (positive : 0 < n)
    (z : crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl))
    (w : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) :
    badLineKostant n positive
        ((crossedBoundaries ((standardBadLineRepresentation n).comp
          SemidirectProduct.inl)).mkQ z)
        (groupCohomology.H1π (upperRadicalLatticeRep n) w) =
      kostantValue (badDualForm n) (z.val (integralRadicalGenerator 0))
        (z.val (integralRadicalGenerator 1)) (w radicalLatticeSecond) (w radicalLatticeFirst) := by
  rw [badLineKostant_apply, upperRadicalH1Coordinate_apply, badLineKostantValue_eq n positive z w]

/-- **Perfectness, left.** -/
theorem badLineKostant_left_eq_zero (n : ℕ) (positive : 0 < n) {c : BadH1 n}
    (h : ∀ c' : groupCohomology.H1 (upperRadicalLatticeRep n),
      badLineKostant n positive c c' = 0) : c = 0 := by
  have h' : binarySwapVar (n + 1) (explicitRadicalBinaryEquiv n positive c) = 0 := by
    apply binApolar_left_eq_zero
    intro g
    have h1 := h ((upperRadicalH1Coordinate n).symm g)
    rw [badLineKostant_apply, LinearEquiv.apply_symm_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  have h'' : explicitRadicalBinaryEquiv n positive c = 0 := by
    have h2 := congrArg (binarySwapVar (n + 1)) h'
    rwa [binarySwapVar_involutive, map_zero] at h2
  exact (LinearEquiv.map_eq_zero_iff _).mp h''

/-- **Perfectness, right.** -/
theorem badLineKostant_right_eq_zero (n : ℕ) (positive : 0 < n)
    {c' : groupCohomology.H1 (upperRadicalLatticeRep n)}
    (h : ∀ c : BadH1 n, badLineKostant n positive c c' = 0) : c' = 0 := by
  have h' : upperRadicalH1Coordinate n c' = 0 := by
    apply binApolar_right_eq_zero
    intro f
    have h1 := h ((explicitRadicalBinaryEquiv n positive).symm (binarySwapVar (n + 1) f))
    rw [badLineKostant_apply, LinearEquiv.apply_symm_apply, binarySwapVar_involutive] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  exact (LinearEquiv.map_eq_zero_iff _).mp h'

/-- **The Kostant pairing of the bad line as a multiple of the classical invariant pairing**:
`K(c, c') = (n+1)!/3 · ⟨σ coord c, rot (coord' c')⟩`, `⟨ , ⟩ = binaryPairing (n+1)`. -/
theorem badLineKostant_eq_binaryPairing (n : ℕ) (positive : 0 < n) (c : BadH1 n)
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    badLineKostant n positive c c' =
      (1 / 3 : ℂ) * (((n + 1).factorial : ℂ) * BinaryPairing.binaryPairing (n + 1)
        (binarySwapVar (n + 1) (explicitRadicalBinaryEquiv n positive c))
        (swappedUpperCoordinate n c')) := by
  rw [badLineKostant_apply, binApolar_eq_binaryPairing, swappedUpperCoordinate_apply]

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
