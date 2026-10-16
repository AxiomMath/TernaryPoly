module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.GoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Binary

@[expose] public section


/-!
# Levi equivariance of the Kostant pairing

The Levi subgroup `GL₂(ℤ)` of the good-line parabolic acts on `H¹(U, V) ≅ Sym^{n+1}` through
`lowerRadicalH1Levi` (the determinant twist `0`), and on the dual factor `H¹(U^φ, V)` of the
identity plane through `upperRadicalH1Levi` (the twist `-1`).  The apolar pairing of binary forms is
invariant under the pair `(g, g^{-T})`: for `γ γ'ᵀ = 1`,

  `⟨γ ⋆ f, γ' ⋆ g⟩ = det(γ)^τ det(γ')^τ' ⟨f, g⟩`     (`binApolar_homogeneousAction`)

for the actions `homogeneousAction N τ` and `homogeneousAction N τ'`.  Consequently the Kostant
pairing of the good line is equivariant for the pair of Levi elements `(m, m')` with `m m'ᵀ = 1`
(`m' = φ(m)` is the image of `m` under the level involution), with the determinant character
`det(m')⁻¹ = det(m)` (`goodLineKostant_levi`).  For a character of the coefficients with
`χ(-1_∞) = -1` the twisted Levi actions are `det m` times the untwisted ones, and the equivariance
is multiplied by the corresponding determinant signs; the radical-level pairing is unchanged.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-- The `3 × 3` matrix acting as `A` on the first two variables and trivially on the third. -/
def extMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

/-- Lifting a binary substitution to the first two ternary variables is the substitution by the
extended matrix. -/
theorem lift_substitute (A : Matrix (Fin 2) (Fin 2) ℂ) (f : Binary.Poly) :
    binaryPolynomialLift (Binary.substitute A f) =
      substitute (extMatrix A) (binaryPolynomialLift f) := by
  have h : binaryPolynomialLift.comp (Binary.substitute A) =
      (substitute (extMatrix A)).comp binaryPolynomialLift := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Binary.substitute_X, binaryPolynomialLift, rename_X,
      substitute_X]
    fin_cases i <;>
      simp [Binary.linearForm, linearForm, extMatrix, Fin.sum_univ_two, Fin.sum_univ_three]
  exact congrArg (fun φ : Binary.Poly →ₐ[ℂ] Poly => φ f) h

/-- If `A Bᵀ = 1` then the extended matrices satisfy the same relation. -/
theorem extMatrix_mul_transpose (A B : Matrix (Fin 2) (Fin 2) ℂ) (h : A * Bᵀ = 1) :
    extMatrix A * (extMatrix B)ᵀ = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination h00
      | linear_combination h01
      | linear_combination h10
      | linear_combination h11

/-- The binary apolar pairing is invariant under `(f, g) ↦ (f ∘ A, g ∘ B)` when `A Bᵀ = 1`. -/
theorem binApolar_substitute (N : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) (h : A * Bᵀ = 1)
    (f g : Binary.HomogeneousPoly N) :
    apolarPoly (binaryPolynomialLift (Binary.substitute A f.val))
        (binaryPolynomialLift (Binary.substitute B g.val)) = binApolar N f g := by
  rw [lift_substitute, lift_substitute]
  exact apolarPoly_substitute _ _ (extMatrix_mul_transpose A B h) _ _

/-- **Invariance of the binary apolar pairing under the Levi actions.**  For `γ γ'ᵀ = 1` and any
determinant twists `τ, τ'`,
`⟨γ ⋆_τ f, γ' ⋆_τ' g⟩ = det(γ)^τ det(γ')^τ' ⟨f, g⟩`. -/
theorem binApolar_homogeneousAction (N : ℕ) (τ τ' : ℤ) (γ γ' : Binary.GL2)
    (h : (γ : Matrix (Fin 2) (Fin 2) ℂ) * (γ' : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1)
    (f g : Binary.HomogeneousPoly N) :
    binApolar N (Binary.homogeneousAction N τ γ f) (Binary.homogeneousAction N τ' γ' g) =
      ((GeneralLinearGroup.det γ : ℂˣ) : ℂ) ^ τ * ((GeneralLinearGroup.det γ' : ℂˣ) : ℂ) ^ τ' *
        binApolar N f g := by
  have hXT : ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ =
      (γ : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h1 : ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) *
        (γ' : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Units.inv_mul γ'
    have h2 : (γ' : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
        ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ
        = 1 * ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := (one_mul _).symm
      _ = ((γ : Matrix (Fin 2) (Fin 2) ℂ) * (γ' : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) *
          ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by rw [h]
      _ = (γ : Matrix (Fin 2) (Fin 2) ℂ) * ((γ' : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
          ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) := mul_assoc _ _ _
      _ = (γ : Matrix (Fin 2) (Fin 2) ℂ) * 1 := by rw [h2]
      _ = (γ : Matrix (Fin 2) (Fin 2) ℂ) := mul_one _
  have hinv : ((γ⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((γ'⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
    rw [hXT]
    exact Units.inv_mul γ
  rw [binApolar_apply, Binary.homogeneousAction_coe, Binary.homogeneousAction_coe,
    Binary.action_apply, Binary.action_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [binApolar_substitute N _ _ hinv f g]
  rw [BinaryPairing.determinantCharacter_apply, BinaryPairing.determinantCharacter_apply]
  ring

/-- The integral Levi matrices `m, m'` with `m m'ᵀ = 1` give complex matrices with the same
relation. -/
theorem map_mul_transpose (m m' : GeneralLinearGroup (Fin 2) ℤ)
    (h : (m : Matrix (Fin 2) (Fin 2) ℤ) * (m' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1) :
    ((GeneralLinearGroup.map (Int.castRingHom ℂ) m : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ) *
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) m' : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 := by
  rw [GeneralLinearGroup.val_map_apply, GeneralLinearGroup.val_map_apply, ← Matrix.transpose_map,
    ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- **Levi equivariance of the Kostant pairing of the good line.**  For `m, m' ∈ GL₂(ℤ)` with
`m m'ᵀ = 1` (so `m'` is the image of `m` under the level involution),
`K(m ⋆ c, m' ⋆ c') = det(m')⁻¹ K(c, c')`, where `m` acts on `H¹(U, V)` through
`lowerRadicalH1Levi` and `m'` on `H¹(U^φ, V)` through `upperRadicalH1Levi`.  Here
`det(m')⁻¹ = det(m)` is the determinant character of the action on `H²(U) = Λ² U^∨`. -/
theorem goodLineKostant_levi (n : ℕ) (positive : 0 < n) (m m' : GeneralLinearGroup (Fin 2) ℤ)
    (h : (m : Matrix (Fin 2) (Fin 2) ℤ) * (m' : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1)
    (c : groupCohomology.H1 (lowerRadicalLatticeRep n))
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    goodLineKostant n positive (lowerRadicalH1Levi n m c) (upperRadicalH1Levi n m' c') =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) m') : ℂˣ) : ℂ) ^
          (-1 : ℤ) * goodLineKostant n positive c c' := by
  have e := binApolar_homogeneousAction (n + 1) 0 (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) m) (GeneralLinearGroup.map (Int.castRingHom ℂ) m')
    (map_mul_transpose m m' h) (lowerRadicalH1Coordinate n positive c)
    (upperRadicalH1Coordinate n c')
  rw [goodLineKostant_apply n positive (lowerRadicalH1Levi n m c) (upperRadicalH1Levi n m' c'),
    lowerRadicalH1Coordinate_equivariant, upperRadicalH1Coordinate_equivariant, e, zpow_zero,
    one_mul, goodLineKostant_apply n positive c c']

/-- **The Kostant pairing of the good line as a multiple of the classical invariant pairing.**
`K(c, c') = (n+1)! · ⟨coord c, rot (coord' c')⟩` where `⟨ , ⟩ = binaryPairing (n+1)` and `rot` is
the rotation `g(x, y) ↦ g(-y, x)` (`binarySwap`). -/
theorem goodLineKostant_eq_binaryPairing (n : ℕ) (positive : 0 < n)
    (c : groupCohomology.H1 (lowerRadicalLatticeRep n))
    (c' : groupCohomology.H1 (upperRadicalLatticeRep n)) :
    goodLineKostant n positive c c' =
      ((n + 1).factorial : ℂ) * BinaryPairing.binaryPairing (n + 1)
        (lowerRadicalH1Coordinate n positive c)
        (binarySwap (n + 1) (upperRadicalH1Coordinate n c')) := by
  rw [goodLineKostant_apply, binApolar_eq_binaryPairing]

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
