module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.GoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitRadical

@[expose] public section


/-!
# The coefficient pairing between the bad-line radical and its dual plane radical

The radical of the stabilizer of the bad line `⟨e₁⟩` is the lattice `U = {I + a E₁₂ + b E₁₃}`; the
level involution `φ(g) = a (g⁻¹)ᵀ a⁻¹` carries it onto the first-column plane radical
`{I − a E₂₁ − 3 b E₃₁}`.  The coefficient pairing `dualPairing` is adjoint between `U` and
`φ(U)⁻¹ = {I + a E₂₁ + 3 b E₃₁}`.  Conjugating by the rational frame
`badFrame = [[0,0,1],[0,1,0],[3,0,0]]` turns `φ(U)⁻¹` into the standard upper plane radical
`{I + b E₁₃ + a E₂₃}` of `upperRadicalLatticeRep` with the two lattice directions exchanged:

  `φ(lineUnipotent a b) · badFrame · planeUnipotent b a = badFrame`     (`badFrame_identity`).

Consequently the bilinear form `badDualForm n (v, w) = ⟨v, ρ(badFrame) w⟩` on ternary forms is
adjoint for the first-row radical and the *upper* plane radical, with the generators exchanged
(`badDualForm_adjoint`):

  `⟨ρ(lineUnipotent a b) v, w⟩ = ⟨v, ρ(planeUnipotent b a) w⟩`.

Its value on a form free of `X₀` is computed by `badDualForm_embedding`:
`⟨P, w⟩ = -1/3 · ⟨P(X₂, X₁), w|_{X₂ = 0}⟩_apolar`, where `P(X₂, X₁)` denotes the exchange of the two
variables of `P`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-! ### Matrices -/

/-- The rational frame `[[0,0,1],[0,1,0],[3,0,0]]` which conjugates the dual radical of the bad
line to the standard upper plane radical. -/
def badFrame : RationalGL3 :=
  ⟨!![0, 0, 1; 0, 1, 0; 3, 0, 0], !![0, 0, 1 / 3; 0, 1, 0; 1, 0, 0], by
    rw [Matrix.mul_fin_three, Matrix.one_fin_three]
    norm_num, by
    rw [Matrix.mul_fin_three, Matrix.one_fin_three]
    norm_num⟩

/-- The level involution of the bad-line radical: `φ(I + aE₁₂ + bE₁₃) = I − aE₂₁ − 3bE₃₁`. -/
theorem dualInvolution_lineUnipotent (a b : ℚ) :
    dualInvolution (lineUnipotent a b : RationalGL3) = lowerLineUnipotent (-a) (-(3 * b)) := by
  have hL : ((levelScale : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 3] := rfl
  have hLi : (((levelScale⁻¹ : RationalGL3)) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 1 / 3] := rfl
  have hT : ((inverseTranspose (lineUnipotent a b : RationalGL3) : RationalGL3) :
      Matrix (Fin 3) (Fin 3) ℚ) = !![1, 0, 0; -a, 1, 0; -b, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  apply Units.ext
  rw [dualInvolution_apply, Units.val_mul, Units.val_mul, hL, hLi, hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, lowerLineUnipotent]

/-- **The frame identity**: `φ(lineUnipotent a b) · badFrame · planeUnipotent b a = badFrame`. -/
theorem badFrame_identity (a b : ℚ) :
    dualInvolution (lineUnipotent a b : RationalGL3) * badFrame * planeUnipotent b a =
      badFrame := by
  rw [dualInvolution_lineUnipotent]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lowerLineUnipotent, badFrame, planeUnipotent]

/-! ### The adjoint form -/

/-- The bilinear form `⟨v, ρ(badFrame) w⟩` on ternary forms of degree `n`. -/
def badDualForm (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ :=
  (dualPairing n).compl₂ (rationalCoefficientComponent n trivialCharacter badFrame)

/-- Unfolding the adjoint form. -/
theorem badDualForm_apply_aux (n : ℕ) (v w : HomogeneousPoly n) :
    badDualForm n v w =
      dualPairing n v (rationalCoefficientComponent n trivialCharacter badFrame w) := rfl

/-- **Adjointness.**  The form is adjoint for the first-row radical (first slot) and the upper plane
radical with the lattice directions exchanged (second slot). -/
theorem badDualForm_adjoint (n : ℕ) (a b : ℚ) (v w : HomogeneousPoly n) :
    badDualForm n (rationalCoefficientComponent n trivialCharacter (lineUnipotent a b) v) w =
      badDualForm n v (rationalCoefficientComponent n trivialCharacter (planeUnipotent b a) w) := by
  have key := dualPairing_invariant n trivialCharacter (lineUnipotent a b) v
    (rationalCoefficientComponent n trivialCharacter badFrame
      (rationalCoefficientComponent n trivialCharacter (planeUnipotent b a) w))
  have e : rationalCoefficientComponent n trivialCharacter
      (dualInvolution (lineUnipotent a b : RationalGL3))
      (rationalCoefficientComponent n trivialCharacter badFrame
        (rationalCoefficientComponent n trivialCharacter (planeUnipotent b a) w)) =
      rationalCoefficientComponent n trivialCharacter badFrame w := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, badFrame_identity]
  rw [e] at key
  exact key

/-! ### Evaluation of the frame on polynomials -/

/-- The complex matrix `[[0,0,1/3],[0,1,0],[1,0,0]]` of the substitution induced by `badFrame`. -/
def badFrameMatrix : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1 / 3; 0, 1, 0; 1, 0, 0]

/-- The permutation matrix exchanging the first and third variables. -/
def permMatrix : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem complexify_badFrame_inv_val :
    (((complexify badFrame)⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) = badFrameMatrix := by
  rw [← map_inv]
  simp only [complexify, MonoidHom.comp_apply, GeneralLinearGroup.val_map_apply]
  have h : ((badFrame⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 0, 1 / 3; 0, 1, 0; 1, 0, 0] := rfl
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [badFrameMatrix]

theorem complexify_badFrame_val :
    ((complexify badFrame : GL3) : Matrix (Fin 3) (Fin 3) ℂ) = !![0, 0, 1; 0, 1, 0; 3, 0, 0] := by
  simp only [complexify, MonoidHom.comp_apply, GeneralLinearGroup.val_map_apply]
  have h : ((badFrame : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 0, 1; 0, 1, 0; 3, 0, 0] := rfl
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coefficient scalar of `badFrame` is `det⁻¹ = -1/3`. -/
theorem coefficientScalar_badFrame : coefficientScalar trivialCharacter badFrame = -1 / 3 := by
  have hdet : ((GeneralLinearGroup.det (complexify badFrame) : ℂˣ) : ℂ) = -3 := by
    rw [GeneralLinearGroup.val_det_apply, complexify_badFrame_val, Matrix.det_fin_three]
    simp
  have h1 : componentCharacter trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) badFrame) = 1 := rfl
  rw [coefficientScalar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1,
    one_mul]
  change ((GeneralLinearGroup.det (complexify badFrame) : ℂˣ) : ℂ) ^ (-1 : ℤ) = -1 / 3
  rw [hdet, zpow_neg_one]
  norm_num

/-- The action of `badFrame` on forms: `ρ(badFrame) w = -1/3 · w(X₂/3, X₁, X₀)`. -/
theorem rho_badFrame_val (n : ℕ) (w : HomogeneousPoly n) :
    ((rationalCoefficientComponent n trivialCharacter badFrame w : HomogeneousPoly n) : Poly) =
      (-1 / 3 : ℂ) • substitute badFrameMatrix w.val := by
  rw [rationalCoefficientComponent_coe, coefficientScalar_badFrame, complexify_badFrame_inv_val]

theorem badFrameMatrix_mul_scale : badFrameMatrix * complexLevelScale = permMatrix := by
  rw [complexLevelScale_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [badFrameMatrix, permMatrix, Matrix.mul_apply, Matrix.diagonal_apply]

theorem permMatrix_mul_transpose : permMatrix * permMatrixᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem permMatrix_mul_self : permMatrix * permMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem substitute_perm_perm (f : Poly) :
    substitute permMatrix (substitute permMatrix f) = f := by
  have h := congrArg (fun φ : Poly →ₐ[ℂ] Poly => φ f)
    (substitute_comp permMatrix permMatrix)
  simp only [AlgHom.comp_apply, permMatrix_mul_self, substitute_one, AlgHom.id_apply] at h
  exact h

/-- The apolar pairing is invariant under the exchange of the first and third variables. -/
theorem apolarPoly_perm (P k : Poly) :
    apolarPoly P (substitute permMatrix k) = apolarPoly (substitute permMatrix P) k := by
  have h := apolarPoly_substitute permMatrix permMatrix permMatrix_mul_transpose
    (substitute permMatrix P) k
  rwa [substitute_perm_perm] at h

/-- **The adjoint form in terms of the apolar pairing**:
`⟨v, w⟩_bad = -1/3 · ⟨v, w(X₂, X₁, X₀)⟩_apolar`. -/
theorem badDualForm_apply (n : ℕ) (v w : HomogeneousPoly n) :
    badDualForm n v w = (-1 / 3 : ℂ) * apolarPoly v.val (substitute permMatrix w.val) := by
  rw [badDualForm_apply_aux, dualPairing_apply, apolar_apply, homogeneousSubstitute_coe,
    rho_badFrame_val, map_smul, map_smul, smul_eq_mul, ← AlgHom.comp_apply, substitute_comp,
    badFrameMatrix_mul_scale]

/-! ### Forms free of `X₀` -/

/-- The exchange of the two binary variables, as a matrix. -/
def swap01 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem linearForm_swap01_zero : Binary.linearForm swap01 0 = (X 1 : Binary.Poly) := by
  simp [Binary.linearForm, swap01, Fin.sum_univ_two]

theorem linearForm_swap01_one : Binary.linearForm swap01 1 = (X 0 : Binary.Poly) := by
  simp [Binary.linearForm, swap01, Fin.sum_univ_two]

/-- The exchange of the third variable with the first sends the embedded binary form
`p(X₁, X₂)` to the lifted form `p(X₁, X₀)`. -/
theorem substitute_perm_embedding (p : Binary.Poly) :
    substitute permMatrix (binaryPolynomialEmbedding p) =
      binaryPolynomialLift (Binary.substitute swap01 p) := by
  have h : (substitute permMatrix).comp binaryPolynomialEmbedding =
      binaryPolynomialLift.comp (Binary.substitute swap01) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, binaryPolynomialEmbedding, binaryPolynomialLift, rename_X,
      substitute_X, Binary.substitute_X]
    fin_cases i <;>
      simp [linearForm, Binary.linearForm, permMatrix, swap01, Fin.sum_univ_three,
        Fin.sum_univ_two]
  exact congrArg (fun φ : Binary.Poly →ₐ[ℂ] Poly => φ p) h

/-- **The adjoint form against a binary form embedded in the variables `X₁, X₂`.** -/
theorem badDualForm_embedding (n : ℕ) (p : Binary.HomogeneousPoly n) (w : HomogeneousPoly n) :
    badDualForm n (binaryHomogeneousEmbedding n p) w =
      (-1 / 3 : ℂ) * apolarPoly (binaryPolynomialLift (Binary.substitute swap01 p.val))
        (binaryPolynomialLift (binaryPolynomialRestrict w.val)) := by
  rw [badDualForm_apply, apolarPoly_perm]
  change (-1 / 3 : ℂ) * apolarPoly (substitute permMatrix (binaryPolynomialEmbedding p.val))
    w.val = _
  rw [substitute_perm_embedding,
    apolarPoly_eq_restrict (binaryPolynomialLift_pderiv_third _) w.val]

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
