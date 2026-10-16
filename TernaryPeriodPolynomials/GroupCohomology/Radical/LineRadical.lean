module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyLine

@[expose] public section


/-!
# `H²(N_L, E)` for a general Levi element `(η, D)`

The table `tab:radical-cohomology` states `H²(N_L, E) = η^{-n-2} det(D)` for the Levi `(η, D)` of the line stabilizer, `η = ±1` and `D ∈ GL₂(ℤ)`
(in the proof `D ∈ Γ₂`).  The library had this only for the diagonal sign group `(η, diag(δ, 1))` (`Statements.AlternatingEven.line_radical_H2`).  Here the action of
the full Levi `(η, D)` on `H²(N_L, Sym^n)` is defined as the pullback along the inverse conjugation of the lattice `N_L ≅ ℤ²` (the row `r ↦ η r D`) with the
coefficient map `ρ(diag(η, D))` -- the same construction as `lineH2Action` for `D = diag(δ,1)` (`lineLeviH2Action_diagonal`) -- and shown to act on the line
`H²(N_L, E) ≅ ℚ` by `η^{-n-2} det(D)` (`lineH2_leviAction`).  The proof is the library's top-cohomology naturality (`explicitQuotientIso_natural`: a lattice
automorphism contributes its determinant) together with the computation that `diag(η, D)` acts on the coinvariants `E_{N_L} = ℚ x^n` by `η^{-n}` (`D`
acts only on `y, z`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Matrix MvPolynomial
noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.R2LineRadical

open TernaryPoly TernaryPoly.LatticeTopCohomology TernaryPoly.RadicalTopCohomology
open TernaryPoly.RadicalFirstCohomologyLattice TernaryPoly.RadicalCoinvariantAlgebra
open TernaryPoly.RelativeStabilizerParameters TernaryPoly.RelativeStabilizerMatrices

/-- The row-vector action `r ↦ η r D` on the line radical `N_L = {1 + r}`, as the column matrix `η • Dᵀ` on the coordinates `(a, b)`. -/
def leviRow (η : ℤˣ) (D : GL2) : GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.mk'' (η.val • D.val.transpose) (by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact (η.isUnit.pow _).mul ((Matrix.isUnit_iff_isUnit_det D.val).mp D.isUnit))

/-- Inverse conjugation of the line radical by the Levi element `diag(η, D)`: `r ↦ η r D`. -/
def lineLeviLattice (η : ℤˣ) (D : GL2) : Lattice ≃* Lattice := matrixLattice (leviRow η D)

theorem line_levi_commute (η : ℤˣ) (D : GL2) (g : Lattice) :
    lineElement η 0 D * lineHom (lineLeviLattice η D g) = lineHom g * lineElement η 0 D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases Int.units_eq_one_or η with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [lineHom, lineElement_val, lineMatrix, lineLeviLattice, leviRow, matrixLattice_coordinates,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The coefficient map `ρ(diag(η, D))` along the inverse conjugation. -/
def lineLeviCoefficientHom (n : ℕ) (η : ℤˣ) (D : GL2) :
    Rep.res (lineLeviLattice η D).toMonoidHom (lineRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (lineElement η 0 D), fun g => by
    change PolynomialGLAction.integralAction n 0 (lineElement η 0 D) *
      PolynomialGLAction.integralAction n 0 (lineHom (lineLeviLattice η D g)) =
      PolynomialGLAction.integralAction n 0 (lineHom g) *
        PolynomialGLAction.integralAction n 0 (lineElement η 0 D)
    rw [← map_mul, ← map_mul, line_levi_commute]⟩

/-- **The action of the line Levi `(η, D)` on `H²(N_L, E)`** (degree two group cohomology of the lattice `N_L`). -/
def lineLeviH2Action (n : ℕ) (η : ℤˣ) (D : GL2) :
    groupCohomology (lineRep n) 2 ⟶ groupCohomology (lineRep n) 2 :=
  groupCohomology.map (lineLeviLattice η D).toMonoidHom (lineLeviCoefficientHom n η D) 2

theorem latticeDeterminant_lineLevi (η : ℤˣ) (D : GL2) :
    (latticeDeterminant (lineLeviLattice η D) : ℚ) = (D.val.det : ℚ) := by
  have : latticeDeterminant (lineLeviLattice η D) = D.val.det := by
    unfold lineLeviLattice
    rw [latticeDeterminant_matrixLattice]
    change (η.val • D.val.transpose).det = _
    rw [Matrix.det_smul, Matrix.det_transpose]
    rcases Int.units_eq_one_or η with rfl | rfl <;> simp
  rw [this]

theorem lineElement_inv (η : ℤˣ) (D : GL2) : (lineElement η 0 D)⁻¹ = lineElement η⁻¹ 0 D⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul]
  have hD : D.val * (D⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h00 := congrFun (congrFun hD 0) 0
  have h01 := congrFun (congrFun hD 0) 1
  have h10 := congrFun (congrFun hD 1) 0
  have h11 := congrFun (congrFun hD 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero, Matrix.GeneralLinearGroup.coe_inv] at h00 h01 h10 h11
  ext i j
  rw [Matrix.mul_apply]
  rcases Int.units_eq_one_or η with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [lineElement_val, lineMatrix, Fin.sum_univ_three] <;>
    assumption

theorem lineEvalAlg_substitute_levi (η : ℤˣ) (D : GL2) (f : PolynomialGLAction.Poly) :
    lineEvalAlg (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement η 0 D)).val f) =
      unaryDiagonal (unitScalar η) (lineEvalAlg f) := by
  have h : lineEvalAlg.comp (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement η 0 D)).val) =
      (unaryDiagonal (unitScalar η)).comp lineEvalAlg := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [lineEvalAlg, PolynomialGLAction.substitute_X, PolynomialGLAction.linearForm, Fin.sum_univ_three,
        unaryDiagonal, Matrix.map, lineElement_val, lineMatrix, unitScalar]
  exact DFunLike.congr_fun h f

theorem lineEval_integralAction_levi (n : ℕ) (η : ℤˣ) (D : GL2) (p : H n) :
    (lineEval n (PolynomialGLAction.integralAction n 0 (lineElement η 0 D) p) : MvPolynomial (Fin 1) ℚ) =
      unaryDiagonal (unitScalar η⁻¹) (lineEval n p) := by
  rw [lineEval_coe, PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_smul]
  rw [← map_inv, lineElement_inv]
  exact lineEvalAlg_substitute_levi η⁻¹ D⁻¹ (p : PolynomialGLAction.Poly)

/-- The coinvariant `E_{N_L} = ℚ x^n` is multiplied by `η^{-n}` by `diag(η, D)`, for every `D`. -/
theorem lineScalar_integralAction_levi (n : ℕ) (η : ℤˣ) (D : GL2) (p : H n) :
    unaryScalarEquiv n (lineEval n (PolynomialGLAction.integralAction n 0 (lineElement η 0 D) p)) =
      unitScalar η⁻¹ ^ n * unaryScalarEquiv n (lineEval n p) := by
  change (_ : MvPolynomial (Fin 1) ℚ).coeff (Finsupp.single (0 : Fin 1) n) = _
  rw [lineEval_integralAction_levi, unaryDiagonal_homogeneous, coeff_smul]
  rfl

/-- The identification `H²(N_L, E) ≅ ℚ` of `Statements.AlternatingEven.line_radical_H2`. -/
def lineH2Equiv (n : ℕ) : groupCohomology (lineRep n) 2 ≃ₗ[ℚ] ℚ :=
  (lineH2Iso n).toLinearEquiv.trans (actualLineScalarEquiv n)

/-- **`H²` column of `tab:radical-cohomology`, line radical, general Levi.**  The Levi element `(η, D)` with `η = ±1` and any
`D ∈ GL₂(ℤ)` (in particular `D ∈ Γ₂`) acts on `H²(N_L, E) ≅ ℚ` by `η^{-n-2} det(D)`. -/
theorem lineH2_leviAction (n : ℕ) (η : ℤˣ) (D : GL2) (v : groupCohomology (lineRep n) 2) :
    lineH2Equiv n (lineLeviH2Action n η D v) =
      (unitScalar η⁻¹ ^ (n + 2) * (D.val.det : ℚ)) * lineH2Equiv n v := by
  change actualLineScalarEquiv n ((lineH2Iso n).hom (lineLeviH2Action n η D v)) =
    _ * actualLineScalarEquiv n ((lineH2Iso n).hom v)
  change actualLineScalarEquiv n (lineQuotientCoordinates n ((explicitQuotientIso (lineRep n)).hom
      (groupCohomology.map (lineLeviLattice η D).toMonoidHom (lineLeviCoefficientHom n η D) 2 v))) =
    _ * actualLineScalarEquiv n (lineQuotientCoordinates n ((explicitQuotientIso (lineRep n)).hom v))
  rw [explicitQuotientIso_natural, map_zsmul]
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective (relations (lineRep n))
    ((explicitQuotientIso (lineRep n)).hom v)
  rw [← hp]
  have h1 : lineQuotientCoordinates n (quotientCoefficientMap (lineLeviLattice η D)
      (lineLeviCoefficientHom n η D) (Submodule.Quotient.mk p)) =
      Submodule.Quotient.mk (PolynomialGLAction.integralAction n 0 (lineElement η 0 D) p) := rfl
  rw [map_zsmul, h1]
  have h2 : lineQuotientCoordinates n (Submodule.Quotient.mk p) = Submodule.Quotient.mk p := rfl
  rw [h2, actualLineScalarEquiv_mk, actualLineScalarEquiv_mk, lineScalar_integralAction_levi,
    ← Int.cast_smul_eq_zsmul ℚ, latticeDeterminant_lineLevi, smul_eq_mul, pow_add]
  have h3 : unitScalar η⁻¹ ^ 2 = 1 := by
    rcases Int.units_eq_one_or η with rfl | rfl <;> simp [unitScalar]
  rw [h3]
  ring

/-- The diagonal sign `diag(δ, 1) ∈ GL₂(ℤ)`. -/
def diagSign (δ : ℤˣ) : GL2 :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal ![δ.val, 1]) (by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_two])

theorem det_diagSign (δ : ℤˣ) : (diagSign δ).val.det = δ.val := by
  change (Matrix.diagonal ![δ.val, 1]).det = _
  simp [Matrix.det_diagonal, Fin.prod_univ_two]

/-- **The general Levi action restricts to the library's diagonal action**: `(η, diag(δ,1))` acts as `lineH2Action n (η, δ)`. -/
theorem lineLeviH2Action_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) (v : groupCohomology (lineRep n) 2) :
    lineLeviH2Action n ε.1 (diagSign ε.2) v = lineH2Action n ε v := by
  apply (lineH2Equiv n).injective
  rw [lineH2_leviAction, det_diagSign]
  symm
  have h := lineH2Iso_action n ε v
  change actualLineScalarEquiv n ((lineH2Iso n).hom (lineH2Action n ε v)) = _
  rw [h, map_smul, lineQuotientDiagonal_intertwine, lineRootDual_formula, smul_eq_mul, ← mul_assoc]
  change _ = _ * actualLineScalarEquiv n ((lineH2Iso n).hom v)
  congr 1
  simp only [unitScalar]
  ring

/-- The independent integral line sign `η` (`D = 1`) acts by `η^{-n-2}`; for the central sign this is `η^n`. -/
theorem lineH2_lineSign (n : ℕ) (η : ℤˣ) (v : groupCohomology (lineRep n) 2) :
    lineH2Equiv n (lineLeviH2Action n η 1 v) = unitScalar η⁻¹ ^ (n + 2) * lineH2Equiv n v := by
  rw [lineH2_leviAction]
  simp

end TernaryPeriodPolynomials.Argument.Identities.R2LineRadical
