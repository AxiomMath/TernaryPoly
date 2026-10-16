module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeFour
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseMetric
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Normalization
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseContraction
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseAdjoint
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Hodge
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Exterior
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Basepoint
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Adjoint

@[expose] public section



/-! Degree-three basepoint adjointness between `symmetricExterior n 3` and `symmetricContraction n 3`,
transported to every point of the positive cone, mirroring the original authors' degree-two file
`PolynomialFormGeometricEnergyBaseAdjoint.lean`/`...Adjoint.lean` one level up (and structurally
parallel to `AdjointFour.lean`'s own degree-four transport, one level further still). This is the
basepoint-adjointness half (piece A) that both clauses of `coercivity_compact_support`
(`a : Core n 3` and `a : Core n 4`) depend on: the degree-3 clause needs it directly, the degree-4
clause needs it via `AdjointFour.lean`'s own machinery.

The array-form degree-four `formPairing` collapse lemma `formPairing_basepoint_four_coords` and the
coordinate-reindexing map `fourArrowEquiv` mirror `threeArrowEquiv`/`formPairing_basepoint_three`
one degree up; `baseFourCoordinates` mirrors `baseThreeCoordinates`; the basepoint identities
`symmetricExterior_three_apply/_basepoint`, `symmetricContraction_four_basepoint`, and the two bridge
lemmas mirror their degree-two namesakes; `symmetricExterior_three_basepoint_adjoint` mirrors
`symmetricExterior_two_basepoint_adjoint`'s exact seven-step rewrite chain substituting the new
degree-four array machinery from `HodgeFour.lean`; `symmetricExterior_three_adjoint` transports it to
every point of the positive cone exactly as `symmetricExterior_four_adjoint` does one level up. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive

/-- The coordinate-tuple-to-quadruple identification on `Fin 4 → α`, mirroring `threeArrowEquiv`
one degree up. -/
def fourArrowEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

def baseFourCoordinates {n : ℕ} (a : FormValue n 4) : FourCoordinates :=
  fun i j k l => (a ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]).val

/-- The array-form collapse of `formPairing` at degree four, mirroring `formPairing_basepoint_three`
one degree up via `fourArrowEquiv` in place of `threeArrowEquiv`. -/
theorem formPairing_basepoint_four_coords (n : ℕ) (a b : FormValue n 4) :
    formPairing n 4 (coordinateChart basepoint) a b =
      fourPairing (baseFourCoordinates a) (baseFourCoordinates b) := by
  rw [formPairing_basepoint_frame]
  have he := (fourArrowEquiv (Fin 5)).symm.sum_comp
    (fun I : Fin 4 → Fin 5 => (∏ r, tangentWeight (I r)) *
      factorialPairing (a (fun r => baseFrame (I r))).val (b (fun r => baseFrame (I r))).val)
  rw [← he, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  unfold fourPairing baseFourCoordinates
  apply congrArg ((1 / 24 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hv : (fun r : Fin 4 => baseFrame ((fourArrowEquiv (Fin 5)).symm (i, j, k, l) r)) =
      ![baseFrame i, baseFrame j, baseFrame k, baseFrame l] := by
    funext r; fin_cases r <;> rfl
  rw [hv]
  change (∏ r : Fin 4, tangentWeight (![i, j, k, l] r)) * _ = _
  simp [Fin.prod_univ_succ, mul_assoc]

/-- The three `IsAlternatingFour` relations for the base-frame coordinates of an actual degree-four
form value, mirroring `baseThreeCoordinates_alternating`'s two swap-based clauses (clauses 1/2, swap
chains on the first three slots) plus a third, new three-swap chain moving the last slot to the
front (clause 3), using the sign/permutation decomposition verified for `IsAlternatingFour`'s own
clause 3: `(0,3)` then `(1,3)` then `(2,3)`. -/
theorem baseFourCoordinates_alternating {n : ℕ} (a : FormValue n 4) :
    IsAlternatingFour (baseFourCoordinates a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    have h := a.toAlternatingMap.map_swap ![baseFrame j, baseFrame i, baseFrame k, baseFrame l]
      (show (0 : Fin 4) ≠ 1 by decide)
    have he : (![baseFrame j, baseFrame i, baseFrame k, baseFrame l] ∘ Equiv.swap (0 : Fin 4) 1) =
        ![baseFrame i, baseFrame j, baseFrame k, baseFrame l] := by
      funext r; fin_cases r <;> rfl
    rw [he] at h
    exact congrArg Subtype.val h
  · intro i j k l
    have h := a.toAlternatingMap.map_swap ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]
      (show (0 : Fin 4) ≠ 2 by decide)
    have he : (![baseFrame i, baseFrame j, baseFrame k, baseFrame l] ∘ Equiv.swap (0 : Fin 4) 2) =
        ![baseFrame k, baseFrame j, baseFrame i, baseFrame l] := by
      funext r; fin_cases r <;> rfl
    rw [he] at h
    have g := a.toAlternatingMap.map_swap ![baseFrame k, baseFrame j, baseFrame i, baseFrame l]
      (show (1 : Fin 4) ≠ 2 by decide)
    have ge : (![baseFrame k, baseFrame j, baseFrame i, baseFrame l] ∘ Equiv.swap (1 : Fin 4) 2) =
        ![baseFrame k, baseFrame i, baseFrame j, baseFrame l] := by
      funext r; fin_cases r <;> rfl
    rw [ge, h, neg_neg] at g
    exact congrArg Subtype.val g.symm
  · intro i j k l
    have h1 := a.toAlternatingMap.map_swap ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]
      (show (0 : Fin 4) ≠ 3 by decide)
    have he1 : (![baseFrame i, baseFrame j, baseFrame k, baseFrame l] ∘ Equiv.swap (0 : Fin 4) 3) =
        ![baseFrame l, baseFrame j, baseFrame k, baseFrame i] := by
      funext r; fin_cases r <;> rfl
    rw [he1] at h1
    have h2 := a.toAlternatingMap.map_swap ![baseFrame l, baseFrame j, baseFrame k, baseFrame i]
      (show (1 : Fin 4) ≠ 3 by decide)
    have he2 : (![baseFrame l, baseFrame j, baseFrame k, baseFrame i] ∘ Equiv.swap (1 : Fin 4) 3) =
        ![baseFrame l, baseFrame i, baseFrame k, baseFrame j] := by
      funext r; fin_cases r <;> rfl
    rw [he2, h1, neg_neg] at h2
    have h3 := a.toAlternatingMap.map_swap ![baseFrame l, baseFrame i, baseFrame k, baseFrame j]
      (show (2 : Fin 4) ≠ 3 by decide)
    have he3 : (![baseFrame l, baseFrame i, baseFrame k, baseFrame j] ∘ Equiv.swap (2 : Fin 4) 3) =
        ![baseFrame l, baseFrame i, baseFrame j, baseFrame k] := by
      funext r; fin_cases r <;> rfl
    rw [he3, h2] at h3
    have h4 := congrArg Neg.neg h3
    rw [neg_neg] at h4
    exact congrArg Subtype.val h4.symm

theorem symmetricExterior_three_apply (n : ℕ) (x : Coordinates) (a : FormValue n 3)
    (u v w z : Coordinates) :
    symmetricExterior n 3 x a ![u, v, w, z] =
      symmetricPart n x u (a ![v, w, z]) - symmetricPart n x v (a ![u, w, z]) +
        symmetricPart n x w (a ![u, v, z]) - symmetricPart n x z (a ![u, v, w]) := by
  have h1 : Fin.removeNth (1 : Fin 4) ![u, v, w, z] = ![u, w, z] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u, v, w, z] = ![u, v, z] := by
    ext j; fin_cases j <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u, v, w, z] = ![u, v, w] := by
    ext j; fin_cases j <;> rfl
  simp [symmetricExterior_apply, Fin.sum_univ_succ, h1, h2, h3, sub_eq_add_neg, add_assoc]

/-- The same exact one-half factor applies to the actual degree-three exterior term. -/
theorem symmetricExterior_three_basepoint (n : ℕ) (a : FormValue n 3) (i j k l : Fin 5) :
    (symmetricExterior n 3 (coordinateChart basepoint) a
      ![baseFrame i, baseFrame j, baseFrame k, baseFrame l]).val =
      (1 / 2 : ℝ) • exteriorThree (baseThreeCoordinates a) i j k l := by
  rw [symmetricExterior_three_apply, symmetricPart_baseFrame, symmetricPart_baseFrame,
    symmetricPart_baseFrame, symmetricPart_baseFrame]
  simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, coefficientInfinitesimal_apply, exteriorThree, baseThreeCoordinates]
  module

/-- The actual degree-four contraction agrees with the algebraic contraction at scale one
half, mirroring `symmetricContraction_three_basepoint` one degree up. -/
theorem symmetricContraction_four_basepoint (n : ℕ) (a : FormValue n 4) (i j k : Fin 5) :
    (symmetricContraction n 3 (coordinateChart basepoint) a
      ![baseFrame i, baseFrame j, baseFrame k]).val =
      (1 / 2 : ℝ) • contractionFour (baseFourCoordinates a) i j k := by
  rw [symmetricContraction_basepoint_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, coefficientInfinitesimal_apply,
    contractionFour, baseFourCoordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  module

theorem baseFourCoordinates_symmetricExterior (n : ℕ) (a : FormValue n 3) :
    baseFourCoordinates (symmetricExterior n 3 (coordinateChart basepoint) a) =
      (1 / 2 : ℝ) • exteriorThree (baseThreeCoordinates a) := by
  funext i j k l
  exact symmetricExterior_three_basepoint n a i j k l

theorem baseThreeCoordinates_symmetricContraction (n : ℕ) (a : FormValue n 4) :
    baseThreeCoordinates (symmetricContraction n 3 (coordinateChart basepoint) a) =
      (1 / 2 : ℝ) • contractionFour (baseFourCoordinates a) := by
  funext i j k
  exact symmetricContraction_four_basepoint n a i j k

/-- Literal basepoint adjointness between `symmetricExterior n 3` and `symmetricContraction n 3`,
mirroring `symmetricExterior_two_basepoint_adjoint`'s exact seven-step rewrite chain one degree up. -/
theorem symmetricExterior_three_basepoint_adjoint (n : ℕ) (a : FormValue n 3) (b : FormValue n 4) :
    formPairing n 4 (coordinateChart basepoint) (symmetricExterior n 3 (coordinateChart basepoint) a) b =
      formPairing n 3 (coordinateChart basepoint) a (symmetricContraction n 3 (coordinateChart basepoint) b) := by
  rw [formPairing_basepoint_four_coords, formPairing_basepoint_three, baseFourCoordinates_symmetricExterior,
    fourPairing_smul_left, exteriorThree_contractionFour_adjoint _ _ (baseFourCoordinates_alternating b),
    baseThreeCoordinates_symmetricContraction, threePairing_smul_right]

/-- Transport of the degree-three basepoint adjointness to every point of the positive cone,
mirroring `symmetricExterior_four_adjoint`'s calc proof one degree down. -/
theorem symmetricExterior_three_adjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n 3) (b : FormValue n 4) :
    formPairing n 4 x (symmetricExterior n 3 x a) b =
      formPairing n 3 x a (symmetricContraction n 3 x b) := by
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let c := realFormPullback n 3 g y a
  let d := realFormPullback n 4 g y b
  have hc := realFormPullback_spec n 3 g y a
  have hd := realFormPullback_spec n 4 g y b
  calc
    formPairing n 4 (coordinateAction g y) (symmetricExterior n 3 (coordinateAction g y) a) b =
        formPairing n 4 y (symmetricExterior n 3 y c) d :=
      formPairing_real n 4 g hg y hy _ _ _ _ (symmetricExterior_real n 3 g hg y hy a c hc) hd
    _ = formPairing n 3 y c (symmetricContraction n 3 y d) :=
      symmetricExterior_three_basepoint_adjoint n c d
    _ = formPairing n 3 (coordinateAction g y) a (symmetricContraction n 3 (coordinateAction g y) b) :=
      (formPairing_real n 3 g hg y hy _ _ _ _ hc
        (symmetricContraction_real n 3 g hg y hy b d hd)).symm

end TernaryPeriodPolynomials.Argument.Coercivity
