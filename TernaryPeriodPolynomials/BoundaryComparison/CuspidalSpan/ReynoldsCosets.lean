module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlaneLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralAdelicNorm

@[expose] public section


/-!
# The eight-coset covering lemma for `PlaneLeviLevel`

Pure algebra (no `CuspidalRepresentation` yet): `GL₂(ℤ̂)` is covered by exactly eight right
`PlaneLeviLevel`-cosets, represented by eight integer matrices of determinant one whose bottom
rows mod three exhaust the nonzero vectors of `(ZMod 3)²`. This is the combinatorial engine
behind the Reynolds averaging operator built in `ReynoldsAverage.lean`.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binary_det_map)

/-- The bottom row of a `GL₂(ZMod 3)` element, as a pair. -/
def bottomRow3 (κ : GeneralLinearGroup (Fin 2) (ZMod 3)) : ZMod 3 × ZMod 3 :=
  (κ.val 1 0, κ.val 1 1)

/-- Reduction mod three of an adelic `GL₂` element.
-/
abbrev red (g : GeneralLinearGroup (Fin 2) IntegralAdeles) : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  GeneralLinearGroup.map integralReduction g

theorem red_mul (g h : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    red (g * h) = red g * red h := GeneralLinearGroup.map_mul integralReduction g h

theorem red_inv (g : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    red g⁻¹ = (red g)⁻¹ := GeneralLinearGroup.map_inv integralReduction g

/-- `PlaneLeviLevel` is exactly "bottom row mod three is `(0,1)`". -/
theorem planeLeviLevel_iff (κ : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    PlaneLeviLevel κ ↔ bottomRow3 (red κ) = (0, 1) := by
  simp only [PlaneLeviLevel, bottomRow3, Prod.mk.injEq]

/-- Row 1 of a matrix product, in terms of row 1 of the left factor. -/
theorem matrix_mul_apply_one {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (j : Fin 2) : (A * B) 1 j = A 1 0 * B 0 j + A 1 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The `GL₂` version of `matrix_mul_apply_one`. -/
theorem gl_mul_apply_one {R : Type*} [CommRing R] (κ μ : GeneralLinearGroup (Fin 2) R)
    (j : Fin 2) : (κ * μ).val 1 j = κ.val 1 0 * μ.val 0 j + κ.val 1 1 * μ.val 1 j := by
  rw [Units.val_mul]
  exact matrix_mul_apply_one κ.val μ.val j

/-- **Coset criterion.** Two `GL₂(ZMod 3)` elements have the same bottom row iff `g * h⁻¹`'s
bottom row is `(0,1)`. -/
theorem bottomRow3_eq_iff (g h : GeneralLinearGroup (Fin 2) (ZMod 3)) :
    bottomRow3 (g * h⁻¹) = ((0 : ZMod 3), (1 : ZMod 3)) ↔ bottomRow3 g = bottomRow3 h := by
  simp only [bottomRow3, Prod.mk.injEq]
  constructor
  · rintro ⟨hg0, hg1⟩
    have hassoc : (g * h⁻¹) * h = g := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have hval0 : ((g * h⁻¹) * h).val 1 0 = h.val 1 0 := by
      rw [gl_mul_apply_one (g * h⁻¹) h 0, hg0, hg1]; ring
    have hval1 : ((g * h⁻¹) * h).val 1 1 = h.val 1 1 := by
      rw [gl_mul_apply_one (g * h⁻¹) h 1, hg0, hg1]; ring
    rw [hassoc] at hval0 hval1
    exact ⟨hval0, hval1⟩
  · rintro ⟨hg0, hg1⟩
    have e0 : (g * h⁻¹).val 1 0 = (h * h⁻¹).val 1 0 := by
      rw [gl_mul_apply_one g h⁻¹ 0, gl_mul_apply_one h h⁻¹ 0, hg0, hg1]
    have e1 : (g * h⁻¹).val 1 1 = (h * h⁻¹).val 1 1 := by
      rw [gl_mul_apply_one g h⁻¹ 1, gl_mul_apply_one h h⁻¹ 1, hg0, hg1]
    rw [mul_inv_cancel, Units.val_one] at e0 e1
    refine ⟨?_, ?_⟩
    · rw [e0]; exact Matrix.one_apply_ne (by decide)
    · rw [e1]; exact Matrix.one_apply_eq 1

/-- **Nonzero bottom row.** The bottom row of the mod-three reduction of any `GL₂(ℤ̂)` element is
never `(0,0)`: else its determinant would reduce to `0`, contradicting that it is a unit. -/
theorem bottomRow3_red_ne_zero (g : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    bottomRow3 (red g) ≠ (0, 0) := by
  intro hz
  have h0 : (red g).val 1 0 = 0 := congrArg Prod.fst hz
  have h1 : (red g).val 1 1 = 0 := congrArg Prod.snd hz
  have hval : (red g).val.det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  have hdet0 : (GeneralLinearGroup.det (red g) : ZMod 3) = 0 := by
    rw [GeneralLinearGroup.val_det_apply]; exact hval
  have hdet1 : GeneralLinearGroup.det (red g) =
      Units.map (integralReduction : IntegralAdeles →+* ZMod 3) (GeneralLinearGroup.det g) :=
    binary_det_map integralReduction g
  rw [hdet1] at hdet0
  exact Units.ne_zero _ hdet0

/-- Build a `GL₂(ℤ̂)` element from four integers of determinant one. -/
def ofIntDetOne (a b c d : ℤ) (h : a * d - b * c = 1) :
    GeneralLinearGroup (Fin 2) IntegralAdeles :=
  GeneralLinearGroup.mk''
    (!![(a : IntegralAdeles), (b : IntegralAdeles); (c : IntegralAdeles), (d : IntegralAdeles)])
    (by
      have hd : (!![(a : IntegralAdeles), (b : IntegralAdeles); (c : IntegralAdeles),
          (d : IntegralAdeles)] : Matrix (Fin 2) (Fin 2) IntegralAdeles).det = 1 := by
        rw [Matrix.det_fin_two_of]
        have h' := congrArg (fun z : ℤ => (z : IntegralAdeles)) h
        push_cast at h'
        linear_combination h'
      rw [hd]
      exact isUnit_one)

theorem bottomRow3_red_ofIntDetOne (a b c d : ℤ) (h : a * d - b * c = 1) :
    bottomRow3 (red (ofIntDetOne a b c d h)) = ((c : ZMod 3), (d : ZMod 3)) := by
  simp [bottomRow3, ofIntDetOne, GeneralLinearGroup.map_apply, GeneralLinearGroup.val_mk'']

/-- The eight coset representatives: `SL₂(ℤ)` matrices whose bottom rows mod three are the eight
nonzero vectors of `(ZMod 3)²`. -/
def γ : Fin 8 → GeneralLinearGroup (Fin 2) IntegralAdeles
  | 0 => ofIntDetOne 1 0 0 1 (by norm_num)
  | 1 => ofIntDetOne (-1) 0 0 (-1) (by norm_num)
  | 2 => ofIntDetOne 0 (-1) 1 0 (by norm_num)
  | 3 => ofIntDetOne 0 1 (-1) 0 (by norm_num)
  | 4 => ofIntDetOne 1 0 1 1 (by norm_num)
  | 5 => ofIntDetOne 0 (-1) 1 (-1) (by norm_num)
  | 6 => ofIntDetOne 1 0 (-1) 1 (by norm_num)
  | 7 => ofIntDetOne 0 1 (-1) (-1) (by norm_num)

/-- The literal bottom rows mod three of the eight representatives (the eight nonzero vectors
of `(ZMod 3)²`). -/
def row : Fin 8 → ZMod 3 × ZMod 3
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (1, 0)
  | 3 => (2, 0)
  | 4 => (1, 1)
  | 5 => (1, 2)
  | 6 => (2, 1)
  | 7 => (2, 2)

theorem bottomRow3_gamma (i : Fin 8) : bottomRow3 (red (γ i)) = row i := by
  fin_cases i <;> simp [γ, row, bottomRow3_red_ofIntDetOne] <;> decide

/-- `row` is injective. -/
theorem row_injective : ∀ i j : Fin 8, row i = row j → i = j := by decide

/-- `row` hits every nonzero vector of `(ZMod 3)²`. -/
theorem row_surj_nonzero : ∀ v : ZMod 3 × ZMod 3, v ≠ (0, 0) → ∃ i : Fin 8, row i = v := by decide

/-- The eight rows exhaust the nonzero vectors of `(ZMod 3)²`, each exactly once. -/
theorem row_exists_unique : ∀ v : ZMod 3 × ZMod 3, v ≠ (0, 0) → ∃! i : Fin 8, v = row i := by
  intro v hv
  obtain ⟨i, hi⟩ := row_surj_nonzero v hv
  exact ⟨i, hi.symm, fun j hj => row_injective j i (hj.symm.trans hi.symm)⟩

/-- **The covering lemma.** Every `g : GL₂(ℤ̂)` lies in exactly one of the eight
`PlaneLeviLevel`-cosets `H · γ i`. -/
theorem exists_unique_coset (g : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    ∃! i : Fin 8, PlaneLeviLevel (g * (γ i)⁻¹) := by
  have key : ∀ i : Fin 8,
      PlaneLeviLevel (g * (γ i)⁻¹) ↔ bottomRow3 (red g) = bottomRow3 (red (γ i)) := by
    intro i
    rw [planeLeviLevel_iff, red_mul, red_inv, bottomRow3_eq_iff]
  simp only [key, bottomRow3_gamma]
  exact row_exists_unique (bottomRow3 (red g)) (bottomRow3_red_ne_zero g)

end TernaryPeriodPolynomials.Argument.CuspidalSpan
