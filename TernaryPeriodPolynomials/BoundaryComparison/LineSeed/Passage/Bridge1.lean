module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Face
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.ConjRel
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusRep

@[expose] public section


/-!
# The pivot embedding `Γ(N) ∩ Q(ℤ) → Λ₁⁺` (Passage bridge, part 1)

`rev3 x` is the matrix `x` with its rows and columns reversed (conjugation by the pivot `Π = (e₁ ↔ e₃)`), an element of `SL₃(ℤ)`; `mapGL ℚ (rev3 x) = Π (mapGL ℚ x) Π`.  For `x ∈ Γ(N) ∩ Q(ℤ)` (`3 ∣ N`)
it lies in the good-line stabilizer, with Levi block of determinant one, so `piMap N h3 : Γ(N) ∩ Q(ℤ) →* Λ₁⁺`.  The line data of `Λ₁⁺` along `piMap` is the line data of `Γ(N) ∩ Q(ℤ)`
(`linePlusLam_piMap`, `linePlusV_piMap`, `linePlusData_lmat_piMap`): the pivot of `Λ₁⁺` was chosen to reverse the Levi block and the bottom row, which is exactly conjugation by `Π`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c (levelPrincipal_le mapGL_mem_levelPrincipal SL2Z)

/-- Conjugation of `SL₃(ℤ)` by the pivot permutation `e₁ ↔ e₃`: reversal of rows and columns. -/
def rev3 : SL(3, ℤ) →* SL(3, ℤ) where
  toFun x := ⟨(x : Matrix (Fin 3) (Fin 3) ℤ).submatrix Fin.revPerm Fin.revPerm, by
    rw [Matrix.det_submatrix_equiv_self Fin.revPerm]; exact x.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fin.revPerm, Fin.rev]
  map_mul' x y := by
    apply Subtype.ext
    change ((x * y : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ).submatrix Fin.revPerm Fin.revPerm =
      (x : Matrix (Fin 3) (Fin 3) ℤ).submatrix Fin.revPerm Fin.revPerm *
        (y : Matrix (Fin 3) (Fin 3) ℤ).submatrix Fin.revPerm Fin.revPerm
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact (Matrix.submatrix_mul_equiv (x : Matrix (Fin 3) (Fin 3) ℤ) (y : Matrix (Fin 3) (Fin 3) ℤ) Fin.revPerm Fin.revPerm Fin.revPerm).symm

theorem rev3_apply (x : SL(3, ℤ)) (i j : Fin 3) :
    ((rev3 x : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) i j = (x : Matrix (Fin 3) (Fin 3) ℤ) i.rev j.rev := rfl

theorem rev3_mapGL (x : SL(3, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℚ (rev3 x) =
      rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x * rationalGoodLine := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rev3_apply, rationalGoodLine, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.rev]


section Pi

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N)

omit [NeZero N] in
theorem rev3_mem_gammaN {x : SL(3, ℤ)} (hx : x ∈ gammaN N) : rev3 x ∈ gammaN N := by
  rw [mem_gammaN] at hx ⊢
  intro i j
  have := hx i.rev j.rev
  rw [rev3_apply]
  simpa [Matrix.one_apply, Fin.rev_inj] using this

omit [NeZero N] in
include h3 in
theorem piMap_mem_lam1 {x : SL(3, ℤ)} (hx : x ∈ gammaNQ N) :
    rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x * rationalGoodLine ∈ Lam1 := by
  rw [← rev3_mapGL]
  refine Subgroup.mem_inf.mpr ⟨levelPrincipal_le N (mapGL_mem_levelPrincipal N h3 (rev3_mem_gammaN N hx.1)), ?_⟩
  rw [rev3_mapGL, MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x * rationalGoodLine *
    rationalGoodLine) : Flags .line) = QuotientGroup.mk _
  apply QuotientGroup.eq.mpr
  have hpp : rationalGoodLine * rationalGoodLine = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]
  have : (rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x * rationalGoodLine * rationalGoodLine)⁻¹ *
      rationalGoodLine = (Matrix.SpecialLinearGroup.mapGL ℚ x)⁻¹ := by
    rw [mul_assoc (rationalGoodLine * _), hpp, mul_one]
    simp [mul_assoc]
  rw [this]
  refine (lineParabolic ℚ).inv_mem ?_
  obtain ⟨-, h1, h2⟩ := hx.2
  refine ⟨?_, ?_⟩
  · change (((x : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℤ) : ℚ) = 0
    rw [h1]; simp
  · change (((x : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0
    rw [h2]; simp


/-- The element `Π x Π` of the good-line stabilizer, for `x ∈ Γ(N) ∩ Q(ℤ)`. -/
def piLam1 (x : ↥(gammaNQ N)) : Lam1 :=
  ⟨rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x.1 * rationalGoodLine, piMap_mem_lam1 N h3 x.2⟩

omit [NeZero N] in
theorem piLam1_val (x : ↥(gammaNQ N)) (i j : Fin 3) :
    (((piLam1 N h3 x : Lam1) : RationalGL3).val i j : ℚ) =
      (((x.1 : Matrix (Fin 3) (Fin 3) ℤ) i.rev j.rev : ℤ) : ℚ) := by
  have h := congrArg (fun m : RationalGL3 => m.val i j) (rev3_mapGL x.1)
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix] at h
  change _ = _ at h
  rw [show ((piLam1 N h3 x : Lam1) : RationalGL3) = Matrix.SpecialLinearGroup.mapGL ℚ (rev3 x.1) from
    (rev3_mapGL x.1).symm]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, rev3_apply]

omit [NeZero N] in
theorem piLam1_plus (x : ↥(gammaNQ N)) : goodLineLeviProjection (piLam1 N h3 x) ∈ SL2Z := by
  have hent := (lam1_entries (piLam1 N h3 x)).2.2.2
  have hM : ∀ i j : Fin 2, (((goodLineLeviProjection (piLam1 N h3 x) : GeneralLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) = ((x.1 : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc.rev j.castSucc.rev) := by
    intro i j
    have := hent i j
    rw [piLam1_val] at this
    exact_mod_cast this
  obtain ⟨h0, h1, h2⟩ := x.2.2
  have hdet : (x.1 : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := x.1.2
  rw [Matrix.det_fin_three, h0, h1, h2] at hdet
  rw [SL2Z, MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hM, hM, hM, hM]
  simp [Fin.rev]
  linear_combination hdet


theorem rationalGoodLine_sq : rationalGoodLine * rationalGoodLine = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The pivot embedding** `Γ(N) ∩ Q(ℤ) → Λ₁⁺`, `x ↦ Π x Π`. -/
def piMap : ↥(gammaNQ N) →* Lam1Plus where
  toFun x := ⟨piLam1 N h3 x, piLam1_plus N h3 x⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    change rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ (1 : SL(3, ℤ)) * rationalGoodLine = 1
    rw [map_one, mul_one, rationalGoodLine_sq]
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    change rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ (x.1 * y.1) * rationalGoodLine =
      (rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x.1 * rationalGoodLine) *
        (rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ y.1 * rationalGoodLine)
    have h := rationalGoodLine_sq
    calc rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ (x.1 * y.1) * rationalGoodLine
        = rationalGoodLine * Matrix.SpecialLinearGroup.mapGL ℚ x.1 * (rationalGoodLine * rationalGoodLine) *
          Matrix.SpecialLinearGroup.mapGL ℚ y.1 * rationalGoodLine := by
          rw [h, mul_one, map_mul]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

omit [NeZero N] in
theorem piMap_val (x : ↥(gammaNQ N)) (i j : Fin 3) :
    ((((piMap N h3 x : Lam1Plus) : Lam1) : RationalGL3).val i j : ℚ) =
      (((x.1 : Matrix (Fin 3) (Fin 3) ℤ) i.rev j.rev : ℤ) : ℚ) := piLam1_val N h3 x i j

omit [NeZero N] in
theorem linePlusLam_piMap (x : ↥(gammaNQ N)) : linePlusData.lam (piMap N h3 x) = (gammaNQLineData N).lam x := by
  obtain ⟨l00, l01, l10, l11⟩ := linePlusLam_entry (piMap N h3 x)
  apply Units.ext
  ext i j
  rw [show (gammaNQLineData N).lam x = gammaNQLam N x from rfl, gammaNQLam_entry]
  fin_cases i <;> fin_cases j
  · exact (l00.trans (by rw [piMap_val]; simp [Fin.rev]))
  · exact (l01.trans (by rw [piMap_val]; simp [Fin.rev]))
  · exact (l10.trans (by rw [piMap_val]; simp [Fin.rev]))
  · exact (l11.trans (by rw [piMap_val]; simp [Fin.rev]))

end Pi

end TernaryPeriodPolynomials.Argument.LineSeed
