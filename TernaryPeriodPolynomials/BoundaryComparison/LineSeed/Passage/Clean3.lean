module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge1
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj
public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralBases
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Transport

@[expose] public section


/-!
# Clean frames for the good line cusps of `Γ(N)` (Passage frame, part P2)

For `h ∈ SL₃(ℤ)` whose line `h⁻¹ℚe₁` is good there are `b ∈ lineBorel`, `h' = b⁻¹h` and a transporter `q ∈ K†` with `q • std = h⁻¹⟨e₁⟩` and `mapGL ℚ h' * q = Π` (a *clean frame*):
take any transporter (`good_lines_transitive`), make its determinant `-1` by composing with the Levi element `diag(1,-1)` of the good line, and put `b = h q Π`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The determinant of an element of the level group is `±1`. -/
theorem det_rationalLevel {q : RationalGL3} (hq : q ∈ rationalLevel) :
    (q.val.det = 1) ∨ (q.val.det = -1) := by
  obtain ⟨g, rfl⟩ := hq
  have hu : IsUnit ((g.1 : IntegralGL3).val.det) := by simp
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have : (rationalInclusion g).val.det = ((g.1 : IntegralGL3).val.det : ℚ) := by
      change ((g.1 : IntegralGL3).val.map (Int.castRingHom ℚ)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [this, h]; simp
  · right
    have : (rationalInclusion g).val.det = ((g.1 : IntegralGL3).val.det : ℚ) := by
      change ((g.1 : IntegralGL3).val.map (Int.castRingHom ℚ)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [this, h]; simp


open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine)

/-- The Levi element `diag(1,-1)` of the good line, in the level group, of determinant `-1`. -/
def leviNeg : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem det_arithmeticLevi_leviNeg : (arithmeticLevi leviNeg).val.det = -1 := by
  simp [arithmeticLevi, leviNeg, planeLevi, planeBlock, Matrix.det_fin_three]

/-- A transporter of determinant `-1` from the standard good line to any good line. -/
theorem exists_detneg_transporter (flag : Flags .line) (hg : GoodFlag .line flag) :
    ∃ q : RationalGL3, q ∈ rationalLevel ∧ q.val.det = -1 ∧ q • stdLine = flag := by
  obtain ⟨γ, hγ⟩ := TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases.good_lines_transitive
    stdLine flag rationalGoodLine_good hg
  have hq0 : rationalInclusion γ ∈ rationalLevel := ⟨γ, rfl⟩
  rcases det_rationalLevel hq0 with h1 | h1
  · have hL : arithmeticLevi leviNeg ∈ flagArithmeticStabilizer .line stdLine := arithmeticLevi_goodLine leviNeg
    have hLl : arithmeticLevi leviNeg ∈ rationalLevel := hL.1
    have hLs : arithmeticLevi leviNeg • stdLine = stdLine := MulAction.mem_stabilizer_iff.mp hL.2
    refine ⟨rationalInclusion γ * arithmeticLevi leviNeg, rationalLevel.mul_mem hq0 hLl, ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, h1, det_arithmeticLevi_leviNeg]; ring
    · rw [mul_smul, hLs]; exact hγ
  · exact ⟨rationalInclusion γ, hq0, h1, hγ⟩


/-- **Clean frames exist for every good line cusp.** -/
theorem exists_clean_frame (h : SL(3, ℤ)) (hgood : GoodFlag .line (lineFlagAt h)) :
    ∃ (b h' : SL(3, ℤ)) (q : RationalGL3), b ∈ lineBorel ∧ q ∈ rationalLevel ∧ h = b * h' ∧
      Matrix.SpecialLinearGroup.mapGL ℚ h' * q = rationalGoodLine ∧ q • stdLine = lineFlagAt h := by
  obtain ⟨q, hq, hdet, hqF⟩ := exists_detneg_transporter (lineFlagAt h) hgood
  obtain ⟨g, rfl⟩ := hq
  have hG : (g.1 : IntegralGL3).val.det = -1 := by
    have : (rationalInclusion g).val.det = (((g.1 : IntegralGL3).val.det : ℤ) : ℚ) := by
      change ((g.1 : IntegralGL3).val.map (Int.castRingHom ℚ)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [this] at hdet
    exact_mod_cast hdet
  let Pint : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  have hP : Pint.det = -1 := by simp [Pint, Matrix.det_fin_three]
  let B : Matrix (Fin 3) (Fin 3) ℤ := (h : Matrix (Fin 3) (Fin 3) ℤ) * (g.1 : IntegralGL3).val * Pint
  have hB : B.det = 1 := by
    simp only [B, Matrix.det_mul, hG, hP, Matrix.SpecialLinearGroup.det_coe]
    norm_num
  let b : SL(3, ℤ) := ⟨B, hB⟩
  have hbmap : Matrix.SpecialLinearGroup.mapGL ℚ b = Matrix.SpecialLinearGroup.mapGL ℚ h * rationalInclusion g *
      rationalGoodLine := by
    apply Units.ext
    change (B.map (Int.castRingHom ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = _
    simp only [B, Matrix.map_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have hPm : Pint.map (Int.castRingHom ℚ) = rationalGoodLine.val := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Pint, rationalGoodLine]
    rw [hPm]
    rfl
  have hmem : Matrix.SpecialLinearGroup.mapGL ℚ b ∈ lineParabolic ℚ := by
    have hq' : (QuotientGroup.mk (rationalInclusion g * rationalGoodLine) : Flags .line) =
        QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) := hqF
    have := QuotientGroup.eq.mp hq'
    have h2 := (lineParabolic ℚ).inv_mem this
    rw [hbmap]
    simpa [mul_assoc] using h2
  have hb : b ∈ lineBorel := by
    obtain ⟨h1, h2⟩ := hmem
    refine ⟨?_, ?_⟩
    · have : ((b : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℚ) = 0 := h1
      exact_mod_cast this
    · have : ((b : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) = 0 := h2
      exact_mod_cast this
  have hs : rationalGoodLine * rationalGoodLine = 1 := rationalGoodLine_sq
  refine ⟨b, b⁻¹ * h, rationalInclusion g, hb, ⟨g, rfl⟩, by group, ?_, hqF⟩
  rw [map_mul, map_inv, hbmap]
  have hs' : rationalGoodLine⁻¹ = rationalGoodLine := inv_eq_of_mul_eq_one_right hs
  have key : ∀ a q : RationalGL3, (a * q * rationalGoodLine)⁻¹ * a * q = rationalGoodLine⁻¹ := by
    intro a q; group
  rw [key, hs']

end TernaryPeriodPolynomials.Argument.LineSeed
