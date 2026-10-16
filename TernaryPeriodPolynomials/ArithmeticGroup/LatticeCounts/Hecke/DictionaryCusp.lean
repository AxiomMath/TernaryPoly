module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.Dictionary

@[expose] public section


/-!
# Level-one cusp forms satisfy the `S`-invariance hypothesis of the lower Hecke dictionary

Formalized by Claude Haiku 5.5.

For `h : CuspForm levelOne k`, the slash invariance `h ∣[k] γ = h` for `γ ∈ SL₂(ℤ)` specialised
to `S = [[0,-1],[1,0]]` (with `denom S z = z`) gives `h (S • z) = z^k * h z`, which is the
hypothesis `hS` of `HeckeDictionary.sum_Fh_lower` in the sign convention used there.
-/

open Matrix UpperHalfPlane ModularForm
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionaryCusp

/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL₂(ℤ)`. -/
def Sint : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

theorem Sint_map :
    (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ) Sint = Sgl := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sint, Sgl_coe, RingHom.mapMatrix_apply]

/-- `S` lies in the level-one group. -/
theorem Sgl_mem : Sgl ∈ levelOne := ⟨Sint, Sint_map⟩

theorem denom_Sgl (z : UpperHalfPlane) : UpperHalfPlane.denom Sgl (z : ℂ) = (z : ℂ) := by
  simp [UpperHalfPlane.denom, Sgl_coe]

/-- Slash invariance of a level-one cusp form under `S`. -/
theorem slash_Sgl {k : ℤ} (h : CuspForm levelOne k) :
    (⇑h ∣[k] Sgl) = ⇑h :=
  SlashInvariantFormClass.slash_action_eq h _ Sgl_mem

/-- The sign convention of `hS`: `h (S • z) = z^k * h z` for a level-one cusp form. -/
theorem cusp_S_transform {k : ℤ} (h : CuspForm levelOne k) (z : UpperHalfPlane) :
    h (Sgl • z) = (z : ℂ) ^ k * h z := by
  have hz := congrFun (slash_Sgl h) z
  have hdetS : (Sgl : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    simp [Sgl_coe, Matrix.det_fin_two]
  simp [slash_apply, σ, hdetS, denom_Sgl] at hz
  have hzne : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hzk : (z : ℂ) ^ k ≠ 0 := zpow_ne_zero k hzne
  rw [← hz]
  field_simp

/-- The lower-triangular Hecke sum for a level-one cusp form, with no `S`-hypothesis. -/
theorem sum_Fh_lower_cusp {k : ℤ} (h : CuspForm levelOne k) {m : ℕ} (hm : 0 < m)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ hnfData m, Fh k ⇑h (Gl t g) =
      (m : ℂ) ^ (1 - (k : ℂ) / 2) *
        (Nf k (Sgl⁻¹ * g) * latticeOp k m ⇑h ((Sgl⁻¹ * g) • UpperHalfPlane.I)) :=
  sum_Fh_lower k ⇑h (cusp_S_transform h) hm g hg

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionaryCusp
