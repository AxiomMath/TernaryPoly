module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.WeightFiltration

@[expose] public section


/-!
# The flag filtration of the coefficient representation

`flagFiltration n χ q i` is the pull-back along `ρ(q⁻¹)` of the weight filtration
`Wsub (2n + 1 - i)`. It is a finite increasing filtration of `HomogeneousPoly n`,
from `⊥` to `⊤`, and every element of `conjUnitri q` acts trivially on its graded
pieces.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness.Weight

theorem unitri_det {u : RationalGL3} (hu : IsUnitri u) : u.val.det = 1 := by
  obtain ⟨u00, u11, u22, u10, u20, u21⟩ := hu
  rw [Matrix.det_fin_three, u00, u11, u22, u10, u20, u21]
  ring

/-- On a unitriangular element the coefficient action is a unitriangular substitution. -/
theorem rho_unitri_val {n : ℕ} (χ : RankOneCharacter) {u : RationalGL3} (hu : IsUnitri u)
    (f : HomogeneousPoly n) :
    ((rationalCoefficientComponent n χ u f : HomogeneousPoly n) : Poly) =
      substitute (((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u))⁻¹ : GL3).val) f.val := by
  have hdet := unitri_det hu
  have hdetU : Matrix.GeneralLinearGroup.det u = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  have hdetR : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u) = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det, hdetU, map_one]
  have hdetC : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u)) = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det, hdetR, map_one]
  change ((componentCharacter χ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u) •
      realCoefficient n (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u) f : HomogeneousPoly n) : Poly) = _
  have hc : componentCharacter χ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u) = 1 := by
    simp only [componentCharacter, MonoidHom.coe_comp, Function.comp_apply, hdetR, map_one]
  rw [hc, one_smul]
  change action (-1) (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u)) f.val = _
  rw [action_apply]
  have hd : determinantCharacter (-1) (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u)) = 1 := by
    simp only [determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, hdetC, Units.val_one, one_zpow]
  rw [hd, one_smul]

theorem inverse_unitriC {u : RationalGL3} (hu : IsUnitri u) :
    IsUnitriC (((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) u))⁻¹ : GL3).val) := by
  obtain ⟨⟨i00, i11, i22, i10, i20, i21⟩, -, -⟩ := unitri_inv hu
  rw [← map_inv, ← map_inv]
  simp only [IsUnitriC, Matrix.GeneralLinearGroup.map_apply, i00, i11, i22, i10, i20, i21,
    map_one, map_zero, and_self]

theorem rho_unitri_sub_mem {n : ℕ} (χ : RankOneCharacter) {u : RationalGL3} (hu : IsUnitri u)
    {k : ℕ} {f : HomogeneousPoly n} (hf : f.val ∈ Wsub k) :
    ((rationalCoefficientComponent n χ u f : HomogeneousPoly n) : Poly) - f.val ∈ Wsub (k + 1) := by
  rw [rho_unitri_val χ hu]
  exact substitute_sub_mem (inverse_unitriC hu) hf

/-- The flag filtration. -/
def flagFiltration (n : ℕ) (χ : RankOneCharacter) (q : RationalGL3) (i : ℕ) :
    Submodule ℂ (HomogeneousPoly n) :=
  (Wsub (2 * n + 1 - i)).comap ((HomogeneousPoly n).subtype ∘ₗ rationalCoefficientComponent n χ q⁻¹)

theorem mem_flagFiltration {n : ℕ} {χ : RankOneCharacter} {q : RationalGL3} {i : ℕ}
    {v : HomogeneousPoly n} :
    v ∈ flagFiltration n χ q i ↔ (rationalCoefficientComponent n χ q⁻¹ v).val ∈ Wsub (2 * n + 1 - i) :=
  Iff.rfl

theorem flagFiltration_mono (n : ℕ) (χ : RankOneCharacter) (q : RationalGL3) :
    Monotone (flagFiltration n χ q) := by
  intro i j hij v hv
  rw [mem_flagFiltration] at hv ⊢
  exact Wsub_anti (by omega) hv

theorem flagFiltration_zero (n : ℕ) (χ : RankOneCharacter) (q : RationalGL3) :
    flagFiltration n χ q 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_flagFiltration, Nat.sub_zero] at hv
  have h0 := homogeneous_Wsub_eq_zero _ hv
  rw [Submodule.mem_bot]
  have := congrArg (rationalCoefficientComponent n χ q) h0
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
    map_zero] at this

theorem flagFiltration_top (n : ℕ) (χ : RankOneCharacter) (q : RationalGL3) (v : HomogeneousPoly n) :
    v ∈ flagFiltration n χ q (2 * n + 1) := by
  rw [mem_flagFiltration, Nat.sub_self]
  exact mem_Wsub_zero _

/-- Elements of `conjUnitri q` act trivially on the graded pieces. -/
theorem flagFiltration_step {n : ℕ} (χ : RankOneCharacter) {q g : RationalGL3}
    (hg : g ∈ conjUnitri q) (i : ℕ) (v : HomogeneousPoly n) (hv : v ∈ flagFiltration n χ q (i + 1)) :
    rationalCoefficientComponent n χ g v - v ∈ flagFiltration n χ q i := by
  rw [mem_flagFiltration] at hv ⊢
  have hconj : rationalCoefficientComponent n χ q⁻¹ (rationalCoefficientComponent n χ g v) =
      rationalCoefficientComponent n χ (q⁻¹ * g * q) (rationalCoefficientComponent n χ q⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [map_sub, Submodule.coe_sub, hconj]
  exact Wsub_anti (by omega) (rho_unitri_sub_mem χ hg hv)

end TernaryPeriodPolynomials.FlagExactness.Weight
