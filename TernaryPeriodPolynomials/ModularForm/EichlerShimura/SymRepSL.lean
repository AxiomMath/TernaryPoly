module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymRep
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# `Sym^m` of `SL(2, ℤ)` acting on coefficient vectors, and the transformation of the frame

Foundation file of the unconditional Eichler--Shimura route.  `symRep m : SL(2, ℤ) →* Matrix` is the representation `P ↦ P ∘ γ⁻¹` in monomial
coordinates.  For `z` in the upper half plane the frame transforms by the automorphy factors
`(cz+d)^j (cz̄+d)^{m-j}` (`symRep_mul_frameE`, `frameT_mul_symRep`), so the Hodge frame components
of an equivariant `Sym^m`-valued form `α(γz) = s • ρ(γ) α(z)` transform by
`s (cz+d)^j (cz̄+d)^{m-j}` (`frame_component_law`).

Formalized by Claude Sonnet 5.5.
-/

open Matrix
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3 (dnm)
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob mob_eq denom_ne_zero')
open TernaryPeriodPolynomials.Argument.ESFoundations

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable (m : ℕ)

/-- The representation `Sym^m` of `SL(2, ℤ)` on coefficient vectors, `P ↦ P ∘ γ⁻¹`. -/
def symRep : SL(2, ℤ) →* Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ where
  toFun γ := symRepGL m (SpecialLinearGroup.mapGL ℝ γ)
  map_one' := by simp [symRepGL_one]
  map_mul' γ δ := by simp [symRepGL_mul]

/-- The automorphy factors `(cz+d)^j (cz̄+d)^{m-j}` of the frame. -/
def autoDiag (γ : SL(2, ℤ)) (z : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.diagonal fun j : Fin (m + 1) =>
    (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ (j : ℕ) *
      (((γ 1 0 : ℤ) : ℂ) * starRingEnd ℂ z + ((γ 1 1 : ℤ) : ℂ)) ^ (m - j)

theorem dnm_mapGL (γ : SL(2, ℤ)) (z : ℂ) :
    dnm (SpecialLinearGroup.mapGL ℝ γ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [dnm, SpecialLinearGroup.mapGL]

theorem symRep_mul_frameE (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    symRep m γ * frameE m z = frameE m (mob γ z) * autoDiag m γ z := by
  have hd := denom_ne_zero' γ hz
  have hw : dnm (SpecialLinearGroup.mapGL ℝ γ) z * mob γ z =
      ((SpecialLinearGroup.mapGL ℝ γ) 0 0 : ℝ) * z + ((SpecialLinearGroup.mapGL ℝ γ) 0 1 : ℝ) := by
    rw [dnm_mapGL, mob_eq γ hz]
    field_simp
    simp [SpecialLinearGroup.mapGL]
  have hw' : dnm (SpecialLinearGroup.mapGL ℝ γ) (starRingEnd ℂ z) * starRingEnd ℂ (mob γ z) =
      ((SpecialLinearGroup.mapGL ℝ γ) 0 0 : ℝ) * starRingEnd ℂ z +
        ((SpecialLinearGroup.mapGL ℝ γ) 0 1 : ℝ) := by
    have := congrArg (starRingEnd ℂ) hw
    simpa [dnm, SpecialLinearGroup.mapGL] using this
  have := symRepGL_mul_frameE m (SpecialLinearGroup.mapGL ℝ γ) z (mob γ z) hw hw'
  rw [dnm_mapGL, dnm_mapGL] at this
  exact this

theorem frameT_mul_symRep (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    frameT m (mob γ z) * symRep m γ = autoDiag m γ z * frameT m z := by
  have hz' : 0 < z.im := hz
  have hw : 0 < (mob γ z).im := (Partition.mob_mem γ z)
  have h := symRep_mul_frameE m γ hz
  have h2 := congrArg (fun M => frameT m (mob γ z) * M * frameT m z) h
  simp only [Matrix.mul_assoc, frameE_mul_frameT m z hz', Matrix.mul_one] at h2
  rw [← Matrix.mul_assoc (frameT m (mob γ z)) (frameE m (mob γ z)),
    frameT_mul_frameE m _ hw, Matrix.one_mul] at h2
  exact h2

theorem autoDiag_mulVec (γ : SL(2, ℤ)) (z : ℂ) (v : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    (autoDiag m γ z *ᵥ v) j =
      ((((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ (j : ℕ) *
        (((γ 1 0 : ℤ) : ℂ) * starRingEnd ℂ z + ((γ 1 1 : ℤ) : ℂ)) ^ (m - j)) * v j := by
  simp [autoDiag, Matrix.mulVec_diagonal]

/-- **Component law of an equivariant form in the Hodge frame**: if
`α(γz) = s • ρ(γ) α(z)` then `(Tα)_j(γz) = s (cz+d)^j (cz̄+d)^{m-j} (Tα)_j(z)`. -/
theorem frame_component_law (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) (s : ℂ)
    (α : ℂ → Fin (m + 1) → ℂ) (h : α (mob γ z) = s • (symRep m γ *ᵥ α z)) (j : Fin (m + 1)) :
    (frameT m (mob γ z) *ᵥ α (mob γ z)) j =
      s * ((((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ (j : ℕ) *
        (((γ 1 0 : ℤ) : ℂ) * starRingEnd ℂ z + ((γ 1 1 : ℤ) : ℂ)) ^ (m - j)) *
          (frameT m z *ᵥ α z) j := by
  rw [h, Matrix.mulVec_smul, Matrix.mulVec_mulVec, frameT_mul_symRep m γ hz,
    show (autoDiag m γ z * frameT m z) *ᵥ α z = autoDiag m γ z *ᵥ (frameT m z *ᵥ α z) from
      (Matrix.mulVec_mulVec _ _ _).symm]
  rw [Pi.smul_apply, autoDiag_mulVec, smul_eq_mul]
  ring

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
