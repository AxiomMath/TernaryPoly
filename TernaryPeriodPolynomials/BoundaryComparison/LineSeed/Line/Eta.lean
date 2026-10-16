module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Rho
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedPsi
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedClass
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The primitive `η = h(τ)(τw₁ + w₂)(τZ - Y)ⁿ dτ` of the line seed (LS4)

`dη = σ_h = h(τ)(τZ - Y)ⁿ (τ dw₁ + dw₂) ∧ dτ`, the `RealEntryNormalization.lineSeedForm`.  No division by `Z` is needed (unlike the
plane primitive), since `(τw₁ + w₂)` is a function of the face point alone and `P_τ = τZ - Y` does not depend on `w`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.SeedC3.Calc
open TernaryPoly.SmoothLocalDeRham

/-- `P = τ Z - Y` as a formal polynomial in the variables of `SeedPsi`. -/
def polP : Pol := pT * vZ - vY

/-- The formal coefficient polynomial of `Ψ = h(τ)(τ w₁ + w₂)(τZ - Y)ⁿ`. -/
def linePsiPoly (n : ℕ) : Pol := pH * (pT * pU1 + pU2) * polP ^ n

theorem pderiv_polP (a : Fin 4) : pderiv (Sum.inr a) polP = if a = 2 then vZ else 0 := by
  unfold polP pT vZ vY
  fin_cases a <;> simp [pderiv_X]

theorem pderiv_linePsi_u1 (n : ℕ) : pderiv (Sum.inr 0) (linePsiPoly n) = pH * pT * polP ^ n := by
  unfold linePsiPoly
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_pow, pderiv_polP]
  simp [pH, pT, pU1, pU2, pderiv_X]
  ring

theorem pderiv_linePsi_u2 (n : ℕ) : pderiv (Sum.inr 1) (linePsiPoly n) = pH * polP ^ n := by
  unfold linePsiPoly
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_pow, pderiv_polP]
  simp [pH, pT, pU1, pU2, pderiv_X]
  ring

section Params

variable (h : ℂ → ℂ)

/-- The `E_n`-valued function `Ψ(x) = h(τ)(τ w₁ + w₂)(τZ - Y)ⁿ` on the face. -/
def linePsiVal (n : ℕ) (x : Face) : Coef n :=
  toCoef n (spec (fun a => sPar h a x) (linePsiPoly n))

theorem spec_polP (z : Fin 4 → ℂ) : spec z polP = C (z 2) * X 2 - X 1 := by
  simp [polP, pT, vZ, vY, spec]

theorem spec_linePsiPoly (n : ℕ) (z : Fin 4 → ℂ) :
    spec z (linePsiPoly n) = C (z 3 * (z 2 * z 0 + z 1)) * Ppoly (z 2) ^ n := by
  simp only [linePsiPoly, map_mul, map_pow, map_add, spec_polP, spec_pH, Ppoly]
  simp [pT, pU1, pU2, spec]

theorem toPoly_linePsiVal (n : ℕ) (x : Face) :
    Coef.toPoly (linePsiVal h n x) =
      C (h (faceTau x) * (faceTau x * (x 0 : ℂ) + (x 1 : ℂ))) * Ppoly (faceTau x) ^ n := by
  unfold linePsiVal
  have hH : (C (h (faceTau x) * (faceTau x * (x 0 : ℂ) + (x 1 : ℂ))) * Ppoly (faceTau x) ^ n :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
    simpa using (isHomogeneous_C (Fin 3) (h (faceTau x) * (faceTau x * (x 0 : ℂ) + (x 1 : ℂ)))).mul
      ((Ppoly_isHomogeneous (faceTau x)).pow n)
  rw [← toPoly_toCoef_of_isHomogeneous n hH]
  congr 1
  rw [spec_linePsiPoly]
  rfl

theorem linePsiVal_hasFDerivAt (n : ℕ) {x : Face} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hxU : faceTau x ∈ U) :
    HasFDerivAt (linePsiVal h n)
      (∑ a : Fin 4, (DPar (deriv h (faceTau x)) a).smulRight
        (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr a) (linePsiPoly n))))) x :=
  hasFDerivAt_toCoef_spec n (sPar h) (DPar (deriv h (faceTau x))) x
    (hasFDerivAt_sPar h hU hh hxU) (linePsiPoly n)

theorem linePsiVal_contDiffOn (n : ℕ) {U : Set ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hmaps : ∀ x ∈ faceSet, faceTau x ∈ U) : ContDiffOn ℝ ∞ (linePsiVal h n) faceSet :=
  contDiffOn_toCoef_spec n faceSet (sPar h) (contDiffOn_sPar h hU hh hmaps) (linePsiPoly n)

/-- The 1-form `η = Ψ dτ`, as an ambient representative. -/
def lineEtaRaw (n : ℕ) (x : Face) : Face [⋀^Fin 1]→L[ℝ] Coef n :=
  oneEquiv (etaCLM n (linePsiVal h n x))

theorem lineEtaRaw_contDiffOn (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) :
    ContDiffOn ℝ ∞ (lineEtaRaw h n) faceSet := by
  have hL : ContDiff ℝ ∞ (fun f : Coef n => (oneEquiv (E := Face) (etaCLM n f))) :=
    (oneEquiv (E := Face) (F := Coef n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (etaCLM n) |>.contDiff
  exact hL.comp_contDiffOn
    (linePsiVal_contDiffOn h n isOpen_upperSet hh fun x hx => faceTau_mem_upper hx)

/-- The 1-form `η = Ψ dτ` as a chart form on the face. -/
def lineEtaForm (n : ℕ) (hh : DifferentiableOn ℂ h upperSet) : Form (F := Coef n) faceSet 1 :=
  restrictForm faceSet (lineEtaRaw h n) (lineEtaRaw_contDiffOn h hh n)

theorem extDeriv_lineEtaRaw_apply (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v w : Face) :
    extDeriv (lineEtaRaw h n) x ![v, w] =
      dtau w • fderiv ℝ (linePsiVal h n) x v - dtau v • fderiv ℝ (linePsiVal h n) x w := by
  have hψ : HasFDerivAt (linePsiVal h n) (fderiv ℝ (linePsiVal h n) x) x :=
    ((linePsiVal_hasFDerivAt h n isOpen_upperSet hh
      (faceTau_mem_upper hx)).differentiableAt).hasFDerivAt
  let L : Coef n →L[ℝ] (Face [⋀^Fin 1]→L[ℝ] Coef n) :=
    (oneEquiv (E := Face) (F := Coef n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (etaCLM n)
  have hη : HasFDerivAt (lineEtaRaw h n) (L.comp (fderiv ℝ (linePsiVal h n) x)) x :=
    L.hasFDerivAt.comp x hψ
  unfold extDeriv
  rw [hη.fderiv, alt_two]
  simp [L, etaCLM, etaLin]

theorem fderiv_linePsiVal_apply (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v : Face) :
    fderiv ℝ (linePsiVal h n) x v =
      (v 0 : ℂ) • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (linePsiPoly n))) +
      (v 1 : ℂ) • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (linePsiPoly n))) +
      dtau v • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 2) (linePsiPoly n))) +
      (deriv h (faceTau x) * dtau v) •
        toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 3) (linePsiPoly n))) := by
  rw [(linePsiVal_hasFDerivAt h n isOpen_upperSet hh (faceTau_mem_upper hx)).fderiv]
  simp [Fin.sum_univ_four, DPar]

theorem toPoly_linePsi_P0 (n : ℕ) (x : Face) :
    Coef.toPoly (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (linePsiPoly n)))) =
      C (h (faceTau x) * faceTau x) * Ppoly (faceTau x) ^ n := by
  rw [pderiv_linePsi_u1]
  have hH : (C (h (faceTau x) * faceTau x) * Ppoly (faceTau x) ^ n :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
    simpa using (isHomogeneous_C (Fin 3) (h (faceTau x) * faceTau x)).mul
      ((Ppoly_isHomogeneous (faceTau x)).pow n)
  have e : spec (fun b => sPar h b x) (pH * pT * polP ^ n) =
      C (h (faceTau x) * faceTau x) * Ppoly (faceTau x) ^ n := by
    simp only [map_mul, map_pow, spec_polP, spec_pH, Ppoly]
    simp [pT, spec, sPar]
  rw [e]
  exact toPoly_toCoef_of_isHomogeneous n (e ▸ hH)

theorem toPoly_linePsi_P1 (n : ℕ) (x : Face) :
    Coef.toPoly (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (linePsiPoly n)))) =
      C (h (faceTau x)) * Ppoly (faceTau x) ^ n := by
  rw [pderiv_linePsi_u2]
  have hH : (C (h (faceTau x)) * Ppoly (faceTau x) ^ n : MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
    simpa using (isHomogeneous_C (Fin 3) (h (faceTau x))).mul ((Ppoly_isHomogeneous (faceTau x)).pow n)
  have e : spec (fun b => sPar h b x) (pH * polP ^ n) = C (h (faceTau x)) * Ppoly (faceTau x) ^ n := by
    simp only [map_mul, map_pow, spec_polP, spec_pH, Ppoly]
    simp [sPar]
  rw [e]
  exact toPoly_toCoef_of_isHomogeneous n (e ▸ hH)

open TernaryPoly.SmoothLocalDeRham in
/-- **`dη` is the line seed.**  The coefficient polynomial of `dη` on `(v, w)` is `h(τ)(τ v₀ + v₁)dτ(w) - h(τ)(τ w₀ + w₁)dτ(v)` times `P_τⁿ`. -/
theorem toPoly_extDeriv_lineEtaRaw (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v w : Face) :
    Coef.toPoly (extDeriv (lineEtaRaw h n) x ![v, w]) =
      C (h (faceTau x) * ((faceTau x * (v 0 : ℂ) + (v 1 : ℂ)) * dtau w -
        (faceTau x * (w 0 : ℂ) + (w 1 : ℂ)) * dtau v)) * Ppoly (faceTau x) ^ n := by
  rw [extDeriv_lineEtaRaw_apply h hh n hx v w, fderiv_linePsiVal_apply h hh n hx v,
    fderiv_linePsiVal_apply h hh n hx w]
  set P0 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (linePsiPoly n)))
  set P1 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (linePsiPoly n)))
  set P2 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 2) (linePsiPoly n)))
  set P3 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 3) (linePsiPoly n)))
  have key : dtau w • ((v 0 : ℂ) • P0 + (v 1 : ℂ) • P1 + dtau v • P2 +
        (deriv h (faceTau x) * dtau v) • P3) -
      dtau v • ((w 0 : ℂ) • P0 + (w 1 : ℂ) • P1 + dtau w • P2 +
        (deriv h (faceTau x) * dtau w) • P3) =
      (dtau w * (v 0 : ℂ) - dtau v * (w 0 : ℂ)) • P0 +
        (dtau w * (v 1 : ℂ) - dtau v * (w 1 : ℂ)) • P1 := by
    module
  rw [key]
  simp only [Coef.toPoly_add, Coef.toPoly_smul, P0, P1, toPoly_linePsi_P0, toPoly_linePsi_P1]
  simp only [map_sub, map_mul, map_add]
  ring

open TernaryPoly.SmoothLocalDeRham in
/-- **`dη = σ_h`** on the coordinate basis: the `lineSeedForm`. -/
theorem toPoly_d_lineEtaForm (n : ℕ) (hh : DifferentiableOn ℂ h upperSet) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly ((d isOpen_faceSet 1 (lineEtaForm h n hh) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1]) =
      TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.lineSeedForm n h (ptOf x)
        i.castSucc j.castSucc := by
  rw [d_apply isOpen_faceSet _ hx]
  have heq : (lineEtaForm h n hh : RawForm Face (Coef n) 1) =ᶠ[nhds x] lineEtaRaw h n := by
    filter_upwards [isOpen_faceSet.mem_nhds hx] with y hy using restrictForm_apply _ _ hy
  rw [heq.extDeriv_eq (𝕜 := ℝ), toPoly_extDeriv_lineEtaRaw h hh n hx]
  unfold TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.lineSeedForm
  have hτ : TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.lineTau (ptOf x) = faceTau x := by
    simpa [TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.lineTau, seedTau] using seedTau_ptOf x
  rw [hτ]
  congr 2
  fin_cases i <;> fin_cases j <;> simp [dtau_apply, seedDTau]

end Params

end TernaryPeriodPolynomials.Argument.LineSeed
