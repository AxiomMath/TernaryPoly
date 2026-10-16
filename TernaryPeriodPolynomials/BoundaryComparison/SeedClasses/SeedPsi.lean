module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PolyCalcCoef
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneAction
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamLowDegree

@[expose] public section


/-!
# The explicit primitive `η = Ψ dτ` of the seed

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3.Psi

open Calc

/-- Formal variables: `X, Y, Z` (first block) and the parameters `u₁, u₂, τ, H = h(τ)`. -/
abbrev Pol := MvPolynomial (Fin 3 ⊕ Fin 4) ℂ

def vX : Pol := X (Sum.inl 0)
def vY : Pol := X (Sum.inl 1)
def vZ : Pol := X (Sum.inl 2)
def pU1 : Pol := X (Sum.inr 0)
def pU2 : Pol := X (Sum.inr 1)
def pT : Pol := X (Sum.inr 2)
def pH : Pol := X (Sum.inr 3)

/-- `A = τY - X`. -/
def polA : Pol := pT * vY - vX
/-- `c = u₁ - τu₂`. -/
def polC : Pol := pU1 - pT * pU2
/-- `B = A + cZ`. -/
def polB : Pol := polA + polC * vZ

/-- The explicit coefficient polynomial of `Ψ = h(τ)(B^{n+1} - A^{n+1})/((n+1)Z)`. -/
def psiPoly (n : ℕ) : Pol :=
  C (((n : ℂ) + 1)⁻¹) * pH * polC * ∑ k ∈ Finset.range (n + 1), polB ^ k * polA ^ (n - k)

theorem polB_sub_polA : polB - polA = polC * vZ := by
  unfold polB; ring

/-- The telescoping identity `(n+1) Z Ψ = h (B^{n+1} - A^{n+1})`. -/
theorem psi_mul_Z (n : ℕ) :
    C ((n : ℂ) + 1) * vZ * psiPoly n = pH * (polB ^ (n + 1) - polA ^ (n + 1)) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  have hgeom : (∑ k ∈ Finset.range (n + 1), polB ^ k * polA ^ (n + 1 - 1 - k)) *
      (polB - polA) = polB ^ (n + 1) - polA ^ (n + 1) := geom_sum₂_mul _ _ _
  rw [polB_sub_polA] at hgeom
  unfold psiPoly
  have h1 : C ((n : ℂ) + 1) * C (((n : ℂ) + 1)⁻¹) = (1 : Pol) := by
    rw [← map_mul, mul_inv_cancel₀ hn, map_one]
  simp only [Nat.add_sub_cancel] at hgeom
  calc C ((n : ℂ) + 1) * vZ * (C (((n : ℂ) + 1)⁻¹) * pH * polC *
        ∑ k ∈ Finset.range (n + 1), polB ^ k * polA ^ (n - k))
      = (C ((n : ℂ) + 1) * C (((n : ℂ) + 1)⁻¹)) * pH * ((∑ k ∈ Finset.range (n + 1),
          polB ^ k * polA ^ (n - k)) * (polC * vZ)) := by ring
    _ = pH * (polB ^ (n + 1) - polA ^ (n + 1)) := by rw [h1, hgeom]; ring

theorem pderiv_polB_u1 : pderiv (Sum.inr 0) polB = vZ := by
  simp [polB, polA, polC, vX, vY, vZ, pT, pU1, pU2, pderiv_X]

theorem pderiv_polB_u2 : pderiv (Sum.inr 1) polB = -(pT * vZ) := by
  simp [polB, polA, polC, vX, vY, vZ, pT, pU1, pU2, pderiv_X]
  ring

theorem pderiv_pH_u1 : pderiv (Sum.inr 0) pH = 0 := by
  simp [pH, pderiv_X]

theorem pderiv_pH_u2 : pderiv (Sum.inr 1) pH = 0 := by
  simp [pH, pderiv_X]

theorem pderiv_vZ (a : Fin 4) : pderiv (Sum.inr a) vZ = 0 := by
  simp [vZ, pderiv_X]

theorem pderiv_polA_u1 : pderiv (Sum.inr 0) polA = 0 := by
  simp [polA, vX, vY, pT, pderiv_X]

theorem pderiv_polA_u2 : pderiv (Sum.inr 1) polA = 0 := by
  simp [polA, vX, vY, pT, pderiv_X]

theorem pderiv_pT_u1 : pderiv (Sum.inr 0) pT = 0 := by
  simp [pT, pderiv_X]

theorem pderiv_pT_u2 : pderiv (Sum.inr 1) pT = 0 := by
  simp [pT, pderiv_X]

theorem Z_ne_zero : (vZ : Pol) ≠ 0 := by
  simp [vZ, X_ne_zero]

theorem Cn1_ne_zero (n : ℕ) : (C ((n : ℂ) + 1) : Pol) ≠ 0 := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  intro h0
  apply hn
  exact C_injective (Fin 3 ⊕ Fin 4) ℂ (by rw [h0, map_zero])

/-- `∂Ψ/∂u₁ = h 𝓑ⁿ`. -/
theorem pderiv_psi_u1 (n : ℕ) : pderiv (Sum.inr 0) (psiPoly n) = pH * polB ^ n := by
  have h := congrArg (pderiv (Sum.inr 0)) (psi_mul_Z n)
  have hne : (C ((n : ℂ) + 1) * vZ : Pol) ≠ 0 := mul_ne_zero (Cn1_ne_zero n) Z_ne_zero
  apply mul_left_cancel₀ hne
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, pderiv_vZ, pderiv_pow, map_sub,
    pderiv_polB_u1, pderiv_polA_u1, pderiv_pH_u1] at h
  have hcast : (((n + 1 : ℕ)) : Pol) = C ((n : ℂ) + 1) := by
    rw [← map_natCast C (n + 1)]
    congr 1
    push_cast
    ring
  simp only [Nat.add_sub_cancel, hcast, mul_zero, add_zero, sub_zero] at h
  linear_combination h

/-- `∂Ψ/∂u₂ = -τ h 𝓑ⁿ`. -/
theorem pderiv_psi_u2 (n : ℕ) : pderiv (Sum.inr 1) (psiPoly n) = -(pT * pH * polB ^ n) := by
  have h := congrArg (pderiv (Sum.inr 1)) (psi_mul_Z n)
  have hne : (C ((n : ℂ) + 1) * vZ : Pol) ≠ 0 := mul_ne_zero (Cn1_ne_zero n) Z_ne_zero
  apply mul_left_cancel₀ hne
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, pderiv_vZ, pderiv_pow, map_sub,
    pderiv_polB_u2, pderiv_polA_u2, pderiv_pH_u2] at h
  have hcast : (((n + 1 : ℕ)) : Pol) = C ((n : ℂ) + 1) := by
    rw [← map_natCast C (n + 1)]
    congr 1
    push_cast
    ring
  simp only [Nat.add_sub_cancel, hcast, mul_zero, add_zero, sub_zero] at h
  linear_combination h

section Params

variable (h : ℂ → ℂ)

/-- The CLM `dτ = dx + i dy` on the face coordinates. -/
def dtau : Face →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) +
    Complex.I • (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3))

theorem dtau_apply (v : Face) : dtau v = (v 2 : ℂ) + Complex.I * (v 3 : ℂ) := by
  simp [dtau]

theorem faceTau_eq (x : Face) : faceTau x = dtau x := by
  rw [dtau_apply, faceTau]; ring

/-- The parameters `(u₁, u₂, τ, h(τ))` of the seed polynomial. -/
def sPar (a : Fin 4) (x : Face) : ℂ :=
  match a with
  | 0 => (x 0 : ℂ)
  | 1 => (x 1 : ℂ)
  | 2 => faceTau x
  | 3 => h (faceTau x)

/-- The real derivatives of the parameters, with the holomorphic derivative `h'` of `h`. -/
def DPar (h' : ℂ) (a : Fin 4) : Face →L[ℝ] ℂ :=
  match a with
  | 0 => Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0)
  | 1 => Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1)
  | 2 => dtau
  | 3 => h' • dtau

theorem hasFDerivAt_sPar {x : Face} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hxU : faceTau x ∈ U) (a : Fin 4) :
    HasFDerivAt (sPar h a) (DPar (deriv h (faceTau x)) a) x := by
  have hτ : HasFDerivAt faceTau dtau x := by
    have : faceTau = ⇑dtau := funext faceTau_eq
    rw [this]; exact dtau.hasFDerivAt
  fin_cases a
  · exact (Complex.ofRealCLM.hasFDerivAt.comp x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt)
  · exact (Complex.ofRealCLM.hasFDerivAt.comp x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).hasFDerivAt)
  · exact hτ
  · exact ((hh.differentiableAt (hU.mem_nhds hxU)).hasDerivAt).comp_hasFDerivAt x hτ

theorem contDiffOn_sPar {U : Set ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hmaps : ∀ x ∈ faceSet, faceTau x ∈ U) (a : Fin 4) :
    ContDiffOn ℝ ∞ (sPar h a) faceSet := by
  fin_cases a
  · exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_pi.mp contDiff_id 0)).contDiffOn
  · exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_pi.mp contDiff_id 1)).contDiffOn
  · exact contDiff_faceTau.contDiffOn
  · have h1 : ContDiffOn ℂ ∞ h U := hh.contDiffOn hU
    exact (h1.restrict_scalars ℝ).comp contDiff_faceTau.contDiffOn hmaps

/-- The `E_n`-valued function `Ψ = h(τ)(B^{n+1} - A^{n+1})/((n+1)Z)` on the face. -/
def psiVal (n : ℕ) (x : Face) : Coef n :=
  toCoef n (spec (fun a => sPar h a x) (psiPoly n))

theorem psiVal_hasFDerivAt (n : ℕ) {x : Face} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hxU : faceTau x ∈ U) :
    HasFDerivAt (psiVal h n)
      (∑ a : Fin 4, (DPar (deriv h (faceTau x)) a).smulRight
        (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr a) (psiPoly n))))) x :=
  hasFDerivAt_toCoef_spec n (sPar h) (DPar (deriv h (faceTau x))) x
    (hasFDerivAt_sPar h hU hh hxU) (psiPoly n)

theorem psiVal_contDiffOn (n : ℕ) {U : Set ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hmaps : ∀ x ∈ faceSet, faceTau x ∈ U) : ContDiffOn ℝ ∞ (psiVal h n) faceSet :=
  contDiffOn_toCoef_spec n faceSet (sPar h) (contDiffOn_sPar h hU hh hmaps) (psiPoly n)

open TernaryPoly.SmoothLocalDeRham in
/-- `v ↦ dτ(v) • f`, as a real-linear map in `f`. -/
def etaLin (n : ℕ) : Coef n →ₗ[ℝ] (Face →L[ℝ] Coef n) where
  toFun f := dtau.smulRight f
  map_add' f g := by ext v; simp [smul_add]
  map_smul' c f := by
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      RingHom.id_apply]
    exact smul_comm _ _ _

/-- The continuous version of `etaLin`. -/
def etaCLM (n : ℕ) : Coef n →L[ℝ] (Face →L[ℝ] Coef n) :=
  LinearMap.toContinuousLinearMap (etaLin n)

open TernaryPoly.SmoothLocalDeRham in
/-- The 1-form `η = Ψ dτ`, as an ambient representative. -/
def etaRaw (n : ℕ) (x : Face) : Face [⋀^Fin 1]→L[ℝ] Coef n :=
  oneEquiv (etaCLM n (psiVal h n x))

/-- The upper half-plane as a subset of `ℂ`. -/
def upperSet : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_upperSet : IsOpen upperSet := isOpen_lt continuous_const Complex.continuous_im

theorem faceTau_mem_upper {x : Face} (hx : x ∈ faceSet) : faceTau x ∈ upperSet :=
  faceTau_im hx

open TernaryPoly.SmoothLocalDeRham in
theorem etaRaw_contDiffOn (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) :
    ContDiffOn ℝ ∞ (etaRaw h n) faceSet := by
  have hL : ContDiff ℝ ∞ (fun f : Coef n => (oneEquiv (E := Face) (etaCLM n f))) :=
    (oneEquiv (E := Face) (F := Coef n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (etaCLM n) |>.contDiff
  exact hL.comp_contDiffOn
    (psiVal_contDiffOn h n isOpen_upperSet hh fun x hx => faceTau_mem_upper hx)

open TernaryPoly.SmoothLocalDeRham in
/-- The 1-form `η = Ψ dτ` as a chart form on the face. -/
def etaForm (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) : Form (F := Coef n) faceSet 1 :=
  restrictForm faceSet (etaRaw h n) (etaRaw_contDiffOn h hh n)

open ContinuousAlternatingMap in
theorem alt_two {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) (v w : E) :
    alternatizeUncurryFin f ![v, w] = f v (![w] : Fin 1 → E) - f w (![v] : Fin 1 → E) := by
  rw [alternatizeUncurryFin_apply]
  have h1 : Fin.removeNth 1 (![v, w] : Fin 2 → E) = ![v] := by
    funext i; fin_cases i; rfl
  simp [Fin.sum_univ_two, h1, sub_eq_add_neg]

open TernaryPoly.SmoothLocalDeRham in
/-- The exterior derivative of `η = Ψ dτ`, evaluated on two vectors. -/
theorem extDeriv_etaRaw_apply (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v w : Face) :
    extDeriv (etaRaw h n) x ![v, w] =
      dtau w • fderiv ℝ (psiVal h n) x v - dtau v • fderiv ℝ (psiVal h n) x w := by
  have hψ : HasFDerivAt (psiVal h n) (fderiv ℝ (psiVal h n) x) x :=
    ((psiVal_hasFDerivAt h n isOpen_upperSet hh
      (faceTau_mem_upper hx)).differentiableAt).hasFDerivAt
  let L : Coef n →L[ℝ] (Face [⋀^Fin 1]→L[ℝ] Coef n) :=
    (oneEquiv (E := Face) (F := Coef n)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (etaCLM n)
  have hη : HasFDerivAt (etaRaw h n) (L.comp (fderiv ℝ (psiVal h n) x)) x :=
    L.hasFDerivAt.comp x hψ
  unfold extDeriv
  rw [hη.fderiv, alt_two]
  simp [L, etaCLM, etaLin]

/-- The point of the 5-dimensional coordinates (with normal height `1`) attached to a face point. -/
def ptOf (x : Face) : Fin 5 → ℝ := ![x 0, x 1, x 2, x 3, 1]

theorem seedTau_ptOf (x : Face) : seedTau (ptOf x) = faceTau x := by
  simp [seedTau, faceTau, ptOf]
  ring

omit h in
theorem spec_polB (z : Fin 4 → ℂ) :
    spec z polB = C (z 2) * X 1 - X 0 + C (z 0 - z 2 * z 1) * X 2 := by
  simp [polB, polA, polC, vX, vY, vZ, pT, pU1, pU2, spec]

omit h in
theorem spec_polA (z : Fin 4 → ℂ) : spec z polA = C (z 2) * X 1 - X 0 := by
  simp [polA, vX, vY, pT, spec]

theorem spec_polB_eq (x : Face) :
    spec (fun a => sPar h a x) polB = seedLinear (ptOf x) := by
  rw [spec_polB, seedLinear, seedTau_ptOf]
  simp [sPar, ptOf]

theorem fderiv_psiVal_apply (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v : Face) :
    fderiv ℝ (psiVal h n) x v =
      (v 0 : ℂ) • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (psiPoly n))) +
      (v 1 : ℂ) • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (psiPoly n))) +
      dtau v • toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 2) (psiPoly n))) +
      (deriv h (faceTau x) * dtau v) •
        toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 3) (psiPoly n))) := by
  rw [(psiVal_hasFDerivAt h n isOpen_upperSet hh (faceTau_mem_upper hx)).fderiv]
  simp [Fin.sum_univ_four, DPar]

omit h in
theorem spec_pH (z : Fin 4 → ℂ) : spec z pH = C (z 3) := by
  simp [pH, spec]

theorem seedLinear_isHomogeneous (p : Fin 5 → ℝ) : (seedLinear p).IsHomogeneous 1 := by
  unfold seedLinear
  exact (((isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X ℂ _)).add
    (isHomogeneous_C_mul_X _ _))

/-- `P₀ = ∂Ψ/∂u₁ = h 𝓑ⁿ` as a polynomial. -/
theorem toPoly_P0 (n : ℕ) (x : Face) :
    Coef.toPoly (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (psiPoly n)))) =
      C (h (faceTau x)) * seedLinear (ptOf x) ^ n := by
  rw [pderiv_psi_u1]
  have hH : (C (h (faceTau x)) * seedLinear (ptOf x) ^ n :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
    simpa using (isHomogeneous_C (Fin 3) (h (faceTau x))).mul
      ((seedLinear_isHomogeneous (ptOf x)).pow n)
  simp only [map_mul, map_pow, spec_polB_eq, spec_pH]
  exact toPoly_toCoef_of_isHomogeneous n (by simpa [sPar] using hH)

/-- `P₁ = ∂Ψ/∂u₂ = -τ h 𝓑ⁿ` as a polynomial. -/
theorem toPoly_P1 (n : ℕ) (x : Face) :
    Coef.toPoly (toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (psiPoly n)))) =
      -(C (faceTau x) * C (h (faceTau x)) * seedLinear (ptOf x) ^ n) := by
  rw [pderiv_psi_u2]
  have hH : (-(C (faceTau x) * C (h (faceTau x)) * seedLinear (ptOf x) ^ n) :
      MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
    have := ((isHomogeneous_C (Fin 3) (faceTau x)).mul
      (isHomogeneous_C (Fin 3) (h (faceTau x)))).mul ((seedLinear_isHomogeneous (ptOf x)).pow n)
    simpa using this.neg
  have e : spec (fun b => sPar h b x) pT = C (faceTau x) := by
    simp [pT, spec, sPar]
  simp only [map_neg, map_mul, map_pow, spec_polB_eq, spec_pH, e]
  exact toPoly_toCoef_of_isHomogeneous n (by simpa [sPar] using hH)

open TernaryPoly.SmoothLocalDeRham in
/-- **`dη` is the seed.** The coefficient polynomial of `dη` on `(v, w)` is
`h(τ)𝓑ⁿ (β ∧ dτ)(v, w)`. -/
theorem toPoly_extDeriv_etaRaw (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (v w : Face) :
    Coef.toPoly (extDeriv (etaRaw h n) x ![v, w]) =
      C (h (faceTau x) * ((dtau w * (v 0 : ℂ) - dtau v * (w 0 : ℂ)) -
        faceTau x * (dtau w * (v 1 : ℂ) - dtau v * (w 1 : ℂ)))) * seedLinear (ptOf x) ^ n := by
  rw [extDeriv_etaRaw_apply h hh n hx v w, fderiv_psiVal_apply h hh n hx v,
    fderiv_psiVal_apply h hh n hx w]
  set P0 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 0) (psiPoly n)))
  set P1 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 1) (psiPoly n)))
  set P2 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 2) (psiPoly n)))
  set P3 := toCoef n (spec (fun b => sPar h b x) (pderiv (Sum.inr 3) (psiPoly n)))
  have key : dtau w • ((v 0 : ℂ) • P0 + (v 1 : ℂ) • P1 + dtau v • P2 +
        (deriv h (faceTau x) * dtau v) • P3) -
      dtau v • ((w 0 : ℂ) • P0 + (w 1 : ℂ) • P1 + dtau w • P2 +
        (deriv h (faceTau x) * dtau w) • P3) =
      (dtau w * (v 0 : ℂ) - dtau v * (w 0 : ℂ)) • P0 +
        (dtau w * (v 1 : ℂ) - dtau v * (w 1 : ℂ)) • P1 := by
    module
  rw [key]
  simp only [Coef.toPoly_add, Coef.toPoly_smul, P0, P1, toPoly_P0, toPoly_P1]
  simp only [map_sub, map_mul]
  ring

open TernaryPoly.SmoothLocalDeRham in
/-- On the coordinate basis, `dη` has exactly the coefficients of the seed `seedForm`. -/
theorem toPoly_dEta_basis (hh : DifferentiableOn ℂ h upperSet) (n : ℕ) {x : Face}
    (hx : x ∈ faceSet) (i j : Fin 4) :
    Coef.toPoly (extDeriv (etaRaw h n) x ![Pi.single i 1, Pi.single j 1]) =
      seedForm n h (ptOf x) i.castSucc j.castSucc := by
  rw [toPoly_extDeriv_etaRaw h hh n hx]
  unfold seedForm
  simp only [seedBeta, seedTau_ptOf]
  congr 2
  fin_cases i <;> fin_cases j <;>
    simp [dtau_apply, seedDTau]

end Params

end TernaryPeriodPolynomials.Argument.SeedC3.Psi
