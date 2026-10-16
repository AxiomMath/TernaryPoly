module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.DecouplingCusp
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.FrameColumns
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Representative
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.EichlerPrim

@[expose] public section


/-!
# Assembly core: the harmonic representative is a pair of cusp forms

Foundation file of the unconditional Eichler--Shimura route.  `ES_assembly_core` composes the harmonic representative of the `L²` Hodge projection
(`L2.HodgeDatum.exists_representative`, for the Hodge datum `hodgeDatumSym (n+1) Γ` of `Sym^{n+1}`)
with the decoupling (`cuspForms_of_pair`): the smooth equivariant closed and co-closed form
`a' dx + b' dy` of finite energy has `dz` coefficient `F · coords ((zX₁ - X₀)^{n+1})` and `dz̄`
coefficient the conjugate of `G · coords ((zX₁ - X₀)^{n+1})`, with `F, G` Mathlib cusp forms of
weight `n + 3` for the image of `Γ` in `GL₂(ℝ)`.  Also `integrable_cutoff_edens` (finite
`θ`-weighted energy is integrability of the cutoff-weighted density) and
`formOf_apply_coef`/`formOf_apply_wd` (the form is `v α + v̄ β`).

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory UpperHalfPlane MvPolynomial
open scoped MatrixGroups ContDiff InnerProductSpace ENNReal
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob cutoff)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP dir)
open TernaryPeriodPolynomials.Argument.ESFoundations.L2
  (Wd Weights Good HodgeDatum Hs formOf)

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

theorem formOf_eq_formOfPair {d : ℕ} (a b : ℂ → Wd d) : formOf a b = formOfPair a b := by
  funext z
  ext v
  simp [L2.formOf_apply, formOfPair]

/-- A form is the sum of its `dz` and `dz̄` parts. -/
theorem formOf_apply_coef {d : ℕ} (a b : ℂ → Wd d) (z v : ℂ) (i : Fin d) :
    formOf a b z v i = v * coefA a b z i + starRingEnd ℂ v * coefB a b z i := by
  rw [L2.formOf_apply]
  simp only [coefA, coefB, PiLp.add_apply, PiLp.smul_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The form `a dx + b dy` as `v ↦ v • α + v̄ • β` in `Wd d`, with `α`, `β` its `dz`, `dz̄`
coefficients. -/
theorem formOf_apply_wd {d : ℕ} (a b : ℂ → Wd d) (z v : ℂ) :
    formOf a b z v = v • (WithLp.toLp 2 (coefA a b z) : Wd d) +
      starRingEnd ℂ v • (WithLp.toLp 2 (coefB a b z) : Wd d) := by
  ext i
  rw [formOf_apply_coef]
  simp

/-- Finite `θ`-weighted energy of an equivariant continuous form is integrability of the
cutoff-weighted energy density. -/
theorem integrable_cutoff_edens {Γ : Subgroup SL(2, ℤ)} {d : ℕ} (D : HodgeDatum Γ d)
    (W : Weights Γ) {L : L2.Form d} (hL : Good D W L) (hE : D.Eqv L) :
    Integrable (fun z => if z ∈ U then cutoff Γ W.R z * D.edens L z else 0) := by
  have hcont : ContinuousOn (fun z => cutoff Γ W.R z * D.edens L z) U :=
    W.continuousOn_χ.mul (L2.Weights.continuousOn_edens D hL.cont)
  have hind : (fun z => if z ∈ U then cutoff Γ W.R z * D.edens L z else 0) =
      U.indicator (fun z => cutoff Γ W.R z * D.edens L z) := by
    funext z; simp [Set.indicator]
  rw [hind]
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_indicator_iff isOpen_U.measurableSet]
    exact hcont.aestronglyMeasurable isOpen_U.measurableSet
  · unfold HasFiniteIntegral
    have h1 := W.lintegral_theta_edens D hL.cont hE
    have h2 := hL.fin
    rw [h1] at h2
    have h3 : ∀ z, ‖U.indicator (fun z => cutoff Γ W.R z * D.edens L z) z‖ₑ =
        U.indicator (fun z => ENNReal.ofReal (W.χ z) * ENNReal.ofReal (D.edens L z)) z := by
      intro z
      by_cases hz : z ∈ U
      · simp only [Set.indicator_of_mem hz]
        rw [← ENNReal.ofReal_mul (W.χ_nonneg z), Real.enorm_eq_ofReal]
        · rfl
        · exact mul_nonneg (W.χ_nonneg z) (D.edens_nonneg L z)
      · simp [Set.indicator_of_notMem hz]
    simp_rw [h3]
    rw [lintegral_indicator isOpen_U.measurableSet]
    exact h2


open TernaryPeriodPolynomials.Argument.SeedC3S4c (LamGL)

/-- **Assembly core.**  For `m = n + 1`, the harmonic representative of the `L²` Hodge projection
(`HodgeDatum.exists_representative` for the Hodge datum of `Sym^{n+1}`) is the sum of two cusp
forms of weight `n + 3`: its `dz` coefficient is `F(τ) · coords ((τX₁ - X₀)^{n+1})` and its `dz̄`
coefficient is the conjugate of `G(τ) · coords ((τX₁ - X₀)^{n+1})`. -/
theorem ES_assembly_core {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∉ Γ)
    (n : ℕ) (W : Weights Γ) {Φ₁ : ℂ → Wd (n + 1 + 1)} (c : Γ → Wd (n + 1 + 1))
    (hΦ : ContDiffOn ℝ ∞ Φ₁ U)
    (hcoc : ∀ δ : Γ, ∀ z ∈ U, Φ₁ (mob (δ : SL(2, ℤ)) z) =
      (hodgeDatumSym (n + 1) Γ).ρ δ (Φ₁ z) + c δ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (h0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ Φ₁ z = 0) :
    ∃ (a' b' : ℂ → Wd (n + 1 + 1)) (F G : CuspForm (LamGL Γ) ((n + 3 : ℕ) : ℤ)),
      ContDiffOn ℝ ∞ a' U ∧ ContDiffOn ℝ ∞ b' U ∧
      (∀ z ∈ U, fderiv ℝ b' z (dir 0) = fderiv ℝ a' z (dir 1)) ∧
      (∀ z ∈ U, fderiv ℝ (fun z => (hodgeDatumSym (n + 1) Γ).H z (a' z)) z (dir 0) +
        fderiv ℝ (fun z => (hodgeDatumSym (n + 1) Γ).H z (b' z)) z (dir 1) = 0) ∧
      (hodgeDatumSym (n + 1) Γ).Eqv (formOf a' b') ∧
      Good (hodgeDatumSym (n + 1) Γ) W (formOf a' b') ∧
      (∀ hω : Good (hodgeDatumSym (n + 1) Γ) W (fun z => fderiv ℝ Φ₁ z),
        (((hodgeDatumSym (n + 1) Γ).xvec W hω -
          (hodgeDatumSym (n + 1) Γ).projB W ((hodgeDatumSym (n + 1) Γ).xvec W hω) :
            Hs (n + 1 + 1)) : ℂ → XP (Wd (n + 1 + 1))) =ᵐ[volume.restrict U]
          (hodgeDatumSym (n + 1) Γ).wcoord W (formOf a' b')) ∧
      ∀ z ∈ U, ∀ i, coefA a' b' z i =
          (TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Γ) n F z •
            coords (n + 1) ((C z * X 1 - X 0 : MvPolynomial (Fin 2) ℂ) ^ (n + 1))) i ∧
        coefB a' b' z i = starRingEnd ℂ
          ((TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Γ) n G z •
            coords (n + 1) ((C z * X 1 - X 0 : MvPolynomial (Fin 2) ℂ) ^ (n + 1))) i) := by
  obtain ⟨a', b', ha, hb, hcl, hco, hE, hG, hae⟩ :=
    (hodgeDatumSym (n + 1) Γ).exists_representative W c hΦ hcoc hK hKU h0
  have hE' : (hodgeDatumSym (n + 1) Γ).Eqv (formOfPair a' b') := by
    rw [← formOf_eq_formOfPair]; exact hE
  have hen : Integrable (fun z => if z ∈ U then
      cutoff Γ W.R z * (hodgeDatumSym (n + 1) Γ).edens (formOfPair a' b') z else 0) := by
    rw [← formOf_eq_formOfPair]
    exact integrable_cutoff_edens _ W hG hE
  obtain ⟨F, G, hFG⟩ := cuspForms_of_pair (Γ := Γ) (m := n + 1) (by omega) hneg W.hR ha hb hcl hco
    hE' hen
  refine ⟨a', b', F, G, ha, hb, hcl, hco, hE, hG, hae, fun z hz i => ?_⟩
  obtain ⟨h1, h2⟩ := hFG ⟨z, hz⟩
  have hcF : TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Γ) n F z = F ⟨z, hz⟩ := by
    simp [TernaryPeriodPolynomials.Argument.SeedC3.cuspH,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hcG : TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Γ) n G z = G ⟨z, hz⟩ := by
    simp [TernaryPeriodPolynomials.Argument.SeedC3.cuspH,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  refine ⟨?_, ?_⟩
  · have := congrFun h1 i
    have hc := congrFun (frameE_last_eq_coords (n + 1) z) i
    rw [hcF]
    simp only at this ⊢
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul, hc]
  · have := congrFun h2 i
    have hc := congrFun (frameE_last_eq_coords (n + 1) z) i
    rw [hcG]
    simp only at this ⊢
    rw [this, conj_smul_frameE_zero]
    simp only [Pi.smul_apply, smul_eq_mul, hc]

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
