module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Approximate
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PeriodContinuity

@[expose] public section


/-!
# The harmonic representative is cohomologous to the original cocycle

Let `Φ₁` be smooth on the upper half plane `U` with `Φ₁(δ z) = ρ(δ) Φ₁(z) + c(δ)` and differential
supported compactly modulo `Γ`, and let `a dx + b dy` be the smooth closed equivariant form
representing `ω - P_B ω` (`ω = dΦ₁`) given by `exists_representative`.  Then `a dx + b dy` has a
smooth primitive `Φ₀` on the convex set `U` (`exists_primitive`), which transforms by a cocycle `c₀`
(`exists_cocycle`), and `c - c₀` is a coboundary (`coboundary_of_projection`): the difference
`Ψ = Φ₁ - Φ₀` is a limit in `L²_loc` of differentials of equivariant approximants
(`exists_approximants`, since `P_B ω` lies in the closure of the exact forms), so the period
continuity theorem `PeriodContinuity.isCoboundary_of_tendsto` applies.

The primitive, cocycle and approximation lemmas (`L2/Primitive.lean`, `L2/Approximate.lean`) are by
Claude Sonnet 5.5; this module is
Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace L2

open MeasureTheory Set Filter Topology Complex UpperHalfPlane
open scoped ContDiff InnerProductSpace MatrixGroups ENNReal NNReal

open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)
open TernaryPeriodPolynomials.Argument.ESFoundations.Weyl (XP dir)

variable {Γ : Subgroup SL(2, ℤ)} {d : ℕ}

namespace HodgeDatum

variable (D : HodgeDatum Γ d) (W : Weights Γ)

/-- **Cohomologous to the harmonic representative.** -/
theorem coboundary_of_projection {Φ₁ : ℂ → Wd d} (c : Γ → Wd d)
    (hΦ : ContDiffOn ℝ ∞ Φ₁ U)
    (hcoc : ∀ δ : Γ, ∀ z ∈ U, Φ₁ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (Φ₁ z) + c δ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (h0 : ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ Φ₁ z = 0)
    {a b : ℂ → Wd d} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hcl : ∀ z ∈ U, fderiv ℝ b z (dir 0) = fderiv ℝ a z (dir 1)) (hE : D.Eqv (formOf a b))
    (hae : ∀ hω : Good D W (fun z => fderiv ℝ Φ₁ z),
      ((D.xvec W hω - D.projB W (D.xvec W hω) : Hs d) : ℂ → XP (Wd d)) =ᵐ[volume.restrict U]
        D.wcoord W (formOf a b)) :
    ∃ Φ₀ : ℂ → Wd d, ∃ c₀ : Γ → Wd d, (∀ z ∈ U, HasFDerivAt Φ₀ (formOf a b z) z) ∧
      (∀ δ : Γ, ∀ z ∈ U, Φ₀ (mob (δ : SL(2, ℤ)) z) = D.ρ δ (Φ₀ z) + c₀ δ) ∧
      ∃ w : Wd d, ∀ δ : Γ, c δ - c₀ δ = D.ρ δ w - w := by
  have hω : Good D W (fun z => fderiv ℝ Φ₁ z) := good_of_cocycle D W c hΦ hcoc hK hKU h0
  obtain ⟨Φ₀, hΦ₀, hder⟩ := exists_primitive ha hb hcl
  obtain ⟨c₀, hc₀⟩ := D.exists_cocycle hder hE
  refine ⟨Φ₀, c₀, hder, hc₀, ?_⟩
  have hdiff0 : ∀ z ∈ U, DifferentiableAt ℝ Φ₀ z := fun z hz => (hder z hz).differentiableAt
  have hdiff1 : ∀ z ∈ U, DifferentiableAt ℝ Φ₁ z := fun z hz =>
    (hΦ.differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hz)
  have hΨd : ∀ z ∈ U, fderiv ℝ (fun w => Φ₁ w - Φ₀ w) z = fderiv ℝ Φ₁ z - formOf a b z := by
    intro z hz
    rw [fderiv_fun_sub (hdiff1 z hz) (hdiff0 z hz), (hder z hz).fderiv]
  have hΨ1 : ContDiffOn ℝ 1 (fun w => Φ₁ w - Φ₀ w) U :=
    (hΦ.of_le (by exact_mod_cast le_top)).sub (hΦ₀.of_le (by exact_mod_cast le_top))
  obtain ⟨φ, hφ, hlim⟩ := exists_approximants D W hω (contDiffOn_formOf ha hb).continuousOn
    (hae hω) hΨd
  have key := PeriodContinuity.isCoboundary_of_tendsto (Γ := Γ) (W := Wd d)
    (fun δ => (D.ρR δ).toLinearMap) (fun δ => c δ - c₀ δ) hΨ1
    (fun δ z hz => by
      show Φ₁ _ - Φ₀ _ = D.ρ δ (Φ₁ z - Φ₀ z) + (c δ - c₀ δ)
      rw [hcoc δ z hz, hc₀ δ z hz, map_sub]
      abel)
    (fun j => (hφ j).1.of_le (by exact_mod_cast le_top))
    (fun j δ z hz => (hφ j).2.1 δ z hz)
    (fun K hK hKU => by
      have := hlim K hK hKU
      have e : ∀ j, ∫ z in K, ‖fderiv ℝ (φ j) z - fderiv ℝ (fun w => Φ₁ w - Φ₀ w) z‖ ^ 2 =
          ∫ z in K, ‖fderiv ℝ (φ j) z - fderiv ℝ (fun w => Φ₁ w - Φ₀ w) z‖ ^ 2 := fun _ => rfl
      exact this)
  obtain ⟨w, hw⟩ := key
  exact ⟨w, hw⟩

end HodgeDatum

end L2
end TernaryPeriodPolynomials.Argument.ESFoundations
