module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.BaseSumZeroBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HomCuspValues

@[expose] public section


/-!
# `Γ(N)` has at least two cusps, and a homomorphism of `Γ(N)` can be nonzero on any given cusp generator

Formalized by Claude Sonnet 5.5.

`exists_ne_cusp`: for `N ≥ 3` and a representative cusp `c`, there is another representative `c' ≠ c` (the cusps `⟨e₁⟩` and `⟨e₂⟩` are inequivalent, since `γ ∈ Γ(N)` has `γ₀₀ ≡ 1`).
`exists_hom_ne_zero`: there is an additive `φ : Γ(N) → ℚ` with `φ(σ_c) = 1`.
-/

open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNStokes

variable {N : ℕ}

theorem gammaN_cusp1_ne_cusp2 (hN : 3 ≤ N) (γ : gammaNGL N) : ((γ : gammaNGL N) : IntegralGL) • cusp1 ≠ cusp2 := by
  intro h
  have hg := isGen_smul' (γ : IntegralGL) (isGen_cusp1)
  have hc := (IsGen.line_eq_iff hg isGen_cusp2).1 h
  have hmem := (mem_gammaNGL.1 γ.2).1
  have h0 : ((γ : IntegralGL).val 0 0 : ℤ) = 0 := by
    rcases hc with hc | hc
    · have := congrFun hc 0
      simpa [e1, e2] using this.symm
    · have := congrFun hc 0
      simp [e1, e2] at this
      omega
  rw [h0] at hmem
  have : Fact (1 < N) := ⟨by omega⟩
  simp at hmem

theorem exists_ne_cusp (hN : 3 ≤ N) (c : RationalLine2) : ∃ c' ∈ (cuspReps hN).R, c' ≠ c := by
  obtain ⟨a, ha, γ1, h1⟩ := (cuspReps hN).cover cusp1
  obtain ⟨b, hb, γ2, h2⟩ := (cuspReps hN).cover cusp2
  by_contra hcon
  have hcon' : ∀ c' ∈ (cuspReps hN).R, c' = c := fun c' h => by
    by_contra hne
    exact hcon ⟨c', h, hne⟩
  have hac : a = c := hcon' a ha
  have hbc : b = c := hcon' b hb
  have : (γ2 * γ1⁻¹) • cusp1 = cusp2 := by
    rw [mul_smul, ← h1, inv_smul_smul, hac, ← hbc, h2]
  exact gammaN_cusp1_ne_cusp2 hN (γ2 * γ1⁻¹) this

theorem exists_hom_ne_zero (hN : 3 ≤ N) (c : ↥(cuspReps hN).R) :
    ∃ φ : gammaNGL N → ℚ, (∀ g h, φ (g * h) = φ g + φ h) ∧ φ (cuspSigma (c : RationalLine2)) = 1 := by
  obtain ⟨c', hc', hne⟩ := exists_ne_cusp hN (c : RationalLine2)
  let c'' : ↥(cuspReps hN).R := ⟨c', hc'⟩
  have hcc : c'' ≠ c := fun h => hne (congrArg Subtype.val h)
  let x : ↥(cuspReps hN).R → ℚ := fun d => (if d = c then 1 else 0) - (if d = c'' then 1 else 0)
  have hx : ∑ d, x d = 0 := by
    simp only [x, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
  obtain ⟨φ, hφ, hv⟩ := exists_hom_cusp_values hN x hx
  refine ⟨φ, hφ, ?_⟩
  rw [hv c]
  simp [x, hcc.symm]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
