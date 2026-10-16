module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalCup

@[expose] public section


/-!
# A homomorphism sums to zero over the cusp generators

Formalized by Claude Sonnet 5.5.

`hom_cusp_sum_zero`: for `N ≥ 3`, every homomorphism `φ : Γ(N) → ℂ` satisfies `∑_{c ∈ cusp orbit reps} φ(σ_c) = 0`.  It is the cusp formula `pV_bdry_eq` for the trivial
coefficient system, the strictly equivariant function `Φ = 1` (whose boundary `dΦ` vanishes) and the cochain `G` with `coc G = φ`.
`cusp_sum_eq_of_relation`: two solutions of the same relation `η(xy) = η x + η y - z x y` have the same cusp sums.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N : ℕ}

/-- **A homomorphism `Γ(N) → ℂ` sums to zero over the cusp generators `σ_c`.** -/
theorem hom_cusp_sum_zero (hN : 3 ≤ N) (φ : gammaNGL N → ℂ) (hφ : ∀ g h, φ (g * h) = φ g + φ h) :
    ∑ c ∈ (cuspReps hN).R, φ (cuspSigma c) = 0 := by
  let A : Rep ℂ (gammaNGL N) := Rep.trivial ℂ (gammaNGL N) ℂ
  have hρ : ∀ (g : gammaNGL N) (v : ℂ), A.ρ g v = v := fun g v => rfl
  have hmem : φ ∈ groupCohomology.cocycles₁ A := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    change φ (g * h) = A.ρ g (φ h) + φ g
    rw [hρ, hφ]
    ring
  obtain ⟨G, hG⟩ := cohMap_surjective A (gammaNFareyData hN) (groupCohomology.H1π A ⟨φ, hmem⟩)
  rw [cohMap_apply, groupCohomology.H1π_eq_iff] at hG
  obtain ⟨u, hu⟩ := hG
  have hcoc : ∀ γ, coc A.ρ G γ = φ γ := by
    intro γ
    have := congrFun hu γ
    simp only [groupCohomology.d₀₁_hom_apply] at this
    change A.ρ γ u - u = coc A.ρ G γ - φ γ at this
    rw [hρ] at this
    linear_combination -this
  let C : Coupling A.ρ A.ρ :=
    { e := LinearMap.mul ℂ ℂ
      inv := fun γ v w => by simp only [hρ]
      left := fun v hv => by have := hv 1; rwa [LinearMap.mul_apply', mul_one] at this
      right := fun w hw => by have := hw 1; rwa [LinearMap.mul_apply', one_mul] at this }
  have hΦ : (fun _ : RationalLine2 => (1 : ℂ)) ∈ EqFn (gammaNGL N) RationalLine2 A.ρ := fun γ x => (hρ γ 1).symm
  have key := pV_bdry_eq hN C hΦ G
  have hb : bdryTw A.ρ hN ⟨fun _ : RationalLine2 => (1 : ℂ), eqFn_le_Tw A.ρ hΦ⟩ = 0 := by
    apply Subtype.ext
    funext q
    rw [bdryTw_apply]
    simp
  rw [hb, map_zero, LinearMap.zero_apply] at key
  have hs : ∑ c ∈ (cuspReps hN).R, C.e 1 (coc A.ρ G (cuspSigma c)) = ∑ c ∈ (cuspReps hN).R, φ (cuspSigma c) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    change (1 : ℂ) * coc A.ρ G (cuspSigma c) = _
    rw [hcoc, one_mul]
  rw [hs] at key
  exact (mul_eq_zero.1 key.symm).resolve_left two_ne_zero

/-- **Cusp sums of two solutions of the same relation agree**: if `η₁, η₂ : Γ(N) → ℂ` both satisfy `η(x y) = η x + η y - z x y`, then `η₁ - η₂` is a homomorphism and
`∑_c η₁(σ_c) = ∑_c η₂(σ_c)`. -/
theorem cusp_sum_eq_of_relation (hN : 3 ≤ N) (z : gammaNGL N → gammaNGL N → ℂ) (η₁ η₂ : gammaNGL N → ℂ)
    (h₁ : ∀ x y, η₁ (x * y) = η₁ x + η₁ y - z x y) (h₂ : ∀ x y, η₂ (x * y) = η₂ x + η₂ y - z x y) :
    ∑ c ∈ (cuspReps hN).R, η₁ (cuspSigma c) = ∑ c ∈ (cuspReps hN).R, η₂ (cuspSigma c) := by
  have := hom_cusp_sum_zero hN (fun g => η₁ g - η₂ g) (fun g h => by simp only [h₁, h₂]; ring)
  simp only [Finset.sum_sub_distrib] at this
  linear_combination this

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
