module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.TwistKoszul
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# Restriction of a face to a finite-index subface: the radical level

Formalized by Claude Sonnet 5.5.

Setting: extensions `ℤ² → E₁ → Γ(N)` (splitting `s₁`) and `ℤ² → E₂ → Γ(M)` (splitting `s₂`), `Γ(M) ≤ Γ(N)`, a homomorphism `ι : E₂ → E₁` and `ψ : ℤ² → ℤ²` with `ι ∘ inl₂ = inl₁ ∘ ψ`, `ι ∘ s₂ = s₁ ∘ incl`,
coefficient modules `W₁`, `W₂` with `T : W₁ → W₂` equivariant over `ι`.  `radTr`: the transport `H¹(N₁, W₁) → H¹(N₂, W₂)`, `c ↦ T ∘ c ∘ ψ`; `radTr_levi`: it intertwines the Levi actions over `incl`;
`radPairing_tr`: the Koszul pairings satisfy `⟨Ξ x, Ξ' y⟩₂ = det(ψ) ⟨x, y⟩₁`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance

section Abs

variable {N M : ℕ} (hle : Gamma M ≤ Gamma N) {E₁ E₂ : Type} [Group E₁] [Group E₂]
  {ext₁ : GroupExtension RadicalLattice E₁ (Gamma N)} {ext₂ : GroupExtension RadicalLattice E₂ (Gamma M)}
  (s₁ : ext₁.Splitting) (s₂ : ext₂.Splitting) (ι : E₂ →* E₁) (ψ : RadicalLattice →* RadicalLattice)
  (hinl : ∀ r, ι (ext₂.inl r) = ext₁.inl (ψ r)) (hsplit : ∀ l, ι (s₂ l) = s₁ (Subgroup.inclusion hle l))

include hinl hsplit in
/-- The Levi actions on the radicals are compatible with `ψ` over `incl`. -/
theorem radInput_compat (m : Gamma M) (r : RadicalLattice) :
    splitRadicalInput s₁ (Subgroup.inclusion hle m) (ψ r) = ψ (splitRadicalInput s₂ m r) := by
  apply ext₁.inl_injective
  have h2 := splitRadicalInput_commute s₂ m r
  have h1 := splitRadicalInput_commute s₁ (Subgroup.inclusion hle m) (ψ r)
  have h3 := congrArg ι h2
  rw [map_mul, map_mul, hinl, hinl, hsplit] at h3
  exact mul_left_cancel (h1.symm.trans h3)

variable (W₁ : Rep ℂ E₁) (W₂ : Rep ℂ E₂) (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ e v, T (W₁.ρ (ι e) v) = W₂.ρ e (T v))

include hinl hT in
theorem radTr_inter (r : RadicalLattice) :
    ((Rep.res ext₂.inl W₂).ρ r).comp T = T.comp ((Rep.res ext₁.inl W₁).ρ (ψ r)) := by
  apply LinearMap.ext
  intro v
  change W₂.ρ (ext₂.inl r) (T v) = T (W₁.ρ (ext₁.inl (ψ r)) v)
  rw [← hinl, hT]

/-- **The transport of radical classes** `H¹(N₁, W₁) → H¹(N₂, W₂)`, `c ↦ T ∘ c ∘ ψ`. -/
def radTr (hinl : ∀ r, ι (ext₂.inl r) = ext₁.inl (ψ r)) :
    groupCohomology.H1 (Rep.res ext₁.inl W₁) →ₗ[ℂ] groupCohomology.H1 (Rep.res ext₂.inl W₂) :=
  oneCocyclePullbackH1 (Rep.res ext₁.inl W₁) (Rep.res ext₂.inl W₂) ψ T (radTr_inter ι ψ hinl W₁ W₂ T hT)

theorem radTr_π (c : groupCohomology.cocycles₁ (Rep.res ext₁.inl W₁)) :
    radTr ι ψ W₁ W₂ T hT hinl (groupCohomology.H1π _ c) = groupCohomology.H1π _
      (oneCocyclePullback (Rep.res ext₁.inl W₁) (Rep.res ext₂.inl W₂) ψ T (radTr_inter ι ψ hinl W₁ W₂ T hT) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

include hsplit in
/-- **`radTr` intertwines the Levi actions** (the Levi `Γ(M)` of the sub-face acts through `incl`). -/
theorem radTr_levi (m : Gamma M) (x : groupCohomology.H1 (Rep.res ext₁.inl W₁)) :
    radTr ι ψ W₁ W₂ T hT hinl (splitRadicalH1Action s₁ W₁ (Subgroup.inclusion hle m) x) =
      splitRadicalH1Action s₂ W₂ m (radTr ι ψ W₁ W₂ T hT hinl x) := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext₁.inl W₁) x
  rw [splitRadicalH1Action_apply, radTr_π, radTr_π, splitRadicalH1Action_apply]
  congr 1
  apply groupCohomology.cocycles₁_ext
  intro r
  simp only [oneCocyclePullback_apply, splitRadicalCocycleAction_apply]
  rw [radInput_compat hle s₁ s₂ ι ψ hinl hsplit, ← hsplit, hT]

variable [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] (T' : dualRepG W₁ →ₗ[ℂ] dualRepG W₂)
  (hT' : ∀ e v, T' ((dualRepG W₁).ρ (ι e) v) = (dualRepG W₂).ρ e (T' v)) (hSe : ∀ a b, T' b (T a) = b a)

include hSe in
/-- **The Koszul pairing of the radicals changes by `det ψ`** under the transport. -/
theorem radPairing_tr (x : groupCohomology.H1 (Rep.res ext₁.inl W₁))
    (y : groupCohomology.H1 (Rep.res ext₁.inl (dualRepG W₁))) :
    radPairingOf (ext := ext₂) (perfectInv_dual W₂) (radTr ι ψ W₁ W₂ T hT hinl x)
        (radTr ι ψ (dualRepG W₁) (dualRepG W₂) T' hT' hinl y) =
      (radDet ψ : ℂ) * radPairingOf (ext := ext₁) (perfectInv_dual W₁) x y := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    induction y using groupCohomology.H1_induction_on with
    | h c' =>
      rw [radTr_π, radTr_π, radPairingOf_spec, radPairingOf_spec]
      refine PhiC_xi (A₁ := Rep.res ext₁.inl W₁) (A₁' := Rep.res ext₁.inl (dualRepG W₁))
        (A₂ := Rep.res ext₂.inl W₂) (A₂' := Rep.res ext₂.inl (dualRepG W₂))
        (e₁ := Module.Dual.eval ℂ W₁) (e₂ := Module.Dual.eval ℂ W₂)
        (fun g a b => (perfectInv_dual W₁).inv (ext₁.inl g) a b) ψ T T' (fun r b => ?_) (fun a b => ?_) c c' _ _
        (fun r => rfl) (fun r => rfl)
      · change (dualRepG W₂).ρ (ext₂.inl r) (T' b) = T' ((dualRepG W₁).ρ (ext₁.inl (ψ r)) b)
        rw [← hinl, hT']
      · exact hSe a b

end Abs

end TernaryPeriodPolynomials.Argument.LevelDescent
