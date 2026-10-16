module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceAction

@[expose] public section


/-!
# The inner elements act trivially on the cuspidal group

Formalized by Claude Sonnet 5.5.

If `g` acts as an inner element `e ∈ E` (`θ g = conj e`, `T g = ρ(e)`), then `leviAct g` is the Levi action of `rightHom e` on `H¹(N, ρ)` (`leviAct_inner`: the radical part of `e` acts trivially on the cohomology of the abelian radical,
`h1_eq_of_twist`) and `cuspAct g` is the identity (`cuspAct_inner`: inner automorphisms act trivially on `H¹(Γ(N), -)`).  Hence the action of the covering group factors through the quotient by the face group `E` of `Γ(N)`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames

variable {N : ℕ} {hN : 3 ≤ N} {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} {ρ : Rep ℂ E}
  {G : Type} [Group G] (F : FaceAction hN ext ρ G) (s : ext.Splitting) (g : G) (e : E)
  (hθ : ∀ e', F.θ g e' = e * e' * e⁻¹) (hTe : ∀ v, F.T g v = ρ.ρ e v)

include s hθ in
theorem FaceAction.alpha_inner (l' : Gamma N) : F.α g l' = ext.rightHom e * l' * (ext.rightHom e)⁻¹ := by
  have e1 : ext.rightHom (s l') = l' := s.rightInverse_rightHom _
  have h := F.rightHom_comm g (s l')
  rw [hθ, e1] at h
  rw [← h, map_mul, map_mul, map_inv, e1]

/-- Every element of the extension is a radical element times the section of its Levi image. -/
theorem decomp_inner (s : ext.Splitting) (e : E) : ∃ n : RadicalLattice, e = ext.inl n * s (ext.rightHom e) := by
  have e1 : ext.rightHom (s (ext.rightHom e)) = ext.rightHom e := s.rightInverse_rightHom _
  have h1 : ext.rightHom (e * (s (ext.rightHom e))⁻¹) = 1 := by
    rw [map_mul, map_inv, e1, mul_inv_cancel]
  have h2 : e * (s (ext.rightHom e))⁻¹ ∈ ext.inl.range := by
    rw [ext.range_inl_eq_ker_rightHom]; exact h1
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

include hθ hTe in
/-- **An inner element acts on `H¹(N, ρ)` as its Levi image.** -/
theorem FaceAction.leviAct_inner (v : splitRadicalH1Representation s ρ) :
    F.leviAct s g v = (splitRadicalH1Representation s ρ).ρ (ext.rightHom e) v := by
  obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext.inl ρ) v
  obtain ⟨n, hn⟩ := decomp_inner s e
  change radXi (F.twist g) ρ ρ (F.T g) (F.hTtw g) _ = splitRadicalH1Action s ρ (ext.rightHom e) _
  rw [radXi_π, splitRadicalH1Action_apply]
  refine h1_eq_of_twist ext ρ _ _ n 0 (fun r => ?_)
  simp only [oneCocyclePullback_apply, splitRadicalCocycleAction_apply, map_zero, sub_zero, add_zero]
  have hφ : (F.twist g).φ.toMonoidHom r = splitRadicalInput s (ext.rightHom e) r := by
    apply ext.inl_injective
    have h1 : ext.inl ((F.twist g).φ.toMonoidHom r) = e⁻¹ * ext.inl r * e := by
      show ext.inl ((F.φ g).symm r) = _
      have := F.inl_comm g ((F.φ g).symm r)
      rw [MulEquiv.apply_symm_apply, hθ] at this
      calc ext.inl ((F.φ g).symm r) = e⁻¹ * (e * ext.inl ((F.φ g).symm r) * e⁻¹) * e := by group
        _ = e⁻¹ * ext.inl r * e := by rw [this]
    have h2 := splitRadicalInput_commute s (ext.rightHom e) r
    have hab : (ext.inl n)⁻¹ * ext.inl r * ext.inl n = ext.inl r := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm n⁻¹ r, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1]
    calc e⁻¹ * ext.inl r * e = (s (ext.rightHom e))⁻¹ * ((ext.inl n)⁻¹ * ext.inl r * ext.inl n) * s (ext.rightHom e) := by
          conv_lhs => rw [hn]
          simp only [mul_inv_rev, mul_assoc]
      _ = (s (ext.rightHom e))⁻¹ * (ext.inl r * s (ext.rightHom e)) := by rw [hab, mul_assoc]
      _ = ext.inl (splitRadicalInput s (ext.rightHom e) r) := by rw [h2, inv_mul_cancel_left]
  have hρe : ρ.ρ e = ρ.ρ (ext.inl n) * ρ.ρ (s (ext.rightHom e)) := by rw [← map_mul, ← hn]
  rw [hφ]
  simp only [LinearEquiv.coe_coe]
  rw [hTe, hρe, Module.End.mul_apply]

include hθ hTe in
/-- **The inner elements act trivially on the cuspidal group.** -/
theorem FaceAction.cuspAct_inner (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) :
    F.cuspAct s g x = x := by
  apply Subtype.ext
  rw [FaceAction.cuspAct_val]
  obtain ⟨c, hc⟩ := oneCocycle_H1_surjective (splitRadicalH1Representation s ρ) x.1
  rw [← hc, oneCocyclePullbackH1_apply, groupCohomology.H1π_eq_iff]
  have hα_all := F.alpha_inner s g e hθ
  have hlev := F.leviAct_inner s g e hθ hTe
  generalize ext.rightHom e = l at hα_all hlev
  refine ⟨c.1 l, ?_⟩
  funext l'
  simp only [groupCohomology.d₀₁_hom_apply]
  have hα : (F.twist g).α.toMonoidHom l' = l⁻¹ * l' * l := by
    show (F.α g).symm l' = _
    rw [MulEquiv.symm_apply_eq, hα_all]
    group
  have h1 := oneCocycle_mul (splitRadicalH1Representation s ρ) c l (l⁻¹ * l' * l)
  have h2 := oneCocycle_mul (splitRadicalH1Representation s ρ) c l' l
  rw [Pi.sub_apply, oneCocyclePullback_apply, hα, hlev]
  have e1 : l * (l⁻¹ * l' * l) = l' * l := by group
  rw [e1] at h1
  change (splitRadicalH1Representation s ρ).ρ l' (c l) - c l =
    (splitRadicalH1Representation s ρ).ρ l (c (l⁻¹ * l' * l)) - c l'
  linear_combination (norm := abel) h1 - h2

end TernaryPeriodPolynomials.Argument.FaceDescent
