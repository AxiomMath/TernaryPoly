module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Cohomology

@[expose] public section


open CategoryTheory

/-!
# The Levi action on `H²(N, E)` is an action, independent of the splitting

Formalized by Claude Sonnet 5.5.

`splitRadicalH2Action s ρ` is a left action of `L` on `H²(N, E)`
(`splitRadicalH2Action_one`, `_mul`, bundled as `splitRadicalH2Representation`), and it does not depend on the splitting `s` of the extension
(`splitRadicalH2Action_splitting_indep`): two lifts of `l` differ by an element of `N`, and inner automorphisms of `N` act trivially on `H²(N, E|_N)`
(`GammaNStokes.h2Map_conj_self`).  In particular the invariants `splitRadicalH2Invariants` of the right edge depend only on the extension.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (s : ext.Splitting) (ρ : Rep ℂ E)

theorem splitRadicalH2Action_one (y : groupCohomology.H2 (Rep.res ext.inl ρ)) :
    splitRadicalH2Action s ρ 1 y = y := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ext.inl ρ) y
  rw [splitRadicalH2Action_π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine (splitRadicalH2Action_cocycle s ρ 1 z a b).trans ?_
  rw [splitRadicalInput_one, splitRadicalInput_one, map_one, map_one]
  rfl

theorem splitRadicalH2Action_mul (l₁ l₂ : L) (y : groupCohomology.H2 (Rep.res ext.inl ρ)) :
    splitRadicalH2Action s ρ (l₁ * l₂) y =
      splitRadicalH2Action s ρ l₁ (splitRadicalH2Action s ρ l₂ y) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ext.inl ρ) y
  rw [splitRadicalH2Action_π, splitRadicalH2Action_π, splitRadicalH2Action_π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  have e1 := splitRadicalH2Action_cocycle s ρ (l₁ * l₂) z a b
  have e2 := splitRadicalH2Action_cocycle s ρ l₁ (groupCohomology.mapCocycles₂ (splitRadicalInput s l₂)
    (EdgeNat.comparison (splitRadicalInput s l₂) (Rep.res ext.inl ρ) (Rep.res ext.inl ρ) (ρ.ρ (s l₂))
      (splitRadicalH2_hT s ρ l₂)) z) a b
  have e3 := splitRadicalH2Action_cocycle s ρ l₂ z (splitRadicalInput s l₁ a) (splitRadicalInput s l₁ b)
  refine e1.trans (Eq.trans ?_ (e2.trans (congrArg (ρ.ρ (s l₁)) e3)).symm)
  rw [splitRadicalInput_mul, splitRadicalInput_mul, map_mul, map_mul]
  rfl

/-- **The Levi representation on `H²(N, E)`.** -/
def splitRadicalH2Representation : Representation ℂ L (groupCohomology.H2 (Rep.res ext.inl ρ)) where
  toFun l := splitRadicalH2Action s ρ l
  map_one' := LinearMap.ext (splitRadicalH2Action_one s ρ)
  map_mul' l₁ l₂ := LinearMap.ext (splitRadicalH2Action_mul s ρ l₁ l₂)


/-- Two lifts of `l ∈ L` differ by an element of the radical. -/
theorem splitting_lift_diff (s s' : ext.Splitting) (l : L) : ∃ n : N, s' l = s l * ext.inl n := by
  have hmem : (s l)⁻¹ * s' l ∈ ext.rightHom.ker := by
    have hs : ext.rightHom (s l) = l := s.rightInverse_rightHom l
    have hs' : ext.rightHom (s' l) = l := s'.rightInverse_rightHom l
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, hs', inv_mul_cancel]
  rw [← ext.range_inl_eq_ker_rightHom] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, by rw [hn]; group⟩

/-- **The Levi action on `H²(N, E)` does not depend on the splitting**: two lifts of `l` differ by an element `n` of the radical, which acts trivially on
`H²(N, E|_N)` (inner automorphisms, `GammaNStokes.h2Map_conj_self`). -/
theorem splitRadicalH2Action_splitting_indep (s s' : ext.Splitting) (l : L)
    (y : groupCohomology.H2 (Rep.res ext.inl ρ)) :
    splitRadicalH2Action s' ρ l y = splitRadicalH2Action s ρ l y := by
  obtain ⟨n, hn⟩ := splitting_lift_diff s s' l
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.res ext.inl ρ) y
  have key : ∀ (t : ext.Splitting) (a : N), ext.inl (splitRadicalInput t l a) = (t l)⁻¹ * ext.inl a * t l := by
    intro t a
    have := splitRadicalInput_commute t l a
    rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
  have hα : ∀ a, splitRadicalInput s' l a = n⁻¹ * splitRadicalInput s l a * n := by
    intro a
    apply ext.inl_injective
    rw [key s' a, hn, map_mul, map_mul, map_inv, key s a, mul_inv_rev]
    group
  have key2 := TernaryPeriodPolynomials.Argument.GammaNStokes.h2Map_conj_self (Rep.res ext.inl ρ) n⁻¹
    (groupCohomology.H2π (Rep.res ext.inl ρ) z)
  rw [EdgeNat.h2Map_π] at key2
  conv_rhs => rw [← key2]
  rw [splitRadicalH2Action_π, splitRadicalH2Action_π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine (splitRadicalH2Action_cocycle s' ρ l z a b).trans (Eq.trans ?_ (splitRadicalH2Action_cocycle s ρ l _ a b).symm)
  change ρ.ρ (s' l) (z.1 (splitRadicalInput s' l a, splitRadicalInput s' l b)) =
    ρ.ρ (s l) ((Rep.res ext.inl ρ).ρ n⁻¹⁻¹ (z.1 (n⁻¹ * splitRadicalInput s l a * n⁻¹⁻¹, n⁻¹ * splitRadicalInput s l b * n⁻¹⁻¹)))
  rw [hα, hα, hn, inv_inv]
  simp only [map_mul, Module.End.mul_apply]
  rfl

end TernaryPeriodPolynomials.Argument.RightEdge
