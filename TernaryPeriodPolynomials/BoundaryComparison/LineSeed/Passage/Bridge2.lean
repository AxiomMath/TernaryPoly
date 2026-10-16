module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge1
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageForms

@[expose] public section


/-!
# Seed cochains along the pivot embedding (Passage bridge, part 2)

Along `piMap : Γ(N) ∩ Q(ℤ) → Λ₁⁺` the line data of `Λ₁⁺` is that of `Γ(N) ∩ Q(ℤ)` (`linePlusV_piMap`, `lmat_piMap`, `rhoC_piMap`), and the closed formula of the zig-zag cochain of the line seed
(`toPoly_cuspSeedCochain`, which involves only `lam`, `v`, `lmat` and the values of the moment primitives on the upper half plane) gives
`lineSeedChain f (π x) (π y) = lineNChain (levelN N f) x y` for a level-one cusp form `f` (`lineSeedChain_piMap`); the same for the antiholomorphic seed (`lineSeedConjChain_piMap`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.KDaggerComparison (levelN)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (momentPrim_unique Lvl1)
open TernaryPeriodPolynomials.Argument.SeedC3

section

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N)

omit [NeZero N] in
theorem linePlusV_piMap (x : ↥(gammaNQ N)) : linePlusData.v (piMap N h3 x) = (gammaNQLineData N).v x := by
  funext i
  fin_cases i <;> simp [linePlusData, linePlusV, gammaNQLineData, gammaNQV, piMap_val, Fin.rev]

omit [NeZero N] in
theorem lmat_piMap (x : ↥(gammaNQ N)) : linePlusData.lmat (piMap N h3 x) = (gammaNQLineData N).lmat x := by
  simp only [LineData.lmat, linePlusLam_piMap, linePlusV_piMap]

omit [NeZero N] in
theorem sigma_piMap (x : ↥(gammaNQ N)) : linePlusData.sigma (piMap N h3 x) = (gammaNQLineData N).sigma x :=
  Units.ext (lmat_piMap N h3 x)

omit [NeZero N] in
theorem rhoC_piMap (n : ℕ) (x : ↥(gammaNQ N)) :
    linePlusData.rhoC n (piMap N h3 x) = (gammaNQLineData N).rhoC n x := by
  simp only [LineData.rhoC, MonoidHom.coe_comp, Function.comp_apply, sigma_piMap]

omit [NeZero N] in
/-- The moment primitives of the restriction `levelN N f` to `Γ₂(N)` agree with those of `f` on the upper half plane. -/
theorem momentPrim_levelN {n : ℕ} (f : CuspForm (Lvl1) ((n + 3 : ℕ) : ℤ)) (j : ℕ) {w : ℂ} (hw : 0 < w.im) :
    momentPrim (leviGroup N) n (levelN N f) j w = momentPrim Lvl1 n f j w :=
  momentPrim_unique f (momentPrim (leviGroup N) n (levelN N f)) (momentPrim_zero (leviGroup N) n (levelN N f))
    (fun j z hz => momentPrim_hasDerivAt (leviGroup N) n (levelN N f) j z hz) j hw


omit [NeZero N] in
theorem lineSeedChain_piMap {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineSeedChain f (piMap N h3 x) (piMap N h3 y) = lineNChain (levelN N f) x y := by
  apply Coef.toPoly_injective
  change Coef.toPoly (cuspSeedCochain linePlusData linePlus_hΛ (f := f) (piMap N h3 x) (piMap N h3 y)) =
    Coef.toPoly (cuspSeedCochain (gammaNQLineData N) (gammaNQ_lam_mem_levi N) (f := levelN N f) x y)
  rw [TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain,
    TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain, linePlusV_piMap, lmat_piMap,
    linePlusLam_piMap]
  have hw : 0 < (mob ((gammaNQLineData N).lam y) Complex.I).im :=
    mob_im_pos _ (by rw [(gammaNQLineData N).det_one y]; simp) (by simp)
  simp only [momentPrim_levelN N f _ hw]

omit [NeZero N] in
theorem lineSeedConjChain_piMap {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineSeedConjChain f (piMap N h3 x) (piMap N h3 y) = lineNConjChain (levelN N f) x y := by
  rw [lineSeedConjChain_eq, lineNConjChain_eq, lineSeedChain_piMap N h3]

end

end TernaryPeriodPolynomials.Argument.LineSeed
