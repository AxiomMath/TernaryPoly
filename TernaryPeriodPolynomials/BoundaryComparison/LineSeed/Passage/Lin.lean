module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Face

@[expose] public section


/-!
# Linearity of the line seed classes in the level-one form (Passage, part D1)

For a level-one cusp form `f` and `c : ℂ` the moment primitives of `c • f` are `c` times those of `f` on the upper half plane (uniqueness of the normalized primitives), so the zig-zag cochain of the line seed of
`levelN N (c • f)` is `c` times that of `levelN N f` (`lineNChain_levelN_smul`), and that of the antiholomorphic seed is `conj c` times (`lineNConjChain_levelN_smul`).  Hence the face seed classes
(`lineFaceSeedKerClass_levelN_smul`, `lineFaceSeedConjKerClass_levelN_smul`) are linear, resp. conjugate-linear, in `f`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory groupCohomology

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

variable {n : ℕ}

/-- The normalized moment primitives are homogeneous in the level-one form (on the upper half plane). -/
theorem momentPrim_smul1 (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (j : ℕ) {w : ℂ} (hw : 0 < w.im) :
    momentPrim Lvl1 n (c • f) j w = c * momentPrim Lvl1 n f j w := by
  symm
  refine momentPrim_unique (c • f) (fun j z => c * momentPrim Lvl1 n f j z) (fun j => by
    show c * momentPrim Lvl1 n f j Complex.I = 0
    rw [momentPrim_zero, mul_zero]) (fun j z hz => ?_) j hw
  have := (momentPrim_hasDerivAt Lvl1 n f j z hz).const_mul c
  have e : (c • f) (UpperHalfPlane.ofComplex z) * z ^ j = c * (cuspH Lvl1 n f z * z ^ j) := by
    change c * f (UpperHalfPlane.ofComplex z) * z ^ j = c * (f (UpperHalfPlane.ofComplex z) * z ^ j)
    ring
  rw [e]
  exact this

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem lineNChain_levelN_smul (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineNChain (levelN N (c • f)) x y = c • lineNChain (levelN N f) x y := by
  apply Coef.toPoly_injective
  have hw : 0 < (mob ((gammaNQLineData N).lam y) Complex.I).im :=
    mob_im_pos _ (by rw [(gammaNQLineData N).det_one y]; simp) (by simp)
  unfold lineNChain
  rw [Coef.toPoly_smul, TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain,
    TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [momentPrim_levelN N _ _ hw, momentPrim_smul1 c f _ hw]
  conv_rhs => rw [← mul_assoc, ← MvPolynomial.C_mul]
  congr 2
  ring

omit [NeZero N] in
theorem conjCoef_smul (c : ℂ) (q : Coef n) : Coef.conjCoef (c • q) = (starRingEnd ℂ c) • Coef.conjCoef q := by
  apply Coef.toPoly_injective
  simp [Coef.toPoly_conjCoef, map_mul, MvPolynomial.map_C]

omit [NeZero N] in
theorem lineNConjChain_levelN_smul (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineNConjChain (levelN N (c • f)) x y = (starRingEnd ℂ c) • lineNConjChain (levelN N f) x y := by
  rw [lineNConjChain_eq, lineNConjChain_eq, lineNChain_levelN_smul, conjCoef_smul]

end


section Classes

variable {n : ℕ} (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem lineNCocycle₂_levelN_smul (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineNCocycle₂ (levelN N (c • f)) = c • lineNCocycle₂ (levelN N f) := by
  apply Subtype.ext
  funext p
  exact lineNChain_levelN_smul N c f p.1 p.2

omit [NeZero N] in
theorem lineNConjCocycle₂_levelN_smul (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineNConjCocycle₂ (levelN N (c • f)) = (starRingEnd ℂ c) • lineNConjCocycle₂ (levelN N f) := by
  apply Subtype.ext
  funext p
  exact lineNConjChain_levelN_smul N c f p.1 p.2

theorem lineFaceSeedKerClass_levelN_smul (h : SL(3, ℤ)) (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineFaceSeedKerClass N n h (levelN N (c • f)) = c • lineFaceSeedKerClass N n h (levelN N f) := by
  have e : lineNSeedKerClass (levelN N (c • f)) = c • lineNSeedKerClass (levelN N f) := by
    unfold lineNSeedKerClass
    have : lineNRel (levelN N (c • f)) = c • lineNRel (levelN N f) :=
      Subtype.ext (lineNCocycle₂_levelN_smul N c f)
    rw [this, map_smul]
  unfold lineFaceSeedKerClass
  rw [e, map_smul]

theorem lineFaceSeedConjKerClass_levelN_smul (h : SL(3, ℤ)) (c : ℂ) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    lineFaceSeedConjKerClass N n h (levelN N (c • f)) =
      (starRingEnd ℂ c) • lineFaceSeedConjKerClass N n h (levelN N f) := by
  have e : lineNSeedConjKerClass (levelN N (c • f)) = (starRingEnd ℂ c) • lineNSeedConjKerClass (levelN N f) := by
    unfold lineNSeedConjKerClass
    have : lineNConjRel (levelN N (c • f)) = (starRingEnd ℂ c) • lineNConjRel (levelN N f) :=
      Subtype.ext (lineNConjCocycle₂_levelN_smul N c f)
    rw [this, map_smul]
  unfold lineFaceSeedConjKerClass
  rw [e, map_smul]

end Classes

end TernaryPeriodPolynomials.Argument.LineSeed
