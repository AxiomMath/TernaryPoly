module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ClassCocycle
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ReflSeed

@[expose] public section


/-!
# The class of the reflection-invariant line seed is determined by its edge (LS15b)

Line mirror of `SeedC3S4c.ReflectionDescent` (`complexify_reflSeed`, `edge_reflSeed`) and `SeedC3S4c.ClassIdentity.eq_seed_of_edge`.  For `n` odd and a level-one cusp form `f` of weight
`n + 3`, the relative cocycle `lineReflRel f` of `σ_f + (-1)ⁿ \overline{σ_{f^*}}` (the `ε = 1` combination `reflSeedInv … f 1`) has Hochschild-Serre edge `-6 · restriction [dlCocycleOf ψ_f]`
(`edge_lineReflRel`), where `ψ_f` is the arithmetic parity-`0` period cocycle of `f`; since the edge of `Λ₁⁺` is injective, any class of the kernel with this edge scaled by `(n+1)/2`... is
the complexified de Rham class (`eq_seed_of_edge_line`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses (binarySwap)
open TernaryPeriodPolynomials.SourceConstruction (dlIntPivot dlCocycleOf lineCocyclePhi)
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 conjB fStar)
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension (restriction restriction_apply restriction_intertwines)

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The relative cocycle of the `ε = 1` reflection-invariant line seed `σ_f + (-1)ⁿ \overline{σ_{f^*}}`. -/
def lineReflRel : relativeTwoCocycles linePlusExtensionS.inl (linePlusRep n) :=
  lineSeedRelCocycle f + (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • lineSeedConjRelCocycle (fStar f)

/-- **Complexification of the `ε`-isotypic line seed class.** -/
theorem lineComplexify_reflSeed :
    lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f 1)) =
      (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineReflRel f)).val := by
  have h1 := deRhamClass_reflSeedInv linePlusData linePlus_hΛ f 1
  have h2 := lineComplexify_cuspSeedClass f
  have h3 := lineComplexify_cuspSeedConjClass (fStar f)
  have h4 := (lineComplexify n).map_add (cuspSeedClass linePlusData linePlus_hΛ (f := f))
    (((1 : ℝ) * (-1 : ℝ) ^ n) • cuspSeedConjClass linePlusData linePlus_hΛ (f := fStar f))
  have h5 := (lineComplexify n).map_smul ((1 : ℝ) * (-1 : ℝ) ^ n)
    (cuspSeedConjClass linePlusData linePlus_hΛ (f := fStar f))
  have e1 := (congrArg (lineComplexify n) h1).trans h4
  have e2 := e1.trans (congrArg (HAdd.hAdd _) h5)
  have h6 := (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n)).map_add
    (lineSeedRelCocycle f) ((((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • lineSeedConjRelCocycle (fStar f))
  have h7 := (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n)).map_smul
    (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) (lineSeedConjRelCocycle (fStar f))
  have h8 := (congrArg Subtype.val (h6.trans (congrArg (HAdd.hAdd _) h7))).trans
    ((Submodule.coe_add _ _).trans (congrArg (HAdd.hAdd _) (Submodule.coe_smul _ _)))
  refine (e2.trans (congrArg₂ HAdd.hAdd h2 (congrArg (HSMul.hSMul _) h3))).trans
    (Eq.trans ?_ h8.symm)
  exact congrArg _ (Complex.coe_smul _ _).symm

variable (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)

/-- The arithmetic parity-`0` period cocycle of `f`, twist `0`. -/
def psiF (hodd : Odd n) : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  classicalArithmeticCocycle f (n + 1) hw hodd.add_one 0 0 (by norm_num)

include hw in
theorem dl_toGL (hodd : Odd n) (m : SpecialLinearGroup (Fin 2) ℤ) :
    ((dlCocycleOf n (psiF f hw hodd)) (SpecialLinearGroup.toGL m) : Binary.HomogeneousPoly (n + 1)) =
      (2 : ℂ)⁻¹ • binarySwap n (cB f hw (pvSL m) + rB f hw (pvSL m)) := by
  change binarySwap n ((psiF f hw hodd) (dlIntPivot (SpecialLinearGroup.toGL m))) = _
  rw [← toGL_pvSL]
  unfold psiF classicalArithmeticCocycle
  rw [arithmeticParityCocycle_specialLinear, modularCocycleParity_apply]
  change binarySwap n ((2 : ℂ)⁻¹ • (cB f hw (pvSL m) + (-1 : ℂ) ^ 0 • rB f hw (pvSL m))) = _
  rw [pow_zero, one_smul, map_smul]

include hw in
theorem edgeComb_eq (hodd : Odd n) (hn : 0 < n) :
    lineEdgeCocycle hn f + (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • lineConjEdgeCocycle hn (fStar f) =
      (-6 : ℂ) • oneCocyclePullback (arithmeticBinaryRep (n + 1) 0) (modularBinaryRep (n + 1) 0)
        SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines (n + 1) 0 0)
        (dlCocycleOf n (psiF f hw hodd)) := by
  apply groupCohomology.cocycles₁_ext
  intro m
  have hs : ((-1 : ℂ) ^ (n + 1)) = 1 := by
    obtain ⟨k, rfl⟩ := hodd
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
  have hk : (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) = -1 := by
    obtain ⟨k, rfl⟩ := hodd
    push_cast
    rw [pow_succ, pow_mul]; norm_num
  change (lineEdgeCocycle hn f m : Binary.HomogeneousPoly (n + 1)) +
      (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineConjEdgeCocycle hn (fStar f) m : Binary.HomogeneousPoly (n + 1)) =
    (-6 : ℂ) • ((dlCocycleOf n (psiF f hw hodd)) (SpecialLinearGroup.toGL m) : Binary.HomogeneousPoly (n + 1))
  rw [lineEdgeCocycle_apply, lineConjEdgeCocycle_apply, dl_toGL f hw hodd, epsB_eq f hw,
    conjB_epsB_fStar f hw, hs, hk, one_smul, one_smul, map_neg, map_add]
  generalize binarySwap n (cB f hw (pvSL m)) = X
  generalize binarySwap n (rB f hw (pvSL m)) = Y
  have key : ∀ X Y : Binary.HomogeneousPoly (n + 1), (-3 : ℂ) • X + (-1 : ℂ) • ((-3 : ℂ) • (-Y)) =
      (-6 : ℂ) • ((2 : ℂ)⁻¹ • (X + Y)) := by
    intro X Y
    module
  exact key X Y

include hw in
/-- The class-level form of `edgeComb_eq`. -/
theorem edgeComb_class (hodd : Odd n) (hn : 0 < n) :
    groupCohomology.H1π (modularBinaryRep (n + 1) 0) (lineEdgeCocycle hn f) +
        (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • groupCohomology.H1π (modularBinaryRep (n + 1) 0)
          (lineConjEdgeCocycle hn (fStar f)) =
      (-6 : ℂ) • restriction (n + 1) 0 0
        (groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n (psiF f hw hodd))) := by
  rw [restriction_apply]
  have e1 := (groupCohomology.H1π (modularBinaryRep (n + 1) 0)).hom.map_add (lineEdgeCocycle hn f)
    ((((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • lineConjEdgeCocycle hn (fStar f))
  have e2 := (groupCohomology.H1π (modularBinaryRep (n + 1) 0)).hom.map_smul
    (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) (lineConjEdgeCocycle hn (fStar f))
  rw [e2] at e1
  rw [← e1, edgeComb_eq f hw hodd hn]
  exact (groupCohomology.H1π (modularBinaryRep (n + 1) 0)).hom.map_smul _ _

end

end TernaryPeriodPolynomials.Argument.LineSeed
