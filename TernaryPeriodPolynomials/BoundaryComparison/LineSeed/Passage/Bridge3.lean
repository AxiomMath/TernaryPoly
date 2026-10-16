module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ReflSeed

@[expose] public section


/-!
# The seed classes along the clean frame (Passage bridge, part 3)

For `h ∈ SL₃(ℤ)` put `cleanHom h : Γ_{h⁻¹Qh} → Λ₁⁺`, `p ↦ Π (h p h⁻¹) Π`, and `cleanMor h : Res(cleanHom h)(linePlusRep n) ⟶ lineFaceRep N h n` the morphism with underlying map `faceT h ∘ pivotT`
(`pivotT = ρ(Π)`, `faceT h = ρ(h⁻¹)`).  `clean_seed`, `clean_conjSeed`: the image under `H²(cleanHom, cleanMor)` of the class of the (complexified) holomorphic, resp. antiholomorphic, line seed cocycle
of a level-one form `f` is the class of the `lineFaceSeedKerClass`, `lineFaceSeedConjKerClass` of `levelN N f` (these are transported from the standard line `⟨e₁⟩` by `h`).

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
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 faceT fStar)
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3

section

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (h : SL(3, ℤ)) (n : ℕ)

/-- The clean-frame homomorphism `Γ_{h⁻¹Qh} → Λ₁⁺`, `p ↦ Π (h p h⁻¹) Π`. -/
def cleanHom : ↥(gammaNQAt N h) →* Lam1Plus := (piMap N h3).comp (conjQ N h).toMonoidHom

/-- The comparison linear map `faceT h ∘ ρ(Π)`. -/
def cleanLin : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n :=
  ((faceT h n : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n).comp (pivotT n)

omit [NeZero N] in
theorem rhoC_eq_std (g : ↥(gammaNQ N)) (w : HomogeneousPoly n) :
    (gammaNQLineData N).rhoC n g w = (lineStdRep N n).ρ g w := by
  rw [lineStdRep_ρ, ← lineNRep_ambient]
  rfl

theorem cleanLin_intertwines (p : ↥(gammaNQAt N h)) (v : HomogeneousPoly n) :
    cleanLin h n ((linePlusRep n).ρ (cleanHom N h3 h p) v) = (lineFaceRep N h n).ρ p (cleanLin h n v) := by
  have h1 : pivotT n ((linePlusRep n).ρ (cleanHom N h3 h p) v) =
      (gammaNQLineData N).rhoC n (conjQ N h p) (pivotT n v) := by
    have := rhoC_linePlus n (cleanHom N h3 h p) (pivotT n v)
    rw [pivotT_mul_self] at this
    rw [← rhoC_piMap N h3 n]
    exact this.symm
  have e1 : cleanLin h n v = faceT h n (pivotT n v) := rfl
  have e2 : cleanLin h n (((linePlusRep n).ρ (cleanHom N h3 h p)) v) =
      faceT h n (pivotT n (((linePlusRep n).ρ (cleanHom N h3 h p)) v)) := rfl
  rw [e2, h1, e1, rhoC_eq_std]
  exact lineFaceT_intertwines N h n p (pivotT n v)

/-- The comparison morphism of representations `Res(cleanHom) (linePlusRep n) ⟶ lineFaceRep N h n`. -/
def cleanMor : Rep.res (cleanHom N h3 h) (linePlusRep n) ⟶ lineFaceRep N h n :=
  Rep.ofHom ⟨cleanLin h n, fun p => LinearMap.ext fun v => cleanLin_intertwines N h3 h n p v⟩


theorem clean_seed_cocycle {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (a b : ↥(gammaNQAt N h)) :
    (groupCohomology.mapCocycles₂ (cleanHom N h3 h) (cleanMor N h3 h n) (lineSeedCocycle₂ f)).1 (a, b) =
      faceT h n (lineNChain (levelN N f) (conjQ N h a) (conjQ N h b)) := by
  rw [← lineSeedChain_piMap N h3 f]
  change cleanLin h n (pivotT n (lineSeedChain f (piMap N h3 (conjQ N h a)) (piMap N h3 (conjQ N h b)))) = _
  have e1 : ∀ w : HomogeneousPoly n, cleanLin h n w = faceT h n (pivotT n w) := fun w => rfl
  rw [e1]
  exact congrArg (⇑(faceT h n)) (pivotT_mul_self n _)


theorem lineFaceSeedKerClass_val {n : ℕ} (f' : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    (lineFaceSeedKerClass N n h f').1 = H2π (lineFaceRep N h n)
      (mapCocycles₂ (lineFaceEquiv N h).toMulEquiv.toMonoidHom
        (FaceTransport.comparison (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
          (lineFaceT_intertwines N h n)) (lineNCocycle₂ f')) := by
  have hk := FaceTransport.kerMap_val (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNSeedKerClass f')
  have hc : (lineNSeedKerClass f').1 = H2π (lineStdRep N n) (lineNCocycle₂ f') := by
    unfold lineNSeedKerClass
    rw [relativeTwoCocycleClass_apply]
    rfl
  have hm := FaceTransport.h2Map_π (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNCocycle₂ f')
  refine hk.trans ?_
  rw [hc]
  exact hm

theorem lineFaceSeedConjKerClass_val {n : ℕ} (f' : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    (lineFaceSeedConjKerClass N n h f').1 = H2π (lineFaceRep N h n)
      (mapCocycles₂ (lineFaceEquiv N h).toMulEquiv.toMonoidHom
        (FaceTransport.comparison (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
          (lineFaceT_intertwines N h n)) (lineNConjCocycle₂ f')) := by
  have hk := FaceTransport.kerMap_val (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNSeedConjKerClass f')
  have hc : (lineNSeedConjKerClass f').1 = H2π (lineStdRep N n) (lineNConjCocycle₂ f') := by
    unfold lineNSeedConjKerClass
    rw [relativeTwoCocycleClass_apply]
    rfl
  have hm := FaceTransport.h2Map_π (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNConjCocycle₂ f')
  refine hk.trans ?_
  rw [hc]
  exact hm

theorem clean_seed {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    (groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom (H2π (linePlusRep n) (lineSeedCocycle₂ f)) =
      (lineFaceSeedKerClass N n h (levelN N f)).1 := by
  refine (groupCohomology.H2π_comp_map_apply (cleanHom N h3 h) (cleanMor N h3 h n)
    (lineSeedCocycle₂ f)).trans ?_
  refine Eq.trans ?_ (lineFaceSeedKerClass_val N h (levelN N f)).symm
  refine congrArg (H2π (lineFaceRep N h n)) ?_
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine (clean_seed_cocycle N h3 h f a b).trans ?_
  rfl


theorem clean_seed_conj_cocycle {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (a b : ↥(gammaNQAt N h)) :
    (groupCohomology.mapCocycles₂ (cleanHom N h3 h) (cleanMor N h3 h n) (lineSeedConjCocycle₂ f)).1 (a, b) =
      faceT h n (lineNConjChain (levelN N f) (conjQ N h a) (conjQ N h b)) := by
  rw [← lineSeedConjChain_piMap N h3 f]
  change cleanLin h n (pivotT n (lineSeedConjChain f (piMap N h3 (conjQ N h a)) (piMap N h3 (conjQ N h b)))) = _
  have e1 : ∀ w : HomogeneousPoly n, cleanLin h n w = faceT h n (pivotT n w) := fun w => rfl
  rw [e1]
  exact congrArg (⇑(faceT h n)) (pivotT_mul_self n _)

theorem clean_conjSeed {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    (groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom
        (H2π (linePlusRep n) (lineSeedConjCocycle₂ f)) =
      (lineFaceSeedConjKerClass N n h (levelN N f)).1 := by
  refine (groupCohomology.H2π_comp_map_apply (cleanHom N h3 h) (cleanMor N h3 h n)
    (lineSeedConjCocycle₂ f)).trans ?_
  refine Eq.trans ?_ (lineFaceSeedConjKerClass_val N h (levelN N f)).symm
  refine congrArg (H2π (lineFaceRep N h n)) ?_
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  refine (clean_seed_conj_cocycle N h3 h f a b).trans ?_
  rfl

/-- **The clean-frame identification of the reflection-isotypic line seed**: the image under `H²(cleanHom, cleanMor)` of the complexified de Rham class of
`σ_f + ε(-1)ⁿ \overline{σ_{f^*}}` (for the line data of `Λ₁⁺`) is the sum of S3's face seed classes of `levelN N f` and `levelN N (f^*)` at the cusp `h⁻¹Qh`. -/
theorem clean_complexify {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (ε : ℝ) :
    (groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom
        (lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
          (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f ε))) =
      (lineFaceSeedKerClass N n h (levelN N f)).1 +
        (((ε * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1 := by
  have h1 : lineComplexify n (cuspSeedClass linePlusData linePlus_hΛ (f := f)) =
      H2π (linePlusRep n) (lineSeedCocycle₂ f) := by
    rw [lineComplexify_cuspSeedClass, relativeTwoCocycleClass_apply]
    rfl
  have h2 : lineComplexify n (cuspSeedConjClass linePlusData linePlus_hΛ (f := fStar f)) =
      H2π (linePlusRep n) (lineSeedConjCocycle₂ (fStar f)) := by
    rw [lineComplexify_cuspSeedConjClass, relativeTwoCocycleClass_apply]
    rfl
  have h3' := (lineComplexify n).map_add (cuspSeedClass linePlusData linePlus_hΛ (f := f))
    ((ε * (-1 : ℝ) ^ n) • cuspSeedConjClass linePlusData linePlus_hΛ (f := fStar f))
  have h4 := (lineComplexify n).map_smul (ε * (-1 : ℝ) ^ n)
    (cuspSeedConjClass linePlusData linePlus_hΛ (f := fStar f))
  rw [TernaryPeriodPolynomials.Argument.LineSeed.deRhamClass_reflSeedInv, h3', h4, h1, h2, ← Complex.coe_smul]
  rw [(groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom.map_add,
    (groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom.map_smul,
    clean_seed N h3 h f, clean_conjSeed N h3 h (fStar f)]

end

end TernaryPeriodPolynomials.Argument.LineSeed
