module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Kappa2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Face
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageForms

@[expose] public section


/-!
# The seed combination as a cocycle of `Q⁺(ℤ)`, and its transport to every line cusp of `Γ(N)` (Passage 10)

For a level-one cusp form `f` and odd `n`, `seedCombCocycle f` is the 2-cocycle `c_f + (-1)ⁿ \overline{c_{f^*}}` of the full line parabolic `Q⁺(ℤ) = lineStab` with values in `E_n`
(`lineStabRep n`).  `seedComb_face`: the combination of the seed classes of `f|Γ₂(N)` and `f^*|Γ₂(N)` at the line cusp `h⁻¹ Q h` of `Γ(N)` is the pullback of its class along
`ψ_h : p ↦ h p h⁻¹` with the coefficient map `ρ(h⁻¹)` (`faceT h`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein Matrix MvPolynomial ComplexConjugate CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3 hiding toPoly_cuspSeedCochain cuspSeedCochain cuspSeedInv cuspSeedClass
  cuspSeedConjClass cuspSeedConjInv cuspSeedCochain_cocycle cuspSeedConjCochain cuspSeedConjCochain_eq
  cuspSeedConjCochain_cocycle deRhamClass_cuspSeed deRhamClass_cuspSeedConj cuspSeedDatum
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 ambRep fStar faceT)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.KDaggerComparison (levelN)

/-- The coefficient module `E_n` restricted to `Q⁺(ℤ)`. -/
abbrev lineStabRep (n : ℕ) : Rep ℂ ↥lineStab := Rep.of ((ambRep n).comp lineStab.subtype)

theorem lineStabRep_ρ (n : ℕ) (g : ↥lineStab) : (lineStabRep n).ρ g = ambRep n g.1 := rfl

theorem lineStab_ρ_std (n : ℕ) (g : ↥lineStab) (x : Coef n) :
    (lineStabRep n).ρ g x = lineStabData.rhoR n g x := by
  have : lineStabData.sigma g = Matrix.SpecialLinearGroup.mapGL (n := Fin 3) (R := ℤ) ℝ g.1 := by
    apply Units.ext
    rw [LineData.sigma_val, lineStab_lmat, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    ext i j
    simp [realMat]
  change ambRep n g.1 x = GeneralEisenstein.realCoefficient n (lineStabData.sigma g) x
  rw [this]
  rfl

variable {n : ℕ}

/-- The cochain value of the seed combination, `c_f + (-1)ⁿ \overline{c_{f^*}}`, in the carrier of `lineStabRep n`. -/
def seedCombR (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥lineStab) : lineStabRep n := seedComb f x y

theorem seedComb_cocycle_coef (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (g h j : ↥lineStab) :
    seedComb f (g * h) j + seedComb f g h = lineStabData.rhoR n g (seedComb f h j) + seedComb f g (h * j) := by
  have e1 := cuspSeedCochain_cocycle lineStabData lineStab_lam_mem (f := f) g h j
  have e2 := cuspSeedConjCochain_cocycle lineStabData lineStab_lam_mem (f := fStar f) g h j
  unfold seedComb
  have hs : ∀ (c : ℂ) (v : Coef n), lineStabData.rhoR n g (c • v) = c • lineStabData.rhoR n g v := fun c v =>
    (lineStabData.rhoCoef n g).map_smul c v
  rw [map_add, hs]
  linear_combination (norm := module) e1 + (((-1 : ℝ) ^ n : ℝ) : ℂ) • e2

/-- **The seed combination `c_f + (-1)ⁿ \overline{c_{f^*}}` as a 2-cocycle of `Q⁺(ℤ)`.** -/
def seedCombCocycle (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) : cocycles₂ (lineStabRep n) :=
  ⟨fun p => seedCombR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e2 : (lineStabRep n).ρ g (seedCombR f h j) = lineStabData.rhoR n g (seedComb f h j) :=
      lineStab_ρ_std n g _
    change seedCombR f (g * h) j + seedCombR f g h = (lineStabRep n).ρ g (seedCombR f h j) + seedCombR f g (h * j)
    rw [e2]
    exact seedComb_cocycle_coef f g h j)⟩

theorem faceT_comb (h : SL(3, ℤ)) (n : ℕ) (a b : GeneralEisenstein.HomogeneousPoly n) (c : ℂ) :
    faceT h n (a + c • b) = faceT h n a + c • faceT h n b := by
  rw [map_add, map_smul]

section Face

variable (N : ℕ) [NeZero N]

/-- The conjugation `p ↦ h p h⁻¹` of the line group of the cusp `h⁻¹ Q h` into `Q⁺(ℤ)`. -/
def psiHom (h : SL(3, ℤ)) : ↥(gammaNQAt N h) →* ↥lineStab :=
  (gammaNQToStab N).comp (conjQ N h).toMonoidHom

omit [NeZero N] in
theorem psiHom_val (h : SL(3, ℤ)) (p : ↥(gammaNQAt N h)) : ((psiHom N h p).1 : SL(3, ℤ)) = h * p.1 * h⁻¹ := rfl

theorem psiHom_T (h : SL(3, ℤ)) (g : ↥(gammaNQAt N h)) (v : lineStabRep n) :
    faceT h n ((lineStabRep n).ρ (psiHom N h g) v) = (lineFaceRep N h n).ρ g (faceT h n v) :=
  lineFaceT_intertwines N h n g v

theorem lineFaceSeedKerClass_val_eq (h : SL(3, ℤ)) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    (lineFaceSeedKerClass N n h g).1 = H2π (lineFaceRep N h n)
      (groupCohomology.mapCocycles₂ (lineFaceEquiv N h).toMulEquiv.toMonoidHom
        (SeedC3S4c.FaceTransport.comparison (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
          (lineFaceT_intertwines N h n)) (lineNCocycle₂ g)) := by
  unfold lineFaceSeedKerClass lineFaceKerMap
  refine (SeedC3S4c.FaceTransport.kerMap_val (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNSeedKerClass g)).trans ?_
  exact SeedC3S4c.FaceTransport.h2Map_π (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNCocycle₂ g)

theorem lineFaceSeedConjKerClass_val_eq (h : SL(3, ℤ)) (g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    (lineFaceSeedConjKerClass N n h g).1 = H2π (lineFaceRep N h n)
      (groupCohomology.mapCocycles₂ (lineFaceEquiv N h).toMulEquiv.toMonoidHom
        (SeedC3S4c.FaceTransport.comparison (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
          (lineFaceT_intertwines N h n)) (lineNConjCocycle₂ g)) := by
  unfold lineFaceSeedConjKerClass lineFaceKerMap
  refine (SeedC3S4c.FaceTransport.kerMap_val (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNSeedConjKerClass g)).trans ?_
  exact SeedC3S4c.FaceTransport.h2Map_π (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n) (lineNConjCocycle₂ g)

omit [NeZero N] in
theorem lineNChain_levelN (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineNChain (levelN N f) x y = cuspSeedCochain lineStabData lineStab_lam_mem (f := f) (gammaNQToStab N x) (gammaNQToStab N y) :=
  cuspSeedCochain_comap lineStabData (gammaNQLineData N) (gammaNQToStab N) (gammaNQ_lam_incl N) (gammaNQ_v_incl N)
    lineStab_lam_mem (gammaNQ_lam_mem_levi N) f (levelN N f) (fun _ _ => rfl) x y

omit [NeZero N] in
theorem lineNConjChain_levelN (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (x y : ↥(gammaNQ N)) :
    lineNConjChain (levelN N f) x y = cuspSeedConjCochain lineStabData lineStab_lam_mem (f := f) (gammaNQToStab N x) (gammaNQToStab N y) :=
  cuspSeedConjCochain_comap lineStabData (gammaNQLineData N) (gammaNQToStab N) (gammaNQ_lam_incl N) (gammaNQ_v_incl N)
    lineStab_lam_mem (gammaNQ_lam_mem_levi N) f (levelN N f) (fun _ _ => rfl) x y

/-- **The seed combination at the line cusp `h⁻¹ Q h`**: the combination `[σ_{f|Γ₂(N)}] + (-1)ⁿ [\overline{σ_{f^*|Γ₂(N)}}]` of the transported seed classes is the pullback of the class
of `seedCombCocycle f` along `p ↦ h p h⁻¹` with the coefficient map `ρ(h⁻¹)`. -/
theorem seedComb_face (h : SL(3, ℤ)) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    (lineFaceSeedKerClass N n h (levelN N f)).1 +
        (((-1 : ℝ) ^ n : ℝ) : ℂ) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1 =
      SeedC3S4c.EdgeNat.h2Map (psiHom N h) (lineStabRep n) (lineFaceRep N h n) (faceT h n).toLinearMap (psiHom_T N h)
        (H2π (lineStabRep n) (seedCombCocycle f)) := by
  have hR := SeedC3S4c.EdgeNat.h2Map_π (psiHom N h) (lineStabRep n) (lineFaceRep N h n) (faceT h n).toLinearMap
    (psiHom_T N h) (seedCombCocycle f)
  rw [lineFaceSeedKerClass_val_eq, lineFaceSeedConjKerClass_val_eq]
  refine Eq.trans ?_ hR.symm
  rw [← map_smul, ← map_add]
  congr 1
  apply Subtype.ext
  funext p
  rw [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
  have hc : seedComb f (psiHom N h p.1) (psiHom N h p.2) =
      lineNChain (levelN N f) (conjQ N h p.1) (conjQ N h p.2) +
        (((-1 : ℝ) ^ n : ℝ) : ℂ) • lineNConjChain (levelN N (fStar f)) (conjQ N h p.1) (conjQ N h p.2) := by
    rw [lineNChain_levelN, lineNConjChain_levelN]
    rfl
  have hC : (seedCombR f (psiHom N h p.1) (psiHom N h p.2) : HomogeneousPoly n) =
      lineNChainR (levelN N f) (conjQ N h p.1) (conjQ N h p.2) +
        (((-1 : ℝ) ^ n : ℝ) : ℂ) • lineNConjChainR (levelN N (fStar f)) (conjQ N h p.1) (conjQ N h p.2) := hc
  refine (faceT_comb h n (lineNChainR (levelN N f) (conjQ N h p.1) (conjQ N h p.2))
    (lineNConjChainR (levelN N (fStar f)) (conjQ N h p.1) (conjQ N h p.2)) (((-1 : ℝ) ^ n : ℝ) : ℂ)).symm.trans ?_
  exact congrArg (faceT h n) hC.symm

end Face

end TernaryPeriodPolynomials.Argument.LineSeed
