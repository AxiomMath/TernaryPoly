module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Cusp
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusRep
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusEdge
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Relative

@[expose] public section


/-!
# The line seed cocycle on `Λ₁⁺` as a relative 2-cocycle, and its complexification (LS13)

Line mirror of `SeedC3S4c.SeedRelative`.  For a level-one cusp form `f` of weight `n + 3`, the zig-zag cochain of the line seed `σ_h` on the pivoted group
`Λ₁⁺ = ℤ² ⋊ SL₂(ℤ)` (`linePlusData`) is a real 2-cocycle with values in `E_n` (`lineSeedChain`); transported by the pivot intertwiner `T = ρ(Π)` it is a complex 2-cocycle
of `Λ₁⁺` with coefficients in the library's `linePlusRep n` (`lineSeedCocycle₂`), vanishing on pairs of radical elements (`lineSeedRelCocycle`).  `lineComplexify` sends the
real de Rham class to the complex class and `lineComplexify_cuspSeedClass` identifies the image of `cuspSeedClass` with the class of `lineSeedRelCocycle`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (SL2Z Lvl1 sl2zToSpecial specialToSL2Z realDescent realDescent_apply)

/-- The `SL(2, ℤ)` element underlying the pivoted Levi block of `g ∈ Λ₁⁺`. -/
def linePlusSL (g : Lam1Plus) : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨((pivotHom (goodLineLeviProjection (g : Lam1)) : GeneralLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ), by
    have hdet : GeneralLinearGroup.det (goodLineLeviProjection (g : Lam1)) = 1 := g.property
    have := congrArg Units.val (det_pivotHom _ hdet)
    simpa [GeneralLinearGroup.val_det_apply] using this⟩

theorem linePlusLam_eq_mapGL (g : Lam1Plus) : linePlusLam g = SpecialLinearGroup.mapGL ℝ (linePlusSL g) := by
  apply Units.ext
  ext i j
  simp [linePlusLam, linePlusSL, SpecialLinearGroup.mapGL]
  rfl

theorem linePlusLam_mem (g : Lam1Plus) : linePlusLam g ∈ Lvl1 := ⟨linePlusSL g, (linePlusLam_eq_mapGL g).symm⟩

theorem linePlus_hΛ (g : Lam1Plus) : (linePlusData.lam g : GL (Fin 2) ℝ) ∈ Lvl1 := linePlusLam_mem g

theorem linePlusLam_inl (r : RadicalLattice) : linePlusLam (linePlusInl r) = 1 := by
  have h : goodLineLeviProjection ((linePlusInl r : Lam1Plus) : Lam1) = 1 := goodLineLeviProjection_radical r
  simp only [linePlusLam, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [h, map_one, map_one]

theorem linePlusV_inl (r : RadicalLattice) :
    linePlusV (linePlusInl r) = ![3 * (r.toAdd.2 : ℝ), 3 * (r.toAdd.1 : ℝ)] := by
  funext i
  fin_cases i <;> simp [linePlusV, linePlusInl, goodLineRadicalInclusion, lowerRadicalLattice, lowerPlaneUnipotent]

theorem linePlusV_section (m : SpecialLinearGroup (Fin 2) ℤ) : linePlusV (linePlusSectionS m) = 0 := by
  funext i
  fin_cases i <;> simp [linePlusV, linePlusSectionS, linePlusSection, goodLineLeviSection,
    arithmeticLeviHom, arithmeticLevi, planeLevi, planeBlock, specialToSL2Z]

theorem linePlusLam_section (m : SpecialLinearGroup (Fin 2) ℤ) :
    linePlusLam (linePlusSectionS m) = SpecialLinearGroup.mapGL ℝ (linePlusSL (linePlusSectionS m)) :=
  linePlusLam_eq_mapGL _

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the line seed of `f`, on `Λ₁⁺`, with values in `E_n`. -/
def lineSeedChain (g k : Lam1Plus) : Coef n :=
  cuspSeedCochain linePlusData linePlus_hΛ (f := f) g k

theorem lineSeedChain_cocycle (g h j : Lam1Plus) :
    lineSeedChain f (g * h) j + lineSeedChain f g h =
      linePlusData.rhoR n g (lineSeedChain f h j) + lineSeedChain f g (h * j) :=
  cuspSeedCochain_cocycle linePlusData linePlus_hΛ g h j

theorem lineSeedChain_inl_inl (r r' : RadicalLattice) :
    lineSeedChain f (linePlusInl r) (linePlusInl r') = 0 := by
  apply Coef.toPoly_injective
  have h1 : linePlusData.lam (linePlusInl r') = 1 := linePlusLam_inl r'
  have h2 : mob (linePlusData.lam (linePlusInl r')) Complex.I = Complex.I := by
    rw [h1]; simp [mob]
  rw [lineSeedChain, TernaryPeriodPolynomials.Argument.LineSeed.toPoly_cuspSeedCochain, h2]
  simp [momentPrim_zero]

end

theorem linePlusRep_ρ (n : ℕ) (g : Lam1Plus) (x : Coef n) :
    pivotT n (linePlusData.rhoR n g x) = (linePlusRep n).ρ g (pivotT n x) := by
  have h := rhoC_linePlus n g x
  change pivotT n (linePlusData.rhoC n g x) = _
  rw [h]
  exact pivotT_mul_self n _

theorem pivotT_sub_add (n : ℕ) (x y z : HomogeneousPoly n) :
    pivotT n (x - y + z) = pivotT n x - pivotT n y + pivotT n z := by
  rw [map_add, map_sub]

theorem pivotT_sub (n : ℕ) (x y : HomogeneousPoly n) : pivotT n (x - y) = pivotT n x - pivotT n y := map_sub _ _ _

/-- Coefficients, real carrier to the library's complex carrier (the pivot intertwiner). -/
def cxVec (n : ℕ) (x : Rep.of (linePlusData.rhoR n)) : linePlusRep n := pivotT n x

/-- Real 2-cocycles of `Λ₁⁺` with values in `E_n` are complex 2-cocycles of the library's representation. -/
def cxCocycles (n : ℕ) :
    cocycles₂ (Rep.of (linePlusData.rhoR n)) →ₗ[ℝ] cocycles₂ (linePlusRep n) where
  toFun c := ⟨fun p => cxVec n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    change cxVec n (c.1 (g * h, j)) + cxVec n (c.1 (g, h)) =
      (linePlusRep n).ρ g (cxVec n (c.1 (h, j))) + cxVec n (c.1 (g, h * j))
    have e2 : (linePlusRep n).ρ g (cxVec n (c.1 (h, j))) =
        cxVec n (linePlusData.rhoR n g (c.1 (h, j))) := (linePlusRep_ρ n g _).symm
    rw [e2]
    change pivotT n (c.1 (g * h, j)) + pivotT n (c.1 (g, h)) =
      pivotT n (linePlusData.rhoR n g (c.1 (h, j))) + pivotT n (c.1 (g, h * j))
    have e3 := congrArg (pivotT n) e
    exact (map_add (pivotT n) (c.1 (g * h, j) : HomogeneousPoly n) (c.1 (g, h))).symm.trans
      (e3.trans (map_add (pivotT n) ((linePlusData.rhoR n g (c.1 (h, j))) : HomogeneousPoly n)
        (c.1 (g, h * j)))))⟩
  map_add' a b := by
    apply Subtype.ext
    funext p
    exact map_add (pivotT n) _ _
  map_smul' r a := by
    apply Subtype.ext
    funext p
    exact (pivotT n).map_smul_of_tower r (a.1 p)

theorem cxCocycles_coe (n : ℕ) (c : cocycles₂ (Rep.of (linePlusData.rhoR n)))
    (p : Lam1Plus × Lam1Plus) : (cxCocycles n c).1 p = cxVec n (c.1 p) := rfl

/-- The complexification map `H²(Λ₁⁺, E_n)_ℝ → H²(Λ₁⁺, E_n)_ℂ` (into the library's representation): the pivot intertwiner on cocycles. -/
def lineComplexify (n : ℕ) :
    H2 (Rep.of (linePlusData.rhoR n)) →ₗ[ℝ] H2 (linePlusRep n) :=
  realDescent (H2π (Rep.of (linePlusData.rhoR n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (linePlusRep n)).hom.restrictScalars ℝ).comp (cxCocycles n))
    (fun a b hab => by
      have h : H2π (Rep.of (linePlusData.rhoR n)) a = H2π (Rep.of (linePlusData.rhoR n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (linePlusRep n) (cxCocycles n a) = H2π (linePlusRep n) (cxCocycles n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVec n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      change (linePlusRep n).ρ p.1 (cxVec n (y p.2)) - cxVec n (y (p.1 * p.2)) + cxVec n (y p.1) =
        cxVec n (a.1 p) - cxVec n (b.1 p)
      have e2 : (linePlusRep n).ρ p.1 (cxVec n (y p.2)) = cxVec n (linePlusData.rhoR n p.1 (y p.2)) :=
        (linePlusRep_ρ n p.1 _).symm
      rw [e2]
      have e3 := congrArg (pivotT n) hp
      exact (pivotT_sub_add n _ _ _).symm.trans (e3.trans (pivotT_sub n _ _)))

theorem lineComplexify_H2π (n : ℕ) (c : cocycles₂ (Rep.of (linePlusData.rhoR n))) :
    lineComplexify n (H2π (Rep.of (linePlusData.rhoR n)) c) = H2π (linePlusRep n) (cxCocycles n c) :=
  realDescent_apply _ _ _ _ c

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The line seed cochain as a complex 2-cocycle of `Λ₁⁺` with coefficients in the library's representation. -/
def lineSeedCocycle₂ : cocycles₂ (linePlusRep n) :=
  cxCocycles n ⟨fun p => lineSeedChain f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => lineSeedChain_cocycle f g h j)⟩

/-- **The relative 2-cocycle of the line seed**: it vanishes on pairs of radical elements. -/
def lineSeedRelCocycle : relativeTwoCocycles linePlusExtensionS.inl (linePlusRep n) :=
  ⟨lineSeedCocycle₂ f, fun r r' => by
    change cxVec n (lineSeedChain f (linePlusInl r) (linePlusInl r')) = 0
    rw [lineSeedChain_inl_inl]
    exact map_zero _⟩

/-- The complexification of the de Rham class of the line seed is the class of `lineSeedRelCocycle`. -/
theorem lineComplexify_cuspSeedClass :
    lineComplexify n (cuspSeedClass linePlusData linePlus_hΛ (f := f)) =
      (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineSeedRelCocycle f)).val := by
  change lineComplexify n (H2π (Rep.of (linePlusData.rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (linePlusRep n) (lineSeedCocycle₂ f)
  rw [lineComplexify_H2π]
  rfl

end

end TernaryPeriodPolynomials.Argument.LineSeed
