module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EichlerCompare
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusSpecial
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp

@[expose] public section


/-!
# The seed cocycle on `Λ₀⁺` as a relative 2-cocycle, and its complexification (Lemma C.3, S4c)

For a level-one cusp form `f` of weight `n + 3`, the zig-zag cochain of the seed `ω_h` of
`SeedC3.SeedCusp` on the plane parabolic group `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` (`plusPlaneData`) is

* a complex 2-cocycle of `Λ₀⁺` with coefficients in the library's `plusRep n` (`seedCocycle₂`),
  vanishing on pairs of radical elements (`seedRelCocycle : relativeTwoCocycles plusExtensionS.inl
  (plusRep n)`, because the Eichler cocycle of the identity vanishes);
* the image of the real de Rham class `cuspSeedClass ∈ H²(Λ₀⁺, E_n)_ℝ` under the complexification
  map `complexify` (identity on cocycles), `complexify_cuspSeedClass`.

Paper: Lemma C.3 (`ar:lem:seed`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

theorem plusLam_inl (r : RadicalLattice) : plusLam (plusInl r) = 1 := by
  have h := identityPlaneLeviProjection_radical r
  simp only [plusLam, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have : identityPlaneLeviProjection ((plusInl r : Lam0Plus) : Lam0) = 1 := h
  rw [this, map_one]

theorem plusW_inl (r : RadicalLattice) :
    plusW (plusInl r) = ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)] := by
  funext i
  fin_cases i <;> simp [plusW, plusInl, identityPlaneRadicalInclusion, upperRadicalLattice,
    planeUnipotent]

theorem plusW_section (m : SpecialLinearGroup (Fin 2) ℤ) : plusW (plusSectionS m) = 0 := by
  funext i
  fin_cases i <;> simp [plusW, plusSectionS, plusSection, identityPlaneLeviSection,
    arithmeticLeviHom, arithmeticLevi, planeLevi, planeBlock, specialToSL2Z]

theorem plusLam_eq_mapGL (g : Lam0Plus) :
    plusLam g = SpecialLinearGroup.mapGL ℝ (plusProjS g) := by
  apply Units.ext
  ext i j
  simp [plusLam, plusProjS, plusProj, sl2zToSpecial, SpecialLinearGroup.mapGL]
  rfl

theorem plusLam_mem (g : Lam0Plus) :
    plusLam g ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range :=
  ⟨plusProjS g, (plusLam_eq_mapGL g).symm⟩

theorem plusLam_section (m : SpecialLinearGroup (Fin 2) ℤ) :
    plusLam (plusSectionS m) = SpecialLinearGroup.mapGL ℝ m := by
  rw [plusLam_eq_mapGL, plusProjS_section]

/-! ### The seed cocycle of the level-one cusp form on `Λ₀⁺` -/

/-- The level-one group `SL₂(ℤ) ⊂ GL₂(ℝ)`. -/
abbrev Lvl1 : Subgroup (GL (Fin 2) ℝ) := (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range

theorem plus_hΛ (g : Lam0Plus) : (plusPlaneData.lam g : GL (Fin 2) ℝ) ∈ Lvl1 := plusLam_mem g

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the seed of `f`, on `Λ₀⁺`, with values in `E_n`. -/
def seedChain (g k : Lam0Plus) : Coef n :=
  cuspSeedCochain plusPlaneData plus_hΛ (f := f) g k

theorem seedChain_cocycle (g h j : Lam0Plus) :
    seedChain f (g * h) j + seedChain f g h =
      plusPlaneData.rhoR n g (seedChain f h j) + seedChain f g (h * j) :=
  cuspSeedCochain_cocycle plusPlaneData plus_hΛ g h j

/-- The Eichler cocycle of the seed's moment primitives, at the Levi part of `k`, as a polynomial
in `X, Y, Z` without `Z`. -/
def seedEps (k : Lam0Plus) : MvPolynomial (Fin 3) ℂ :=
  rename Fin.castSucc (eichlerCocycle n (momentPrim Lvl1 n f) (plusPlaneData.lam k))

theorem toPoly_seedChain (g k : Lam0Plus) :
    Coef.toPoly (seedChain f g k) =
      C (((n : ℂ) + 1)⁻¹) *
        ddiv (rho (plusPlaneData.plm g) (seedEps f k) -
          rho (parabolicMatrix (plusPlaneData.lamM g) 0) (seedEps f k)) :=
  toPoly_cuspSeedCochain plusPlaneData plus_hΛ (f := f) g k

theorem seedEps_inl (r : RadicalLattice) : seedEps f (plusInl r) = 0 := by
  have h1 : (plusPlaneData.lam (plusInl r)) = 1 := plusLam_inl r
  have h2 : mob (plusPlaneData.lam (plusInl r)) Complex.I = Complex.I := by
    rw [h1]; simp [mob]
  unfold seedEps
  rw [eichlerCocycle, h2, eichlerPoly_base n _ (momentPrim_zero Lvl1 n f), map_zero]

theorem seedChain_inl_inl (r r' : RadicalLattice) :
    seedChain f (plusInl r) (plusInl r') = 0 := by
  apply Coef.toPoly_injective
  rw [toPoly_seedChain, seedEps_inl]
  simp [rho, ddiv_zero]

end

theorem plusRep_ρ (n : ℕ) (g : Lam0Plus) (x : Coef n) :
    (plusRep n).ρ g x = plusPlaneData.rhoR n g x := by
  have h : (plusRep n).ρ g = plusPlaneData.rhoC n g := (plusPlaneData_rhoC n g).symm
  rw [h]
  rfl

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The seed cochain with values in the carrier of `plusRep n`. -/
def seedChainR (g k : Lam0Plus) : plusRep n := seedChain f g k

/-- The seed cochain as a complex 2-cocycle of `Λ₀⁺` with coefficients in `E_n`. -/
def seedCocycle₂ : groupCohomology.cocycles₂ (plusRep n) :=
  ⟨fun p => seedChainR f p.1 p.2, (groupCohomology.mem_cocycles₂_iff _).2 (fun g h j => by
    have e := seedChain_cocycle f g h j
    change seedChainR f (g * h) j + seedChainR f g h =
      (plusRep n).ρ g (seedChainR f h j) + seedChainR f g (h * j)
    have e2 : (plusRep n).ρ g (seedChainR f h j) = plusPlaneData.rhoR n g (seedChain f h j) :=
      plusRep_ρ n g _
    rw [e2]
    exact e)⟩

/-- **(a) The relative 2-cocycle of the seed**: it vanishes on pairs of radical elements. -/
def seedRelCocycle : relativeTwoCocycles plusExtensionS.inl (plusRep n) :=
  ⟨seedCocycle₂ f, fun r r' => seedChain_inl_inl f r r'⟩

end

/-! ### (b) Complexification of the coefficients -/

open CategoryTheory groupCohomology

/-- Coefficients, real carrier to complex carrier (the identity). -/
def cxVec (n : ℕ) (x : Rep.of (plusPlaneData.rhoR n)) : plusRep n := x

/-- Real 2-cocycles of `Λ₀⁺` with values in `E_n` are complex 2-cocycles: the identity on
functions. -/
def cxCocycles (n : ℕ) :
    cocycles₂ (Rep.of (plusPlaneData.rhoR n)) →ₗ[ℝ] cocycles₂ (plusRep n) where
  toFun c := ⟨fun p => cxVec n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    change cxVec n (c.1 (g * h, j)) + cxVec n (c.1 (g, h)) =
      (plusRep n).ρ g (cxVec n (c.1 (h, j))) + cxVec n (c.1 (g, h * j))
    have e2 : (plusRep n).ρ g (cxVec n (c.1 (h, j))) =
        cxVec n (plusPlaneData.rhoR n g (c.1 (h, j))) :=
      plusRep_ρ n g _
    rw [e2]
    exact e)⟩
  map_add' a b := rfl
  map_smul' r a := rfl

theorem cxCocycles_coe (n : ℕ) (c : cocycles₂ (Rep.of (plusPlaneData.rhoR n)))
    (p : Lam0Plus × Lam0Plus) : (cxCocycles n c).1 p = cxVec n (c.1 p) := rfl

/-- Descent of a real-linear map along a surjection. -/
def realDescent {V W U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup U] [Module ℝ U] (projection : V →ₗ[ℝ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℝ] U)
    (fibers : ∀ first second, projection first = projection second →
      coordinate first = coordinate second) : W →ₗ[ℝ] U where
  toFun vector := coordinate (surjective vector).choose
  map_add' first second := by
    calc
      _ = coordinate ((surjective first).choose + (surjective second).choose) :=
        fibers _ _ (by rw [map_add, (surjective first).choose_spec, (surjective second).choose_spec,
          (surjective (first + second)).choose_spec])
      _ = _ := map_add coordinate _ _
  map_smul' scalar vector := by
    calc
      _ = coordinate (scalar • (surjective vector).choose) :=
        fibers _ _ (by rw [map_smul, (surjective vector).choose_spec,
          (surjective (scalar • vector)).choose_spec])
      _ = _ := map_smul coordinate scalar _

theorem realDescent_apply {V W U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [AddCommGroup U] [Module ℝ U] (projection : V →ₗ[ℝ] W)
    (surjective : Function.Surjective projection) (coordinate : V →ₗ[ℝ] U)
    (fibers : ∀ first second, projection first = projection second →
      coordinate first = coordinate second) (vector : V) :
    realDescent projection surjective coordinate fibers (projection vector) = coordinate vector :=
  fibers _ _ (surjective (projection vector)).choose_spec

/-- The complexification map `H²(Λ₀⁺, E_n)_ℝ → H²(Λ₀⁺, E_n)_ℂ`, the identity on cocycles. -/
def complexify (n : ℕ) :
    H2 (Rep.of (plusPlaneData.rhoR n)) →ₗ[ℝ] H2 (plusRep n) :=
  realDescent (H2π (Rep.of (plusPlaneData.rhoR n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (plusRep n)).hom.restrictScalars ℝ).comp (cxCocycles n))
    (fun a b hab => by
      have h : H2π (Rep.of (plusPlaneData.rhoR n)) a = H2π (Rep.of (plusPlaneData.rhoR n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (plusRep n) (cxCocycles n a) = H2π (plusRep n) (cxCocycles n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVec n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      change (plusRep n).ρ p.1 (cxVec n (y p.2)) - cxVec n (y (p.1 * p.2)) + cxVec n (y p.1) =
        cxVec n (a.1 p) - cxVec n (b.1 p)
      have e2 : (plusRep n).ρ p.1 (cxVec n (y p.2)) = cxVec n (plusPlaneData.rhoR n p.1 (y p.2)) :=
        plusRep_ρ n p.1 _
      rw [e2]
      exact hp)

theorem complexify_H2π (n : ℕ) (c : cocycles₂ (Rep.of (plusPlaneData.rhoR n))) :
    complexify n (H2π (Rep.of (plusPlaneData.rhoR n)) c) = H2π (plusRep n) (cxCocycles n c) :=
  realDescent_apply _ _ _ _ c

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- **(b)** The complexification of the de Rham class of the seed is the class of the relative
2-cocycle `seedRelCocycle`. -/
theorem complexify_cuspSeedClass :
    complexify n (cuspSeedClass plusPlaneData plus_hΛ (f := f)) =
      (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedRelCocycle f)).val := by
  change complexify n (H2π (Rep.of (plusPlaneData.rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (plusRep n) (seedCocycle₂ f)
  rw [complexify_H2π]
  rfl

end

end TernaryPeriodPolynomials.Argument.SeedC3S4c
