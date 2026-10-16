module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Exactness

@[expose] public section


/-!
# The `Q`-side of the Hochschild-Serre step in degree three

Formalized by Claude Sonnet 5.5.

Let `Z` be a chain complex of projective `Q`-representations and `0 → P1 → P0 → 1 → 0` a short exact sequence of projective
`Q`-representations (a two-term projective resolution of the trivial representation; for `Q = GL₂(ℤ)` the dual Farey tree).
Tensoring `Z` with the sequence and taking coinvariants termwise gives a short exact sequence of complexes of `ℚ`-vector
spaces (`sesC_shortExact`: each `Z_j` is projective, so `P ↦ (Z_j ⊗ P)_Q` is exact by `Exactness`).  Since `P1, P0` are
projective, `Z ↦ (Z ⊗ P_i)_Q` commutes with homology (`phiH`, naturally in `P_i`: `phiH_square`).  The long exact homology
sequence then gives (`thmAEquiv`), when `H_3(Z) = 0`:

`H_3((Z ⊗ 1)_Q) ≃ ker ( (H_2 Z ⊗ P1)_Q → (H_2 Z ⊗ P0)_Q )`.
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q]

section ThmA

variable (Z : ChainComplex (Rep.{0} ℚ Q) ℕ)

/-- `(Z ⊗ X)_Q` degreewise. -/
abbrev CxF (X : Rep.{0} ℚ Q) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((FX X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z

/-- The map of complexes induced by `φ : X ⟶ Y`. -/
def CxMap {X Y : Rep.{0} ℚ Q} (φ : X ⟶ Y) : CxF Z X ⟶ CxF Z Y :=
  (NatTrans.mapHomologicalComplex (FXmap φ) (ComplexShape.down ℕ)).app Z

theorem CxMap_f {X Y : Rep.{0} ℚ Q} (φ : X ⟶ Y) (j : ℕ) :
    (CxMap Z φ).f j = (FXmap φ).app (Z.X j) := rfl

theorem CxMap_comp {X Y W : Rep.{0} ℚ Q} (φ : X ⟶ Y) (ψ : Y ⟶ W) :
    CxMap Z φ ≫ CxMap Z ψ = CxMap Z (φ ≫ ψ) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  simp only [HomologicalComplex.comp_f, CxMap_f, FXmap_comp]

theorem CxMap_zero {X Y : Rep.{0} ℚ Q} : CxMap Z (0 : X ⟶ Y) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  simp only [CxMap_f, FXmap_zero, HomologicalComplex.zero_f_apply]

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)

/-- The short complex of coinvariant complexes. -/
def sesC : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (CxMap Z d) (CxMap Z ε) (by rw [CxMap_comp, hdε, CxMap_zero])

theorem sesC_shortExact [Projective P1] [Projective P0] (hZ : ∀ j, Projective (Z.X j))
    (hS : (ShortComplex.mk d ε hdε).ShortExact) : (sesC Z P1 P0 d ε hdε).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j => ?_
  have h1 := FX_shortExact (Z.X j) _ hS
  let e : (ShortComplex.mk d ε hdε).map ((Rep.coinvariantsTensor ℚ Q).obj (Z.X j)) ≅
      (ShortComplex.mk d ε hdε).map (FX (Z.X j)) :=
    ShortComplex.mapNatIso _ (brNat (Z.X j))
  have h2 : ((ShortComplex.mk d ε hdε).map ((Rep.coinvariantsTensor ℚ Q).obj (Z.X j))).ShortExact :=
    ShortComplex.shortExact_of_iso e.symm h1
  exact h2

/-- The comparison `H_n(Z ⊗ X)_Q ≅ (H_n Z ⊗ X)_Q` for projective `X`. -/
def phiH (X : Rep.{0} ℚ Q) [Projective X] (n : ℕ) :
    (CxF Z X).homology n ≅ (FX X).obj (Z.homology n) :=
  haveI := FX_preservesHomology X
  (Z.sc n).mapHomologyIso (FX X)

theorem phiH_square' (S : ShortComplex (Rep.{0} ℚ Q)) (X Y : Rep.{0} ℚ Q) [Projective X] [Projective Y]
    (φ : X ⟶ Y) :
    haveI := FX_preservesHomology X
    haveI := FX_preservesHomology Y
    ShortComplex.homologyMap (S.mapNatTrans (FXmap φ)) ≫ (S.mapHomologyIso (FX Y)).hom =
      (S.mapHomologyIso (FX X)).hom ≫ (FXmap φ).app S.homology := by
  have := FX_preservesHomology X
  have := FX_preservesHomology Y
  rw [ShortComplex.homologyMap_mapNatTrans, Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id, Category.comp_id]

theorem phiH_square (X Y : Rep.{0} ℚ Q) [Projective X] [Projective Y] (φ : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (CxMap Z φ) n ≫ (phiH Z Y n).hom =
      (phiH Z X n).hom ≫ (FXmap φ).app (Z.homology n) :=
  phiH_square' (Z.sc n) X Y φ

section Main

variable (hZ : ∀ j, Projective (Z.X j)) [Projective P1] [Projective P0]
  (hS : (ShortComplex.mk d ε hdε).ShortExact)

theorem isZero_homology_three (hZ3 : IsZero (Z.homology 3)) : IsZero ((CxF Z P0).homology 3) := by
  have := FX_preservesHomology P0
  exact IsZero.of_iso (Functor.map_isZero (FX P0) hZ3) (phiH Z P0 3)

/-- **The abstract Hochschild-Serre step.**  For a complex `Z` of projective `Q`-modules with `H_3(Z) = 0` and a short exact
sequence `0 → P1 → P0 → 1 → 0` of projective modules, `H_3((Z ⊗ 1)_Q)` is the kernel of
`(H_2 Z ⊗ P1)_Q → (H_2 Z ⊗ P0)_Q`. -/
def thmAEquiv (hZ3 : IsZero (Z.homology 3)) :
    (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3 ≃ₗ[ℚ]
      LinearMap.ker ((FXmap d).app (Z.homology 2)).hom := by
  have hG := sesC_shortExact Z P1 P0 d ε hdε hZ hS
  have hrel : (ComplexShape.down ℕ).Rel 3 2 := rfl
  have hmono : Mono (hG.δ 3 2 hrel) := hG.mono_δ 3 2 hrel (isZero_homology_three Z P0 hZ3)
  have hex := hG.homology_exact₁ 3 2 hrel
  have hrange : LinearMap.range (hG.δ 3 2 hrel).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (CxMap Z d) 2).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hex
  have hinj : Function.Injective (hG.δ 3 2 hrel).hom := (ModuleCat.mono_iff_injective _).1 hmono
  have hker : Submodule.map (phiH Z P1 2).toLinearEquiv.toLinearMap
      (LinearMap.ker (HomologicalComplex.homologyMap (CxMap Z d) 2).hom) =
      LinearMap.ker ((FXmap d).app (Z.homology 2)).hom := by
    refine Submodule.ext fun y => ?_
    have hsq := phiH_square Z P1 P0 d 2
    have hel : ∀ x : (CxF Z P1).homology 2, (phiH Z P0 2).hom.hom
        ((HomologicalComplex.homologyMap (CxMap Z d) 2).hom x) =
          ((FXmap d).app (Z.homology 2)).hom ((phiH Z P1 2).hom.hom x) := fun x =>
      congrArg (fun φ => φ.hom x) hsq
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker] at hx
      change ((FXmap d).app (Z.homology 2)).hom ((phiH Z P1 2).hom.hom x) = 0
      rw [← hel, hx, map_zero]
    · intro hy
      have hh : (phiH Z P1 2).hom.hom ((phiH Z P1 2).toLinearEquiv.symm y) = y :=
        (phiH Z P1 2).toLinearEquiv.apply_symm_apply y
      refine ⟨(phiH Z P1 2).toLinearEquiv.symm y, ?_, hh⟩
      rw [LinearMap.mem_ker]
      apply (phiH Z P0 2).toLinearEquiv.injective
      change (phiH Z P0 2).hom.hom ((HomologicalComplex.homologyMap (CxMap Z d) 2).hom
        ((phiH Z P1 2).toLinearEquiv.symm y)) = (phiH Z P0 2).hom.hom 0
      rw [hel, map_zero, hh]
      exact hy
  let e1 : (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3 ≃ₗ[ℚ] LinearMap.range (hG.δ 3 2 hrel).hom :=
    LinearEquiv.ofInjective (hG.δ 3 2 hrel).hom hinj
  let e2 : LinearMap.range (hG.δ 3 2 hrel).hom ≃ₗ[ℚ]
      LinearMap.ker (HomologicalComplex.homologyMap (CxMap Z d) 2).hom :=
    LinearEquiv.ofEq _ _ hrange
  let e3 : LinearMap.ker (HomologicalComplex.homologyMap (CxMap Z d) 2).hom ≃ₗ[ℚ]
      LinearMap.ker ((FXmap d).app (Z.homology 2)).hom :=
    LinearEquiv.ofSubmodules (phiH Z P1 2).toLinearEquiv _ _ hker
  exact e1.trans (e2.trans e3)

end Main

end ThmA

end TernaryPeriodPolynomials.Argument.HochschildSerre
