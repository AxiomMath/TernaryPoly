module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QSide
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Inflation

@[expose] public section


/-!
# Naturality in `Z` of the abstract Hochschild-Serre step

Formalized by Claude Sonnet 5.5.

For a chain map `f : Z ⟶ Z'` of complexes of projective `Q`-modules, `CxMapZ f X : CxF Z X ⟶ CxF Z' X`, and
`thmAEquiv_natural`: `thmAEquiv Z'` of the image of a class in `H₃((Z ⊗ 1)_Q)` is the image under `(FX P1).map (H₂ f)` of
`thmAEquiv Z` of the class (naturality of the connecting homomorphism of the short exact sequence of complexes
`sesC`, `HomologicalComplex.HomologySequence.δ_naturality`, and of `phiH`).  `homologyKerMap` is the map induced on the
kernels.
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q]

section Natural

variable {Z Z' : ChainComplex (Rep.{0} ℚ Q) ℕ} (f : Z ⟶ Z')

/-- The chain map `CxF Z X ⟶ CxF Z' X` induced by `f`. -/
def CxMapZ (X : Rep.{0} ℚ Q) : CxF Z X ⟶ CxF Z' X :=
  ((FX X).mapHomologicalComplex (ComplexShape.down ℕ)).map f

theorem CxMapZ_f (X : Rep.{0} ℚ Q) (j : ℕ) : (CxMapZ f X).f j = (FX X).map (f.f j) := rfl

theorem phiH_natural_Z (X : Rep.{0} ℚ Q) [Projective X] (n : ℕ) :
    HomologicalComplex.homologyMap (CxMapZ f X) n ≫ (phiH Z' X n).hom =
      (phiH Z X n).hom ≫ (FX X).map (HomologicalComplex.homologyMap f n) := by
  have := FX_preservesHomology X
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) (FX X)

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)

/-- The map induced on the kernels of `(H₂ ⊗ d)_Q` by a chain map. -/
def homologyKerMap :
    LinearMap.ker ((FXmap d).app (Z.homology 2)).hom →ₗ[ℚ]
      LinearMap.ker ((FXmap d).app (Z'.homology 2)).hom :=
  ((FX P1).map (HomologicalComplex.homologyMap f 2)).hom.restrict (by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := congrArg (fun φ => φ.hom x)
      ((FXmap d).naturality (HomologicalComplex.homologyMap f 2))
    change ((FXmap d).app (Z'.homology 2)).hom (((FX P1).map (HomologicalComplex.homologyMap f 2)).hom x) =
      ((FX P0).map (HomologicalComplex.homologyMap f 2)).hom (((FXmap d).app (Z.homology 2)).hom x) at h
    rw [h, hx, map_zero])

variable [Projective P1] [Projective P0] (hS : (ShortComplex.mk d ε hdε).ShortExact)
  (hZ : ∀ j, Projective (Z.X j)) (hZ' : ∀ j, Projective (Z'.X j))
  (hZ3 : IsZero (Z.homology 3)) (hZ3' : IsZero (Z'.homology 3))

/-- The morphism of short complexes `sesC Z ⟶ sesC Z'`. -/
def sesCMapZ : sesC Z P1 P0 d ε hdε ⟶ sesC Z' P1 P0 d ε hdε where
  τ₁ := CxMapZ f P1
  τ₂ := CxMapZ f P0
  τ₃ := CxMapZ f (Rep.trivial ℚ Q ℚ)
  comm₁₂ := by
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    simp only [sesC, HomologicalComplex.comp_f, CxMap_f, CxMapZ_f]
    exact ((FXmap d).naturality (f.f j))
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    simp only [sesC, HomologicalComplex.comp_f, CxMap_f, CxMapZ_f]
    exact ((FXmap ε).naturality (f.f j))

theorem thmAEquiv_val (x : (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3) :
    ((thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 x :
          LinearMap.ker ((FXmap d).app (Z.homology 2)).hom) : (FX P1).obj (Z.homology 2)) =
      (phiH Z P1 2).hom.hom
        (((sesC_shortExact Z P1 P0 d ε hdε hZ hS).δ 3 2 rfl).hom x) := rfl

/-- **Naturality of the abstract Hochschild-Serre step in `Z`.** -/
theorem thmAEquiv_natural (x : (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3) :
    ((thmAEquiv Z' P1 P0 d ε hdε hZ' hS hZ3' ((HomologicalComplex.homologyMap
        (CxMapZ f (Rep.trivial ℚ Q ℚ)) 3).hom x) :
      LinearMap.ker ((FXmap d).app (Z'.homology 2)).hom) :
        (FX P1).obj (Z'.homology 2)) =
      ((FX P1).map (HomologicalComplex.homologyMap f 2)).hom
        ((thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 x :
          LinearMap.ker ((FXmap d).app (Z.homology 2)).hom) : (FX P1).obj (Z.homology 2)) := by
  rw [thmAEquiv_val, thmAEquiv_val]
  have hδ := congrArg (fun m => m.hom x)
    (HomologicalComplex.HomologySequence.δ_naturality (sesCMapZ f P1 P0 d ε hdε)
      (sesC_shortExact Z P1 P0 d ε hdε hZ hS) (sesC_shortExact Z' P1 P0 d ε hdε hZ' hS) 3 2 rfl)
  have hφ := congrArg (fun m => m.hom
    (((sesC_shortExact Z P1 P0 d ε hdε hZ hS).δ 3 2 rfl).hom x)) (phiH_natural_Z f P1 2)
  change (HomologicalComplex.homologyMap (CxMapZ f P1) 2).hom
      (((sesC_shortExact Z P1 P0 d ε hdε hZ hS).δ 3 2 rfl).hom x) =
    ((sesC_shortExact Z' P1 P0 d ε hdε hZ' hS).δ 3 2 rfl).hom
      ((HomologicalComplex.homologyMap (CxMapZ f (Rep.trivial ℚ Q ℚ)) 3).hom x) at hδ
  rw [← hδ]
  exact hφ

omit [Projective P1] [Projective P0] in
theorem homologyKerMap_bijective [IsIso (HomologicalComplex.homologyMap f 2)] :
    Function.Bijective (homologyKerMap f P1 P0 d) := by
  let e : Z.homology 2 ≅ Z'.homology 2 := asIso (HomologicalComplex.homologyMap f 2)
  have h : ∀ y, ((homologyKerMap f P1 P0 d y : LinearMap.ker ((FXmap d).app (Z'.homology 2)).hom) :
        (FX P1).obj (Z'.homology 2)) =
      (kerNatEquiv (FXmap d) e y : (FX P1).obj (Z'.homology 2)) := fun y => rfl
  have hk : homologyKerMap f P1 P0 d = (kerNatEquiv (FXmap d) e).toLinearMap := by
    ext y
    exact h y
  rw [hk]
  exact (kerNatEquiv (FXmap d) e).bijective

include P1 P0 d ε hdε hS hZ hZ' hZ3 hZ3' in
/-- **A chain map that is an isomorphism on `H₂` induces a bijection on `H₃((Z ⊗ 1)_Q)`.** -/
theorem homologyMap_three_bijective [IsIso (HomologicalComplex.homologyMap f 2)] :
    Function.Bijective (HomologicalComplex.homologyMap (CxMapZ f (Rep.trivial ℚ Q ℚ)) 3).hom := by
  have hnat := thmAEquiv_natural f P1 P0 d ε hdε hS hZ hZ' hZ3 hZ3'
  have hb := homologyKerMap_bijective f P1 P0 d
  constructor
  · intro x y hxy
    have h1 := hnat x
    have h2 := hnat y
    rw [hxy] at h1
    have h3 : homologyKerMap f P1 P0 d (thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 x) =
        homologyKerMap f P1 P0 d (thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3 y) := by
      apply Subtype.ext
      exact h1.symm.trans h2
    exact (thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3).injective (hb.1 h3)
  · intro y
    obtain ⟨k, hk⟩ := hb.2 (thmAEquiv Z' P1 P0 d ε hdε hZ' hS hZ3' y)
    obtain ⟨x, rfl⟩ := (thmAEquiv Z P1 P0 d ε hdε hZ hS hZ3).surjective k
    refine ⟨x, ?_⟩
    apply (thmAEquiv Z' P1 P0 d ε hdε hZ' hS hZ3').injective
    apply Subtype.ext
    exact (hnat x).trans (congrArg Subtype.val hk)

end Natural

end TernaryPeriodPolynomials.Argument.HochschildSerre
