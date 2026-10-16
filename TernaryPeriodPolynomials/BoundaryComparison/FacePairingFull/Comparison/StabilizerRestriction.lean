module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerCoordinate
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


/-!
# The Shapiro coordinate of a restricted class is Mathlib's restriction to the stabilizer

For a point `z` of a `Γ`-set `Z` with stabilizer `S`, the coordinate `faceCoord` at `z` of the pullback
to `Z` of a class `x` on the point resolution is `groupCohomology.map` along `S ≤ Γ` of the group-cohomology
class `fixCoordH x` of `x` (`faceCoord_restriction`).  Proof: Mathlib's `groupCohomologyIso` for the bar
resolution is the homology of the inhomogeneous cochains (`gisoBar_hom`); the restriction on inhomogeneous
cochains, conjugated to Hom cochains of the bar resolutions, is `restrictBarChain`
(`restrictBarChain_apply`); and on bar generators both composites evaluate the invariant function at the
simplex with vertices the partial products (`restrict_chain_eq`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section

variable {G : Type} [Group G] (A : Rep.{0} ℚ G) (n : ℕ)

theorem gisoBar_hom :
    (gisoBar A n).hom =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n := by
  have e : (Rep.barResolution.extIso ℚ G A n).inv ≫ ((Rep.barResolution ℚ G).isoExt n A).hom =
      𝟙 _ := Iso.inv_hom_id _
  have h2 : (gisoBar A n).hom =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
        ((Rep.barResolution.extIso ℚ G A n).inv ≫ ((Rep.barResolution ℚ G).isoExt n A).hom) := rfl
  rw [h2, e]
  exact Category.comp_id _

end

section Restriction

open TernaryPoly.EquivariantSingularSmall

variable {Γ : Type} [Group Γ] (S : Subgroup Γ) (W : Rep.{0} ℚ Γ)

/-- The restriction `Hom(barComplex Γ, W) ⟶ Hom(barComplex S, Res W)` induced by `S ≤ Γ` on the
inhomogeneous cochains. -/
def restrictBarChain : homCochains (Rep.barComplex ℚ Γ) W ⟶
    homCochains (Rep.barComplex ℚ S) (Rep.res S.subtype W) :=
  (groupCohomology.inhomogeneousCochainsIso W).inv ≫
    groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype W)) ≫
    (groupCohomology.inhomogeneousCochainsIso (Rep.res S.subtype W)).hom

theorem restrictBarChain_apply (k : ℕ) (φ : (Rep.barComplex ℚ Γ).X k ⟶ W) (x : Fin k → S) :
    (((restrictBarChain S W).f k).hom φ).hom (single x (MonoidAlgebra.single 1 1)) =
      φ.hom (single (fun i => (x i : Γ)) (MonoidAlgebra.single 1 1)) := by
  have key : ∀ (F : (Fin k → S) → Rep.res S.subtype W),
      ((Rep.freeLiftLEquiv ℚ S (Fin k → S) (Rep.res S.subtype W)).symm F).hom
        (single x (MonoidAlgebra.single 1 1)) = F x := by
    intro F
    change (Representation.freeLift (Rep.res S.subtype W).ρ F)
      (single x (MonoidAlgebra.single 1 1)) = F x
    rw [Representation.freeLift_single_single]
    simp
  change ((Rep.freeLiftLEquiv ℚ S (Fin k → S) (Rep.res S.subtype W)).symm
    (fun y => (𝟙 (Rep.res S.subtype W) : Rep.res S.subtype W ⟶ Rep.res S.subtype W).hom
      ((Rep.freeLiftLEquiv ℚ Γ (Fin k → Γ) W φ) (fun i => (y i : Γ))))).hom
      (single x (MonoidAlgebra.single 1 1)) = _
  rw [key]
  rfl

theorem coe_partialProd {k : ℕ} (x : Fin k → S) (i : Fin (k + 1)) :
    ((Fin.partialProd x i : S) : Γ) = Fin.partialProd (fun j => (x j : Γ)) i := by
  induction i using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ j ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, ih]

end Restriction

section Main

open TernaryPoly.EquivariantSingularSmall

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]
  (S : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z)

theorem restrict_chain_eq :
    homPullback (prodMapHom Γ V Z (fun _ => PUnit.unit) (fun _ _ => rfl)) W ≫
        stabCoord S W v₀ z hz =
      fixCoord v₀ PUnit.unit (fun _ => rfl) W ≫ restrictBarChain S W := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.free_ext
  intro x
  change (((stabCoord S W v₀ z hz).f k).hom
      (((prodMapHom Γ V Z (fun _ => PUnit.unit) (fun _ _ => rfl)).f k) ≫ c)).hom
        (single x (MonoidAlgebra.single 1 1)) =
    (((restrictBarChain S W).f k).hom (((fixThetaBar v₀ PUnit.unit (fun _ => rfl)).f k) ≫ c)).hom
        (single x (MonoidAlgebra.single 1 1))
  rw [stabCoord_single, restrictBarChain_apply]
  have h1 := homFunA_comp_map (A := W) (V := V) (Γ := Γ) (Z := Z) (Z' := PUnit)
    (fun _ => PUnit.unit) (fun _ _ => rfl) c (fun i => Fin.partialProd x i • v₀) z
  refine h1.trans ?_
  change c.hom (MonoidAlgebra.single (fun i => Fin.partialProd x i • v₀, PUnit.unit) 1) =
    c.hom (((fixThetaBar v₀ PUnit.unit (fun _ => rfl)).f k).hom
      (single (fun i => (x i : Γ)) (MonoidAlgebra.single 1 1)))
  rw [fixThetaBar_f_single]
  have h2 : (fun i => Fin.partialProd (fun j => (x j : Γ)) i • v₀) =
      fun i => (Fin.partialProd x i : S) • v₀ := by
    funext i
    rw [← coe_partialProd]
    rfl
  rw [h2]
  rfl

/-- **Restriction to the stabilizer.**  The Shapiro coordinate at `z` of the pullback to `Z` of a class on the
point resolution is the Mathlib restriction `groupCohomology.map` along the inclusion `S ≤ Γ` of the
class's group cohomology. -/
theorem faceCoord_restriction (n : ℕ) :
    HomologicalComplex.homologyMap
        (homPullback (prodMapHom Γ V Z (fun _ => PUnit.unit) (fun _ _ => rfl)) W) n ≫
      faceCoord S W v₀ z hz n =
    fixCoordH v₀ PUnit.unit (fun _ => rfl) W n ≫
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype W)) n := by
  have hS := gisoBar_hom (Rep.res S.subtype W) n
  have hΓ := gisoBar_hom W n
  have hinv : (gisoBar W n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso W).inv n :=
    Iso.inv_ext (by
      erw [hΓ, ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
        HomologicalComplex.homologyMap_id]
      rfl)
  have T1 : HomologicalComplex.homologyMap (restrictBarChain S W) n ≫
      (gisoBar (Rep.res S.subtype W) n).inv =
      (gisoBar W n).inv ≫
        groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype W)) n := by
    unfold restrictBarChain
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hinv]
    simp only [Category.assoc]
    erw [← hS, Iso.hom_inv_id, Category.comp_id]
    rfl
  have T2 : HomologicalComplex.homologyMap
        (homPullback (prodMapHom Γ V Z (fun _ => PUnit.unit) (fun _ _ => rfl)) W) n ≫
      HomologicalComplex.homologyMap (stabCoord S W v₀ z hz) n =
      HomologicalComplex.homologyMap (fixCoord v₀ PUnit.unit (fun _ => rfl) W) n ≫
        HomologicalComplex.homologyMap (restrictBarChain S W) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      restrict_chain_eq]
  have e1 : HomologicalComplex.homologyMap (stabResChain (Z := Z) S W) n ≫
      HomologicalComplex.homologyMap (fixCoord v₀ z hz (Rep.res S.subtype W)) n =
      HomologicalComplex.homologyMap (stabCoord S W v₀ z hz) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    rfl
  unfold faceCoord fixCoordH
  calc _ = (HomologicalComplex.homologyMap
        (homPullback (prodMapHom Γ V Z (fun _ => PUnit.unit) (fun _ _ => rfl)) W) n ≫
        (HomologicalComplex.homologyMap (stabResChain (Z := Z) S W) n ≫
          HomologicalComplex.homologyMap (fixCoord v₀ z hz (Rep.res S.subtype W)) n)) ≫
        (gisoBar (Rep.res S.subtype W) n).inv := by
          simp only [Category.assoc]
    _ = (HomologicalComplex.homologyMap (fixCoord v₀ PUnit.unit (fun _ => rfl) W) n ≫
        HomologicalComplex.homologyMap (restrictBarChain S W) n) ≫
        (gisoBar (Rep.res S.subtype W) n).inv := by
          rw [e1, T2]
    _ = _ := by
          rw [Category.assoc, T1, ← Category.assoc]

end Main

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
