module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ShapiroCut

@[expose] public section


/-!
# Naturality of the Shapiro coordinates: base points, conjugation and subgroups

Formalized by Claude Sonnet 5.5.

* `barChainMap f φ`: the map of Hom cochains of the bar resolutions induced by a group homomorphism `f : G → H` and a comparison `φ : Res_f A ⟶ B` of coefficient modules (the
  generalization of `restrictBarChain` from inclusions), with the formula on generators and its relation to `groupCohomology.map`;
* `stabCoord_conj`: the coordinate at `γ z` with respect to `S₂`, with base vertex `v₀`, is `barChainMap` of the coordinate at `z` with respect to `S₁`, with base vertex `γ⁻¹ v₀`,
  when `S₂ = γ S₁ γ⁻¹` (or just receives the conjugation `f`);
* `faceCoord_conj`: on cohomology (the base vertex does not matter), `H(stabCoord_{S₂, γ z}) = H(stabCoord_{S₁, z}) ≫ H(barChainMap f φ)`.
-/

open CategoryTheory Limits Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section BarMap

variable {G H : Type} [Group G] [Group H] (f : G →* H) {A : Rep.{0} ℚ H} {B : Rep.{0} ℚ G}
  (φ : Rep.res f A ⟶ B)

/-- The map of Hom cochains of the bar resolutions induced by `f` and `φ`. -/
def barChainMap : homCochains (Rep.barComplex ℚ H) A ⟶ homCochains (Rep.barComplex ℚ G) B :=
  (groupCohomology.inhomogeneousCochainsIso A).inv ≫ groupCohomology.cochainsMap f φ ≫
    (groupCohomology.inhomogeneousCochainsIso B).hom

theorem barChainMap_apply (k : ℕ) (c : (Rep.barComplex ℚ H).X k ⟶ A) (x : Fin k → G) :
    (((barChainMap f φ).f k).hom c).hom (single x (MonoidAlgebra.single 1 1)) =
      φ.hom (c.hom (single (fun i => f (x i)) (MonoidAlgebra.single 1 1))) := by
  have key : ∀ (F : (Fin k → G) → B),
      ((Rep.freeLiftLEquiv ℚ G (Fin k → G) B).symm F).hom
        (single x (MonoidAlgebra.single 1 1)) = F x := by
    intro F
    change (Representation.freeLift B.ρ F) (single x (MonoidAlgebra.single 1 1)) = F x
    rw [Representation.freeLift_single_single]
    simp
  change ((Rep.freeLiftLEquiv ℚ G (Fin k → G) B).symm
    (fun y => φ.hom ((Rep.freeLiftLEquiv ℚ H (Fin k → H) A c) (fun i => f (y i))))).hom
      (single x (MonoidAlgebra.single 1 1)) = _
  rw [key]
  rfl


theorem barChainMap_homology (n : ℕ) :
    HomologicalComplex.homologyMap (barChainMap f φ) n ≫ (gisoBar B n).inv =
      (gisoBar A n).inv ≫ groupCohomology.map f φ n := by
  have hS := gisoBar_hom B n
  have hΓ := gisoBar_hom A n
  have hinv : (gisoBar A n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n :=
    Iso.inv_ext (by
      erw [hΓ, ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
        HomologicalComplex.homologyMap_id]
      rfl)
  unfold barChainMap
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hinv]
  simp only [Category.assoc]
  erw [← hS, Iso.hom_inv_id, Category.comp_id]
  rfl

end BarMap


section Base

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]

theorem fixThetaBar_aug (G : Type) [Group G] [MulAction G V] [MulAction G Z] (v v' : V) (z : Z)
    (hz : ∀ g : G, g • z = z) (hfree : ∀ (γ : G) (v : V), γ • v = v → γ = 1) (v₀ : V) :
    (fixThetaBar v z hz).f 0 ≫ (prodResolution G V Z v₀ hfree).π.f 0 =
      (fixThetaBar v' z hz).f 0 ≫ (prodResolution G V Z v₀ hfree).π.f 0 := by
  apply Rep.free_ext
  intro x
  change (prodEps G V Z).hom (((fixThetaBar v z hz).f 0).hom (single x (MonoidAlgebra.single 1 1))) =
    (prodEps G V Z).hom (((fixThetaBar v' z hz).f 0).hom (single x (MonoidAlgebra.single 1 1)))
  rw [fixThetaBar_f_single, fixThetaBar_f_single]
  erw [prodEps_single, prodEps_single]

/-- **The Shapiro coordinate on cohomology does not depend on the base vertex.** -/
theorem homologyMap_stabCoord_base (S : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v v' : V) (z : Z)
    (hz : ∀ g : S, g • z = z) (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (n : ℕ) :
    HomologicalComplex.homologyMap (stabCoord S W v' z hz) n =
      HomologicalComplex.homologyMap (stabCoord S W v z hz) n := by
  unfold stabCoord fixCoord
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  congr 1
  exact fixCoord_homology_eq (G := S) (V := V) (Z := Z) (Rep.res S.subtype W) v z hz (free_stab S hfree)
    (fixThetaBar v' z hz) (fixThetaBar_aug S v' v z hz (free_stab S hfree) v) n

end Base


section Conj

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (W : Rep.{0} ℚ Γ)
  (v₀ : V) (z : Z) (γ : Γ) (S₁ S₂ : Subgroup Γ)
  (hS₁ : ∀ g : S₁, g • z = z) (hS₂ : ∀ g : S₂, g • (γ • z) = γ • z)
  (f : S₂ →* S₁) (hf : ∀ s : S₂, (f s : Γ) = γ⁻¹ * s * γ)

/-- The coefficient comparison `ρ_W(γ)` between the restriction to `S₁` transported along `f` and the restriction to `S₂`. -/
def conjComparison : Rep.res f (Rep.res S₁.subtype W) ⟶ Rep.res S₂.subtype W :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (W.ρ γ) (fun s v => by
    change W.ρ γ (W.ρ (f s : Γ) v) = W.ρ (s : Γ) (W.ρ γ v)
    rw [hf s, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group))

include hf in
theorem conj_partialProd {k : ℕ} (x : Fin k → S₂) (i : Fin (k + 1)) :
    ((Fin.partialProd (fun j => f (x j)) i : S₁) : Γ) = γ⁻¹ * (Fin.partialProd x i : S₂) * γ := by
  induction i using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ j ih =>
    rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, Subgroup.coe_mul, ih, hf]
    group

include hf in
theorem stabCoord_conj_apply (k : ℕ) (c : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → S₂) :
    (((stabCoord S₂ W v₀ (γ • z) hS₂).f k).hom c).hom (single x (MonoidAlgebra.single 1 1)) =
      W.ρ γ ((((stabCoord S₁ W (γ⁻¹ • v₀) z hS₁).f k).hom c).hom
        (single (fun i => f (x i)) (MonoidAlgebra.single 1 1))) := by
  rw [stabCoord_single, stabCoord_single]
  have hy : (fun i => (Fin.partialProd x i : S₂) • v₀, γ • z) =
      γ • ((fun i => (Fin.partialProd (fun j => f (x j)) i : S₁) • (γ⁻¹ • v₀), z) :
        (Fin (k + 1) → V) × Z) := by
    refine Prod.ext (funext fun i => ?_) rfl
    change (Fin.partialProd x i : S₂) • v₀ = γ • ((Fin.partialProd (fun j => f (x j)) i : S₁) • (γ⁻¹ • v₀))
    change ((Fin.partialProd x i : S₂) : Γ) • v₀ =
      γ • (((Fin.partialProd (fun j => f (x j)) i : S₁) : Γ) • (γ⁻¹ • v₀))
    rw [conj_partialProd γ S₁ S₂ f hf, ← mul_smul, ← mul_smul]
    congr 1
    group
  rw [hy]
  exact homFunA_equivariant c γ _


include hf in
/-- **The coordinate at `γ z` is the transport of the coordinate at `z` (with base vertex `γ⁻¹ v₀`).** -/
theorem stabCoord_conj :
    stabCoord S₂ W v₀ (γ • z) hS₂ =
      stabCoord S₁ W (γ⁻¹ • v₀) z hS₁ ≫ barChainMap f (conjComparison W γ S₁ S₂ f hf) := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.free_ext
  intro x
  refine Eq.trans (stabCoord_conj_apply W v₀ z γ S₁ S₂ hS₁ hS₂ f hf k c x) ?_
  exact (barChainMap_apply f (conjComparison W γ S₁ S₂ f hf) k
    (((stabCoord S₁ W (γ⁻¹ • v₀) z hS₁).f k).hom c) x).symm

include hf in
/-- … on cohomology, where the base vertex does not matter. -/
theorem homologyMap_stabCoord_conj (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (n : ℕ) :
    HomologicalComplex.homologyMap (stabCoord S₂ W v₀ (γ • z) hS₂) n =
      HomologicalComplex.homologyMap (stabCoord S₁ W v₀ z hS₁) n ≫
        HomologicalComplex.homologyMap (barChainMap f (conjComparison W γ S₁ S₂ f hf)) n := by
  rw [stabCoord_conj W v₀ z γ S₁ S₂ hS₁ hS₂ f hf, HomologicalComplex.homologyMap_comp,
    homologyMap_stabCoord_base S₁ W v₀ (γ⁻¹ • v₀) z hS₁ hfree]

end Conj


section Pullback

variable {Γ : Type} [Group Γ] {V Z Z' : Type} [MulAction Γ V] [MulAction Γ Z] [MulAction Γ Z']

/-- **Naturality of the Shapiro coordinate along an equivariant map of label sets.** -/
theorem stabCoord_pullback (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z) (S : Subgroup Γ)
    (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z) (hz' : ∀ g : S, g • α z = α z) :
    homPullback (prodMapHom Γ V Z α hα) W ≫ stabCoord S W v₀ z hz = stabCoord S W v₀ (α z) hz' := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.free_ext
  intro x
  change (((stabCoord S W v₀ z hz).f k).hom ((prodMapHom Γ V Z α hα).f k ≫ c)).hom
      (single x (MonoidAlgebra.single 1 1)) =
    (((stabCoord S W v₀ (α z) hz').f k).hom c).hom (single x (MonoidAlgebra.single 1 1))
  rw [stabCoord_single]
  erw [stabCoord_single]
  exact homFunA_comp_map (A := W) (V := V) (Γ := Γ) (Z := Z) (Z' := Z') α hα c
    (fun i => Fin.partialProd x i • v₀) z

end Pullback

section Sub

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]

/-- **Passing to a smaller subgroup.** -/
theorem stabCoord_sub (S S' : Subgroup Γ) (h : S' ≤ S) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z)
    (hz : ∀ g : S, g • z = z) (hz' : ∀ g : S', g • z = z) :
    stabCoord S' W v₀ z hz' = stabCoord S W v₀ z hz ≫
      barChainMap (Subgroup.inclusion h) (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W))) := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.free_ext
  intro x
  refine Eq.trans ?_ (barChainMap_apply (Subgroup.inclusion h) _ k
    (((stabCoord S W v₀ z hz).f k).hom c) x).symm
  have hid : ∀ {G : Type} [Group G] (X : Rep.{0} ℚ G) (v : X), Rep.Hom.hom (𝟙 X) v = v := fun _ _ => rfl
  refine Eq.trans ?_ (hid _ _).symm
  erw [stabCoord_single, stabCoord_single]
  have h2 : (fun i => Fin.partialProd x i • v₀) =
      fun i => (Fin.partialProd (fun j => Subgroup.inclusion h (x j)) i : S) • v₀ := by
    funext i
    have : ((Fin.partialProd (fun j => Subgroup.inclusion h (x j)) i : S) : Γ) =
        ((Fin.partialProd x i : S') : Γ) := by
      induction i using Fin.induction with
      | zero => simp [Fin.partialProd_zero]
      | succ j ih =>
        rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, Subgroup.coe_mul, ih]
        rfl
    change ((Fin.partialProd x i : S') : Γ) • v₀ = ((Fin.partialProd (fun j => Subgroup.inclusion h (x j)) i : S) : Γ) • v₀
    rw [this]
  rw [h2]

end Sub

end TernaryPeriodPolynomials.Argument.GammaNStokes
