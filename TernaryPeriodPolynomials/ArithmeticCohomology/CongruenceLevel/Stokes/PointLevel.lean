module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.OrbitPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.FaceCoordCone

@[expose] public section


/-!
# Point level: every class of the group cohomology of `Γ(6)` is the Mathlib class of a class of the point resolution

Formalized by Claude Sonnet 5.5.

* `map_two_injective_of_bijective`: restriction of `H²` along a bijective homomorphism is injective;
* `fixCoordH_pt_surjective`: `fixCoordH` of the point resolution of `Γ(6)` is onto `groupCohomology W 2`, from the product bijectivity of the Shapiro coordinates for the
  one-point label set.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.EquivariantSingularSmall

section Bijective

variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]

/-- Restriction of `H²` along a bijective group homomorphism is injective. -/
theorem map_two_injective_of_bijective (f : G →* H) (hf : Function.Bijective f) (A : Rep k H)
    (x y : groupCohomology.H2 A)
    (h : (groupCohomology.map f (𝟙 (Rep.res f A)) 2).hom x = (groupCohomology.map f (𝟙 (Rep.res f A)) 2).hom y) :
    x = y := by
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    induction y using groupCohomology.H2_induction_on with
    | h z' =>
      have h1 := groupCohomology.H2π_comp_map_apply f (𝟙 (Rep.res f A)) z
      have h2 := groupCohomology.H2π_comp_map_apply f (𝟙 (Rep.res f A)) z'
      rw [h1, h2, groupCohomology.H2π_eq_iff] at h
      rw [groupCohomology.H2π_eq_iff]
      obtain ⟨b, hb⟩ := h
      let e : G ≃ H := Equiv.ofBijective f hf
      refine ⟨fun u => b (e.symm u), ?_⟩
      funext ⟨u, v⟩
      obtain ⟨a, rfl⟩ := hf.2 u
      obtain ⟨c, rfl⟩ := hf.2 v
      have := congrFun hb (a, c)
      have hs : ∀ a : G, e.symm (f a) = a := fun a => e.symm_apply_apply a
      change A.ρ (f a) (b (e.symm (f c))) - b (e.symm (f a * f c)) + b (e.symm (f a)) = _
      rw [← map_mul, hs, hs, hs]
      exact this

end Bijective


section Point

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

open GeneralEisenstein

theorem homPullback_id' {C : ChainComplex (Rep ℚ Γ6) ℕ} (W : Rep.{0} ℚ Γ6) :
    homPullback (𝟙 C) W = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (𝟙 C : C ⟶ C).f k ≫ c = c
  exact Category.id_comp c

theorem ptMap_punit : ptMap PUnit = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro k
  refine hom_ext_single ((Fin (k + 1) → RationalGL3) × PUnit) _ (fun y => ?_)
  obtain ⟨x, z⟩ := y
  change ((prodMapHom Γ6 RationalGL3 PUnit (fun _ => PUnit.unit) (fun _ _ => rfl)).f k).hom
    (MonoidAlgebra.single (x, z) 1) = _
  rw [prodMapHom_f_single]
  rfl

theorem labelOrbits_punit_subsingleton : Subsingleton (labelOrbits Γ6 PUnit) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn' with
  | h a =>
    induction b using Quotient.inductionOn' with
    | h b =>
      exact Quotient.sound' ⟨1, Subsingleton.elim _ _⟩

/-- **Every class of `H²(Γ(6), W)` is `fixCoordH` of a class of the point resolution.** -/
theorem fixCoordH_pt_surjective (W : Rep.{0} ℚ Γ6) (w : groupCohomology W 2) :
    ∃ X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2,
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W 2).hom X = w := by
  have hsub := labelOrbits_punit_subsingleton
  let o₀ : labelOrbits Γ6 PUnit := Quotient.mk'' PUnit.unit
  obtain ⟨X, hX⟩ := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := PUnit) (1 : RationalGL3)
    vertexAction_free' W).2 (fun o => (groupCohomology.map (stabilizer Γ6 o.out).subtype
      (𝟙 (Rep.res (stabilizer Γ6 o.out).subtype W)) 2).hom w)
  have h0 := congrFun hX o₀
  refine ⟨X, ?_⟩
  have hr := congrArg (fun m => m.hom X) (faceCoord_restriction (stabilizer Γ6 o₀.out) W (1 : RationalGL3)
    o₀.out (fun g => g.2) 2)
  have hid : ∀ Y, (HomologicalComplex.homologyMap (homPullback (prodMapHom Γ6 RationalGL3 PUnit
      (fun _ => PUnit.unit) (fun _ _ => rfl)) W) 2).hom Y = Y := by
    intro Y
    have : prodMapHom Γ6 RationalGL3 PUnit (fun _ => PUnit.unit) (fun _ _ => rfl) = 𝟙 _ := ptMap_punit
    rw [this, homPullback_id']
    simp
  have hr' : (faceCoord (stabilizer Γ6 o₀.out) W (1 : RationalGL3) o₀.out (fun g => g.2) 2).hom X =
      (groupCohomology.map (stabilizer Γ6 o₀.out).subtype
        (𝟙 (Rep.res (stabilizer Γ6 o₀.out).subtype W)) 2).hom
        ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W 2).hom X) := by
    have h := hr
    simp only [CategoryTheory.comp_apply] at h
    erw [hid X] at h
    exact h
  have hbij : Function.Bijective (stabilizer Γ6 o₀.out).subtype := by
    refine ⟨Subtype.val_injective, fun g => ⟨⟨g, ?_⟩, rfl⟩⟩
    exact Subsingleton.elim _ _
  exact map_two_injective_of_bijective _ hbij W _ _ (hr'.symm.trans h0)

end Point

end TernaryPeriodPolynomials.Argument.GammaNStokes
