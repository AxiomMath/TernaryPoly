module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.BoundaryCap
public import TernaryPeriodPolynomials.GroupCohomology.Homology.ResolutionTransfer

@[expose] public section


open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.SymmetricSpaceBoundaryFullTransfer TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.RationalCohomologyDescent
  TernaryPoly.SingularLocalHomology TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCone
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FiberModel

/-!
# Level G: cochain-level descent projector and fixed classes

Element-level formulas for the descent projector on boundary cochains, and the fact that a
class of `H¹(Hom(C₍∂₎, M))` fixed by all of `GL₃(ℤ)` lies in the range of restriction
from the full group.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (n : ℕ) (e : ℤ)

/-- Value of the descent projector on a cochain: the average of the conjugation actions over the cosets. -/
theorem descentProjector_apply (m : ℕ)
    (φ : boundaryChains.X m ⟶ restrictedCoefficients n e)
    (x : boundaryChains.X m) :
    ((((descentProjector principalSix fullBoundaryChains (actualCoefficients n e)).f m).hom φ).hom x) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ∑ r : RightCosets principalSix,
        (conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹ φ).hom x := by
  change ((transferHom principalSix (fullBoundaryChains.X m) (actualCoefficients n e)) φ).hom x = _
  erw [transferHom_apply]
  have hp : ∀ g : IntegralGL,
      (conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) g⁻¹ φ).hom x =
        (actualCoefficients n e).ρ g⁻¹ (φ.hom ((fullBoundaryChains.X m).ρ g x)) := fun g => by
    rw [conjHom_apply, inv_inv]
    rfl
  simp only [hp]
  rfl

theorem rep_sum_apply {H : Type} [Group H] {X Y : Rep.{0} ℚ H} {α : Type*} (s : Finset α) (f : α → (X ⟶ Y)) (x : X) :
    (∑ a ∈ s, f a).hom x = ∑ a ∈ s, (f a).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Rep.add_hom]; exact congrArg₂ (· + ·) rfl ih

theorem cochain_sum_f {C C' : CochainComplex (ModuleCat.{0} ℚ) ℕ} {α : Type*} (s : Finset α) (f : α → (C ⟶ C')) (m : ℕ) :
    (∑ x ∈ s, f x).f m = ∑ x ∈ s, (f x).f m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, HomologicalComplex.add_f_apply]

/-- Cochain-level average formula (element form in the Hom module). -/
theorem descentProjector_f_apply (m : ℕ) (φ : boundaryChains.X m ⟶ restrictedCoefficients n e) :
    ((descentProjector principalSix fullBoundaryChains (actualCoefficients n e)).f m).hom φ =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ∑ r : RightCosets principalSix,
        conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹ φ := by
  apply rep_hom_ext'
  intro x
  refine (descentProjector_apply n e m φ x).trans ?_
  have h := rep_sum_apply (Finset.univ : Finset (RightCosets principalSix))
    (fun r => conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹ φ) x
  change _ = (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ((∑ r : RightCosets principalSix,
        conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹ φ).hom x)
  rw [h]

/-- The restriction of an equivariant cochain is fixed by the conjugation action. -/
theorem restriction_hcAct (g : IntegralGL) :
    restriction principalSix fullBoundaryChains (actualCoefficients n e) ≫
        hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) g =
      restriction principalSix fullBoundaryChains (actualCoefficients n e) := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  let φ' : fullBoundaryChains.X m ⟶ actualCoefficients n e := φ
  change (conjHom (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) g
    (restrictHom principalSix (fullBoundaryChains.X m) (actualCoefficients n e) φ')).hom x = φ'.hom x
  refine (conjHom_apply (bdryAct.act m) (GAct.ofRep principalSix (actualCoefficients n e)) g
    (restrictHom principalSix (fullBoundaryChains.X m) (actualCoefficients n e) φ') x).trans ?_
  have h := Rep.hom_comm_apply φ' g ((fullBoundaryChains.X m).ρ g⁻¹ x)
  change (actualCoefficients n e).ρ g (φ'.hom ((fullBoundaryChains.X m).ρ g⁻¹ x)) = φ'.hom x
  rw [← h]
  congr 1
  exact LinearMap.congr_fun (show (fullBoundaryChains.X m).ρ g * (fullBoundaryChains.X m).ρ g⁻¹ = 1 by
    rw [← map_mul, mul_inv_cancel, map_one]) x

/-- A class of `Hom_Γ(C_*(∂X̃), W)` fixed by the conjugation action of `G` is the restriction of a class of `Hom_G`. -/
theorem fixed_mem_range_restriction
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1)
    (hx : ∀ g : IntegralGL,
      homologyMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) g) 1 x = x) :
    x ∈ LinearMap.range (homologyMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1).hom := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1)).mp inferInstance x
  have inj : Function.Injective ((homCochains boundaryChains (restrictedCoefficients n e)).iCycles 1).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hw : cyclesMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 z =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ • ∑ r : RightCosets principalSix,
        cyclesMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹) 1 z := by
    apply inj
    have hi : ∀ (g : IntegralGL),
        ((homCochains boundaryChains (restrictedCoefficients n e)).iCycles 1).hom
          (cyclesMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) g) 1 z) =
        ((hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) g).f 1).hom
          (((homCochains boundaryChains (restrictedCoefficients n e)).iCycles 1).hom z) := fun g =>
      ConcreteCategory.congr_hom
        (cyclesMap_i (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) g) 1) z
    have hd : ((homCochains boundaryChains (restrictedCoefficients n e)).iCycles 1).hom
        (cyclesMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 z) =
        ((descentProjector principalSix fullBoundaryChains (actualCoefficients n e)).f 1).hom
          (((homCochains boundaryChains (restrictedCoefficients n e)).iCycles 1).hom z) :=
      ConcreteCategory.congr_hom (cyclesMap_i _ 1) z
    rw [hd, map_smul, map_sum]
    simp only [hi]
    exact descentProjector_f_apply n e 1 _
  have hπ : (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
      (cyclesMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 z) =
      (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 z := by
    rw [hw, map_smul, map_sum]
    have hall : ∀ r : RightCosets principalSix,
        (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1
          (cyclesMap (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹) 1 z) =
        (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 z := fun r => by
      have := hx r.out⁻¹
      have hn := congrArg (fun m => m z)
        (homologyπ_naturality (hcAct bdryAct (GAct.ofRep principalSix (actualCoefficients n e)) r.out⁻¹) 1)
      exact hn.symm.trans this
    simp only [hall, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := RightCosets principalSix)).ne'), one_smul]
  have hn := congrArg (fun m => m z)
    (homologyπ_naturality (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  have hfix : homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 z) =
      (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 z := hn.trans hπ
  have hcomp : ∀ y, homologyMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1
      (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 y) =
      homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 y := fun y => by
    change (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 ≫
      homologyMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1) y = _
    rw [← homologyMap_comp]
    rfl
  exact ⟨_, (hcomp _).trans hfix⟩

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
