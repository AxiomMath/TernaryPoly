module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.MathlibShapiro
public import TernaryPeriodPolynomials.GroupCohomology.Homology.ShapiroInv

@[expose] public section


/-!
# Mathlib's Shapiro isomorphism for `M = Ind_K^G E_{n,t}` is inverse to `Cor ∘ ι_*`

Formalized by Claude Sonnet 5.5.

`iotaK n t : E_{n,t} ⟶ Res_K M` is the unit of the induction-restriction adjunction read through `TernaryPoly.inducedIso`: it
sends `a` to the vector of `M` with value `a` at the distinguished covector and `0` elsewhere (`iotaK_apply`).
`mathlibShapiro_inv`: the inverse of `mathlibShapiro` is `groupHomology.map K.subtype (iotaK n t) 3` (from
`GroupHomology.indIso_inv_eq_map`), the classical description of the Shapiro isomorphism by corestriction.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryActualEvaluation
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPoly.PolynomialGLAction TernaryPoly.OrdinaryCovectors
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical

/-- The unit `E ⟶ Res_K Ind_K^G E`, read in the 26-covector model `M`: `a ↦ (a at the distinguished covector, 0 elsewhere)`. -/
def iotaK (n : ℕ) (t : Fin 2) : EK n t ⟶ Rep.res K.subtype (MG n t) :=
  indUnit K (subgroupCoefficients n (expT t)) ≫ (Rep.resFunctor K.subtype).map (inducedIso n (expT t)).hom

theorem mem_K_iff_rowMove (g : IntegralGL) : g ∈ K ↔ rowMove g distinguished = distinguished := by
  constructor
  · intro hg
    apply Subtype.ext
    simpa [rowMove] using hg
  · intro h
    have := congrArg Subtype.val h
    simpa [rowMove] using this

theorem rowMove_distinguished (g : IntegralGL) : rowMove g distinguished = nonzeroRow g := by
  apply Subtype.ext
  simp [rowMove]
  rfl

theorem mem_K_iff_nonzeroRow (g : IntegralGL) : g ∈ K ↔ nonzeroRow g = distinguished := by
  rw [mem_K_iff_rowMove, rowMove_distinguished]

theorem representative_mem_K_iff (r : NonzeroCovector) : representative r ∈ K ↔ r = distinguished := by
  rw [mem_K_iff_nonzeroRow, representative_row]

theorem iotaK_apply (n : ℕ) (t : Fin 2) (a : V n) : (iotaK n t).hom a = Pi.single distinguished a := by
  funext r
  have h1 : (iotaK n t).hom a = (inducedIso n (expT t)).hom.hom
      (Representation.IndV.mk K.subtype (subgroupCoefficients n (expT t)).ρ 1 a) := rfl
  rw [h1]
  unfold inducedIso
  simp only [Iso.trans_hom]
  change fromCoinduced n (expT t) (Rep.indToCoind (subgroupCoefficients n (expT t))
    (Representation.IndV.mk K.subtype (subgroupCoefficients n (expT t)).ρ 1 a)) r = _
  have h2 : ∀ g' : IntegralGL, ((subgroupCoefficients n (expT t)).indToCoind
        ((Representation.IndV.mk K.subtype (subgroupCoefficients n (expT t)).ρ 1) a)).val g' =
      Rep.indToCoindAux (subgroupCoefficients n (expT t)) 1 a g' := fun g' => by
    simp [Rep.indToCoind, Representation.IndV.mk]
    rfl
  show integralAction n (expT t) (representative r)⁻¹ (((subgroupCoefficients n (expT t)).indToCoind
        ((Representation.IndV.mk K.subtype (subgroupCoefficients n (expT t)).ρ 1) a)).val (representative r)) = _
  rw [h2]
  by_cases hr : r = distinguished
  · subst hr
    have hk : representative distinguished ∈ K := (representative_mem_K_iff _).mpr rfl
    unfold Rep.indToCoindAux
    rw [LinearMap.pi_apply, dite_eq_left]
    · rw [Pi.single_eq_same]
      change integralAction n (expT t) (representative distinguished)⁻¹
        (integralAction n (expT t) (representative distinguished * 1⁻¹) a) = a
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    · rw [QuotientGroup.rightRel_apply]
      simpa using K.inv_mem hk
  · rw [Pi.single_eq_of_ne hr, Rep.indToCoindAux_of_not_rel, map_zero]
    rw [QuotientGroup.rightRel_apply]
    intro h
    apply hr
    rw [← representative_mem_K_iff]
    simpa using K.inv_mem h

theorem indUnit_comp (n : ℕ) (t : Fin 2) :
    indUnit K (subgroupCoefficients n (expT t)) ≫
      (Rep.resFunctor K.subtype).map (inducedIso n (expT t)).hom = iotaK n t := rfl

/-- **Mathlib's Shapiro isomorphism is inverse to the corestriction of the identity-coset inclusion.** -/
theorem mathlibShapiro_inv (n : ℕ) (t : Fin 2) :
    (mathlibShapiro n t).inv = groupHomology.map K.subtype (iotaK n t) 3 := by
  have h1 : (mathlibShapiro n t).inv = (groupHomology.indIso K (subgroupCoefficients n (expT t)) 3).inv ≫
      groupHomology.map (MonoidHom.id IntegralGL) (inducedIso n (expT t)).hom 3 := rfl
  rw [h1, indIso_inv_eq_map]
  have h2 := groupHomology.map_comp (k := ℚ) (C := MG n t) K.subtype (MonoidHom.id IntegralGL)
    (indUnit K (subgroupCoefficients n (expT t)))
    (show Rep.ind K.subtype (subgroupCoefficients n (expT t)) ⟶ Rep.res (MonoidHom.id IntegralGL) (MG n t) from
      (inducedIso n (expT t)).hom) 3
  rw [← h2]
  exact groupHomology.map_congr (MonoidHom.id_comp _) rfl 3

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
