module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.Helpers

theorem representative_exists (t : HeckeCorrespondence) (gamma : rationalLevel)
    (representative : t.representatives) :
    ∃ target ∈ t.representatives,
      target⁻¹ * (gamma.val⁻¹ * representative.val) ∈ rationalLevel := by
  obtain ⟨left, right, heq⟩ := t.inDoubleCoset representative.val representative.property
  obtain ⟨target, htarget, hlevel⟩ := t.complete (gamma⁻¹ * left) right
  refine ⟨target, htarget, ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, heq, mul_assoc] using hlevel

def representativeMap (t : HeckeCorrespondence) (gamma : rationalLevel)
    (representative : t.representatives) : t.representatives :=
  ⟨(representative_exists t gamma representative).choose,
    (representative_exists t gamma representative).choose_spec.1⟩

theorem representativeMap_mem (t : HeckeCorrespondence) (gamma : rationalLevel)
    (representative : t.representatives) :
    (representativeMap t gamma representative).val⁻¹ *
      (gamma.val⁻¹ * representative.val) ∈ rationalLevel :=
  (representative_exists t gamma representative).choose_spec.2

theorem representativeMap_injective (t : HeckeCorrespondence) (gamma : rationalLevel) :
    Function.Injective (representativeMap t gamma) := by
  intro first second heq
  apply Subtype.ext
  apply t.disjoint first.val first.property second.val second.property
  have hfirst := representativeMap_mem t gamma first
  have hsecond := representativeMap_mem t gamma second
  have hproduct := rationalLevel.mul_mem (rationalLevel.inv_mem hfirst) hsecond
  have hvalues := congrArg Subtype.val heq
  simpa only [hvalues, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel_left] using hproduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def cochainSum (rho : Representation ℂ RationalGL3 V) (t : HeckeCorrespondence)
    (degree : ℕ) (cochain : cochains rationalLevel rho degree)
    (vertices : Fin (degree + 1) → RationalGL3) : V :=
  ∑ representative ∈ t.representatives,
    rho representative (cochain.val (fun index => representative⁻¹ * vertices index))

theorem cochainSum_equivariant (rho : Representation ℂ RationalGL3 V)
    (t : HeckeCorrespondence) (degree : ℕ) (cochain : cochains rationalLevel rho degree)
    (gamma : rationalLevel) (vertices : Fin (degree + 1) → RationalGL3) :
    cochainSum rho t degree cochain (fun index => gamma.val * vertices index) =
      rho gamma.val (cochainSum rho t degree cochain vertices) := by
  classical
  unfold cochainSum
  rw [map_sum]
  simp only [← Finset.sum_coe_sort t.representatives]
  apply Fintype.sum_bijective (representativeMap t gamma)
    ⟨representativeMap_injective t gamma,
      Finite.surjective_of_injective (representativeMap_injective t gamma)⟩ _ _
  intro representative
  let target := representativeMap t gamma representative
  let delta : rationalLevel :=
    ⟨target.val⁻¹ * (gamma.val⁻¹ * representative.val),
      representativeMap_mem t gamma representative⟩
  have hvertices :
      (fun index => representative.val⁻¹ * (gamma.val * vertices index)) =
        (fun index => delta.val⁻¹ * (target.val⁻¹ * vertices index)) := by
    funext index
    simp only [delta, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hequivariant := cochain.property delta⁻¹
    (fun index => target.val⁻¹ * vertices index)
  simp only [Subgroup.coe_inv] at hequivariant
  rw [hvertices, hequivariant]
  change rho representative.val (rho delta.val⁻¹
    (cochain.val (fun index => target.val⁻¹ * vertices index))) = _
  rw [← Module.End.mul_apply, ← map_mul]
  have hgroup : representative.val * delta.val⁻¹ = gamma.val * target.val := by
    simp only [delta, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [hgroup, map_mul, Module.End.mul_apply]

def cochainAction (rho : Representation ℂ RationalGL3 V) (t : HeckeCorrespondence)
    (degree : ℕ) : Module.End ℂ (cochains rationalLevel rho degree) where
  toFun cochain := ⟨cochainSum rho t degree cochain,
    cochainSum_equivariant rho t degree cochain⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices
    simp only [cochainSum, Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext vertices
    simp only [cochainSum, Submodule.coe_smul, Pi.smul_apply, map_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem translate_pair (multiplier first second : RationalGL3) :
    (fun index : Fin 2 => multiplier * ![first, second] index) =
      ![multiplier * first, multiplier * second] := by
  funext index
  fin_cases index <;> rfl

theorem translate_triple (multiplier first second third : RationalGL3) :
    (fun index : Fin 3 => multiplier * ![first, second, third] index) =
      ![multiplier * first, multiplier * second, multiplier * third] := by
  funext index
  fin_cases index <;> rfl

theorem differentialOne_action (rho : Representation ℂ RationalGL3 V)
    (t : HeckeCorrespondence) (cochain : cochains rationalLevel rho 1) :
    differentialOne rationalLevel rho (cochainAction rho t 1 cochain) =
      cochainAction rho t 2 (differentialOne rationalLevel rho cochain) := by
  apply Subtype.ext
  funext vertices
  change
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val (fun index => representative⁻¹ * ![vertices 1, vertices 2] index))) -
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val (fun index => representative⁻¹ * ![vertices 0, vertices 2] index))) +
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val (fun index => representative⁻¹ * ![vertices 0, vertices 1] index))) =
    ∑ representative ∈ t.representatives, rho representative
      (cochain.val ![representative⁻¹ * vertices 1, representative⁻¹ * vertices 2] -
       cochain.val ![representative⁻¹ * vertices 0, representative⁻¹ * vertices 2] +
       cochain.val ![representative⁻¹ * vertices 0, representative⁻¹ * vertices 1])
  simp only [translate_pair, map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem cochainAction_cocycle (rho : Representation ℂ RationalGL3 V)
    (t : HeckeCorrespondence) (cochain : cocycles rationalLevel rho) :
    cochainAction rho t 2 cochain.val ∈ cocycles rationalLevel rho := by
  funext vertices
  change
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val.val (fun index => representative⁻¹ *
        ![vertices 1, vertices 2, vertices 3] index))) -
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val.val (fun index => representative⁻¹ *
        ![vertices 0, vertices 2, vertices 3] index))) +
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val.val (fun index => representative⁻¹ *
        ![vertices 0, vertices 1, vertices 3] index))) -
    (∑ representative ∈ t.representatives, rho representative
      (cochain.val.val (fun index => representative⁻¹ *
        ![vertices 0, vertices 1, vertices 2] index))) = 0
  simp only [translate_triple, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← map_sub, ← map_add]
  apply Finset.sum_eq_zero
  intro representative _
  have hzero := congrFun cochain.property
    (fun index => representative⁻¹ * vertices index)
  change rho representative
    (differentialTwo rationalLevel rho cochain.val
      (fun index => representative⁻¹ * vertices index)) = 0
  rw [hzero, Pi.zero_apply, map_zero]

def cocycleAction (rho : Representation ℂ RationalGL3 V) (t : HeckeCorrespondence) :
    Module.End ℂ (cocycles rationalLevel rho) :=
  ((cochainAction rho t 2).comp (cocycles rationalLevel rho).subtype).codRestrict _
    (cochainAction_cocycle rho t)

theorem cocycleAction_boundary (rho : Representation ℂ RationalGL3 V)
    (t : HeckeCorrespondence) (cochain : cochains rationalLevel rho 1) :
    cocycleAction rho t (boundaryMap rationalLevel rho cochain) =
      boundaryMap rationalLevel rho (cochainAction rho t 1 cochain) := by
  apply Subtype.ext
  exact (differentialOne_action rho t cochain).symm

def cohomologyAction (rho : Representation ℂ RationalGL3 V) (t : HeckeCorrespondence) :
    Module.End ℂ (H2 rationalLevel rho) :=
  (LinearMap.range (boundaryMap rationalLevel rho)).mapQ
    (LinearMap.range (boundaryMap rationalLevel rho)) (cocycleAction rho t) (by
      rintro cocycle ⟨cochain, rfl⟩
      exact ⟨cochainAction rho t 1 cochain, (cocycleAction_boundary rho t cochain).symm⟩)

theorem cohomologyAction_realizes (rho : Representation ℂ RationalGL3 V) :
    RealizesHecke rho (cohomologyAction rho) := by
  intro correspondence cocycle
  refine ⟨cocycleAction rho correspondence cocycle, ?_, ?_⟩
  · intro vertices
    rfl
  · exact Submodule.mapQ_apply _ _ _ cocycle

end TernaryPeriodPolynomials.HeckeTranslate.Helpers
