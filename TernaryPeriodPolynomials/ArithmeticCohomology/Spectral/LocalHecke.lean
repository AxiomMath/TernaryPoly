module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Hecke operators of a finite union of cosets on stabilizer cohomology

For a subgroup `Λ` of an ambient group `G` and a finite set `S ⊆ G` whose cosets `sΛ` are disjoint
and permuted by left multiplication by `Λ`, the formula
`c ↦ (x ↦ ∑_{s ∈ S} ρ(s) c(s⁻¹x))`
acts on the ambient homogeneous cochains of `Λ`, commutes with the differentials, and hence acts
on `H2 Λ ρ`. This generalizes the finite double-coset action of the definitions
(`heckeCochain`, `RealizesHecke`) from the arithmetic level to an arbitrary subgroup; it is used for
the parabolic stabilizers of rational flags.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Spectral.LocalHecke

variable {G : Type} [Group G]

/-- A finite set of representatives of a left-`Λ`-stable finite union of cosets `sΛ`. -/
structure LocalCorrespondence (level : Subgroup G) where
  representatives : Finset G
  stable : ∀ element ∈ level, ∀ s ∈ representatives,
    ∃ target ∈ representatives, target⁻¹ * (element * s) ∈ level
  disjoint : ∀ s ∈ representatives, ∀ s' ∈ representatives, s⁻¹ * s' ∈ level → s = s'

variable {level : Subgroup G}

theorem representative_exists (S : LocalCorrespondence level) (element : level)
    (s : S.representatives) :
    ∃ target ∈ S.representatives, target⁻¹ * (element.val⁻¹ * s.val) ∈ level :=
  S.stable _ (level.inv_mem element.property) s.val s.property

/-- Left multiplication by `element⁻¹` permutes the representatives. -/
def representativeMap (S : LocalCorrespondence level) (element : level)
    (s : S.representatives) : S.representatives :=
  ⟨(representative_exists S element s).choose, (representative_exists S element s).choose_spec.1⟩

theorem representativeMap_mem (S : LocalCorrespondence level) (element : level)
    (s : S.representatives) :
    (representativeMap S element s).val⁻¹ * (element.val⁻¹ * s.val) ∈ level :=
  (representative_exists S element s).choose_spec.2

theorem representativeMap_injective (S : LocalCorrespondence level) (element : level) :
    Function.Injective (representativeMap S element) := by
  intro first second heq
  apply Subtype.ext
  apply S.disjoint first.val first.property second.val second.property
  have hfirst := representativeMap_mem S element first
  have hsecond := representativeMap_mem S element second
  have hproduct := level.mul_mem (level.inv_mem hfirst) hsecond
  have hvalues := congrArg Subtype.val heq
  simpa only [hvalues, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel_left] using hproduct

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The cochain-level formula `∑_{s ∈ S} ρ(s) c(s⁻¹x)`. -/
def cochainSum (rho : Representation ℂ G V) (S : LocalCorrespondence level)
    (degree : ℕ) (cochain : cochains level rho degree)
    (vertices : Fin (degree + 1) → G) : V :=
  ∑ s ∈ S.representatives, rho s (cochain.val (fun index => s⁻¹ * vertices index))

theorem cochainSum_equivariant (rho : Representation ℂ G V)
    (S : LocalCorrespondence level) (degree : ℕ) (cochain : cochains level rho degree)
    (element : level) (vertices : Fin (degree + 1) → G) :
    cochainSum rho S degree cochain (fun index => element.val * vertices index) =
      rho element.val (cochainSum rho S degree cochain vertices) := by
  classical
  unfold cochainSum
  rw [map_sum]
  simp only [← Finset.sum_coe_sort S.representatives]
  apply Fintype.sum_bijective (representativeMap S element)
    ⟨representativeMap_injective S element,
      Finite.surjective_of_injective (representativeMap_injective S element)⟩ _ _
  intro s
  let target := representativeMap S element s
  let delta : level :=
    ⟨target.val⁻¹ * (element.val⁻¹ * s.val), representativeMap_mem S element s⟩
  have hvertices :
      (fun index => s.val⁻¹ * (element.val * vertices index)) =
        (fun index => delta.val⁻¹ * (target.val⁻¹ * vertices index)) := by
    funext index
    simp only [delta, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hequivariant := cochain.property delta⁻¹ (fun index => target.val⁻¹ * vertices index)
  simp only [Subgroup.coe_inv] at hequivariant
  rw [hvertices, hequivariant]
  change rho s.val (rho delta.val⁻¹
    (cochain.val (fun index => target.val⁻¹ * vertices index))) = _
  rw [← Module.End.mul_apply, ← map_mul]
  have hgroup : s.val * delta.val⁻¹ = element.val * target.val := by
    simp only [delta, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [hgroup, map_mul, Module.End.mul_apply]

/-- The local Hecke action on homogeneous cochains of `level`. -/
def cochainAction (rho : Representation ℂ G V) (S : LocalCorrespondence level)
    (degree : ℕ) : Module.End ℂ (cochains level rho degree) where
  toFun cochain := ⟨cochainSum rho S degree cochain, cochainSum_equivariant rho S degree cochain⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertices
    simp only [cochainSum, Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext vertices
    simp only [cochainSum, Submodule.coe_smul, Pi.smul_apply, map_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem cochainAction_apply (rho : Representation ℂ G V) (S : LocalCorrespondence level)
    (degree : ℕ) (cochain : cochains level rho degree) (vertices : Fin (degree + 1) → G) :
    (cochainAction rho S degree cochain).val vertices =
      ∑ s ∈ S.representatives, rho s (cochain.val (fun index => s⁻¹ * vertices index)) := rfl

theorem translate_pair (multiplier first second : G) :
    (fun index : Fin 2 => multiplier * ![first, second] index) =
      ![multiplier * first, multiplier * second] := by
  funext index
  fin_cases index <;> rfl

theorem translate_triple (multiplier first second third : G) :
    (fun index : Fin 3 => multiplier * ![first, second, third] index) =
      ![multiplier * first, multiplier * second, multiplier * third] := by
  funext index
  fin_cases index <;> rfl

theorem differentialOne_action (rho : Representation ℂ G V)
    (S : LocalCorrespondence level) (cochain : cochains level rho 1) :
    differentialOne level rho (cochainAction rho S 1 cochain) =
      cochainAction rho S 2 (differentialOne level rho cochain) := by
  apply Subtype.ext
  funext vertices
  change
    (∑ s ∈ S.representatives, rho s
      (cochain.val (fun index => s⁻¹ * ![vertices 1, vertices 2] index))) -
    (∑ s ∈ S.representatives, rho s
      (cochain.val (fun index => s⁻¹ * ![vertices 0, vertices 2] index))) +
    (∑ s ∈ S.representatives, rho s
      (cochain.val (fun index => s⁻¹ * ![vertices 0, vertices 1] index))) =
    ∑ s ∈ S.representatives, rho s
      (cochain.val ![s⁻¹ * vertices 1, s⁻¹ * vertices 2] -
       cochain.val ![s⁻¹ * vertices 0, s⁻¹ * vertices 2] +
       cochain.val ![s⁻¹ * vertices 0, s⁻¹ * vertices 1])
  simp only [translate_pair, map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem cochainAction_cocycle (rho : Representation ℂ G V)
    (S : LocalCorrespondence level) (cochain : cocycles level rho) :
    cochainAction rho S 2 cochain.val ∈ cocycles level rho := by
  funext vertices
  change
    (∑ s ∈ S.representatives, rho s
      (cochain.val.val (fun index => s⁻¹ * ![vertices 1, vertices 2, vertices 3] index))) -
    (∑ s ∈ S.representatives, rho s
      (cochain.val.val (fun index => s⁻¹ * ![vertices 0, vertices 2, vertices 3] index))) +
    (∑ s ∈ S.representatives, rho s
      (cochain.val.val (fun index => s⁻¹ * ![vertices 0, vertices 1, vertices 3] index))) -
    (∑ s ∈ S.representatives, rho s
      (cochain.val.val (fun index => s⁻¹ * ![vertices 0, vertices 1, vertices 2] index))) = 0
  simp only [translate_triple, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← map_sub, ← map_add]
  apply Finset.sum_eq_zero
  intro s _
  have hzero := congrFun cochain.property (fun index => s⁻¹ * vertices index)
  change rho s (differentialTwo level rho cochain.val (fun index => s⁻¹ * vertices index)) = 0
  rw [hzero, Pi.zero_apply, map_zero]

/-- The local Hecke action on cocycles. -/
def cocycleAction (rho : Representation ℂ G V) (S : LocalCorrespondence level) :
    Module.End ℂ (cocycles level rho) :=
  ((cochainAction rho S 2).comp (cocycles level rho).subtype).codRestrict _
    (cochainAction_cocycle rho S)

theorem cocycleAction_boundary (rho : Representation ℂ G V)
    (S : LocalCorrespondence level) (cochain : cochains level rho 1) :
    cocycleAction rho S (boundaryMap level rho cochain) =
      boundaryMap level rho (cochainAction rho S 1 cochain) := by
  apply Subtype.ext
  exact (differentialOne_action rho S cochain).symm

/-- The local Hecke operator on `H2 level rho`. -/
def cohomologyAction (rho : Representation ℂ G V) (S : LocalCorrespondence level) :
    Module.End ℂ (H2 level rho) :=
  (LinearMap.range (boundaryMap level rho)).mapQ
    (LinearMap.range (boundaryMap level rho)) (cocycleAction rho S) (by
      rintro cocycle ⟨cochain, rfl⟩
      exact ⟨cochainAction rho S 1 cochain, (cocycleAction_boundary rho S cochain).symm⟩)

theorem cohomologyAction_classOf (rho : Representation ℂ G V) (S : LocalCorrespondence level)
    (cocycle : cocycles level rho) :
    cohomologyAction rho S (classOf level rho cocycle) =
      classOf level rho (cocycleAction rho S cocycle) :=
  Submodule.mapQ_apply _ _ _ cocycle

end TernaryPeriodPolynomials.Spectral.LocalHecke
