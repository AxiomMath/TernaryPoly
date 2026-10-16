/-
  Concrete actual Hecke data: the identity double coset `Γ 1 Γ`.

  This module constructs a genuine `HeckeCorrespondence`, verifies the
  level-normaliser condition for its representative, and instantiates the
  (conditional) Hecke-stability of the associate pair on it.  It shows the
  `hnorm` hypothesis of `TernaryPeriodPolynomials.HeckeTranslate.HeckeStabilityAssembly` is satisfiable, so
  the reduction of the target to a Hecke-stable complement is not vacuous.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeStabilityAssembly
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TrivialCorrespondence

open TernaryPeriodPolynomials.HeckeTranslate

/-- The identity double coset `Γ 1 Γ`, a genuine `HeckeCorrespondence`. -/
def trivialCorrespondence : HeckeCorrespondence where
  g := 1
  representatives := {1}
  inDoubleCoset := by
    intro r hr
    have hr' : r ∈ ({1} : Finset RationalGL3) := hr
    rw [Finset.mem_singleton] at hr'
    subst hr'
    exact ⟨1, 1, by simp⟩
  complete := by
    intro a b
    refine ⟨1, Finset.mem_singleton_self 1, ?_⟩
    simpa using rationalLevel.mul_mem a.property b.property
  disjoint := by
    intro r hr t ht _
    have hr' : r ∈ ({1} : Finset RationalGL3) := hr
    have ht' : t ∈ ({1} : Finset RationalGL3) := ht
    rw [Finset.mem_singleton] at hr' ht'
    rw [hr', ht']

/-- The representative of the identity double coset normalises every congruence
level, so the level-normaliser condition holds for it. -/
theorem trivialCorrespondence_hnorm (k : finiteLevel) :
    ∀ r ∈ trivialCorrespondence.representatives,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel := by
  intro r hr
  have hr' : r ∈ ({1} : Finset RationalGL3) := hr
  rw [Finset.mem_singleton] at hr'
  subst hr'
  simpa only [map_one, inv_one, one_mul, mul_one] using k.property

/-- Hecke-stability of the associate pair for the identity double coset,
instantiating `TernaryPeriodPolynomials.HeckeTranslate.HeckeStabilityAssembly.associatePair_hecke_stable`. -/
theorem associatePair_stable_trivialCorrespondence {n : ℕ} {D : InducingData n}
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    ∀ y ∈ associatePair D, pairHecke D hecke trivialCorrespondence y ∈ associatePair D :=
  HeckeStabilityAssembly.associatePair_hecke_stable trivialCorrespondence hecke hhecke
    (fun r hr k => trivialCorrespondence_hnorm k r hr)

section IdentityAction

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The finite-coset Hecke cochain action of the identity double coset is the
identity. -/
theorem cochainAction_trivial (rho : Representation ℂ RationalGL3 V) (degree : ℕ)
    (c : cochains rationalLevel rho degree) :
    Helpers.cochainAction rho trivialCorrespondence degree c = c := by
  apply Subtype.ext
  funext vertices
  show Helpers.cochainSum rho trivialCorrespondence degree c vertices = c.val vertices
  rw [Helpers.cochainSum,
    show trivialCorrespondence.representatives = ({1} : Finset RationalGL3) from rfl,
    Finset.sum_singleton]
  simp

/-- The descended Hecke action of the identity double coset is the identity. -/
theorem cocycleAction_trivial (rho : Representation ℂ RationalGL3 V) :
    Helpers.cocycleAction rho trivialCorrespondence = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  show Helpers.cochainAction rho trivialCorrespondence 2 z.val = z.val
  exact cochainAction_trivial rho 2 z.val

/-- The Hecke action on cohomology of the identity double coset is the identity. -/
theorem cohomologyAction_trivial (rho : Representation ℂ RationalGL3 V) :
    Helpers.cohomologyAction rho trivialCorrespondence = LinearMap.id := by
  unfold Helpers.cohomologyAction
  simp only [cocycleAction_trivial rho, Submodule.mapQ_id]

end IdentityAction

/-- Every realised boundary Hecke action is the identity on the identity double
coset (by uniqueness of the finite-coset realisation). -/
theorem hecke_trivial {n : ℕ} {D : InducingData n} (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) :
    hecke side trivialCorrespondence = LinearMap.id := by
  rw [show hecke side = Helpers.cohomologyAction
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) from
      realizesHecke_unique _ _ _ (hhecke side) (Helpers.cohomologyAction_realizes _)]
  exact cohomologyAction_trivial _

/-- The diagonal product action of the identity double coset is the identity on
the boundary coordinates. -/
theorem pairHecke_trivial {n : ℕ} {D : InducingData n} (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    pairHecke D hecke trivialCorrespondence = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp only [pairHecke, LinearMap.prodMap_apply, hecke_trivial hecke hhecke .plane,
    hecke_trivial hecke hhecke .line, LinearMap.id_apply]

/-- The realised boundary Hecke action is uniquely determined by
`ActualBoundaryHecke`. -/
theorem hecke_unique {n : ℕ} {D : InducingData n} (hecke hecke' : BoundaryHecke n D.chi)
    (h : ActualBoundaryHecke n D.chi hecke) (h' : ActualBoundaryHecke n D.chi hecke') :
    hecke = hecke' := by
  funext side
  exact realizesHecke_unique _ _ _ (h side) (h' side)

/-- Consequently the diagonal product Hecke action `pairHecke` is determined by
`ActualBoundaryHecke` alone, so the target's `hecke` is not a free parameter. -/
theorem pairHecke_congr {n : ℕ} {D : InducingData n} (hecke hecke' : BoundaryHecke n D.chi)
    (h : ActualBoundaryHecke n D.chi hecke) (h' : ActualBoundaryHecke n D.chi hecke') :
    pairHecke D hecke = pairHecke D hecke' := by
  rw [hecke_unique hecke hecke' h h']

end TernaryPeriodPolynomials.HeckeTranslate.TrivialCorrespondence

end
