module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Comparison
public import TernaryPeriodPolynomials.Building.Reference.ApartmentRelations

@[expose] public section


/-!
# Lemma 3.3, G3: the arithmetic top evaluator is non-zero

`apartmentChain_ne_zero`: for good lines `L, M, N` pairwise distinct with `N` outside the plane of `L, M`, the
oriented apartment chain has coefficient `1` at the flag `(L, L ⊔ M)`, so it is non-zero.
`referenceApartment_ne_zero`, `identityApartment_ne_zero`: the coordinate frame gives a non-zero ordinary cycle
(`frameCycle 1 = cycleInclusion referenceApartment`, injectivity of `cycleInclusion`).
`groupApartmentEvaluation_ne_zero`: for the coefficient system `ordinaryCyclesRep` the identity functional is sent to
the non-zero identity apartment, so the evaluator is non-zero (`groupOrdinaryIso` is an isomorphism).
`scalar_ne_zero_of_bridge`: with this, the non-circular scalar argument needs only the bridge and the surjectivity
of `cellGroupHomologyMap ordinaryCyclesRep 3`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open TernaryPoly TernaryPoly.GoodIncidenceConnected TernaryPoly.GoodApartmentCycles

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

variable {Good : RationalSubspace → Prop}

/-- The coefficient of `apartmentChain L M N` at the flag `(L, L ⊔ M)` is `1` when the three lines are
pairwise distinct and `N` is not in the plane of `L, M`. -/
theorem apartmentChain_ne_zero (L M N : Line Good) (hLM : L ≠ M) (hLN : L ≠ N) (hMN : M ≠ N)
    (hN : ¬ N.val ≤ L.val ⊔ M.val) : apartmentChain Good L M N ≠ 0 := by
  intro h0
  have hNL : N ≠ L := fun h => hLN h.symm
  have hf := congrArg (fun c => c ⟨(L, spanPlane Good L M hLM), line_lt_plane Good (line_le_spanPlane_left Good L M hLM)⟩) h0
  simp only [apartmentChain, lineChain_of_ne Good L M hLM, lineChain_of_ne Good M N hMN,
    lineChain_of_ne Good N L hNL, flagChain, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at hf
  have n1 : M ≠ L := fun h => hLM h.symm
  have n3 : spanPlane Good N L hNL ≠ spanPlane Good L M hLM := by
    intro h
    apply hN
    have := congrArg Subtype.val h
    change N.val ⊔ L.val = L.val ⊔ M.val at this
    rw [← this]
    exact le_sup_left
  simp [Subtype.mk.injEq, Prod.mk.injEq, n1, hNL, n3] at hf


open TernaryPoly.GoodUnimodularOrbit TernaryPoly.GoodIntegralFrames TernaryPoly.ModThreeGoodAction in
theorem referenceApartment_ne_zero : referenceApartment ≠ 0 := by
  have key : ∀ j k l : Fin 3, j ≠ k → j ≠ l →
      ¬ (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized j).val ≤
        (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized k).val ⊔
          (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized l).val := by
    intro j k l hjk hjl h
    have hv : rationalVector (fun i => (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) ∈
        (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized j).val :=
      Submodule.subset_span (Set.mem_singleton _)
    have hm := h hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a', rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨b', rfl⟩ := Submodule.mem_span_singleton.mp hb
    have := congrFun hab j
    simp [rationalVector, Matrix.one_apply, hjk, hjl] at this
  intro h
  have h0 : apartmentChain ModThreeGoodAction.Good
      (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized 0)
      (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized 1)
      (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized 2) = 0 :=
    congrArg Subtype.val h
  have dist : ∀ j k : Fin 3, j ≠ k →
      columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized j ≠
        columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) identity_normalized k := by
    intro j k hjk heq
    apply key j k k hjk hjk
    rw [heq]
    exact le_sup_left
  exact apartmentChain_ne_zero _ _ _ (dist 0 1 (by decide)) (dist 0 2 (by decide)) (dist 1 2 (by decide))
    (key 2 0 1 (by decide) (by decide)) h0


open TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.IntegralGL3Congruence CategoryTheory in
/-- **The identity apartment is a non-zero ordinary cycle**, hence the arithmetic top evaluator
`groupApartmentEvaluation` is non-zero for the coefficient system `ordinaryCyclesRep` (take the identity
functional). -/
theorem identityApartment_ne_zero : (identityApartment : ordinaryCyclesRep) ≠ 0 := by
  intro h
  exact referenceApartment_ne_zero (OrdinaryIncidenceChains.cycleInclusion_injective
    (by rw [map_zero, ← TernaryPoly.OrdinaryFiberComparison.frameCycle_one]; exact h))

open TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.IntegralGL3Congruence CategoryTheory in
theorem groupApartmentEvaluation_ne_zero : groupApartmentEvaluation ordinaryCyclesRep ≠ 0 := by
  intro h
  have h1 : identityApartmentEvaluation ordinaryCyclesRep = 0 := by
    have : (groupOrdinaryIso ordinaryCyclesRep).hom ≫ identityApartmentEvaluation ordinaryCyclesRep = 0 := h
    exact (cancel_epi (groupOrdinaryIso ordinaryCyclesRep).hom).mp (by rw [this, Limits.comp_zero])
  have h2 := congrArg (fun f => f.hom (𝟙 ordinaryCyclesRep)) h1
  exact identityApartment_ne_zero h2


open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology in
/-- **The scalar argument with the evaluator non-vanishing discharged**: the bridge for some constant `κ` and the
surjectivity of `cellGroupHomologyMap` for the coefficient system `ordinaryCyclesRep` give `κ ≠ 0 ∧ dT0 ≠ 0`. -/
theorem scalar_ne_zero_of_bridge {κ : ℚ} (hB : FlatIntersectionBridge κ)
    (hsurj : Function.Surjective (cellGroupHomologyMap ordinaryCyclesRep 3).hom) :
    κ ≠ 0 ∧ LocalDegree.dT0 ≠ 0 :=
  dT0_ne_zero_of_bridge hB ordinaryCyclesRep hsurj groupApartmentEvaluation_ne_zero

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
