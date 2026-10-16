module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent

@[expose] public section


/-!
# Shapiro's isomorphism is inverse to the map induced by the unit

For a subgroup `S ≤ G` and `A : Rep k S`, Mathlib's `groupHomology.indIso S A n : H_n(G, Ind_S^G A) ≅ H_n(S, A)`
has inverse `groupHomology.map S.subtype η n`, where `η : A ⟶ Res_S Ind_S^G A` is the unit of the
induction-restriction adjunction (`indIso_inv_eq_map`).  The proof compares both with Mathlib's description of
`groupHomologyIso` through resolutions (`groupHomologyIso_bar_hom`, `groupHomologyIso_hom_comp`) on generators of the
inhomogeneous chains.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory Finsupp Rep

section

variable {k G : Type u} [Field k] [Group G] [DecidableEq G] (S : Subgroup G) (A : Rep.{u} k S)

/-- The unit `A ⟶ Res_S Ind_S^G A`. -/
abbrev indUnit : A ⟶ Rep.res S.subtype (Rep.ind S.subtype A) :=
  (Rep.indResAdjunction.{u, u, u} k S.subtype).unit.app A


/-- The chain map `C_G(Ind A) ⟶ (Res bar(G) ⊗ A)_S` underlying Shapiro's isomorphism. -/
def indChainMap :
    groupHomology.inhomogeneousChains (Rep.ind S.subtype A) ⟶
      (((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).complex).coinvariantsTensorObj A :=
  (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom ≫
    (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm.hom

omit [DecidableEq G] in
theorem symm_f_mk (n : ℕ) (a : A) (y : (barComplex k G).X n) :
    (((groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm.hom.f n).hom
      (Representation.Coinvariants.mk ((Rep.ind S.subtype A).ρ.tprod ((barComplex k G).X n).ρ)
        (Representation.IndV.mk S.subtype A.ρ 1 a ⊗ₜ[k] y))) =
      Representation.Coinvariants.mk (A.ρ.tprod (Rep.res S.subtype ((barComplex k G).X n)).ρ) (a ⊗ₜ[k] y) := by
  have h := coinvariantsTensorIndHom_mk_tmul_indVMk (k := k) S.subtype (A := A) (B := (barComplex k G).X n) 1 a y
  have e : ((groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm.hom.f n) =
      coinvariantsTensorIndHom S.subtype A ((barComplex k G).X n) := rfl
  rw [e]
  refine h.trans ?_
  rw [map_one]
  rfl

theorem chains_unit_apply (n : ℕ) (x : Fin n → S) (a : A) :
    ((groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (barResolution k G)).symm.hom.f n).hom
      (((groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom.f n).hom
        (((groupHomology.chainsMap S.subtype (indUnit S A)).f n).hom (single x a))) =
    (HomologicalComplex.Hom.f
      ((((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (barMap (k := k) S.subtype)) n).hom
      (((groupHomology.inhomogeneousChainsIso A).hom.f n).hom (single x a)) := by
  have eL : ((groupHomology.chainsMap S.subtype (indUnit S A)).f n).hom (single x a) =
      single (S.subtype ∘ x) ((indUnit S A).hom a) := by
    have := groupHomology.chainsMap_f_single S.subtype (indUnit S A) n x a
    simpa using this
  rw [eL]
  have e1 := inhomIso_hom_f_single (Rep.ind S.subtype A) n (S.subtype ∘ x) ((indUnit S A).hom a)
  have e5 := inhomIso_hom_f_single A n x a
  have e2 := coinvTensor_map_mk A ((barMap (k := k) S.subtype).f n) a
    (single x (MonoidAlgebra.single (1 : S) (1 : k)))
  have e3 : ((barMap (k := k) S.subtype).f n).hom (single x (MonoidAlgebra.single (1 : S) (1 : k))) =
      single (S.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : k)) := by
    change (barTerm (k := k) S.subtype n).hom _ = _
    rw [barTerm_single, map_one]
  rw [e1, e5]
  erw [symm_f_mk S A n a (single (S.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : k)))]
  erw [e2, e3]
  rfl

theorem chains_unit_comm :
    groupHomology.chainsMap S.subtype (indUnit S A) ≫ indChainMap S A =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (barMap (k := k) S.subtype) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  exact chains_unit_apply S A n x a

/-- **Shapiro's isomorphism is inverse to the map induced by the unit.** -/
theorem indIso_inv_eq_map (n : ℕ) :
    (groupHomology.indIso S A n).inv = groupHomology.map S.subtype (indUnit S A) n := by
  have h1 := groupHomologyIso_hom_comp (k := k) (G := S) A n (P := barResolution k S)
    (Q := (resFunctor S.subtype).mapProjectiveResolution (barResolution k G)) (barMap S.subtype)
    (barMap_pi (k := k) S)
  rw [groupHomologyIso_bar_hom] at h1
  have h2 : HomologicalComplex.homologyMap (groupHomology.chainsMap S.subtype (indUnit S A)) n ≫
      HomologicalComplex.homologyMap (indChainMap S A) n =
      HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      HomologicalComplex.homologyMap
        ((((coinvariantsTensor k ↥S).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (barMap S.subtype)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chains_unit_comm S A)
  have hhom : (groupHomology.indIso S A n).hom = HomologicalComplex.homologyMap (indChainMap S A) n ≫
        (groupHomologyIso A n ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G))).inv := by
    rfl
  have h3 : groupHomology.map S.subtype (indUnit S A) n ≫ HomologicalComplex.homologyMap (indChainMap S A) n =
      (groupHomologyIso A n ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G))).hom :=
    h2.trans h1
  have key : groupHomology.map S.subtype (indUnit S A) n ≫ (groupHomology.indIso S A n).hom = 𝟙 _ := by
    refine (congrArg (fun m => groupHomology.map S.subtype (indUnit S A) n ≫ m) hhom).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ (groupHomologyIso A n
      ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G))).inv) h3).trans ?_
    exact Iso.hom_inv_id _
  calc (groupHomology.indIso S A n).inv
      = 𝟙 _ ≫ (groupHomology.indIso S A n).inv := (Category.id_comp _).symm
    _ = (groupHomology.map S.subtype (indUnit S A) n ≫ (groupHomology.indIso S A n).hom) ≫
          (groupHomology.indIso S A n).inv := by rw [key]
    _ = groupHomology.map S.subtype (indUnit S A) n := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end TernaryPeriodPolynomials.Argument.GroupHomology
