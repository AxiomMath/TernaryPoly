module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ZetaMap
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ZetaCount
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HeckeNat
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Functorial

@[expose] public section


/-!
# The `P`-level resolution operator is the Hecke-type operator `hmuC` of the quotient correspondence

Formalized by Claude Sonnet 5.5.

`resCorr_hmuC`: under the isomorphism `ZIso : (ZP U A ⊗ 1)_{P/U} ≅ (A ⊗ bar P)_P`, the resolution operator `ResCorr` of the
correspondence `(S, f, c)` with lift `lam` is the Hecke-type endomorphism `hmuC Γ₀ χ Z ζ` of the `P/U`-coinvariant complex
(`HochschildSerre.hmuC`), for the quotient correspondence `(Γ₀, χ, ζ)` of `ZetaMap.lean`.  The proof is the splitting
`S\P ≅ (Γ₀\(P/U)) × ((S ∩ U)\U)` of the coset sum (`ZetaCount.lean`).  Consequently the homology operator of `(S, f, c)` on
`H₃(P, A)` corresponds to `H₃(hmuC …)` on `H₃((Z ⊗ 1)_{P/U})` (`groupHomologyZIso_corr`).
-/

open CategoryTheory MonoidalCategory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.HochschildSerre TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section Ambient

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex] (f : S →* P)
  (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U) (A : Rep.{0} ℚ P) (c : Rep.res S.subtype A ⟶ Rep.res f A)
  (lam : LiftG (Rep.barResolution ℚ P) S f)

/-- The class map into the `P/U`-coinvariants of `Z_j ⊗ 1`. -/
abbrev mkQ (j : ℕ) :=
  Coinvariants.mk (((ZP U A).X j).ρ.tprod (Rep.trivial ℚ (P ⧸ U) ℚ).ρ)

/-- The summand function of the coset sum. -/
def phiS (j : ℕ) (a : A) (r : (Rep.barComplex ℚ P).X j) (w : P) :
    Coinvariants (((ZP U A).X j).ρ.tprod (Rep.trivial ℚ (P ⧸ U) ℚ).ρ) :=
  mkQ U A j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
    (cLin S f A c (A.ρ w a) ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ w r)) ⊗ₜ[ℚ] (1 : ℚ))

omit [S.FiniteIndex] in
theorem phiS_invariant (j : ℕ) (a : A) (r : (Rep.barComplex ℚ P).X j) (s : S) (w : P) :
    phiS U S f A c lam j a r (s * w) = phiS U S f A c lam j a r w := by
  have e1 : cLin S f A c (A.ρ ((s : P) * w) a) = A.ρ (f s) (cLin S f A c (A.ρ w a)) := by
    rw [map_mul]
    exact cLin_equiv S f A c s _
  have e2 : lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ ((s : P) * w) r) =
      ((Rep.barComplex ℚ P).X j).ρ (f s) (lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ w r)) := by
    rw [map_mul]
    exact lamLin_equiv S f lam j s _
  unfold phiS
  change mkQ U A j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (cLin S f A c (A.ρ ((s : P) * w) a) ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ ((s : P) * w) r)) ⊗ₜ[ℚ] (1 : ℚ)) = _
  rw [e1, e2]
  have e3 : Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (A.ρ (f s) (cLin S f A c (A.ρ w a)) ⊗ₜ[ℚ]
        ((Rep.barComplex ℚ P).X j).ρ (f s) (lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ w r))) =
      ((ZP U A).X j).ρ (QuotientGroup.mk (f s)) (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ w a) ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ w r))) := rfl
  rw [e3]
  exact Coinvariants.mk_self_apply (((ZP U A).X j).ρ.tprod (Rep.trivial ℚ (P ⧸ U) ℚ).ρ) (QuotientGroup.mk (f s))
    (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (cLin S f A c (A.ρ w a) ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ w r)) ⊗ₜ[ℚ] (1 : ℚ))

theorem resCorr_hmuC :
    ResCorr A (Rep.barResolution ℚ P) S f c lam ≫ (ZIso U A).inv =
      (ZIso U A).inv ≫ hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c lam)
        (lamTriv (G0 U S) (chi U S f hfU)) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (TensorProduct.ext' fun a (r : (Rep.barComplex ℚ P).X j) => ?_))
  change ((ZIso U A).inv.f j).hom (((ResCorr A (Rep.barResolution ℚ P) S f c lam).f j).hom
      (Coinvariants.mk ((YA A).X j).ρ (a ⊗ₜ[ℚ] r))) =
    ((hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c lam)
        (lamTriv (G0 U S) (chi U S f hfU))).f j).hom
      (((ZIso U A).inv.f j).hom (Coinvariants.mk ((YA A).X j).ρ (a ⊗ₜ[ℚ] r)))
  -- left side: the resolution operator is the sum over `S\P`
  have hL : ((ZIso U A).inv.f j).hom (((ResCorr A (Rep.barResolution ℚ P) S f c lam).f j).hom
      (Coinvariants.mk ((YA A).X j).ρ (a ⊗ₜ[ℚ] r))) = ∑ x : RC S, phiS U S f A c lam j a r x.out := by
    refine (congrArg ((ZIso U A).inv.f j).hom (ResCorr_f_mk A (Rep.barResolution ℚ P) S f c lam j a r)).trans ?_
    refine (map_sum _ _ _).trans ?_
    exact Finset.sum_congr rfl fun x _ => ZIso_inv_mk (U := U) A j _
  -- right side: the Hecke-type operator of the quotient correspondence
  have hR1 := hmuC_f_mk (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c lam)
    (lamTriv (G0 U S) (chi U S f hfU)) j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r)) (1 : ℚ)
  have hR : ((hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c lam)
        (lamTriv (G0 U S) (chi U S f hfU))).f j).hom
      (((ZIso U A).inv.f j).hom (Coinvariants.mk ((YA A).X j).ρ (a ⊗ₜ[ℚ] r))) =
      ∑ γ : RC (G0 U S), ∑ i : RC (U1 U S), phiS U S f A c lam j a r (((i.out : U) : P) * tRep U S γ) := by
    refine (congrArg _ (ZIso_inv_mk (U := U) A j (a ⊗ₜ[ℚ] r))).trans (hR1.trans ?_)
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hg : (γ.out : P ⧸ U) = QuotientGroup.mk (tRep U S γ) := (mk_tRep U S γ).symm
    have hz := zetaLin_mk U S f hfU A c lam j (A.ρ (tRep U S γ) a)
      (((Rep.barComplex ℚ P).X j).ρ (tRep U S γ) r)
    change mkQ U A j ((zetaLin U S f hfU A c lam j (((ZP U A).X j).ρ γ.out
      (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r)))) ⊗ₜ[ℚ] (1 : ℚ)) = _
    rw [hg]
    change mkQ U A j ((zetaLin U S f hfU A c lam j (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (A.ρ (tRep U S γ) a ⊗ₜ[ℚ] ((Rep.barComplex ℚ P).X j).ρ (tRep U S γ) r))) ⊗ₜ[ℚ] (1 : ℚ)) = _
    rw [hz]
    erw [TensorProduct.sum_tmul]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold phiS
    simp only [map_mul, Module.End.mul_apply]
  rw [hL, hR]
  exact sum_rc_split U S (phiS U S f A c lam j a r) (phiS_invariant U S f A c lam j a r)

/-- A lift of an injective correspondence to the bar resolution (by projectivity). -/
def liftBar (hf : Function.Injective f) : LiftG (Rep.barResolution ℚ P) S f :=
  ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ S ℚ))
    (resfResolution S.subtype (Rep.barResolution ℚ P) (fun q => projective_res_bar S.subtype Subtype.val_injective q))
    (resfResolution f (Rep.barResolution ℚ P) (fun q => projective_res_bar f hf q))

omit [S.FiniteIndex] in
theorem liftBar_overId (hf : Function.Injective f) : LiftGOverId (Rep.barResolution ℚ P) S f (liftBar S f hf) := by
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial ℚ S ℚ))
    (resfResolution S.subtype (Rep.barResolution ℚ P) (fun q => projective_res_bar S.subtype Subtype.val_injective q))
    (resfResolution f (Rep.barResolution ℚ P) (fun q => projective_res_bar f hf q))
  exact h.trans (Category.comp_id _)

/-- **The homology operator of a correspondence on `H_n(P, A)` is `H_n(hmuC …)` on `H_n((Z ⊗ 1)_{P/U})`.** -/
theorem corr_ZIso_hmuC (hf : Function.Injective f) (n : ℕ) :
    (trR S A n ≫ groupHomology.map f c n) ≫ (groupHomologyZIso U A n).hom =
      (groupHomologyZIso U A n).hom ≫ HomologicalComplex.homologyMap
        (hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c (liftBar S f hf))
          (lamTriv (G0 U S) (chi U S f hfU))) n := by
  have h1 := corr_resolution A (Rep.barResolution ℚ P) S f c (liftBar S f hf) (liftBar_overId S f hf)
    (fun q => projective_res_bar f hf q) n
  have h2 := congrArg (fun m => HomologicalComplex.homologyMap m n)
    (resCorr_hmuC U S f hfU A c (liftBar S f hf))
  have h2' : HomologicalComplex.homologyMap (ResCorr A (Rep.barResolution ℚ P) S f c (liftBar S f hf)) n ≫
      HomologicalComplex.homologyMap (ZIso U A).inv n =
      HomologicalComplex.homologyMap (ZIso U A).inv n ≫ HomologicalComplex.homologyMap
        (hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c (liftBar S f hf))
          (lamTriv (G0 U S) (chi U S f hfU))) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans (h2.trans (HomologicalComplex.homologyMap_comp _ _ n))
  have h3 : (groupHomologyZIso U A n).hom = (eK A n).hom ≫ HomologicalComplex.homologyMap (ZIso U A).inv n := rfl
  calc (trR S A n ≫ groupHomology.map f c n) ≫ (groupHomologyZIso U A n).hom
      = ((trR S A n ≫ groupHomology.map f c n) ≫ (eK A n).hom) ≫ HomologicalComplex.homologyMap (ZIso U A).inv n := by
        rw [h3]; simp only [Category.assoc]
    _ = ((eK A n).hom ≫ HomologicalComplex.homologyMap (ResCorr A (Rep.barResolution ℚ P) S f c (liftBar S f hf)) n) ≫
          HomologicalComplex.homologyMap (ZIso U A).inv n := congrArg (fun w => w ≫ HomologicalComplex.homologyMap (ZIso U A).inv n) h1.symm
    _ = (eK A n).hom ≫ HomologicalComplex.homologyMap (ResCorr A (Rep.barResolution ℚ P) S f c (liftBar S f hf)) n ≫
          HomologicalComplex.homologyMap (ZIso U A).inv n := Category.assoc _ _ _
    _ = (eK A n).hom ≫ HomologicalComplex.homologyMap (ZIso U A).inv n ≫ HomologicalComplex.homologyMap
        (hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c (liftBar S f hf))
          (lamTriv (G0 U S) (chi U S f hfU))) n := congrArg (fun w => (eK A n).hom ≫ w) h2'
    _ = (groupHomologyZIso U A n).hom ≫ HomologicalComplex.homologyMap
        (hmuC (G0 U S) (chi U S f hfU) (ZP U A) (zetaC U S f hfU A c (liftBar S f hf))
          (lamTriv (G0 U S) (chi U S f hfU))) n := by
        rw [h3]; simp only [Category.assoc]

end Ambient

end TernaryPeriodPolynomials.Argument.HeckeHomology
