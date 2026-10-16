module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Mackey
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModel

@[expose] public section


/-!
# The Hecke operator on `H₁` computed in the dual Farey resolution

Formalized by Claude Sonnet 5.5.  Lemma B.1, "The Hecke transfer".

Specialization of `heckeOp_resolution` (ResolutionModel.lean) to the two-term resolution `farResolution` of the
trivial `IntegralGL`-module by the dual Farey tree.  `H1Iso A : H₁(Γ, A) ≅ ker dC` (FareyEdge.lean) is the identification
of `H₁` with the kernel of `dC : (A ⊗ P₁)_Γ → (A ⊗ P₀)_Γ`.

* `H1Iso_spec`, `H1lift`, `homologyMap_H1lift`: `H1Iso` lifts a homology class to the cycle in `ker dC`, and every
  chain endomorphism `ψ` of `(A ⊗ P_•)_Γ` acts on `H₁` as `ψ₁` on these cycles.
* `ResHecke_comm_dC`, `ResHeckeKer`: the ambient operator `ResHecke D M farResolution lam` commutes with `dC`, hence its
  degree-one component restricts to an endomorphism of `ker dC`.
* `heckeOp_H1_incl`, `heckeOp_H1Iso`: for a lift `lam` over the identity of the correspondence to `farResolution` (with
  `Res_f` of the terms projective), `heckeOp D M 1 ≫ (H1Iso A).hom = (H1Iso A).hom ≫ ResHeckeKer D M lam`, equivalently
  `heckeOp D M 1 ≫ H1Iso.hom ≫ kerIncl = H1Iso.hom ≫ kerIncl ≫ (ResHecke D M farResolution lam).f 1`.
-/

open CategoryTheory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.FareyTree

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly.RankTwoAugmentedFrames

section Farey

open scoped Classical

variable (A : Rep.{0} ℚ IntegralGL)

/-- The inclusion of the kernel of `dC`. -/
def kerIncl : ModuleCat.of ℚ (LinearMap.ker (dC A).hom) ⟶
    farResolution.complex.coinvariantsTensorObj A |>.X 1 :=
  ModuleCat.ofHom (Submodule.subtype _)

theorem eqToHom_kerIncl {M N : ModuleCat.{0} ℚ} {f g : M ⟶ N} (h : f = g)
    (e : ModuleCat.of ℚ (LinearMap.ker f.hom) = ModuleCat.of ℚ (LinearMap.ker g.hom)) :
    eqToHom e ≫ ModuleCat.ofHom (Submodule.subtype (LinearMap.ker g.hom)) =
      ModuleCat.ofHom (Submodule.subtype (LinearMap.ker f.hom)) := by
  subst h
  simp

/-- The second map of the short complex of degrees `2 → 1 → 0` is `dC`. -/
theorem sc_g_eq :
    (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).g = dC A := by
  change ((Rep.coinvariantsTensor ℚ IntegralGL).obj A).map (farComplex.d 1 0) = _
  rw [show farComplex.d 1 0 = d1 from ChainComplex.of_d farX farD 0]
  rfl

theorem sc_f_eq_zero :
    (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).f = 0 := by
  change ((Rep.coinvariantsTensor ℚ IntegralGL).obj A).map (farComplex.d 2 1) = 0
  have : farComplex.d 2 1 = 0 := ChainComplex.of_d farX farD 1
  rw [this, Functor.map_zero]

/-- The homology class of degree one, lifted to a cycle: `homologyπ ≫ (gF.inv ≫ H1Iso.hom ≫ kerIncl) = iCycles`. -/
theorem H1Iso_spec :
    (farResolution.complex.coinvariantsTensorObj A).homologyπ 1 ≫ (groupHomologyFarey A 1).inv ≫
      (H1Iso A).hom ≫ kerIncl A = (farResolution.complex.coinvariantsTensorObj A).iCycles 1 := by
  have := ShortComplex.isIso_homologyπ
    (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0) (sc_f_eq_zero A)
  have e' : (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).moduleCatLeftHomologyData.K =
      ModuleCat.of ℚ (LinearMap.ker (dC A).hom) :=
    by
      change ModuleCat.of ℚ (LinearMap.ker (HomologicalComplex.sc'
        (farResolution.complex.coinvariantsTensorObj A) 2 1 0).g.hom) = _
      rw [sc_g_eq A]
      rfl
  have hH : (H1Iso A).hom = (groupHomologyFarey A 1).hom ≫
      (HomologicalComplex.homologyIsoSc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0 (by simp) (by simp)).hom ≫
      (asIso (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).homologyπ).inv ≫
      (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).moduleCatCyclesIso.hom ≫
      (eqToIso e').hom := rfl
  rw [hH]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
  simp only [asIso_inv, IsIso.hom_inv_id_assoc, eqToIso.hom]
  have hk := eqToHom_kerIncl (sc_g_eq A) e'
  have hi : (HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj A) 2 1 0).moduleCatLeftHomologyData.i =
      ModuleCat.ofHom (Submodule.subtype (LinearMap.ker (HomologicalComplex.sc'
        (farResolution.complex.coinvariantsTensorObj A) 2 1 0).g.hom)) := rfl
  have hk' : eqToHom e' ≫ kerIncl A = (HomologicalComplex.sc'
      (farResolution.complex.coinvariantsTensorObj A) 2 1 0).moduleCatLeftHomologyData.i := hk.trans hi.symm
  rw [hk']
  erw [ShortComplex.moduleCatCyclesIso_hom_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- The lift of a degree-one homology class to a cycle of the Farey complex of coinvariants. -/
def H1lift : (farResolution.complex.coinvariantsTensorObj A).homology 1 ⟶
    (farResolution.complex.coinvariantsTensorObj A).X 1 :=
  (groupHomologyFarey A 1).inv ≫ (H1Iso A).hom ≫ kerIncl A

theorem homologyπ_H1lift :
    (farResolution.complex.coinvariantsTensorObj A).homologyπ 1 ≫ H1lift A =
      (farResolution.complex.coinvariantsTensorObj A).iCycles 1 := H1Iso_spec A

/-- Every chain endomorphism of the Farey complex of coinvariants acts on `H₁` as its degree-one component
on the corresponding cycles. -/
theorem homologyMap_H1lift (ψ : farResolution.complex.coinvariantsTensorObj A ⟶
    farResolution.complex.coinvariantsTensorObj A) :
    HomologicalComplex.homologyMap ψ 1 ≫ H1lift A = H1lift A ≫ ψ.f 1 := by
  refine (cancel_epi ((farResolution.complex.coinvariantsTensorObj A).homologyπ 1)).1 ?_
  rw [HomologicalComplex.homologyπ_naturality_assoc, homologyπ_H1lift, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, homologyπ_H1lift]

section FareyHecke

variable {Ĝ : Type} [Group Ĝ] {ι : IntegralGL →* Ĝ} {g : Ĝ} (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ)
  (lam : LiftRes D farResolution)

theorem d_one_zero_eq : (farResolution.complex.coinvariantsTensorObj A).d 1 0 = dC A := sc_g_eq A

/-- The ambient operator commutes with the boundary `dC`. -/
theorem ResHecke_comm_dC :
    (ResHecke D M farResolution lam).f 1 ≫ dC (Rep.res ι M) =
      dC (Rep.res ι M) ≫ (ResHecke D M farResolution lam).f 0 := by
  have h := (ResHecke D M farResolution lam).comm 1 0
  rwa [d_one_zero_eq] at h

/-- The ambient operator in degree one preserves the kernel of `dC`. -/
def ResHeckeKer : ModuleCat.of ℚ (LinearMap.ker (dC (Rep.res ι M)).hom) ⟶
    ModuleCat.of ℚ (LinearMap.ker (dC (Rep.res ι M)).hom) :=
  ModuleCat.ofHom (LinearMap.restrict ((ResHecke D M farResolution lam).f 1).hom (fun z hz => by
    have h : (dC (Rep.res ι M)).hom (((ResHecke D M farResolution lam).f 1).hom z) =
        ((ResHecke D M farResolution lam).f 0).hom ((dC (Rep.res ι M)).hom z) :=
      congrArg (fun φ => φ.hom z) (ResHecke_comm_dC D M lam)
    have hz' : (dC (Rep.res ι M)).hom z = 0 := hz
    rw [hz'] at h
    exact h.trans (map_zero _)))

theorem heckeOp_H1_incl (hlam : LiftOverId D farResolution lam)
    (hproj : ∀ q, Projective ((Rep.resFunctor D.f).obj (farResolution.complex.X q))) :
    heckeOp D M 1 ≫ (H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M) =
      (H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M) ≫ (ResHecke D M farResolution lam).f 1 := by
  have hres := heckeOp_resolution D M farResolution lam hlam hproj 1
  have hF : ∀ i : DecidableEq IntegralGL, @groupHomologyIso ℚ IntegralGL _ _ i (Rep.res ι M) 1 farResolution =
      groupHomologyFarey (Rep.res ι M) 1 := fun i => by
    unfold groupHomologyFarey
    exact groupHomologyIso_inst_irrel _ _ _ _ _
  rw [hF] at hres
  have hθ : (H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M) =
      (groupHomologyFarey (Rep.res ι M) 1).hom ≫ H1lift (Rep.res ι M) := by
    unfold H1lift
    simp
  calc heckeOp D M 1 ≫ (H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M)
      = heckeOp D M 1 ≫ (groupHomologyFarey (Rep.res ι M) 1).hom ≫ H1lift (Rep.res ι M) := by rw [hθ]
    _ = (heckeOp D M 1 ≫ (groupHomologyFarey (Rep.res ι M) 1).hom) ≫ H1lift (Rep.res ι M) :=
        (Category.assoc _ _ _).symm
    _ = ((groupHomologyFarey (Rep.res ι M) 1).hom ≫
          HomologicalComplex.homologyMap (ResHecke D M farResolution lam) 1) ≫ H1lift (Rep.res ι M) := by
        rw [hres]
    _ = (groupHomologyFarey (Rep.res ι M) 1).hom ≫ H1lift (Rep.res ι M) ≫
          (ResHecke D M farResolution lam).f 1 := by
        rw [Category.assoc, homologyMap_H1lift]
    _ = ((H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M)) ≫ (ResHecke D M farResolution lam).f 1 := by
        rw [hθ, Category.assoc]
    _ = (H1Iso (Rep.res ι M)).hom ≫ kerIncl (Rep.res ι M) ≫ (ResHecke D M farResolution lam).f 1 :=
        Category.assoc _ _ _

instance : Mono (kerIncl A) := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)

theorem ResHeckeKer_incl :
    ResHeckeKer D M lam ≫ kerIncl (Rep.res ι M) =
      kerIncl (Rep.res ι M) ≫ (ResHecke D M farResolution lam).f 1 := rfl

/-- **Lemma B.1, Farey model.** Under `H1Iso`, the Hecke operator on `H₁(Γ, M)` is the restriction to
`ker dC` of the degree-one component of the ambient operator on `(M ⊗ P_•)_Γ`. -/
theorem heckeOp_H1Iso (hlam : LiftOverId D farResolution lam)
    (hproj : ∀ q, Projective ((Rep.resFunctor D.f).obj (farResolution.complex.X q))) :
    heckeOp D M 1 ≫ (H1Iso (Rep.res ι M)).hom = (H1Iso (Rep.res ι M)).hom ≫ ResHeckeKer D M lam := by
  refine (cancel_mono (kerIncl (Rep.res ι M))).1 ?_
  rw [Category.assoc, Category.assoc, ResHeckeKer_incl]
  exact heckeOp_H1_incl D M lam hlam hproj

end FareyHecke

end Farey
end TernaryPeriodPolynomials.Argument.HeckeHomology
