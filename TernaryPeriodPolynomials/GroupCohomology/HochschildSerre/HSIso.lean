module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.H2U2
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Assembly

@[expose] public section


/-!
# The action of `P/U` on `H₂(U, A)`: `H₂(ZP U A) ≅ res π D`

Formalized by Claude Sonnet 5.5.

Let `U ⊲ P`, `eU : ℤ² ≃* U`, and let `A : Rep ℚ P` be finite-dimensional with `U` acting trivially.

* `cAct_Psi`: the conjugation action `c_g = H₂(conj g, ρ_A g)` on `H₂(U, A)` corresponds, under `H₂(ℤ², A) ≅ H₂(U, A)`, to
  `H₂(μ_g, ρ_A g)` with `μ_g = eU⁻¹ ∘ conj g ∘ eU` (`muG`);
* `homology_action`: for any complex `Z` of representations and `r`, the action of `r` on `H_n(Z)` is the map induced on homology
  of the underlying vector-space complex by the chain map "act by `r`" (via Mathlib's `homologyMap_mapNatTrans` applied to the
  natural endomorphism `actNat r` of the forgetful functor);
* `gammaEquiv`: `A ≃ₗ H₂(ZP U A)`, `a ↦` class of the fundamental 2-cycle, and `gammaEquiv_equivariant`: `g ∈ P` acts on
  `H₂(ZP U A)` by `deltaG g · ρ_A(g)` where `deltaG g = ω(μ_g e₁, μ_g e₂)` is the determinant of the conjugation on `U ≅ ℤ²`
 (`conj_comparison`, and `H2U2.map_kappa0_gen`);
* `homologyIsoRes`: if `A ≅ D` as vector spaces compatibly with `deltaG · ρ_A` and `π : P/U → Γ`, then
  `H₂(ZP U A) ≅ res π D` in `Rep (P/U)`;
* `isZero_res_three`: `H₃(U, A) = 0` (the Koszul resolution of `ℤ²`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)
open TernaryPeriodPolynomials.Argument.GroupHomology

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (eU : U2 ≃* U) (A : Rep.{0} ℚ P)

/-- Conjugation by `g` transported to `U2`. -/
def muG (g : P) : U2 →* U2 :=
  (eU.symm.toMonoidHom).comp ((conjN U g).comp eU.toMonoidHom)

theorem eU_muG (g : P) (v : U2) : eU (muG U eU g v) = conjN U g (eU v) := by
  simp [muG]

variable {U} {A}

/-- `H₂(U2, A) ≅ H₂(U, A)` along `eU` (trivial action of `U` on `A`). -/
def PsiIso (hA : ∀ u : U, A.ρ u = 1) : groupHomology (TV A.V) 2 ≅ groupHomology (Rep.res U.subtype A) 2 :=
  groupHomology.mapIso eU (LinearEquiv.refl ℚ A.V) (fun g => by
    ext a
    change a = (A.ρ (eU g).1) a
    have : A.ρ (eU g).1 = 1 := hA (eU g)
    rw [this]; rfl) 2

theorem cAct_Psi (hA : ∀ u : U, A.ρ u = 1) (g : P) (x : groupHomology (TV A.V) 2) :
    groupHomology.map (conjN U g) (conjRep U A g) 2 ((PsiIso eU hA).hom.hom x) =
      (PsiIso eU hA).hom.hom
        (groupHomology.map (muG U eU g) (trivHomRes (muG U eU g) (A.ρ g)) 2 x) := by
  let φ0 : TV A.V ⟶ Rep.res eU.toMonoidHom (Rep.res U.subtype A) :=
    Rep.ofHom ⟨(LinearEquiv.refl ℚ A.V).toLinearMap, fun g => by
      ext a
      change a = (A.ρ (eU g).1) a
      have : A.ρ (eU g).1 = 1 := hA (eU g)
      rw [this]; rfl⟩
  have hL := groupHomology.map_comp eU.toMonoidHom (conjN U g) φ0 (conjRep U A g) 2
  have hR := groupHomology.map_comp (muG U eU g) eU.toMonoidHom
    (trivHomRes (muG U eU g) (A.ρ g)) φ0 2
  have hfg : (conjN U g).comp eU.toMonoidHom = eU.toMonoidHom.comp (muG U eU g) := by
    ext v
    exact congrArg Subtype.val (eU_muG U eU g v).symm
  have hc : groupHomology.map eU.toMonoidHom φ0 2 ≫ groupHomology.map (conjN U g) (conjRep U A g) 2 =
      groupHomology.map (muG U eU g) (trivHomRes (muG U eU g) (A.ρ g)) 2 ≫
        groupHomology.map eU.toMonoidHom φ0 2 :=
    hL.symm.trans ((groupHomology.map_congr hfg (by ext a; rfl) 2).trans hR)
  have := congrArg (fun φ => φ.hom x) hc
  exact this

section Action

variable {R : Type} [Group R]

/-- The action of `r ∈ R` as a natural endomorphism of the forgetful functor `Rep ℚ R ⥤ ModuleCat ℚ`. -/
def actNat (r : R) : forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ) ⟶ forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ) where
  app X := ModuleCat.ofHom (X.ρ r)
  naturality X Y f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (Rep.hom_comm_apply f r x).symm

/-- The action of `r` on the homology of a complex of representations, in terms of the chain map. -/
theorem homology_action (Z : ChainComplex (Rep.{0} ℚ R) ℕ) (n : ℕ) (r : R)
    (z : (forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ)).obj (Z.homology n)) :
    (Z.homology n).ρ r z =
      ((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ))).hom.hom
        ((ShortComplex.homologyMap ((Z.sc n).mapNatTrans (actNat r))).hom
          (((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ))).inv.hom z)) := by
  have h := ShortComplex.homologyMap_mapNatTrans (Z.sc n) (actNat r)
  have h2 : ((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ))).inv ≫
      ShortComplex.homologyMap ((Z.sc n).mapNatTrans (actNat r)) ≫
        ((Z.sc n).mapHomologyIso (forget₂ (Rep.{0} ℚ R) (ModuleCat ℚ))).hom =
      (actNat r).app (Z.sc n).homology := by
    rw [h]; simp
  have h3 := congrArg (fun φ => φ.hom z) h2
  simp only [ModuleCat.hom_comp] at h3
  exact h3.symm

end Action

section Iso


theorem actNat_GY (g : P) :
    ShortComplex.homologyMap ((ZP U A).sc 2 |>.mapNatTrans (actNat (QuotientGroup.mk (s := U) g))) =
      HomologicalComplex.homologyMap (GY U (YA A) g) 2 := rfl

variable [Module.Finite ℚ A.V]

/-- The explicit isomorphism `A ≅ H₂(ZP U A)` (class of the fundamental 2-cycle). -/
def gammaEquiv (hA : ∀ u : U, A.ρ u = 1) : A.V ≃ₗ[ℚ] ((ZP U A).homology 2).V :=
  (LinearEquiv.ofBijective (kappa0 A.V) ⟨kappa0_injective A.V, kappa0_surjective⟩).trans
    ((PsiIso eU hA).toLinearEquiv.trans
      ((eN U A 2).toLinearEquiv.trans
        (((ZP U A).sc 2).mapHomologyIso
          (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ))).toLinearEquiv))

theorem gammaEquiv_equivariant (hA : ∀ u : U, A.ρ u = 1) (g : P) (a : A.V) :
    ((ZP U A).homology 2).ρ (QuotientGroup.mk g) (gammaEquiv eU hA a) =
      (omegaZ (muG U eU g e1) (muG U eU g e2) : ℚ) • gammaEquiv eU hA (A.ρ g a) := by
  set Θ := ((ZP U A).sc 2).mapHomologyIso (forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)) with hΘ
  rw [homology_action]
  have hinv : Θ.inv.hom (gammaEquiv eU hA a) =
      (eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V a)) := by
    have := congrArg (fun φ => φ.hom ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom (kappa0 A.V a))))
      Θ.hom_inv_id
    exact this
  rw [hinv]
  rw [actNat_GY]
  have hconj := congrArg (fun φ => φ.hom ((PsiIso eU hA).hom.hom (kappa0 A.V a)))
    (conj_comparison U A g 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hconj
  refine (congrArg Θ.hom.hom hconj.symm).trans ?_
  rw [cAct_Psi eU hA g, map_kappa0_gen (muG U eU g) (A.ρ g) a]
  change Θ.hom.hom ((eN U A 2).hom.hom ((PsiIso eU hA).hom.hom
    ((omegaZ (muG U eU g e1) (muG U eU g e2) : ℚ) • kappa0 A.V (A.ρ g a)))) = _
  rw [map_smul, map_smul]
  erw [map_smul]
  rfl

/-- The factor by which `g` acts on the fundamental class of `H₂(U)`. -/
def deltaG (g : P) : ℚ := (omegaZ (muG U eU g e1) (muG U eU g e2) : ℚ)

/-- **`H₂(ZP U A) ≅ res π D` in `Rep (P/U)`**, given an identification `lin : A ≅ D` of the underlying spaces in which `g`
acts on `D` through `π` as `deltaG g · ρ_A(g)`. -/
def homologyIsoRes {Γ : Type} [Group Γ] (hA : ∀ u : U, A.ρ u = 1) (D : Rep.{0} ℚ Γ)
    (π : P ⧸ U →* Γ) (lin : A.V ≃ₗ[ℚ] D.V)
    (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) = D.ρ (π (QuotientGroup.mk g)) (lin a)) :
    (ZP U A).homology 2 ≅ Rep.res π D :=
  Rep.mkIso (σ := D.ρ.comp π) (ρ := ((ZP U A).homology 2).ρ)
    (Representation.Equiv.mk ((gammaEquiv eU hA).symm.trans lin) (fun q => by
      induction q using QuotientGroup.induction_on with
      | H g =>
        refine LinearMap.ext fun z => ?_
        obtain ⟨a, rfl⟩ := (gammaEquiv eU hA).surjective z
        change lin ((gammaEquiv eU hA).symm
            (((ZP U A).homology 2).ρ (QuotientGroup.mk g) (gammaEquiv eU hA a))) =
          D.ρ (π (QuotientGroup.mk g)) (lin ((gammaEquiv eU hA).symm (gammaEquiv eU hA a)))
        rw [gammaEquiv_equivariant eU hA g a, map_smul, LinearEquiv.symm_apply_apply,
          LinearEquiv.symm_apply_apply, ← hcompat g a]
        rfl))

/-- `H₃(U2, A) ≅ H₃(U, A)` along `eU`. -/
def PsiIso3 (hA : ∀ u : U, A.ρ u = 1) :
    groupHomology (TV A.V) 3 ≅ groupHomology (Rep.res U.subtype A) 3 :=
  groupHomology.mapIso eU (LinearEquiv.refl ℚ A.V) (fun g => by
    ext a
    change a = (A.ρ (eU g).1) a
    have : A.ρ (eU g).1 = 1 := hA (eU g)
    rw [this]; rfl) 3

omit [U.Normal] [Module.Finite ℚ A.V] in
theorem isZero_res_three (e : U2 ≃* U) (hA : ∀ u : U, A.ρ u = 1) :
    IsZero (groupHomology (Rep.res U.subtype A) 3) :=
  IsZero.of_iso (TernaryPeriodPolynomials.Argument.GroupHomologyDescent.isZero_groupHomology_U2
    (TV A.V) 0) (PsiIso3 e hA).symm

end Iso

end TernaryPeriodPolynomials.Argument.HochschildSerre
