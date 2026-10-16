module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.ResolutionZ

@[expose] public section


/-!
# Conjugation, corestriction and averaging for an arbitrary projective resolution

Formalized by Claude Sonnet 5.5.

For a projective resolution `R` of the trivial `K`-module and a normal subgroup `N`, `eNR`, `eKR` are the isomorphisms of
group homology with the homology of the `N`- resp. `K`-coinvariants of `A ⊗ R`.  Through the comparison
`fY : A ⊗ bar → A ⊗ R` they are transported from the bar-resolution statements of `NormalDescent` (`eNR_hom`,
`eKR_hom`), and the actions `GY`, the quotient `QY` are natural in the resolution (`CxNf_GY`, `CxNf_QY`).  Results:
`eNR_cAct` (conjugation is `GY`), `eKR_corN` (corestriction is `QY`), `avgY` the chain-level average over `K/N`
(`avgY_homology`, `avgY_QY`), and `eNR_avgN` (averaging is `avgH`, equivalently the homology of `avgY`).
-/

open CategoryTheory Representation Limits
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open TernaryPeriodPolynomials.Argument.HochschildSerre

variable {K : Type} [Group K] (N : Subgroup K) [N.Normal]
  (R : ProjectiveResolution (Rep.trivial ℚ K ℚ)) (A : Rep.{0} ℚ K)

/-- `Hₙ(N, Res A) ≅ Hₙ((Res R ⊗ Res A)_N)` through the restricted resolution. -/
abbrev eNR (n : ℕ) : groupHomology (Rep.res N.subtype A) n ≅ (CxN N (YAR R A)).homology n :=
  groupHomologyIso (Rep.res N.subtype A) n ((Rep.resFunctor N.subtype).mapProjectiveResolution R)

/-- `Hₙ(K, A) ≅ Hₙ((R ⊗ A)_K)`. -/
abbrev eKR (n : ℕ) : groupHomology A n ≅ (CxK (YAR R A)).homology n := groupHomologyIso A n R

/-- The chain map `(Res fY)_N : CxN (YA A) ⟶ CxN (YAR R A)`. -/
def CxNf : CxN N (YA A) ⟶ CxN N (YAR R A) :=
  ((cN (k := ℚ) N).mapHomologicalComplex _).map (fY R A)

omit [N.Normal] in
theorem mapRes_comm :
    (((Rep.resFunctor.{0} (k := ℚ) N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map (fR R)).f 0 ≫
      ((Rep.resFunctor N.subtype).mapProjectiveResolution R).π.f 0 =
    ((Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ K)).π.f 0 := by
  have h := congrArg (fun t => t.f 0) (fR_comm R)
  simp only [HomologicalComplex.comp_f] at h
  rw [(ChainComplex.single₀ _).map_id, HomologicalComplex.id_f, Category.comp_id] at h
  have e0 : ∀ (S : ProjectiveResolution (Rep.trivial ℚ K ℚ)),
      ((Rep.resFunctor N.subtype).mapProjectiveResolution S).π.f 0 = (Rep.resFunctor.{0} N.subtype).map (S.π.f 0) := by
    intro S
    simp
    exact (congrArg (fun m => (Rep.resFunctor.{0} N.subtype).map (S.π.f 0) ≫ m)
        ((Rep.resFunctor.{0} N.subtype).map_id (Rep.trivial ℚ K ℚ))).trans (Category.comp_id _)
  rw [e0, e0]
  exact ((Rep.resFunctor.{0} N.subtype).map_comp ((fR R).f 0) (R.π.f 0)).symm.trans
    (congrArg (fun m => (Rep.resFunctor.{0} N.subtype).map m) h)

omit [N.Normal] in
theorem eNR_hom (n : ℕ) :
    (eNR N R A n).hom = (eN N A n).hom ≫ HomologicalComplex.homologyMap (CxNf N R A) n := by
  have h := groupHomologyIso_hom_comp (k := ℚ) (G := N) (Rep.res N.subtype A) n
    (P := (Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ K))
    (Q := (Rep.resFunctor N.subtype).mapProjectiveResolution R)
    (((Rep.resFunctor.{0} (k := ℚ) N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map (fR R))
    (mapRes_comm N R)
  exact h.symm

theorem CxNf_GY (g : K) : CxNf N R A ≫ GY N (YAR R A) g = GY N (YA A) g ≫ CxNf N R A :=
  (NatTrans.mapHomologicalComplex (gamNat (k := ℚ) N g) (ComplexShape.down ℕ)).naturality (fY R A)

omit [N.Normal] in
theorem CxNf_QY : CxNf N R A ≫ QY N (YAR R A) =
    QY N (YA A) ≫ ((cK (k := ℚ) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A) :=
  (NatTrans.mapHomologicalComplex (qNat (k := ℚ) N) (ComplexShape.down ℕ)).naturality (fY R A)

omit [N.Normal] in
theorem eKR_hom (n : ℕ) :
    (eKR R A n).hom = (eK A n).hom ≫ HomologicalComplex.homologyMap
      (((cK (k := ℚ) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A)) n := by
  have comm : (fR R).f 0 ≫ R.π.f 0 = (Rep.barResolution ℚ K).π.f 0 := by
    have h := congrArg (fun t => t.f 0) (fR_comm R)
    simp only [HomologicalComplex.comp_f] at h
    rw [(ChainComplex.single₀ _).map_id, HomologicalComplex.id_f, Category.comp_id] at h
    exact h
  exact (groupHomologyIso_hom_comp (k := ℚ) (G := K) A n (P := Rep.barResolution ℚ K) (Q := R) (fR R) comm).symm

/-- **Conjugation on the chain level for any resolution.** -/
theorem eNR_cAct (n : ℕ) (g : K) (z : groupHomology (Rep.res N.subtype A) n) :
    (eNR N R A n).hom.hom (cAct N A n g z) =
      (HomologicalComplex.homologyMap (GY N (YAR R A) g) n).hom ((eNR N R A n).hom.hom z) := by
  have h : HomologicalComplex.homologyMap (GY N (YA A) g) n ≫ HomologicalComplex.homologyMap (CxNf N R A) n =
      HomologicalComplex.homologyMap (CxNf N R A) n ≫ HomologicalComplex.homologyMap (GY N (YAR R A) g) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, CxNf_GY]
  have h2 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) ((eN N A n).hom.hom z)
  rw [eNR_hom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2 ⊢
  rw [eN_cAct, h2]

omit [N.Normal] in
/-- **Corestriction on the chain level for any resolution.** -/
theorem eKR_corN (n : ℕ) (z : groupHomology (Rep.res N.subtype A) n) :
    (eKR R A n).hom.hom (corN N A n z) =
      (HomologicalComplex.homologyMap (QY N (YAR R A)) n).hom ((eNR N R A n).hom.hom z) := by
  have h : HomologicalComplex.homologyMap (QY N (YA A)) n ≫ HomologicalComplex.homologyMap
        (((cK (k := ℚ) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A)) n =
      HomologicalComplex.homologyMap (CxNf N R A) n ≫ HomologicalComplex.homologyMap (QY N (YAR R A)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, CxNf_QY]
  have h2 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) ((eN N A n).hom.hom z)
  rw [eNR_hom, eKR_hom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2 ⊢
  rw [eK_corN, h2]

section Avg

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable [N.FiniteIndex]

/-- The chain-level average over `K/N` on the `N`-coinvariant complex. -/
def avgY (Y : ChainComplex (Rep.{0} ℚ K) ℕ) : CxN N Y ⟶ CxN N Y :=
  ((Fintype.card (K ⧸ N) : ℚ)⁻¹) • ∑ x : K ⧸ N, GY N Y x.out

theorem avgY_homology (Y : ChainComplex (Rep.{0} ℚ K) ℕ) (n : ℕ) :
    (HomologicalComplex.homologyMap (avgY N Y) n).hom = avgH N Y n := by
  unfold avgY avgH
  rw [homologyMap_smul', homologyMap_sum', ModuleCat.hom_smul, ModuleCat.hom_sum]

theorem avgY_QY (Y : ChainComplex (Rep.{0} ℚ K) ℕ) : avgY N Y ≫ QY N Y = QY N Y := by
  unfold avgY
  rw [Linear.smul_comp, Preadditive.sum_comp]
  simp only [GY_QY, Finset.sum_const, Finset.card_univ]
  have hc : (Fintype.card (K ⧸ N) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K ⧸ N)).ne'
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Averaging on the chain level for any resolution.** -/
theorem eNR_avgN (n : ℕ) (z : groupHomology (Rep.res N.subtype A) n) :
    (eNR N R A n).hom.hom (avgN N A n z) = avgH N (YAR R A) n ((eNR N R A n).hom.hom z) := by
  unfold avgN avgH
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, eNR_cAct]

theorem eNR_avgN' (n : ℕ) (z : groupHomology (Rep.res N.subtype A) n) :
    (eNR N R A n).hom.hom (avgN N A n z) =
      (HomologicalComplex.homologyMap (avgY N (YAR R A)) n).hom ((eNR N R A n).hom.hom z) := by
  rw [eNR_avgN, avgY_homology]

end Avg

end TernaryPeriodPolynomials.Argument.GroupHomology
