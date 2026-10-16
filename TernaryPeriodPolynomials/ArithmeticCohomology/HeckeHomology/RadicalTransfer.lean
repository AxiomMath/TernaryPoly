module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Functorial
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Transfer

@[expose] public section


/-!
# The radical correspondence on the top homology of the unipotent radical

Formalized by Claude Sonnet 5.5.

For a group `U ≅ ℤ²` (`eU : U2 ≃* U`) acting trivially on `A`, a finite-index subgroup `N ≤ U`, a homomorphism `ν : N →* U` and an
endomorphism `μ : U →* U` with `μ ∘ ν = incl` (the image of `ν` has finite index and `μ` is the rational inverse of `ν`
followed by the inclusion), the correspondence `tr_N` then `H(ν, c)` multiplies the fundamental class by `[U : N] / det μ`
(`radical_corr`).  For the index-`p` sublattice `N = {u₀ ≡ 0}` and `ν(u₀, u₁) = (u₀/p, u₁)` this is `p / p = 1`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)
open TernaryPeriodPolynomials.Argument.GroupHomology

section Psi

variable {P : Type} [Group P] {U : Subgroup P} [U.Normal] (eU : U2 ≃* U) {A : Rep.{0} ℚ P}

/-- An endomorphism of `U` transported to `U2`. -/
def muPsi (ψ : U →* U) : U2 →* U2 := eU.symm.toMonoidHom.comp (ψ.comp eU.toMonoidHom)

omit [U.Normal] in
theorem eU_muPsi (ψ : U →* U) (v : U2) : eU (muPsi eU ψ v) = ψ (eU v) := by
  simp [muPsi]

omit [U.Normal] in
/-- `H₂` of an endomorphism `ψ` of `U` with a coefficient morphism `a`, in the coordinates `PsiIso`. -/
theorem psi_map (hA : ∀ u : U, A.ρ u = 1) (ψ : U →* U)
    (a : Rep.res U.subtype A ⟶ Rep.res ψ (Rep.res U.subtype A)) (x : groupHomology (TV A.V) 2) :
    groupHomology.map ψ a 2 ((PsiIso eU hA).hom.hom x) =
      (PsiIso eU hA).hom.hom
        (groupHomology.map (muPsi eU ψ) (trivHomRes (muPsi eU ψ) a.hom.toLinearMap) 2 x) := by
  let φ0 : TV A.V ⟶ Rep.res eU.toMonoidHom (Rep.res U.subtype A) :=
    Rep.ofHom ⟨(LinearEquiv.refl ℚ A.V).toLinearMap, fun g => by
      ext a
      change a = (A.ρ (eU g).1) a
      have : A.ρ (eU g).1 = 1 := hA (eU g)
      rw [this]; rfl⟩
  have hL := groupHomology.map_comp eU.toMonoidHom ψ φ0 a 2
  have hR := groupHomology.map_comp (muPsi eU ψ) eU.toMonoidHom
    (trivHomRes (muPsi eU ψ) a.hom.toLinearMap) φ0 2
  have hfg : ψ.comp eU.toMonoidHom = eU.toMonoidHom.comp (muPsi eU ψ) := by
    ext v
    exact congrArg Subtype.val (eU_muPsi eU ψ v).symm
  have hc : groupHomology.map eU.toMonoidHom φ0 2 ≫ groupHomology.map ψ a 2 =
      groupHomology.map (muPsi eU ψ) (trivHomRes (muPsi eU ψ) a.hom.toLinearMap) 2 ≫
        groupHomology.map eU.toMonoidHom φ0 2 :=
    hL.symm.trans ((groupHomology.map_congr hfg (by ext a; rfl) 2).trans hR)
  have := congrArg (fun φ => φ.hom x) hc
  exact this

end Psi

section Rad

open scoped Classical

variable {P : Type} [Group P] {U : Subgroup P} [U.Normal] (eU : U2 ≃* U) {A : Rep.{0} ℚ P}
  (hA : ∀ u : U, A.ρ u = 1)

/-- The coefficient morphism of a linear endomorphism `cc` of a trivial `U`-module along any pair of homomorphisms `j, ν`. -/
def cTriv {N : Type} [Group N] (j ν : N →* U) (cc : A.V →ₗ[ℚ] A.V) :
    Rep.res j (Rep.res U.subtype A) ⟶ Rep.res ν (Rep.res U.subtype A) :=
  Rep.ofHom ⟨cc, fun n => by
    ext a
    change cc (A.ρ (j n).1 a) = A.ρ (ν n).1 (cc a)
    rw [hA, hA]
    rfl⟩

/-- The morphism `Res_U A ⟶ Res_ν Res_U A` with underlying map `cc`. -/
def cTriv0 (ν : U →* U) (cc : A.V →ₗ[ℚ] A.V) :
    Rep.res U.subtype A ⟶ Rep.res ν (Rep.res U.subtype A) :=
  Rep.ofHom ⟨cc, fun n => by
    ext a
    change cc (A.ρ n.1 a) = A.ρ (ν n).1 (cc a)
    rw [hA, hA]
    rfl⟩

theorem omegaZ_e1_e2 : (omegaZ e1 e2 : ℤ) = 1 := by
  simp [omegaZ, e1, e2]

omit [U.Normal] in
theorem muPsi_id (v : U2) : muPsi eU (MonoidHom.id U) v = v := by
  apply eU.injective
  rw [eU_muPsi]
  rfl

variable [Module.Finite ℚ A.V]

omit [U.Normal] in
/-- **The radical correspondence.**  Let `N ≤ U` have finite index, `ν : N →* U`, and `μ : U →* U` with `μ ∘ ν = incl`.  Then
`ω(μ) · H₂(ν, c) ∘ tr_N = [U : N] · H₂(c)` on the fundamental class, where `ω(μ)` is the determinant of `μ` on `U ≅ ℤ²`. -/
theorem radical_corr (N : Subgroup U) [N.FiniteIndex] (ν : N →* U) (μ : U →* U)
    (hμ : ∀ n : N, μ (ν n) = (n : U)) (cc : A.V →ₗ[ℚ] A.V) (x : A.V) :
    (omegaZ (muPsi eU μ e1) (muPsi eU μ e2) : ℚ) •
        (groupHomology.map ν (cTriv hA N.subtype ν cc) 2).hom
          ((trR N (Rep.res U.subtype A) 2).hom ((PsiIso eU hA).hom.hom (kappa0 A.V x))) =
      (Fintype.card (RC N) : ℚ) • (PsiIso eU hA).hom.hom (kappa0 A.V (cc x)) := by
  set y := (PsiIso eU hA).hom.hom (kappa0 A.V x) with hy
  set T := (groupHomology.map ν (cTriv hA N.subtype ν cc) 2).hom ((trR N (Rep.res U.subtype A) 2).hom y) with hT
  -- step D: `T` is a multiple of the fundamental class, so `μ` acts on it by `ω`
  obtain ⟨t, ht⟩ := kappa0_surjective (V := A.V) ((PsiIso eU hA).inv.hom T)
  have hTt : T = (PsiIso eU hA).hom.hom (kappa0 A.V t) := by
    rw [ht]
    exact (congrArg (fun m => m.hom T) (PsiIso eU hA).inv_hom_id).symm
  have hD : (groupHomology.map μ (cTriv0 hA μ LinearMap.id) 2).hom T =
      (omegaZ (muPsi eU μ e1) (muPsi eU μ e2) : ℚ) • T := by
    rw [hTt, psi_map eU hA μ (cTriv0 hA μ LinearMap.id) (kappa0 A.V t)]
    rw [show (cTriv0 hA μ (LinearMap.id : A.V →ₗ[ℚ] A.V)).hom.toLinearMap = LinearMap.id from rfl]
    rw [map_kappa0_gen (muPsi eU μ) LinearMap.id t]
    simp only [LinearMap.id_apply, map_smul]
  -- step A: composing the two correspondences gives the inclusion with the coefficient `cc`
  have hA1 := groupHomology.map_comp ν μ (cTriv hA N.subtype ν cc) (cTriv0 hA μ LinearMap.id) 2
  have hμν : μ.comp ν = N.subtype := MonoidHom.ext fun n => hμ n
  have hA2 : groupHomology.map (μ.comp ν)
      (cTriv hA N.subtype ν cc ≫ (Rep.resFunctor ν).map (cTriv0 hA μ LinearMap.id)) 2 =
      groupHomology.map N.subtype (cTriv hA N.subtype N.subtype cc) 2 :=
    groupHomology.map_congr hμν (by ext a; rfl) 2
  have hA3 := groupHomology.map_comp N.subtype (MonoidHom.id U)
    (𝟙 (Rep.res N.subtype (Rep.res U.subtype A))) (cTriv0 hA (MonoidHom.id U) cc) 2
  have hA4 : groupHomology.map ((MonoidHom.id U).comp N.subtype)
      (𝟙 (Rep.res N.subtype (Rep.res U.subtype A)) ≫
        (Rep.resFunctor N.subtype).map (cTriv0 hA (MonoidHom.id U) cc)) 2 =
      groupHomology.map N.subtype (cTriv hA N.subtype N.subtype cc) 2 :=
    groupHomology.map_congr rfl (by ext a; rfl) 2
  have hcomp : groupHomology.map ν (cTriv hA N.subtype ν cc) 2 ≫
      groupHomology.map μ (cTriv0 hA μ LinearMap.id) 2 =
      groupHomology.map N.subtype (𝟙 (Rep.res N.subtype (Rep.res U.subtype A))) 2 ≫
        groupHomology.map (MonoidHom.id U) (cTriv0 hA (MonoidHom.id U) cc) 2 :=
    hA1.symm.trans (hA2.trans (hA4.symm.trans hA3))
  -- step B: transfer followed by corestriction is the index
  have hB := congrArg (fun m => m.hom y) (trR_cor N (Rep.res U.subtype A) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at hB
  -- step C: the coefficient endomorphism on the fundamental class
  have hC : (groupHomology.map (MonoidHom.id U) (cTriv0 hA (MonoidHom.id U) cc) 2).hom y =
      (PsiIso eU hA).hom.hom (kappa0 A.V (cc x)) := by
    refine (psi_map eU hA (MonoidHom.id U) (cTriv0 hA (MonoidHom.id U) cc) (kappa0 A.V x)).trans ?_
    change (PsiIso eU hA).hom.hom ((groupHomology.map (muPsi eU (MonoidHom.id U))
      (trivHomRes (muPsi eU (MonoidHom.id U)) cc) 2).hom (kappa0 A.V x)) = _
    rw [map_kappa0_gen (muPsi eU (MonoidHom.id U)) cc x, muPsi_id eU, muPsi_id eU, omegaZ_e1_e2]
    simp
  have hE := congrArg (fun m => m.hom ((trR N (Rep.res U.subtype A) 2).hom y)) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hE
  calc (omegaZ (muPsi eU μ e1) (muPsi eU μ e2) : ℚ) • T
      = (groupHomology.map μ (cTriv0 hA μ LinearMap.id) 2).hom T := hD.symm
    _ = (groupHomology.map (MonoidHom.id U) (cTriv0 hA (MonoidHom.id U) cc) 2).hom
          ((groupHomology.map N.subtype (𝟙 (Rep.res N.subtype (Rep.res U.subtype A))) 2).hom
            ((trR N (Rep.res U.subtype A) 2).hom y)) := hE
    _ = (Fintype.card (RC N) : ℚ) • (groupHomology.map (MonoidHom.id U) (cTriv0 hA (MonoidHom.id U) cc) 2).hom y := by
        rw [hB, map_smul]
    _ = _ := by rw [hC]

end Rad

end TernaryPeriodPolynomials.Argument.HeckeHomology
