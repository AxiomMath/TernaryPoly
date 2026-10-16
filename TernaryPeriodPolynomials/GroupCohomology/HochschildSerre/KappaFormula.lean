module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.KappaViaResolution
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeInstance
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.TreeTheorem
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.EvalQ
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.SchurSym

@[expose] public section


/-!
# The formula for `edge2 ∘ hsFarey` on the image of a tree map

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
  TernaryPeriodPolynomials.Argument.BinaryDuality

section Step1

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π) (hker : (π.ker : Set (P ⧸ U)).Finite)
  [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
  (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (D : Rep.{0} ℚ IntegralGL)
  (e : (ZP U A).homology 2 ≅ Rep.res π D)
  {L : Rep.{0} ℚ (P ⧸ U)}
  (t3 : L ⊗ Rep.res π P1 ⟶ (Phi U).obj (R.complex.X 3))
  (t2 : L ⊗ Rep.res π P0 ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ Rep.resMap π d1) ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0)

include hU3 hi hii in
theorem edge2_hsFarey_LamH (x : KM (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (Abar U A ⊗ L)) :
    edge2 D (hsFarey U A π hπ hker hU3 D e ((groupHomologyZIsoR U R A 3).inv.hom
      (LamH (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (Abar U A ⊗ L)
        (ThetaIn U A R t3) (ThetaIn U A R t2) (ThetaIn_comm U A R (Rep.resMap π d1) t3 t2 hi) x))) =
      (-((Nat.card π.ker : ℚ)⁻¹)) • (PsiInst U A R (Rep.resMap π d1) (epsQ π) (resD1_epsQ π)
        (sesQ_shortExact π) t3 t2 hi hii ≫ (eR U A R π D e).hom).hom
        (evalQ π hker (Abar U A ⊗ L) x.1) := by
  rw [hsFarey_apply_ZR U A R π hπ hker hU3 D e]
  have hZ : ∀ z, (groupHomologyZIsoR U R A 3).hom.hom ((groupHomologyZIsoR U R A 3).inv.hom z) = z :=
    fun z => congrArg (fun t => t.hom z) (groupHomologyZIsoR U R A 3).inv_hom_id
  rw [hZ]
  have hw := thmAEquiv_LamH (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
    (resD1_epsQ π) (Abar U A ⊗ L) (sesQ_shortExact π) (ThetaIn U A R t3) (ThetaIn U A R t2)
    (ThetaIn_comm U A R (Rep.resMap π d1) t3 t2 hi) (ThetaIn_cyc U A R t2 hii) (ZR_projective U R A)
    (isZero_ZR_homology_of_group U R A 3 hU3) x
  set w := thmAEquiv (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
    (resD1_epsQ π) (ZR_projective U R A) (sesQ_shortExact π)
    (isZero_ZR_homology_of_group U R A 3 hU3) (LamH (ZR U R A) (Rep.res π P1) (Rep.res π P0)
      (Rep.resMap π d1) (Abar U A ⊗ L) (ThetaIn U A R t3) (ThetaIn U A R t2)
      (ThetaIn_comm U A R (Rep.resMap π d1) t3 t2 hi) x) with hwdef
  have hedge : ∀ z : LinearMap.ker ((FXmap d1).app D).hom,
      edge2 D ((H1Iso D).toLinearEquiv.symm z) = evalP D ((inclC D).hom z.1) := by
    intro z
    have h1 : (H1Iso D).hom.hom ((H1Iso D).toLinearEquiv.symm z) = z :=
      (H1Iso D).toLinearEquiv.apply_symm_apply z
    change evalP D ((inclC D).hom (((H1Iso D).hom.hom ((H1Iso D).toLinearEquiv.symm z) :
      LinearMap.ker (dC D).hom) : CT D P1)) = _
    rw [h1]
  rw [hedge]
  have hz : ((kerInflEquiv π hπ d1 D (kerNatEquiv (FXmap (Rep.resMap π d1)) (eR U A R π D e) w)) :
      (FX P1).obj D) =
      inflEquiv π hπ D P1 (((FX (Rep.res π P1)).map (eR U A R π D e).hom).hom (w : (FX (Rep.res π P1)).obj
        ((ZR U R A).homology 2))) := rfl
  have hcard : (Nat.card π.ker : ℚ) ≠ 0 := by
    have : Finite π.ker := hker.to_subtype
    exact_mod_cast (Nat.card_pos (α := π.ker)).ne'
  set Ψ := PsiInst U A R (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) (sesQ_shortExact π) t3 t2 hi hii ≫
    (eR U A R π D e).hom with hΨ
  have hw0 : ((FX (Rep.res π P1)).map (eR U A R π D e).hom).hom (w : (FX (Rep.res π P1)).obj
      ((ZR U R A).homology 2)) = - ((FX (Rep.res π P1)).map Ψ).hom x.1 := by
    rw [hw, map_neg]
    congr 1
    rw [hΨ, Functor.map_comp]
    rfl
  rw [hz, hw0]
  simp only [map_neg]
  have h1 := evalQ_infl π hπ hker D (((FX (Rep.res π P1)).map Ψ).hom x.1)
  rw [evalQ_nat π hker Ψ x.1] at h1
  have h2 : evalP D ((inclC D).hom (inflEquiv π hπ D P1 (((FX (Rep.res π P1)).map Ψ).hom x.1))) =
      ((Nat.card π.ker : ℚ)⁻¹) • Ψ.hom (evalQ π hker (Abar U A ⊗ L) x.1) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [h2, neg_smul]


end Step1

/-- `a ⊗ ℓ ↦ f₀(ℓ) lin(a)`. -/
def Psi0 {V W X : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W] [AddCommGroup X]
    [Module ℚ X] (lin : V ≃ₗ[ℚ] W) (f₀ : X →ₗ[ℚ] ℚ) : V ⊗[ℚ] X →ₗ[ℚ] W :=
  lin.toLinearMap ∘ₗ (TensorProduct.rid ℚ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id f₀

theorem Psi0_tmul {V W X : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup X] [Module ℚ X] (lin : V ≃ₗ[ℚ] W) (f₀ : X →ₗ[ℚ] ℚ) (a : V) (x : X) :
    Psi0 lin f₀ (a ⊗ₜ[ℚ] x) = f₀ x • lin a := by
  simp [Psi0, TensorProduct.rid_tmul, map_smul]

theorem Psi0_bijective {V W X : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup X] [Module ℚ X] (lin : V ≃ₗ[ℚ] W) (f₀ : X →ₗ[ℚ] ℚ) (x₀ : X) (h₀ : f₀ x₀ = 1)
    (hx : ∀ m : V ⊗[ℚ] X, ∃ a : V, m = a ⊗ₜ[ℚ] x₀) : Function.Bijective (Psi0 lin f₀) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨a, rfl⟩ := hx m
    rw [Psi0_tmul, h₀, one_smul] at hm
    have : a = 0 := lin.injective (by rw [hm, map_zero])
    rw [this]; simp
  · intro w
    refine ⟨lin.symm w ⊗ₜ[ℚ] x₀, ?_⟩
    rw [Psi0_tmul, h₀, one_smul, LinearEquiv.apply_symm_apply]

section Schur

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (eU : U2 ≃* U)
  {L : Rep.{0} ℚ (P ⧸ U)} (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π) (d : ℕ)
  (lin : A.V ≃ₗ[ℚ] (Dplain d).V)
  (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) = (Dplain d).ρ (π (QuotientGroup.mk g)) (lin a))
  (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L.V = 1)
  (hLchar : ∀ g : P, L.ρ (QuotientGroup.mk g) = deltaG eU g • LinearMap.id)

include hcompat hℓ hL hLchar hπ in
theorem Schur_scalar (f : Abar U A ⊗ L ⟶ Rep.res π (Dplain d)) :
    ∃ lam : ℚ, ∀ a : A.V, f.hom (a ⊗ₜ[ℚ] ℓ₀) = lam • lin a := by
  obtain ⟨f₀, hf₀⟩ := Module.Projective.exists_dual_eq_one ℚ hℓ
  have hx := fun m : A.V ⊗[ℚ] L.V => one_dim_tmul ℓ₀ hℓ hL m
  have hbij := Psi0_bijective lin f₀ ℓ₀ hf₀ hx
  let Ψ₀ := LinearEquiv.ofBijective (Psi0 lin f₀) hbij
  have hf₀L : ∀ ℓ : L.V, f₀ ℓ • ℓ₀ = ℓ := by
    intro ℓ
    obtain ⟨c, rfl⟩ := ((finrank_eq_one_iff_of_nonzero' ℓ₀ hℓ).1 hL) ℓ
    rw [map_smul, hf₀, smul_eq_mul, mul_one]
  have hΨeq : ∀ (g : P) (m : A.V ⊗[ℚ] L.V),
      Psi0 lin f₀ ((Abar U A ⊗ L).ρ (QuotientGroup.mk g) m) =
        (Dplain d).ρ (π (QuotientGroup.mk g)) (Psi0 lin f₀ m) := by
    intro g m
    induction m using TensorProduct.inductionOn with
    | tmul a ℓ =>
      change Psi0 lin f₀ (A.ρ g a ⊗ₜ[ℚ] L.ρ (QuotientGroup.mk g) ℓ) = _
      rw [hLchar g, Psi0_tmul, Psi0_tmul]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
      rw [← hcompat g a, map_smul]
      simp only [smul_smul, smul_eq_mul, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  let φ : (Dplain d).V →ₗ[ℚ] (Dplain d).V := f.hom.toLinearMap ∘ₗ Ψ₀.symm.toLinearMap
  have hφ : ∀ (γ : IntegralGL) (v : (Dplain d).V), φ ((Dplain d).ρ γ v) = (Dplain d).ρ γ (φ v) := by
    intro γ v
    obtain ⟨q, rfl⟩ := hπ γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, rfl⟩ := Ψ₀.surjective v
    have h1 : Ψ₀.symm ((Dplain d).ρ (π (QuotientGroup.mk g)) (Ψ₀ m)) =
        (Abar U A ⊗ L : Rep.{0} ℚ (P ⧸ U)).ρ (QuotientGroup.mk g) m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hΨeq g m).symm
    change f.hom (Ψ₀.symm ((Dplain d).ρ (π (QuotientGroup.mk g)) (Ψ₀ m))) =
      (Dplain d).ρ (π (QuotientGroup.mk g)) (f.hom (Ψ₀.symm (Ψ₀ m)))
    rw [h1, LinearEquiv.symm_apply_apply]
    exact Rep.hom_comm_apply f (QuotientGroup.mk g) m
  obtain ⟨c, hc⟩ := dplain_endo_scalar d φ hφ
  refine ⟨c, fun a => ?_⟩
  have h2 : Ψ₀ (a ⊗ₜ[ℚ] ℓ₀) = lin a := by
    change Psi0 lin f₀ (a ⊗ₜ[ℚ] ℓ₀) = _
    rw [Psi0_tmul, hf₀, one_smul]
  have := hc (lin a)
  change f.hom (Ψ₀.symm (lin a)) = c • lin a at this
  have h3 : Ψ₀.symm (lin a) = a ⊗ₜ[ℚ] ℓ₀ := by
    rw [LinearEquiv.symm_apply_eq]; exact h2.symm
  rw [h3] at this
  exact this

end Schur


section Step3

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)]
  (eU : U2 ≃* U) (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  (π : P ⧸ U →* IntegralGL) (hπ : Function.Surjective π) (hker : (π.ker : Set (P ⧸ U)).Finite)
  [Projective (Rep.res π P1)] [Projective (Rep.res π P0)]
  (hU3 : IsZero (groupHomology (Rep.res U.subtype A) 3)) (d : ℕ)
  (lin : A.V ≃ₗ[ℚ] (Dplain d).V)
  (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) = (Dplain d).ρ (π (QuotientGroup.mk g)) (lin a))
  (e : (ZP U A).homology 2 ≅ Rep.res π (Dplain d))
  {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (hL : Module.finrank ℚ L.V = 1)
  (t3 : L ⊗ Rep.res π P1 ⟶ (Phi U).obj (R.complex.X 3))
  (t2 : L ⊗ Rep.res π P0 ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ Rep.resMap π d1) ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0)
  (h3 : t2.hom (ℓ₀ ⊗ₜ[ℚ] sZero (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (epsQ π)
      (resD1_epsQ π) (sesQ_shortExact π)) ∉
    LinearMap.range ((Phi U).map (R.complex.d 3 2)).hom.toLinearMap)

/-- The coefficient of a vector of the line `L` with respect to `ℓ₀`. -/
def coefL {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) : L.V →ₗ[ℚ] ℚ :=
  (Module.Projective.exists_dual_eq_one ℚ hℓ).choose

theorem coefL_spec {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) : coefL U ℓ₀ hℓ ℓ₀ = 1 :=
  (Module.Projective.exists_dual_eq_one ℚ hℓ).choose_spec

/-- `a ⊗ ℓ ↦ coefficient(ℓ) • a`. -/
def iotaM {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) : (Abar U A ⊗ L).V →ₗ[ℚ] A.V :=
  (TensorProduct.rid ℚ A.V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id (coefL U ℓ₀ hℓ)

theorem iotaM_tmul {L : Rep.{0} ℚ (P ⧸ U)} (ℓ₀ : L.V) (hℓ : ℓ₀ ≠ 0) (a : A.V) (ℓ : L.V) :
    iotaM U A ℓ₀ hℓ (a ⊗ₜ[ℚ] ℓ) = coefL U ℓ₀ hℓ ℓ • a := by
  simp [iotaM, TensorProduct.rid_tmul]

include hU3 hi hii hcompat hπ h3 hL in
/-- **The formula for `edge2 ∘ hsFarey` on tree images**: `edge2 (hsFarey y) = c · lin (ι (evalQ x))` with `c ≠ 0`. -/
theorem edge2_hsFarey_tree :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ x : KM (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (Abar U A ⊗ L),
      edge2 (Dplain d) (hsFarey U A π hπ hker hU3 (Dplain d) e ((groupHomologyZIsoR U R A 3).inv.hom
        (LamH (ZR U R A) (Rep.res π P1) (Rep.res π P0) (Rep.resMap π d1) (Abar U A ⊗ L)
          (ThetaIn U A R t3) (ThetaIn U A R t2) (ThetaIn_comm U A R (Rep.resMap π d1) t3 t2 hi) x))) =
        c • lin (iotaM U A ℓ₀ hℓ (evalQ π hker (Abar U A ⊗ L) x.1)) := by
  have hLchar : ∀ g : P, L.ρ (QuotientGroup.mk g) = deltaG eU g • LinearMap.id := fun g =>
    L_character U R (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) (sesQ_shortExact π) t3 t2 hi hii eU ℓ₀ hℓ hL h3 g
  set f := PsiInst U A R (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) (sesQ_shortExact π) t3 t2 hi hii ≫
    (eR U A R π (Dplain d) e).hom with hf
  have hinj : Function.Injective f.hom := by
    have h1 := PsiInst_injective U A R (Rep.resMap π d1) (epsQ π) (resD1_epsQ π) (sesQ_shortExact π)
      t3 t2 hi hii ℓ₀ hℓ hL h3
    have h2 : Function.Injective (eR U A R π (Dplain d) e).hom.hom :=
      (ConcreteCategory.bijective_of_isIso ((forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)).map
        (eR U A R π (Dplain d) e).hom)).1
    exact h2.comp h1
  obtain ⟨lam, hlam⟩ := Schur_scalar U A eU π hπ d lin hcompat ℓ₀ hℓ hL hLchar f
  have hf_all : ∀ m : (Abar U A ⊗ L).V, ∃ a : A.V, m = a ⊗ₜ[ℚ] ℓ₀ := fun m => one_dim_tmul ℓ₀ hℓ hL m
  obtain ⟨lam', hlam', hlam0⟩ : ∃ lam' : ℚ, lam' ≠ 0 ∧ ∀ a : A.V, f.hom (a ⊗ₜ[ℚ] ℓ₀) = lam' • lin a := by
    by_cases h0 : lam = 0
    · refine ⟨1, one_ne_zero, fun a => ?_⟩
      have : f.hom (a ⊗ₜ[ℚ] ℓ₀) = 0 := by rw [hlam, h0, zero_smul]
      have ha : a ⊗ₜ[ℚ] ℓ₀ = 0 := hinj (this.trans (map_zero _).symm)
      have : a = 0 := by
        have h := congrArg (iotaM U A ℓ₀ hℓ) ha
        rw [iotaM_tmul, coefL_spec, one_smul, map_zero] at h
        exact h
      rw [this]; simp
    · exact ⟨lam, h0, hlam⟩
  have hcard : (Nat.card π.ker : ℚ) ≠ 0 := by
    have : Finite π.ker := hker.to_subtype
    exact_mod_cast (Nat.card_pos (α := π.ker)).ne'
  refine ⟨-((Nat.card π.ker : ℚ)⁻¹) * lam', mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hcard)) hlam', fun x => ?_⟩
  rw [edge2_hsFarey_LamH U A R π hπ hker hU3 (Dplain d) e t3 t2 hi hii x]
  obtain ⟨a, ha⟩ := hf_all (evalQ π hker (Abar U A ⊗ L) x.1)
  have hia : iotaM U A ℓ₀ hℓ (evalQ π hker (Abar U A ⊗ L) x.1) = a := by
    rw [ha, iotaM_tmul, coefL_spec, one_smul]
  rw [hia]
  change (-((Nat.card π.ker : ℚ)⁻¹)) • f.hom (evalQ π hker (Abar U A ⊗ L) x.1) = _
  rw [ha, hlam0, smul_smul]

end Step3

end TernaryPeriodPolynomials.Argument.HochschildSerre
