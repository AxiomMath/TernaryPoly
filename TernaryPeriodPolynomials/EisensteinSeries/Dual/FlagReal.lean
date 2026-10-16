module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GramBridge
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspRows
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# The real/complex flag dictionary: real vanishing on `Γ(N) ∩ h⁻¹Bh` from complex vanishing on the flag stabilizer

Formalized by Claude Sonnet 5.5.

the flag statements (`EisensteinClass.FlagCusp`) are about the COMPLEX coefficient representation
`faceRep N h n` and the flag stabilizer `faceFlagStab N h F ≤ Γ_{h⁻¹Ph}`, whereas the dual transport (`Cusps.dual_restrictions_transport`) restricts REAL classes to the
arithmetic flag groups `gammaNBAt N h ≤ SL₃(ℤ)`.  Three generic facts and one dictionary:

* `cxGen_injective`: complexification (the identity on cocycles) is injective on `H²`;
* `map_mulEquiv_injective`: pullback along a group isomorphism (identity on coefficients) is injective on `H²`;
* `resTo_flag_eq_zero_iff`: for `K = (faceFlagStab N h F).map subtype` (the `faceFlagStab_map_eq_gammaNBAt`, `faceFlagStab_one_map`), the real restriction of a class `c'` of
  `Γ(N)` to `K` vanishes iff the complexified restriction of `c'` to the plane group of `h⁻¹Ph`, restricted to the flag stabilizer (`twoCohomologyRestriction`), vanishes;
* `resTo_flag_zero_of_cuspidal`, `resTo_gammaNBAt_zero_of_cuspidal`: hence `r_B c' = 0` at the flag of any frame (in particular at `gammaNBAt N h`, which covers every flag group)
  as soon as the complexified plane restriction at that cusp is mixed cuspidal (the `flag_vanishing_at_cusp`);
* `dual_rB_zero_of_cuspidal`: the dual `r_B = 0` row, `resTo (gammaNBAt N h) (ȷ^* c') = 0`, given mixed cuspidality of the complexified plane restriction of `c'` at `ȷ(h)`
  (the only missing input is the mixed cuspidality of the transported seeds).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

section Generic

variable {G : Type} [Group G] {n : ℕ} (ρ : Representation ℝ G (TernaryPeriodPolynomials.Argument.SeedC3.Coef n))
  (ρC : Representation ℂ G (GeneralEisenstein.HomogeneousPoly n))
  (hρ : ∀ g (v : TernaryPeriodPolynomials.Argument.SeedC3.Coef n),
    ((ρ g v : TernaryPeriodPolynomials.Argument.SeedC3.Coef n) : GeneralEisenstein.HomogeneousPoly n) = ρC g (v : GeneralEisenstein.HomogeneousPoly n))

/-- **Complexification is injective on `H²`**: a complex coboundary is a real one (same underlying function). -/
theorem cxGen_injective : Function.Injective (cxGen ρ ρC hρ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with
  | _ c =>
    rw [cxGen_H2π] at hx
    rw [H2π_eq_zero_iff] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← map_zero (H2π (Rep.of ρ)).hom, H2π_eq_iff]
    refine ⟨fun g => (y g : TernaryPeriodPolynomials.Argument.SeedC3.Coef n), ?_⟩
    funext p
    have hp := congrFun hy p
    simp only [d₁₂_hom_apply] at hp ⊢
    erw [d₁₂_hom_apply]
    refine Eq.trans ?_ (hp.trans ?_)
    · erw [hρ p.1 (y p.2)]
      rfl
    · exact (sub_zero (c.1 p)).symm

end Generic


section Equiv

variable {k : Type} [Field k] {G G' : Type} [Group G] [Group G'] {V : Type} [AddCommGroup V] [Module k V]
  (e : G ≃* G') (ρ' : Representation k G' V)

/-- **Pullback along a group isomorphism is injective on `H²`** (identity on the coefficient module). -/
theorem map_mulEquiv_injective :
    Function.Injective (groupCohomology.map e.toMonoidHom
      (resMorK e.toMonoidHom (ρ'.comp e.toMonoidHom) ρ' (fun _ => rfl)) 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with
  | _ c =>
    rw [H2π_comp_map_apply, H2π_eq_zero_iff] at hx
    obtain ⟨y, hy⟩ := hx
    rw [H2π_eq_zero_iff]
    refine ⟨fun g' => y (e.symm g'), ?_⟩
    funext p
    have hp := congrFun hy (e.symm p.1, e.symm p.2)
    erw [d₁₂_hom_apply] at hp ⊢
    have e1 : e.symm (p.1 * p.2) = e.symm p.1 * e.symm p.2 := map_mul _ _ _
    rw [e1]
    have e2 : ((ConcreteCategory.hom (mapCocycles₂ e.toMonoidHom (resMorK e.toMonoidHom (ρ'.comp e.toMonoidHom) ρ' (fun _ => rfl))))
        c) (e.symm p.1, e.symm p.2) = c p := by
      change c (e (e.symm p.1), e (e.symm p.2)) = c p
      simp
    rw [e2] at hp
    have e3 : (Rep.of (ρ'.comp e.toMonoidHom)).ρ (e.symm p.1) = (Rep.of ρ').ρ p.1 := by
      change ρ' (e (e.symm p.1)) = ρ' p.1
      rw [MulEquiv.apply_symm_apply]
    rw [e3] at hp
    exact hp

end Equiv


section Flag

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ)) (F : GL (Fin 2) ℚ) {K : Subgroup SL(3, ℤ)}
  (hK : (faceFlagStab N h F).map (gammaNPAt N h).subtype = K)

/-- The isomorphism between the flag stabilizer in the plane group and its image `K` in `SL₃(ℤ)`. -/
def flagEquiv : faceFlagStab N h F ≃* K :=
  (Subgroup.equivMapOfInjective (faceFlagStab N h F) (gammaNPAt N h).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr hK)

theorem flagEquiv_val (x : faceFlagStab N h F) : ((flagEquiv N h F hK x : K) : SL(3, ℤ)) = x.1.1 := rfl

theorem flag_le_N (hK : (faceFlagStab N h F).map (gammaNPAt N h).subtype = K) : K ≤ gammaN N := by
  rw [← hK]
  rintro _ ⟨x, _, rfl⟩
  exact gammaNPAt_le N h x.2


theorem resTo_flag_key (c' : H2 (Rep.of (gammaRho (gammaN N) n))) :
    (groupCohomology.map (flagEquiv N h F hK).toMonoidHom
        (resMorK (flagEquiv N h F hK).toMonoidHom
          (((gammaRho (gammaN N) n).comp (Subgroup.inclusion (flag_le_N N h F hK))).comp (flagEquiv N h F hK).toMonoidHom)
          ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (flag_le_N N h F hK))) (fun _ => rfl)) 2).hom
        (resTo K (flag_le_N N h F hK) (gammaRho (gammaN N) n) c') =
      (groupCohomology.map (faceFlagStab N h F).subtype
        (resMor (faceFlagStab N h F).subtype ((rhoAt N h n).comp (faceFlagStab N h F).subtype) (rhoAt N h n) (fun _ => rfl)) 2).hom
        (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c') := by
  let β' : faceFlagStab N h F →* gammaN N := (Subgroup.inclusion (gammaNPAt_le N h)).comp (faceFlagStab N h F).subtype
  have h1 := restrict_comp (flagEquiv N h F hK).toMonoidHom (Subgroup.inclusion (flag_le_N N h F hK)) β' (fun _ => rfl)
    (gammaRho (gammaN N) n) ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (flag_le_N N h F hK))) (fun _ => rfl)
    ((gammaRho (gammaN N) n).comp β') (fun _ => rfl) (fun _ => rfl) c'
  have h2 := restrict_comp (faceFlagStab N h F).subtype (Subgroup.inclusion (gammaNPAt_le N h)) β' (fun _ => rfl)
    (gammaRho (gammaN N) n) (rhoAt N h n) (fun _ => rfl)
    ((gammaRho (gammaN N) n).comp β') (fun _ => rfl) (fun _ => rfl) c'
  exact h1.symm.trans h2


/-- **Real vanishing at a flag group from complex vanishing on the flag stabilizer.**  For `K` the image in `SL₃(ℤ)` of the stabilizer of the flag of the frame `F` over the
plane `h⁻¹Ph`: the real restriction to `K` of a class `c'` of `Γ(N)` vanishes iff the complexified restriction of `c'` to the plane group, restricted to the flag
stabilizer (S3's `twoCohomologyRestriction`), vanishes. -/
theorem resTo_flag_eq_zero_iff (c' : H2 (Rep.of (gammaRho (gammaN N) n))) :
    resTo K (flag_le_N N h F hK) (gammaRho (gammaN N) n) c' = 0 ↔
      twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)
        (complexifyAt N h n (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c')) = 0 := by
  have key := resTo_flag_key N n h F hK c'
  have inj := map_mulEquiv_injective (flagEquiv N h F hK)
    ((gammaRho (gammaN N) n).comp (Subgroup.inclusion (flag_le_N N h F hK)))
  have hcx : twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)
        (complexifyAt N h n (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c')) =
      cxGen ((rhoAt N h n).comp (faceFlagStab N h F).subtype)
        ((gammaRhoC (gammaNPAt N h) n).comp (faceFlagStab N h F).subtype) (fun _ _ => rfl)
        ((groupCohomology.map (faceFlagStab N h F).subtype
          (resMor (faceFlagStab N h F).subtype ((rhoAt N h n).comp (faceFlagStab N h F).subtype) (rhoAt N h n) (fun _ => rfl)) 2).hom
          (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c')) := by
    have cm := cxGen_map ((rhoAt N h n).comp (faceFlagStab N h F).subtype)
      ((gammaRhoC (gammaNPAt N h) n).comp (faceFlagStab N h F).subtype) (fun _ _ => rfl)
      (rhoAt N h n) (gammaRhoC (gammaNPAt N h) n) (fun _ _ => rfl) (faceFlagStab N h F).subtype (fun _ => rfl) (fun _ => rfl)
      (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c')
    have e1 : complexifyAt N h n (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c') =
        cxGen (rhoAt N h n) (gammaRhoC (gammaNPAt N h) n) (fun _ _ => rfl)
          (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c') :=
      (cxGen_eq_complexify n (gammaNPAt N h) _).symm
    rw [e1]
    exact cm.symm
  rw [hcx, ← key]
  constructor
  · intro hz
    rw [hz]
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  · intro hz
    have := cxGen_injective _ _ (fun _ _ => rfl) (hz.trans (map_zero _).symm)
    exact inj (this.trans (map_zero _).symm)


/-- **`r_B = 0` at the flag of any frame, given mixed cuspidality of the complexified plane restriction.** -/
theorem resTo_flag_zero_of_cuspidal (c' : H2 (Rep.of (gammaRho (gammaN N) n)))
    (hcusp : complexifyAt N h n (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c') ∈
      faceCuspidalInH2 N h n) :
    resTo K (flag_le_N N h F hK) (gammaRho (gammaN N) n) c' = 0 :=
  (resTo_flag_eq_zero_iff N n h F hK c').mpr (flag_vanishing_at_cusp N h n _ hcusp F)

/-- **`r_B = 0` on `Γ(N) ∩ h⁻¹Bh`** (the standard flag over the plane cusp `h⁻¹Ph`; every flag group `gammaNBAt N k` arises this way with `h = k`). -/
theorem resTo_gammaNBAt_zero_of_cuspidal (hN : 3 ≤ N) (c' : H2 (Rep.of (gammaRho (gammaN N) n)))
    (hcusp : complexifyAt N h n (resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) c') ∈
      faceCuspidalInH2 N h n) :
    resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (gammaRho (gammaN N) n) c' = 0 :=
  resTo_flag_zero_of_cuspidal N n h 1 (TernaryPeriodPolynomials.Argument.GammaNFacesFull.faceFlagStab_one_map N hN h) c' hcusp

/-- **The dual `r_B = 0` row**: if the complexified plane restriction of `c'` at the cusp `ȷ(h)` is mixed cuspidal, then the flag restriction at `h⁻¹Bh` of the
`ȷ`-dual class `ȷ^* c'` vanishes (transport `dual_restrictions_transport.3` of `resTo_gammaNBAt_zero_of_cuspidal` at `ȷ(h)`). -/
theorem dual_rB_zero_of_cuspidal (hN : 3 ≤ N) (c' : H2 (Rep.of (gammaRho (gammaN N) n))) (h : SL(3, ℤ))
    (hcusp : complexifyAt N (jmath h) n (resTo (gammaNPAt N (jmath h)) (gammaNPAt_le N (jmath h)) (gammaRho (gammaN N) n) c') ∈
      faceCuspidalInH2 N (jmath h) n) :
    resTo (gammaNBAt N h) (gammaNBAt_le_N N h) (dualRhoN N n) (jPull N n c') = 0 := by
  rw [(dual_restrictions_transport (N := N) (n := n) c').2.2 h, resTo_gammaNBAt_zero_of_cuspidal N n (jmath h) hN c' hcusp]
  exact map_zero (pullBB N n h)

end Flag

end TernaryPeriodPolynomials.Argument.EisensteinDual
