module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeMixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.PairingLifts
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeUniq
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FlagDictionary

@[expose] public section


/-!
# The induced class of a level-`M` class with zero flag restrictions has zero flag restrictions at level 6

Formalized by Claude Sonnet 5.5.

`Δ6 M = Γ(M)` as a subgroup of `Γ(6)`; `c₀ ∈ H²(Γ(M), E)` with zero flag restrictions; `transportΔ c₀` its transport to `H²(Δ6 M, E)` along `Δ6 M ≅ Γ(M)` (generic in the
representations `ρ` of `Γ(6)` and `ρM` of `Γ(M)` that agree on `Δ6 M`).  For a subgroup `K` of `Γ(6)` contained in a flag group `Γ(6) ∩ g₀⁻¹ B g₀` the Mackey pull-backs
`κ_u^*` of the transport on `K ∩ uΔu⁻¹` vanish (`pullback_flag_zero`): `u⁻¹(K ∩ Δ)u ⊂ Γ(M) ∩ (g₀u)⁻¹ B (g₀u)`, a flag group of level `M`, where `c₀` restricts to zero.
Hence every induced class `c_V` (`PhiH c_V = transportΔ c₀`) has zero flag restrictions at level 6 (`res_flag_ind_zero`), and by the `lineMixedSub_of_zeroFlags`,
`planeMixedSub_of_zeroFlags` it restricts to a mixed class of every face.
-/

open CategoryTheory
open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.SeedC3

section Pullback

variable (M : ℕ) [NeZero M] (n : ℕ)

/-- `Γ(M)` as a subgroup of `Γ(6)`. -/
def Δ6 : Subgroup ↥(gammaN 6) := (gammaN M).subgroupOf (gammaN 6)

/-- The isomorphism-onto-image `Δ6 M → Γ(M)`. -/
def eΔ : ↥(Δ6 M) →* ↥(gammaN M) where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

instance Δ6_finiteIndex : (Δ6 M).FiniteIndex := inferInstanceAs ((gammaN M).subgroupOf (gammaN 6)).FiniteIndex

omit [NeZero M] in
/-- Membership in the flag group of level `M` at `g₀ u` of a Mackey-conjugated element of a subgroup of the flag group of level `6` at `g₀`. -/
theorem conj_mem_gammaNBAt (g₀ : SL(3, ℤ)) (K : Subgroup ↥(gammaN 6)) (hK : ∀ k ∈ K, (k : SL(3, ℤ)) ∈ gammaNBAt 6 g₀)
    (u : ↥(gammaN 6)) (k : ↥(stabAt (Δ6 M) K u)) :
    ((u⁻¹ * k.val * u : ↥(gammaN 6)) : SL(3, ℤ)) ∈ gammaNBAt M (g₀ * (u : SL(3, ℤ))) := by
  have hk1 : (k.val : SL(3, ℤ)) ∈ gammaNBAt 6 g₀ := hK _ k.2.1
  have hk2 : ((u⁻¹ * k.val * u : ↥(gammaN 6)) : SL(3, ℤ)) ∈ gammaN M := k.2.2
  rw [mem_gammaNBAt] at hk1 ⊢
  have e : g₀ * (u : SL(3, ℤ)) * ((u⁻¹ * k.val * u : ↥(gammaN 6)) : SL(3, ℤ)) * (g₀ * (u : SL(3, ℤ)))⁻¹ =
      g₀ * (k.val : SL(3, ℤ)) * g₀⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hk1).2⟩
  have := (gammaN_normal M).conj_mem _ hk2 (g₀ * (u : SL(3, ℤ)))
  have e2 : g₀ * (u : SL(3, ℤ)) * ((u⁻¹ * k.val * u : ↥(gammaN 6)) : SL(3, ℤ)) * (g₀ * (u : SL(3, ℤ)))⁻¹ =
      g₀ * (k.val : SL(3, ℤ)) * g₀⁻¹ := e
  rw [e2] at this
  exact this

/-- The Mackey conjugation, landing in the flag group of level `M` at `g₀ u`. -/
def flagConj (g₀ : SL(3, ℤ)) (K : Subgroup ↥(gammaN 6)) (hK : ∀ k ∈ K, (k : SL(3, ℤ)) ∈ gammaNBAt 6 g₀)
    (u : ↥(gammaN 6)) : ↥(stabAt (Δ6 M) K u) →* ↥(gammaNBAt M (g₀ * (u : SL(3, ℤ)))) where
  toFun k := ⟨((u⁻¹ * k.val * u : ↥(gammaN 6)) : SL(3, ℤ)), conj_mem_gammaNBAt M g₀ K hK u k⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])


section CompZero

variable {K H G : Type} [Group K] [Group H] [Group G]

theorem h2Map_comp_zero (α₁ : H →* G) (α₂ : K →* H) (A : Rep ℂ G) (B : Rep ℂ H) (C : Rep ℂ K)
    (T₁ : A →ₗ[ℂ] B) (hT₁ : ∀ (g : H) (v : A), T₁ (A.ρ (α₁ g) v) = B.ρ g (T₁ v))
    (T₂ : B →ₗ[ℂ] C) (hT₂ : ∀ (g : K) (v : B), T₂ (B.ρ (α₂ g) v) = C.ρ g (T₂ v))
    (x : groupCohomology.H2 A) (hx : EdgeNat.h2Map α₁ A B T₁ hT₁ x = 0) :
    EdgeNat.h2Map (α₁.comp α₂) A C (T₂ ∘ₗ T₁) (compHT α₁ α₂ A B C T₁ hT₁ T₂ hT₂) x = 0 := by
  rw [← h2Map_comp α₁ α₂ A B C T₁ hT₁ T₂ hT₂ x, hx, map_zero]

end CompZero

section Generic

variable {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E)
  (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

omit [NeZero M] in
include hρ in
theorem eΔ_hT (g : ↥(Δ6 M)) (v : E) :
    (LinearMap.id : E →ₗ[ℂ] E) ((Rep.of ρM).ρ (eΔ M g) v) = (Rep.of (ρ.comp (Δ6 M).subtype)).ρ g (LinearMap.id (R := ℂ) (M := E) v) := by
  change ρM (eΔ M g) v = ρ g.1 v
  rw [hρ g]

/-- The transport of a level-`M` class to a class of `H²(Δ6 M, E)` along `Δ6 M ≅ Γ(M)`. -/
def transportΔ (c₀ : groupCohomology.H2 (Rep.of ρM)) : groupCohomology.H2 (Rep.of (ρ.comp (Δ6 M).subtype)) :=
  EdgeNat.h2Map (eΔ M) (Rep.of ρM) (Rep.of (ρ.comp (Δ6 M).subtype)) LinearMap.id (eΔ_hT M ρ ρM hρ) c₀

omit [NeZero M] in
include hρ in
/-- **The Mackey pull-backs of the transport of `c₀` on the subgroups of a level-6 flag group vanish when `c₀` has zero flag restrictions.** -/
theorem pullback_flag_zero (c₀ : groupCohomology.H2 (Rep.of ρM))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN M g)) (Rep.of ρM) c₀ = 0)
    (g₀ : SL(3, ℤ)) (K : Subgroup ↥(gammaN 6)) (hK : ∀ k ∈ K, (k : SL(3, ℤ)) ∈ gammaNBAt 6 g₀) (u : ↥(gammaN 6)) :
    EdgeNat.h2Map (kappa (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u))
      (Rep.of (ρ.comp (Δ6 M).subtype)) (Rep.of (ρ.comp (stabAt (Δ6 M) K u).subtype)) (ρ u)
      (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u)) (transportΔ M ρ ρM hρ c₀) = 0 := by
  have h0 : EdgeNat.h2Map (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))) (Rep.of ρM)
      (Rep.res (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))) (Rep.of ρM)) LinearMap.id (fun _ _ => rfl) c₀ = 0 :=
    hz (g₀ * (u : SL(3, ℤ)))
  have e2 := h2Map_comp_zero (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))) (flagConj M g₀ K hK u)
    (Rep.of ρM) (Rep.res (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))) (Rep.of ρM))
    (Rep.of (ρ.comp (stabAt (Δ6 M) K u).subtype))
    LinearMap.id (fun _ _ => rfl) (ρ u)
    (fun g v => by
      have h := kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u) g v
      have h2 : ((Rep.res (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))) (Rep.of ρM)).ρ
          (flagConj M g₀ K hK u g)) v =
          ((Rep.of (ρ.comp (Δ6 M).subtype)).ρ (kappa (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u) g)) v :=
        congrArg (fun f => f v) (hρ (kappa (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u) g))
      rw [h2]
      exact h) c₀ h0
  have e1 := h2Map_comp (eΔ M) (kappa (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u)) (Rep.of ρM)
    (Rep.of (ρ.comp (Δ6 M).subtype)) (Rep.of (ρ.comp (stabAt (Δ6 M) K u).subtype))
    LinearMap.id (eΔ_hT M ρ ρM hρ) (ρ u) (kappa_hT ρ (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u)) c₀
  have hα : (eΔ M).comp (kappa (Δ6 M) (stabAt (Δ6 M) K u) u (stabAt_hu (Δ6 M) K u)) =
      (Subgroup.inclusion (gammaNBAt_le_gammaN M (g₀ * (u : SL(3, ℤ))))).comp (flagConj M g₀ K hK u) := by
    ext k; rfl
  unfold transportΔ
  refine e1.trans ?_
  exact (h2Map_congr hα _ _ _ _ rfl c₀).trans e2

include hρ in
/-- **The induced class of a level-`M` class with zero flag restrictions has zero flag restrictions at level 6**: `c_V` with `PhiH c_V = transportΔ c₀`
restricts to zero on every flag group `Γ(6) ∩ g⁻¹ B g`. -/
theorem res_flag_ind_zero (c₀ : groupCohomology.H2 (Rep.of ρM))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN M g)) (Rep.of ρM) c₀ = 0)
    (cV : groupCohomology.H2 (Rep.of (permRep ρ (Δ6 M)))) (hcV : PhiH ρ (Δ6 M) cV = transportΔ M ρ ρM hρ c₀) (g : SL(3, ℤ)) :
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp)) (Rep.of (permRep ρ (Δ6 M))) cV = 0 :=
  res_hom_eq_zero_of_pullbacks ρ (Δ6 M) _ (transportΔ M ρ ρM hρ c₀) cV hcV fun u =>
    pullback_flag_zero M ρ ρM hρ c₀ hz g _ (fun k hk => by obtain ⟨y, rfl⟩ := hk; exact y.2) u

end Generic

end Pullback

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
