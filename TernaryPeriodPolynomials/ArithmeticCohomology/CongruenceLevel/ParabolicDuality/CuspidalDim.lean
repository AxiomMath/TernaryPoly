module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalPotentials

@[expose] public section


/-!
# Dimension count for the cuspidal subspaces and the Poincaré-Lefschetz pairing

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

For `Γ = Γ(N)`, `N ≥ 3`, finite dimensional representations `A`, `A'` and a perfect invariant pairing `C`:
* `bdryEq`: the Farey differential `Φ ↦ dΦ` on strictly equivariant cusp functions (compactly supported cocycles that are boundaries of the
  boundary components); `Pperp` its annihilator in `C¹(A')`;
* `finrank_cuspidal_add (R1)`: `dim 𝒞(A') + dim (range bdryEq) = dim ker d_c(A)` (Poincaré-Lefschetz duality plus the cusp criterion);
* `finrank_cuspidal_le (R2)`: `dim 𝒞(A) + dim (range bdryEq) ≤ dim ker d_c(A)`, with equality exactly when every compactly supported
  cocycle is the Farey differential of a normalized twisted cusp function.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol Module
open scoped Classical

/-- Rank-nullity for a map out of a submodule (abstract, to avoid unification through the large cochain modules). -/
theorem finrank_rn {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    (P : Submodule ℂ V) (g : P →ₗ[ℂ] W) :
    finrank ℂ (LinearMap.range g) + finrank ℂ (LinearMap.ker g) = finrank ℂ P :=
  LinearMap.finrank_range_add_finrank_ker g

/-- Abstract form of the dimension count `dim 𝒞 + dim W = dim Kc`. -/
theorem finrank_range_add_of_inj {T K Q : Type} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
    [AddCommGroup K] [Module ℂ K] [AddCommGroup Q] [Module ℂ Q] (h : T →ₗ[ℂ] K) (hinj : Function.Injective h)
    (g : T →ₗ[ℂ] Q) (B : Submodule ℂ K) (hB : Submodule.map h (LinearMap.ker g) = B) :
    finrank ℂ (LinearMap.range g) + finrank ℂ B = finrank ℂ (LinearMap.range h) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : finrank ℂ (LinearMap.ker g) = finrank ℂ B := by
    rw [← hB]; exact (Submodule.equivMapOfInjective h hinj _).finrank_eq
  have h3 : finrank ℂ (LinearMap.range h) = finrank ℂ T := LinearMap.finrank_range_of_inj hinj
  omega

/-- Dimension of the image in a quotient of a submodule containing the divisor. -/
theorem finrank_map_mkQ_add {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P q : Submodule ℂ V)
    (hq : q ≤ P) : finrank ℂ (Submodule.map q.mkQ P) + finrank ℂ q = finrank ℂ P := by
  let g : P →ₗ[ℂ] V ⧸ q := q.mkQ.comp P.subtype
  have h1 := finrank_rn P g
  have hr : LinearMap.range g = Submodule.map q.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker g = Submodule.comap P.subtype q := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hk2 : finrank ℂ (LinearMap.ker g) = finrank ℂ q := by
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe hq).finrank_eq
  rw [hr, hk2] at h1
  exact h1

section Dim

variable {N : ℕ}

/-- The Farey differential `dΦ` of a strictly equivariant cusp function. -/
def bdryEq (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (gammaNGL N) E) :
    EqFn (gammaNGL N) RationalLine2 ρ →ₗ[ℂ] C1 ρ :=
  (bdryTw ρ hN).comp (Submodule.inclusion (eqFn_le_Tw ρ))

theorem bdryEq_apply (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (gammaNGL N) E)
    (Φ : EqFn (gammaNGL N) RationalLine2 ρ) : bdryEq hN ρ Φ = bdryTw ρ hN ⟨Φ.1, eqFn_le_Tw ρ Φ.2⟩ := rfl

/-- The annihilator in `C¹(A')` of the Farey differentials of strictly equivariant cusp functions of `A`. -/
def Pperp (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) : Submodule ℂ (C1 A'.ρ) :=
  perp (pV C (gammaNFareyData hN)) (LinearMap.range (bdryEq hN A.ρ))

theorem mem_Pperp (hN : 3 ≤ N) {A A' : Rep ℂ (gammaNGL N)} (C : Coupling A.ρ A'.ρ) {G : C1 A'.ρ} :
    G ∈ Pperp hN C ↔ ∀ Φ : EqFn (gammaNGL N) RationalLine2 A.ρ, pV C (gammaNFareyData hN) (bdryEq hN A.ρ Φ) G = 0 := by
  unfold Pperp
  rw [mem_perp]
  constructor
  · intro h Φ; exact h _ ⟨Φ, rfl⟩
  · rintro h _ ⟨Φ, rfl⟩; exact h Φ

theorem cohMap_eq_comp (A : Rep ℂ (gammaNGL N)) (D : FareyData (gammaNGL N)) :
    cohMap A = (cohIso A D).toLinearMap.comp (LinearMap.range (delta A.ρ)).mkQ := by
  ext F
  rfl

variable (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
  (C : Coupling A.ρ A'.ρ)

include hN in
/-- The class of a cochain is cuspidal iff it lies in `Pperp`. -/
theorem cohMap_mem_cuspidal_iff {G : C1 A'.ρ} : cohMap A' G ∈ cuspidalSub A' ↔ G ∈ Pperp hN C := by
  rw [cuspidal_iff_orth hN A A' C G, mem_Pperp]
  constructor
  · intro h Φ; exact h Φ.1 Φ.2
  · intro h Φ hΦ; exact h ⟨Φ, hΦ⟩

include hN in
theorem map_cohMap_Pperp : Submodule.map (cohMap A') (Pperp hN C) = cuspidalSub A' := by
  ext x
  constructor
  · rintro ⟨G, hG, rfl⟩
    exact (cohMap_mem_cuspidal_iff hN A A' C).mpr hG
  · intro hx
    have hobtain1 := cohMap_surjective A' (gammaNFareyData hN) x
    obtain ⟨G, rfl⟩ := hobtain1
    exact ⟨G, (cohMap_mem_cuspidal_iff hN A A' C).mp hx, rfl⟩


include hN in
theorem perp_ker_dc : perp (pV C (gammaNFareyData hN)) (LinearMap.ker (dc A.ρ)) = LinearMap.range (delta A'.ρ) := by
  ext G
  rw [mem_perp]
  constructor
  · intro h
    exact annihilator_ker_dc C (gammaNFareyData hN) G (fun F hF => h F (LinearMap.mem_ker.mpr hF))
  · rintro ⟨H', rfl⟩ F hF
    rw [pV_delta, LinearMap.mem_ker.mp hF]
    simp [pW]

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ A'] in
include hN in
theorem pV_perfect_left : ∀ F : C1 A.ρ, (∀ G : C1 A'.ρ, pV C (gammaNFareyData hN) F G = 0) → F = 0 :=
  fun F h => pair1_left_perfect C.e C.inv (gammaNFareyData hN) C.left F (fun G => h G)

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ A'] in
include hN in
theorem pV_perfect_right : ∀ G : C1 A'.ρ, (∀ F : C1 A.ρ, pV C (gammaNFareyData hN) F G = 0) → G = 0 :=
  fun G h => pair1_right_perfect C.e C.inv (gammaNFareyData hN) C.right G (fun F => h F)

include hN C in
/-- **(R1)** `dim 𝒞(A') + dim (Farey differentials of cusp functions of A) = dim (compactly supported cocycles of A)`. -/
theorem finrank_cuspidal_add :
    finrank ℂ (cuspidalSub A') + finrank ℂ (LinearMap.range (bdryEq hN A.ρ)) = finrank ℂ (LinearMap.ker (dc A.ρ)) := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  have := c1_finite (ρ := A'.ρ) (gammaNFareyData hN)
  have ha := finrank_perp (pV C (gammaNFareyData hN)) (pV_perfect_left hN A A' C) (pV_perfect_right hN A A' C)
    (LinearMap.ker (dc A.ρ))
  rw [perp_ker_dc hN A A' C] at ha
  have hb := finrank_perp (pV C (gammaNFareyData hN)) (pV_perfect_left hN A A' C) (pV_perfect_right hN A A' C)
    (LinearMap.range (bdryEq hN A.ρ))
  have hb' : finrank ℂ (Pperp hN C) + finrank ℂ (LinearMap.range (bdryEq hN A.ρ)) = finrank ℂ (C1 A.ρ) := hb
  have hle : LinearMap.range (delta A'.ρ) ≤ Pperp hN C := by
    rintro G ⟨H, rfl⟩
    rw [← cohMap_mem_cuspidal_iff hN A A' C]
    have : cohMap A' (delta A'.ρ H) = 0 := (cohMap_eq_zero_iff A' _).mpr ⟨H, rfl⟩
    rw [this]; exact Submodule.zero_mem _
  have hc : finrank ℂ (cuspidalSub A') + finrank ℂ (LinearMap.range (delta A'.ρ)) = finrank ℂ (Pperp hN C) := by
    have h1 := finrank_map_mkQ_add (Pperp hN C) (LinearMap.range (delta A'.ρ)) hle
    have hr : finrank ℂ (cuspidalSub A') = finrank ℂ (Submodule.map (LinearMap.range (delta A'.ρ)).mkQ (Pperp hN C)) := by
      rw [← map_cohMap_Pperp hN A A' C, cohMap_eq_comp A' (gammaNFareyData hN), Submodule.map_comp]
      exact LinearEquiv.finrank_map_eq (cohIso A' (gammaNFareyData hN)) _
    rw [hr]; exact h1
  omega

section Tn

variable {E : Type} [AddCommGroup E] [Module ℂ E]

/-- The normalized twisted cusp functions (vanishing at `cusp₁`). -/
def Tn (ρ : Representation ℂ (gammaNGL N) E) : Submodule ℂ (Tw ρ) :=
  LinearMap.ker ((LinearMap.proj cusp1 : (RationalLine2 → E) →ₗ[ℂ] E).comp (Tw ρ).subtype)

theorem mem_Tn {ρ : Representation ℂ (gammaNGL N) E} {Φ : Tw ρ} : Φ ∈ Tn ρ ↔ Φ.1 cusp1 = 0 := by
  simp [Tn]

/-- The Farey differential on normalized twisted cusp functions. -/
def hT (hN : 3 ≤ N) (ρ : Representation ℂ (gammaNGL N) E) : Tn ρ →ₗ[ℂ] C1 ρ := (bdryTw ρ hN).comp (Tn ρ).subtype

end Tn

theorem injective_of_ker_eq_zero {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (h : ∀ v, f v = 0 → v = 0) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact h

theorem hT_inj (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) : Function.Injective (hT hN A.ρ) :=
  injective_of_ker_eq_zero (V := Tn A.ρ) (W := C1 A.ρ) (hT hN A.ρ) fun (Φ : Tn A.ρ) hΦ => by
    have h0 : Φ.1.1 cusp1 = 0 := mem_Tn.mp Φ.2
    exact Subtype.ext (bdryTw_injOn hN A h0 hΦ)

theorem range_hT_le (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) : LinearMap.range (hT hN A.ρ) ≤ LinearMap.ker (dc A.ρ) := by
  rintro _ ⟨Φ, rfl⟩
  exact LinearMap.mem_ker.mpr (dc_bdryTw A.ρ hN Φ.1)

/-- The class map on normalized twisted cusp functions, valued in the quotient model of `H¹`. -/
def gq (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) : Tn A.ρ →ₗ[ℂ] Hq A.ρ :=
  ((cohIso A (gammaNFareyData hN)).symm : groupCohomology.H1 A →ₗ[ℂ] Hq A.ρ).comp ((mTw A).comp (Tn A.ρ).subtype)

theorem range_gq (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) :
    LinearMap.range (gq hN A) = Submodule.map ((cohIso A (gammaNFareyData hN)).symm : groupCohomology.H1 A →ₗ[ℂ] Hq A.ρ) (cuspidalSub A) := by
  ext z
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨mTw A Φ.1, mTw_mem_cuspidal A Φ.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hobtain2 := exists_Tn_of_cuspidal hN A hx
    obtain ⟨Φ, h0, hΦ⟩ := hobtain2
    exact ⟨⟨Φ, mem_Tn.mpr h0⟩, by simp [gq, hΦ]⟩

theorem map_hT_ker_gq (hN : 3 ≤ N) (A : Rep ℂ (gammaNGL N)) :
    Submodule.map (hT hN A.ρ) (LinearMap.ker (gq hN A)) = LinearMap.range (bdryEq hN A.ρ) := by
  ext F
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    have hm : mTw A Φ.1 = 0 := by
      have : (cohIso A (gammaNFareyData hN)).symm (mTw A Φ.1) = 0 := hΦ
      simpa using this
    have hobtain3 := ker_mTw A Φ.1 (mem_Tn.mp Φ.2) hm
    obtain ⟨Ψ, hΨ, hΦΨ⟩ := hobtain3
    refine ⟨⟨Ψ, hΨ⟩, ?_⟩
    have hfun : Φ.1.1 = fun x => Ψ x - Ψ cusp1 := funext hΦΨ
    rw [bdryEq_apply]
    change _ = bdryTw A.ρ hN Φ.1
    have : Φ.1 = ⟨fun x => Ψ x - Ψ cusp1, shift_mem_Tw A hΨ _⟩ := Subtype.ext hfun
    rw [this, bdryTw_shift hN A hΨ]
  · rintro ⟨Ψ, rfl⟩
    refine ⟨⟨⟨fun x => Ψ.1 x - Ψ.1 cusp1, shift_mem_Tw A Ψ.2 _⟩, mem_Tn.mpr (by simp)⟩, ?_, ?_⟩
    · change (cohIso A (gammaNFareyData hN)).symm (mTw A ⟨fun x => Ψ.1 x - Ψ.1 cusp1, shift_mem_Tw A Ψ.2 _⟩) = 0
      rw [mTw_shift A Ψ.2, map_zero]
    · change bdryTw A.ρ hN ⟨fun x => Ψ.1 x - Ψ.1 cusp1, shift_mem_Tw A Ψ.2 _⟩ = _
      rw [bdryTw_shift hN A Ψ.2]
      rfl

include hN in
/-- **(R2)** `dim 𝒞(A) + dim (Farey differentials of cusp functions) = dim (Farey differentials of normalized twisted cusp functions)`. -/
theorem finrank_cuspidal_eq_range_hT :
    finrank ℂ (cuspidalSub A) + finrank ℂ (LinearMap.range (bdryEq hN A.ρ)) = finrank ℂ (LinearMap.range (hT hN A.ρ)) := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  have : FiniteDimensional ℂ (Tn A.ρ) := Module.Finite.of_injective (hT hN A.ρ) (hT_inj hN A)
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := ↥(Tn A.ρ)) (V₂ := Hq A.ρ)
    (gq hN A)
  have h3 : finrank ℂ (LinearMap.ker (gq hN A)) = finrank ℂ (LinearMap.range (bdryEq hN A.ρ)) := by
    rw [← map_hT_ker_gq hN A]
    exact (Submodule.equivMapOfInjective (hT hN A.ρ) (hT_inj hN A) _).finrank_eq
  have h4 : finrank ℂ (LinearMap.range (hT hN A.ρ)) = finrank ℂ (Tn A.ρ) :=
    LinearMap.finrank_range_of_inj (hT_inj hN A)
  have h2 : finrank ℂ (LinearMap.range (gq hN A)) = finrank ℂ (cuspidalSub A) := by
    rw [range_gq]
    exact LinearEquiv.finrank_map_eq (cohIso A (gammaNFareyData hN)).symm _
  omega

include hN C in
/-- **The dimension count.**  The two cuspidal subspaces have the same dimension, and every compactly supported Farey cocycle is the
Farey differential of a normalized twisted cusp function (on both sides). -/
theorem cuspidal_dims :
    finrank ℂ (cuspidalSub A) = finrank ℂ (cuspidalSub A') ∧
      LinearMap.range (hT hN A.ρ) = LinearMap.ker (dc A.ρ) ∧ LinearMap.range (hT hN A'.ρ) = LinearMap.ker (dc A'.ρ) := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  have := c1_finite (ρ := A'.ρ) (gammaNFareyData hN)
  have h1 := finrank_cuspidal_add hN A A' C
  have h1' := finrank_cuspidal_add hN A' A C.flip
  have h2 := finrank_cuspidal_eq_range_hT hN A
  have h2' := finrank_cuspidal_eq_range_hT hN A'
  have hc1 := Submodule.finrank_mono (range_hT_le hN A)
  have hc2 := Submodule.finrank_mono (range_hT_le hN A')
  have hcc : finrank ℂ (cuspidalSub A) = finrank ℂ (cuspidalSub A') := by omega
  refine ⟨hcc, ?_, ?_⟩
  · exact Submodule.eq_of_le_of_finrank_eq (range_hT_le hN A) (by omega)
  · exact Submodule.eq_of_le_of_finrank_eq (range_hT_le hN A') (by omega)

end Dim
