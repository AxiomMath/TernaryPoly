module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeAbarSym
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftFinite

@[expose] public section


/-!
# The functional `D` of the degree computation (L4)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeD

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

variable (p : ℕ) [Fact p.Prime]

local instance finiteQuotK : Finite (IntegralGL ⧸ (binDatum p).f.range) := finite_quot_f_range p

theorem det_C1_inv_pos : 0 < (((C1 p)⁻¹.val.det : ℚ) : ℝ) := by
  have : ((C1 p)⁻¹.val.det : ℚ) = (p : ℚ) := by
    simp [C1, Matrix.det_fin_two]
  rw [this]
  have : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact_mod_cast this

theorem det_C1_pos : 0 < (((C1 p).val.det : ℚ) : ℝ) := by
  rw [det_C1]
  have : (0 : ℚ) < (p : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  exact_mod_cast this

/-- The functional `D_ξ = Ā_ξ ∘ s₁ - Ā_{gξ}` on `P1`. -/
def Dfun (s : DualLift p) (ξ : Fin 2 → ℝ) : P1 →ₗ[ℚ] ℝ :=
  (abarL ξ).comp (antiSub.subtype ∘ₗ s.s1) - (abarL (actG (C1 p) ξ)).comp antiSub.subtype

theorem Dfun_apply (s : DualLift p) (ξ : Fin 2 → ℝ) (x : P1) :
    Dfun p s ξ x = abarL ξ ((s.s1 x : P1) : PE) - abarL (actG (C1 p) ξ) (x : PE) := rfl

/-- Change of reference vector does not change `D` on `P1` (the symbol of `s₁ x` is `g⁻¹` times that of `x`). -/
theorem Dfun_indep (s : DualLift p) {a b : Fin 2 → ℝ} (ha : Adm a) (hb : Adm b) (x : P1) :
    Dfun p s a x = Dfun p s b x := by
  rw [Dfun_apply, Dfun_apply]
  have h1 := abarL_sub ha hb ((s.s1 x : P1) : PE)
  have h2 := abarL_sub (ha.act (C1 p)) (hb.act (C1 p)) (x : PE)
  have hs : (piT.hom ((s.s1 x : P1) : PE)).val = (divisorAction (C1 p)⁻¹ (piT.hom (x : PE)).val) := by
    have := s.symbol x
    change piT.hom ((s.s1 x : P1) : PE) = action (C1 p)⁻¹ (piT.hom (x : PE)) at this
    rw [this]; rfl
  rw [hs, Hlin_act ha hb _ (det_C1_inv_pos p), inv_inv] at h1
  linarith

/-- `D` is invariant under `K = f(S)`. -/
theorem Dfun_K (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (σ : (binDatum p).S) (x : P1) :
    Dfun p s ξ (P1.ρ ((binDatum p).f σ) x) = Dfun p s ξ x := by
  have hξ' : Adm (actG (binIota σ.1⁻¹) ξ) := hξ.act _
  have e1 : abarL ξ ((s.s1 (P1.ρ ((binDatum p).f σ) x) : P1) : PE) =
      abarL (actG (binIota σ.1⁻¹) ξ) ((s.s1 x : P1) : PE) := by
    rw [s.eq1 σ x]
    exact abarL_equiv ξ σ.1 _
  have e2 : abarL (actG (C1 p) ξ) ((P1.ρ ((binDatum p).f σ) x : P1) : PE) =
      abarL (actG (C1 p) (actG (binIota σ.1⁻¹) ξ)) (x : PE) := by
    change abarL (actG (C1 p) ξ) (PE.ρ ((binDatum p).f σ) (x : PE)) = _
    rw [abarL_equiv]
    congr 1
    have hm : (binIota ((binDatum p).f σ))⁻¹ * C1 p = C1 p * binIota σ.1⁻¹ := by
      rw [(binDatum p).hf σ, map_inv]
      group
    rw [map_inv, ← actG_mul, hm, actG_mul]
  rw [Dfun_apply, e1, e2, ← Dfun_apply, Dfun_indep p s hξ' hξ]

theorem Dfun_beta (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (u : P0) :
    Dfun p s ξ (betaL u) = 2 * (((epsMap.hom u : ℚ) : ℝ) - ((epsMap.hom (s.s0 u) : ℚ) : ℝ)) := by
  rw [Dfun_apply, ← s.chain]
  have h1 := abarL_bdryMap hξ (s.s0 u)
  have h2 := abarL_bdryMap (hξ.act (C1 p)) u
  change abarL ξ (bdryMap.hom (s.s0 u)) - abarL (actG (C1 p) ξ) (bdryMap.hom u) = _
  rw [h1, h2]; ring

/-- A right-`K`-invariant function summed over `G/K` is invariant under left translation. -/
theorem finsum_quot_translate {G : Type*} [Group G] (K : Subgroup G) (F : G → ℝ)
    (hF : ∀ (y : G) (κ : K), F (y * κ) = F y) (γ : G) :
    ∑ᶠ Y : G ⧸ K, F (γ * Quotient.out Y) = ∑ᶠ Y : G ⧸ K, F (Quotient.out Y) := by
  have h : ∀ Y : G ⧸ K, F (γ * Quotient.out Y) = F (Quotient.out (γ • Y)) := by
    intro Y
    have hY : (QuotientGroup.mk (Quotient.out Y) : G ⧸ K) = Y := QuotientGroup.out_eq' Y
    have hsm : γ • Y = (QuotientGroup.mk (γ * Quotient.out Y) : G ⧸ K) := by
      conv_lhs => rw [← hY]
      rfl
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul K (γ * Quotient.out Y)
    rw [hsm, hκ, hF]
  simp_rw [h]
  exact finsum_comp_equiv (MulAction.toPerm γ) (f := fun Y : G ⧸ K => F (Quotient.out Y))

theorem P1_ρ_val (γ : IntegralGL) (x : P1) : ((P1.ρ γ x : P1) : PE) = PE.ρ γ (x : PE) := rfl

/-- The `K\Γ`-trace of `D`. -/
def Dhat (s : DualLift p) (ξ : Fin 2 → ℝ) (x : P1) : ℝ :=
  ∑ᶠ Y : IntegralGL ⧸ (binDatum p).f.range, Dfun p s ξ (P1.ρ (Quotient.out Y)⁻¹ x)

theorem P1_ρ_mul (γ δ : IntegralGL) (x : P1) : P1.ρ (γ * δ) x = P1.ρ γ (P1.ρ δ x) := by
  rw [map_mul]; rfl

theorem Dfun_range (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (κ : IntegralGL)
    (hκ : κ ∈ (binDatum p).f.range) (x : P1) : Dfun p s ξ (P1.ρ κ x) = Dfun p s ξ x := by
  obtain ⟨σ, rfl⟩ := hκ
  exact Dfun_K p s hξ σ x

theorem Dhat_inv (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) (γ : IntegralGL) (x : P1) :
    Dhat p s ξ (P1.ρ γ x) = Dhat p s ξ x := by
  unfold Dhat
  have hF : ∀ (y : IntegralGL) (κ : (binDatum p).f.range),
      (fun y : IntegralGL => Dfun p s ξ (P1.ρ y⁻¹ x)) (y * κ) = (fun y : IntegralGL => Dfun p s ξ (P1.ρ y⁻¹ x)) y := by
    intro y κ
    show Dfun p s ξ (P1.ρ (y * κ)⁻¹ x) = Dfun p s ξ (P1.ρ y⁻¹ x)
    rw [mul_inv_rev, P1_ρ_mul]
    exact Dfun_range p s hξ _ ((binDatum p).f.range.inv_mem κ.2) _
  have := finsum_quot_translate (binDatum p).f.range (fun y : IntegralGL => Dfun p s ξ (P1.ρ y⁻¹ x)) hF γ⁻¹
  rw [← this]
  refine finsum_congr fun Y => ?_
  rw [mul_inv_rev, inv_inv, ← P1_ρ_mul]

theorem Dhat_add (s : DualLift p) (ξ : Fin 2 → ℝ) (x y : P1) :
    Dhat p s ξ (x + y) = Dhat p s ξ x + Dhat p s ξ y := by
  unfold Dhat
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun Y => by rw [map_add, map_add]

theorem Dhat_neg (s : DualLift p) (ξ : Fin 2 → ℝ) (x : P1) : Dhat p s ξ (-x) = - Dhat p s ξ x := by
  unfold Dhat
  rw [← finsum_neg_distrib]
  exact finsum_congr fun Y => by rw [map_neg, map_neg]

theorem P1_sOne_E0 : P1.ρ sOne E0 = -E0 := by
  apply Subtype.ext
  change PE.ρ sOne ((MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) : PE)) =
    -(MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) : PE)
  rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, sOne_smul_p0,
    show sOne • p0.swap = p0 by rw [← OTE.swap_smul, sOne_smul_p0, OTE.swap_swap]]
  abel

theorem Dhat_E0 (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) : Dhat p s ξ E0 = 0 := by
  have h := Dhat_inv p s hξ sOne E0
  rw [P1_sOne_E0, Dhat_neg] at h
  linarith

theorem betaL_triPlus : betaL (MonoidAlgebra.single triPlus (1 : ℚ)) =
    -(E0 + P1.ρ rho E0 + P1.ρ rho2 E0) := by
  apply Subtype.ext
  have h1 : ((betaL (MonoidAlgebra.single triPlus (1 : ℚ)) : P1) : PE) = bdryV triPlus := by
    change bdryMap.hom (MonoidAlgebra.single triPlus (1 : ℚ)) = _
    rw [bdryMap_single, one_smul]
  rw [h1]
  unfold bdryV
  rw [sum_nbF_triPlus]
  change _ = -(((E0 : P1) : PE) + PE.ρ rho ((E0 : P1) : PE) + PE.ρ rho2 ((E0 : P1) : PE))
  change _ = -((MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) : PE) +
    PE.ρ rho (MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) : PE) +
    PE.ρ rho2 (MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) : PE))
  simp only [map_sub, Representation.ofMulAction_single, ← OTE.swap_smul]
  abel

theorem Dhat_beta_triPlus (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) :
    Dhat p s ξ (betaL (MonoidAlgebra.single triPlus (1 : ℚ))) = 0 := by
  rw [betaL_triPlus, Dhat_neg, Dhat_add, Dhat_add, Dhat_inv p s hξ, Dhat_inv p s hξ, Dhat_E0 p s hξ]
  simp

theorem betaL_ρ (γ : IntegralGL) (u : P0) : betaL (P0.ρ γ u) = P1.ρ γ (betaL u) := by
  apply Subtype.ext
  change bdryMap.hom (P0.ρ γ u) = PE.ρ γ (bdryMap.hom u)
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | single t r =>
    rw [Representation.ofMulAction_single, bdryMap_single, bdryMap_single, bdryV_smul, map_smul]

/-- **Trace identity.**  The `K\Γ`-average of `ε ∘ s₀` over the translates of the base triangle is `1`. -/
theorem trace_sum (s : DualLift p) {ξ : Fin 2 → ℝ} (hξ : Adm ξ) :
    ∑ᶠ Y : IntegralGL ⧸ (binDatum p).f.range,
      ((epsMap.hom (s.s0 (MonoidAlgebra.single ((Quotient.out Y)⁻¹ • triPlus) (1 : ℚ))) : ℚ) : ℝ) =
      (Nat.card (IntegralGL ⧸ (binDatum p).f.range) : ℝ) := by
  have h := Dhat_beta_triPlus p s hξ
  unfold Dhat at h
  have hY : ∀ Y : IntegralGL ⧸ (binDatum p).f.range,
      Dfun p s ξ (P1.ρ (Quotient.out Y)⁻¹ (betaL (MonoidAlgebra.single triPlus (1 : ℚ)))) =
      2 * (1 - ((epsMap.hom (s.s0 (MonoidAlgebra.single ((Quotient.out Y)⁻¹ • triPlus) (1 : ℚ))) : ℚ) : ℝ)) := by
    intro Y
    rw [← betaL_ρ, Dfun_beta p s hξ, Representation.ofMulAction_single, epsMap_single]
    simp
  simp_rw [hY] at h
  have : Fintype (IntegralGL ⧸ (binDatum p).f.range) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at h ⊢
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card]
  rcases mul_eq_zero.mp h with h2 | h2
  · norm_num at h2
  · linarith

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeD
