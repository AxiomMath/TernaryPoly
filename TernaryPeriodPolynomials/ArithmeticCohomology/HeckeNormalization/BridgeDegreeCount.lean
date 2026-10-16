module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDegreeD
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftReindex
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDegreeOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDegreeIndex

@[expose] public section


noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeCount

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeOrbit
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeD (trace_sum)
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeAbar (exists_adm)

/-- The coefficient of a triangle in a chain. -/
def coef (v : P0) (t : Tri) : ℚ := MonoidAlgebra.coeffLinearEquiv ℚ v t

theorem coef_single (t t' : Tri) (r : ℚ) : coef (MonoidAlgebra.single t r) t' = if t = t' then r else 0 := by
  simp [coef, Finsupp.single_apply]

theorem coef_ρ (γ : IntegralGL) (v : P0) (t : Tri) : coef (P0.ρ γ v) (γ • t) = coef v t := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp [coef]
  | add a b ha hb => simp only [coef, map_add, Finsupp.add_apply] at ha hb ⊢; rw [ha, hb]
  | single u r =>
    rw [Representation.ofMulAction_single, coef_single, coef_single]
    simp [(MulAction.injective γ).eq_iff]

theorem coef_finite_support (v : P0) : (Function.support fun t => coef v t).Finite :=
  (MonoidAlgebra.coeffLinearEquiv ℚ v).support.finite_toSet.subset (by
    intro t ht
    simpa [coef] using ht)

theorem coef_add (a b : P0) (t : Tri) : coef (a + b) t = coef a t + coef b t := by
  simp [coef]

theorem eps_eq_finsum (v : P0) : (epsMap.hom v : ℚ) = ∑ᶠ t, coef v t := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp [coef]
  | add a b ha hb =>
    rw [map_add, ha, hb]
    rw [finsum_congr (coef_add a b), finsum_add_distrib (coef_finite_support a) (coef_finite_support b)]
  | single u r =>
    rw [epsMap_single]
    rw [finsum_eq_single _ u (fun t ht => by rw [coef_single, ite_eq_right (Ne.symm ht)]), coef_single, ite_eq_left rfl]

theorem pairT_eq_finsum (u v : P0) : pairT u v = ∑ᶠ t, coef u t * coef v t := by
  unfold pairT
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset _ (s := (MonoidAlgebra.coeffLinearEquiv ℚ u).support)]
  · rfl
  · intro t ht
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ht
    simpa [coef] using ht.1

theorem pairT_single_right (u : P0) (t' : Tri) : pairT u (MonoidAlgebra.single t' (1 : ℚ)) = coef u t' := by
  rw [pairT_eq_finsum, finsum_eq_single _ t' (fun t ht => by rw [coef_single, ite_eq_right (Ne.symm ht), mul_zero]),
    coef_single, ite_eq_left rfl, mul_one]

theorem pairT_single_left (t : Tri) (v : P0) : pairT (MonoidAlgebra.single t (1 : ℚ)) v = coef v t := by
  rw [pairT_eq_finsum, finsum_eq_single _ t (fun t' ht => by rw [coef_single, ite_eq_right (Ne.symm ht), zero_mul]),
    coef_single, ite_eq_left rfl, one_mul]

/-- The matrix of the dual lift `s₀`: the coefficient of `t` in `s₀ [t']`. -/
def cmat {p : ℕ} [Fact p.Prime] (s : DualLift p) (t t' : Tri) : ℚ := coef (s.s0 (MonoidAlgebra.single t' (1 : ℚ))) t

/-- Adjointness: the coefficient of `t'` in `lam₀ [t]` is `cmat t t'`. -/
theorem coef_lam {p : ℕ} [Fact p.Prime] (s : DualLift p) (l : LiftData p) (hl : l.IsAdjoint s) (t t' : Tri) :
    coef (l.lam0 (MonoidAlgebra.single t (1 : ℚ))) t' = cmat s t t' := by
  have := hl.1 (MonoidAlgebra.single t (1 : ℚ)) (MonoidAlgebra.single t' (1 : ℚ))
  rw [pairT_single_right, pairT_single_left] at this
  exact this

/-- Equivariance of the matrix: `c(σ t, f(σ) t') = c(t, t')`. -/
theorem cmat_equiv {p : ℕ} [Fact p.Prime] (s : DualLift p) (σ : (binDatum p).S) (t t' : Tri) :
    cmat s (σ.1 • t) ((binDatum p).f σ • t') = cmat s t t' := by
  unfold cmat
  have := s.eq0 σ (MonoidAlgebra.single t' (1 : ℚ))
  rw [Representation.ofMulAction_single] at this
  rw [this, coef_ρ]

section Count

variable {p : ℕ} [Fact p.Prime]

theorem lam_row_sum (s : DualLift p) (l : LiftData p) (hl : l.IsAdjoint s) (t : Tri) :
    (epsMap.hom (l.lam0 (MonoidAlgebra.single t (1 : ℚ))) : ℚ) = ∑ᶠ t', cmat s t t' := by
  rw [eps_eq_finsum]
  exact finsum_congr fun t' => coef_lam s l hl t t'

theorem s0_col_sum (s : DualLift p) (t' : Tri) :
    (epsMap.hom (s.s0 (MonoidAlgebra.single t' (1 : ℚ))) : ℚ) = ∑ᶠ t, cmat s t t' := by
  rw [eps_eq_finsum]
  rfl

theorem cmat_support_right (s : DualLift p) (l : LiftData p) (hl : l.IsAdjoint s) (t : Tri) :
    (Function.support fun t' => cmat s t t').Finite := by
  have : (fun t' => cmat s t t') = fun t' => coef (l.lam0 (MonoidAlgebra.single t (1 : ℚ))) t' :=
    funext fun t' => (coef_lam s l hl t t').symm
  rw [this]
  exact coef_finite_support _

theorem cmat_support_left (s : DualLift p) (t' : Tri) :
    (Function.support fun t => cmat s t t').Finite :=
  coef_finite_support _

/-- The row sums of the adjoint lift are constant (exactness of the Farey resolution). -/
theorem lam_const (l : LiftData p) (t : Tri) :
    epsMap.hom (l.lam0 (MonoidAlgebra.single t (1 : ℚ))) =
      epsMap.hom (l.lam0 (MonoidAlgebra.single triPlus (1 : ℚ))) := by
  have h0 : epsMap.hom (MonoidAlgebra.single t (1 : ℚ) - MonoidAlgebra.single triPlus (1 : ℚ) : P0) = 0 := by
    rw [map_sub, epsMap_single, epsMap_single]; ring
  obtain ⟨a, ha⟩ := exists_d1_preimage _ h0
  have h1 : epsMap.hom (l.lam0 (MonoidAlgebra.single t (1 : ℚ) - MonoidAlgebra.single triPlus (1 : ℚ) : P0)) = 0 := by
    rw [← ha]
    have := l.chain a
    change d1L (l.lam1 a) = l.lam0 (d1L a) at this
    have e : d1L a = d1.hom a := rfl
    rw [e] at this
    rw [← this]
    exact eps_d1 _
  rw [map_sub, map_sub] at h1
  exact sub_eq_zero.mp h1

/-- The kernel of the double counting: `T y x = c(x t₀, y⁻¹ t₀)`. -/
def Tker (s : DualLift p) (y x : IntegralGL) : ℚ := cmat s (x • triPlus) (y⁻¹ • triPlus)

theorem Tker_inv (s : DualLift p) (σ : (binDatum p).S) (y x : IntegralGL) :
    Tker s (y * (binDatum p).f σ) ((σ : IntegralGL)⁻¹ * x) = Tker s y x := by
  unfold Tker
  have h := cmat_equiv s σ⁻¹ (x • triPlus) (y⁻¹ • triPlus)
  rw [map_inv, Subgroup.coe_inv] at h
  rw [mul_inv_rev, mul_smul, mul_smul]
  exact h

theorem Tker_support_y (s : DualLift p) (l : LiftData p) (hl : l.IsAdjoint s) (x : IntegralGL) :
    (Function.support fun y => Tker s y x).Finite := by
  have h1 := preimage_finite (cmat_support_right s l hl (x • triPlus))
  have h2 : (fun y : IntegralGL => y⁻¹) ⁻¹' {y : IntegralGL | y • triPlus ∈
      Function.support fun t' => cmat s (x • triPlus) t'} |>.Finite := h1.preimage inv_injective.injOn
  exact h2.subset (fun y hy => hy)

theorem Tker_support_x (s : DualLift p) (y : IntegralGL) :
    (Function.support fun x => Tker s y x).Finite := by
  have h1 := preimage_finite (cmat_support_left s (y⁻¹ • triPlus))
  exact h1.subset (fun x hx => hx)

local instance finiteQuotKc : Finite (IntegralGL ⧸ (binDatum p).f.range) := finite_quot_f_range p

theorem trace_sum_Q (s : DualLift p) :
    ∑ᶠ Y : IntegralGL ⧸ (binDatum p).f.range,
      (epsMap.hom (s.s0 (MonoidAlgebra.single ((Quotient.out Y)⁻¹ • triPlus) (1 : ℚ))) : ℚ) =
      (Nat.card (IntegralGL ⧸ (binDatum p).f.range) : ℚ) := by
  obtain ⟨ξ, hξ⟩ := exists_adm
  have h := trace_sum p s hξ
  have : Fintype (IntegralGL ⧸ (binDatum p).f.range) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at h ⊢
  rw [Nat.card_eq_fintype_card] at h ⊢
  exact_mod_cast h

theorem lam_one (s : DualLift p) (l : LiftData p) (hl : l.IsAdjoint s) :
    epsMap.hom (l.lam0 (MonoidAlgebra.single triPlus (1 : ℚ))) = 1 := by
  set N : ℚ := (Nat.card (MulAction.stabilizer IntegralGL triPlus) : ℚ) with hN
  set lam0 : ℚ := epsMap.hom (l.lam0 (MonoidAlgebra.single triPlus (1 : ℚ))) with hlam
  have hre := sum_reindex (binDatum p).S (binDatum p).f (binDatum_f_injective p) (Tker s) (Tker_inv s)
    (Tker_support_y s l hl) (Tker_support_x s)
  have hL : ∀ X : RC (binDatum p).S, ∑ᶠ y, Tker s y (Quotient.out X) = N * lam0 := by
    intro X
    have e1 : ∑ᶠ y : IntegralGL, Tker s y (Quotient.out X) =
        ∑ᶠ y : IntegralGL, cmat s ((Quotient.out X) • triPlus) (y • triPlus) := by
      exact finsum_comp_equiv (Equiv.inv IntegralGL)
        (f := fun y : IntegralGL => cmat s ((Quotient.out X) • triPlus) (y • triPlus))
    rw [e1, finsum_orbit _ (cmat_support_right s l hl _), ← lam_row_sum s l hl, lam_const l]
  have hR : ∀ Y : IntegralGL ⧸ (binDatum p).f.range, ∑ᶠ x, Tker s (Quotient.out Y) x =
      N * epsMap.hom (s.s0 (MonoidAlgebra.single ((Quotient.out Y)⁻¹ • triPlus) (1 : ℚ))) := by
    intro Y
    rw [s0_col_sum]
    exact finsum_orbit (fun t => cmat s t ((Quotient.out Y)⁻¹ • triPlus)) (cmat_support_left s _)
  simp_rw [hL, hR] at hre
  have : Fintype (IntegralGL ⧸ (binDatum p).f.range) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at hre
  have hT := trace_sum_Q s
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hre
  simp only [finsum_eq_sum_of_fintype] at hT
  rw [hT] at hre
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hre
  have hcard : (Fintype.card (RC (binDatum p).S) : ℚ) = Nat.card (IntegralGL ⧸ (binDatum p).f.range) := by
    rw [← Nat.card_eq_fintype_card, BridgeDegreeIndex.card_rc_eq p]
  rw [hcard] at hre
  have hn : (Nat.card (IntegralGL ⧸ (binDatum p).f.range) : ℚ) ≠ 0 := by
    have : 0 < Nat.card (IntegralGL ⧸ (binDatum p).f.range) := Nat.card_pos
    exact_mod_cast this.ne'
  have hN0 : N ≠ 0 := by
    have := tri_stabilizer_finite triPlus
    have : 0 < Nat.card (MulAction.stabilizer IntegralGL triPlus) := Nat.card_pos
    rw [hN]; exact_mod_cast this.ne'
  have h2 : (Nat.card (IntegralGL ⧸ (binDatum p).f.range) : ℚ) * N * (lam0 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hn hN0)
  · linarith

/-- **L4**: the transposed lift covers the identity. -/
theorem L4_holds : L4 p := by
  intro s l hl t
  induction t using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single u r =>
    have h1 : (MonoidAlgebra.single u r : P0) = r • MonoidAlgebra.single u (1 : ℚ) := by
      rw [MonoidAlgebra.smul_single']; simp
    rw [h1, map_smul, map_smul, map_smul, lam_const l u, lam_one s l hl, epsMap_single]

end Count

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeDegreeCount
