module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftData

@[expose] public section


/-!
# Unfolding lemmas for the edge-coefficient formula (L5)

Formalized by Claude Sonnet 5.5.

* `coeff_PE_ρ`, `pairE_*`, `EeL`, `adj_coeff`: coefficients of the permutation module `PE` and the adjointness `coeff_e (λ₁ E_{e'}) = coeff_{e'} (s₁ E_e)`
  for a transposed lift;
* `SS F c = ∑ᶠ_ε c(ε p₀) F(ε)`, with `evalP_mk_eq` (**U1**): `evalP [m ⊗ c] = SS (ε ↦ ε⁻¹ m) c`, and `phi_formula` (**U2**):
  `2 nP Φ(c) = SS (ε ↦ ε Φ(E₀)) c` for every `Γ`-equivariant `Φ : P1 → N`.
-/

open CategoryTheory Representation

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

section Basic

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.BinaryDuality

theorem coeff_PE_ρ (γ : IntegralGL) (c : PE) (e : OTE) : (PE.ρ γ c).coeff e = c.coeff (γ⁻¹ • e) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, ha, hb]
  | single q r =>
    have h1 : PE.ρ γ (MonoidAlgebra.single q r) = MonoidAlgebra.single (γ • q) r :=
      Representation.ofMulAction_single γ q r
    rw [h1, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    have : (γ • q = e) ↔ (q = γ⁻¹ • e) := by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp only [this]

example (d : ℕ) : Dplain d = Rep.res binIota (binMod d) := rfl

theorem pairE_single_right (u : PE) (e : OTE) (r : ℚ) :
    pairE u (MonoidAlgebra.single e r) = u.coeff e * r := by
  unfold pairE
  change (u.coeff).sum (fun t a => a * (MonoidAlgebra.single e r : PE).coeff t) = _
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finsupp.sum_eq_single e (fun t _ ht => by simp [Ne.symm ht]) (fun h => by simp)]
  simp

theorem pairE_add_right (u v w : PE) : pairE u (v + w) = pairE u v + pairE u w := by
  unfold pairE
  rw [map_add, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [Finsupp.add_apply, mul_add]

theorem pairE_neg_right (u v : PE) : pairE u (-v) = - pairE u v := by
  unfold pairE
  rw [map_neg, ← Finsupp.sum_neg]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [Finsupp.neg_apply, mul_neg]

theorem pairE_sub_right (u v w : PE) : pairE u (v - w) = pairE u v - pairE u w := by
  rw [sub_eq_add_neg, pairE_add_right, pairE_neg_right, ← sub_eq_add_neg]

theorem pairE_add_left (u v w : PE) : pairE (u + v) w = pairE u w + pairE v w := by
  unfold pairE
  rw [map_add]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem pairE_neg_left (u v : PE) : pairE (-u) v = - pairE u v := by
  have h := pairE_add_left u (-u) v
  rw [add_neg_cancel] at h
  have h0 : pairE 0 v = 0 := by unfold pairE; simp
  linarith

theorem pairE_sub_left (u v w : PE) : pairE (u - v) w = pairE u w - pairE v w := by
  rw [sub_eq_add_neg, pairE_add_left, pairE_neg_left, ← sub_eq_add_neg]

theorem pairE_single_left (e : OTE) (r : ℚ) (c : PE) :
    pairE (MonoidAlgebra.single e r) c = r * c.coeff e := by
  unfold pairE
  change ((MonoidAlgebra.single e r : PE).coeff).sum (fun t a => a * c.coeff t) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

/-- The antisymmetric edge element `[e] - [ē]`. -/
def EeL (e : OTE) : PE := MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ)

theorem EeL_mem (e : OTE) : EeL e ∈ antiSub := by
  rw [mem_antiSub]
  unfold EeL
  rw [map_sub, swapMap_single, swapMap_single, OTE.swap_swap]; abel

theorem pairE_EeL_right (u : PE) (e : OTE) : pairE u (EeL e) = u.coeff e - u.coeff e.swap := by
  unfold EeL
  rw [pairE_sub_right, pairE_single_right, pairE_single_right]; ring

theorem pairE_EeL_left (e : OTE) (c : PE) : pairE (EeL e) c = c.coeff e - c.coeff e.swap := by
  unfold EeL
  rw [pairE_sub_left, pairE_single_left, pairE_single_left]; ring

theorem EeL_ρ (γ : IntegralGL) (e : OTE) : PE.ρ γ (EeL e) = EeL (γ • e) := by
  unfold EeL
  rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, OTE.swap_smul]

theorem E0_coe : ((E0 : P1) : PE) = EeL p0 := rfl

theorem adj_coeff {p : ℕ} [Fact p.Prime] (s : DualLift p) (l : LiftData p) (h : l.IsAdjoint s) (e e' : OTE) :
    ((l.lam1 ⟨EeL e', EeL_mem e'⟩ : P1) : PE).coeff e = ((s.s1 ⟨EeL e, EeL_mem e⟩ : P1) : PE).coeff e' := by
  have h1 := h.2 ⟨EeL e', EeL_mem e'⟩ ⟨EeL e, EeL_mem e⟩
  rw [pairE_EeL_right, pairE_EeL_left] at h1
  have a1 := coeff_antisymm (l.lam1 ⟨EeL e', EeL_mem e'⟩).2 e
  have a2 := coeff_antisymm (s.s1 ⟨EeL e, EeL_mem e⟩).2 e'
  linarith

/-- The group elements carrying the base edge to `e`. -/
def fiberE (e : OTE) : Set IntegralGL := {ε | ε • p0 = e}

theorem fiberE_finite (e : OTE) : (fiberE e).Finite := by
  obtain ⟨u, hu⟩ := ote_transitive e
  have : fiberE e ⊆ (fun σ => u * σ) '' (MulAction.stabilizer IntegralGL p0 : Set IntegralGL) := by
    intro ε hε
    refine ⟨u⁻¹ * ε, ?_, mul_inv_cancel_left u ε⟩
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    have h1 : ε • p0 = e := hε
    rw [mul_smul, h1, ← hu, inv_smul_smul]
  have hfin : Finite (MulAction.stabilizer IntegralGL p0) := ote_stabilizer_finite p0
  exact (Set.Finite.image _ (Set.toFinite _)).subset this

theorem finite_support_coeff {M : Type*} [AddCommGroup M] [Module ℚ M] (c : PE) (F : IntegralGL → M) :
    (Function.support fun ε : IntegralGL => c.coeff (ε • p0) • F ε).Finite := by
  refine ((c.coeff.support.finite_toSet).biUnion fun e _ => fiberE_finite e).subset ?_
  intro ε hε
  simp only [Function.mem_support, ne_eq] at hε
  simp only [Set.mem_iUnion, Finset.mem_coe]
  refine ⟨ε • p0, ?_, rfl⟩
  rw [Finsupp.mem_support_iff]
  intro h0
  exact hε (by rw [h0, zero_smul])

section FinsumS

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- The sum `∑_ε c(ε p₀) F(ε)` over the group elements. -/
def SS (F : IntegralGL → M) (c : PE) : M := ∑ᶠ ε : IntegralGL, c.coeff (ε • p0) • F ε

theorem SS_add (F : IntegralGL → M) (c c' : PE) : SS F (c + c') = SS F c + SS F c' := by
  unfold SS
  rw [← finsum_add_distrib (finite_support_coeff c F) (finite_support_coeff c' F)]
  refine finsum_congr fun ε => ?_
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]

theorem SS_smul (F : IntegralGL → M) (r : ℚ) (c : PE) : SS F (r • c) = r • SS F c := by
  unfold SS
  rw [smul_finsum' _ (finite_support_coeff c F)]
  refine finsum_congr fun ε => ?_
  have : (r • c).coeff = r • c.coeff := rfl
  rw [this, Finsupp.smul_apply, smul_assoc]

theorem SS_zero (F : IntegralGL → M) : SS F 0 = 0 := by
  unfold SS
  simp

theorem SS_map {N : Type*} [AddCommGroup N] [Module ℚ N] (g : M →ₗ[ℚ] N) (F : IntegralGL → M) (c : PE) :
    g (SS F c) = SS (fun ε => g (F ε)) c := by
  unfold SS
  rw [map_finsum _ (finite_support_coeff c F)]
  refine finsum_congr fun ε => ?_
  rw [map_smul]

theorem SS_ρ (F : IntegralGL → M) (γ : IntegralGL) (c : PE) :
    SS F (PE.ρ γ c) = SS (fun ε => F (γ * ε)) c := by
  unfold SS
  have h : ∀ ε : IntegralGL, (PE.ρ γ c).coeff (ε • p0) = c.coeff ((γ⁻¹ * ε) • p0) := by
    intro ε
    rw [coeff_PE_ρ, mul_smul]
  simp only [h]
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun ε => ?_
  simp [Equiv.coe_mulLeft]

theorem SS_single (F : IntegralGL → M) (e : OTE) (r : ℚ) :
    SS F (MonoidAlgebra.single e r) = r • ∑ ε ∈ (fiberE_finite e).toFinset, F ε := by
  unfold SS
  have hsub : (Function.support fun ε : IntegralGL => (MonoidAlgebra.single e r : PE).coeff (ε • p0) • F ε) ⊆
      ((fiberE_finite e).toFinset : Set IntegralGL) := by
    intro ε hε
    simp only [Function.mem_support, ne_eq, MonoidAlgebra.coeff_single, Finsupp.single_apply] at hε
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, fiberE, Set.mem_ofPred_eq]
    by_contra hne
    exact hε (by rw [ite_eq_right (fun h => hne h.symm), zero_smul])
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ε hε => ?_
  have h1 : ε • p0 = e := by simpa [fiberE] using hε
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, h1, ite_true]

end FinsumS

/-- **U1**: the standard-edge evaluation as a sum over the group. -/
theorem evalP_mk_eq (M : Rep ℚ IntegralGL) (m : M) (c : PE) :
    evalP M (Coinvariants.mk _ (m ⊗ₜ[ℚ] c)) = SS (fun ε => M.ρ ε⁻¹ m) c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp [SS_zero]
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb, SS_add]
  | single e r =>
    rw [SS_single]
    change evalTen (ote_stabilizer_finite p0) M (m ⊗ₜ[ℚ] MonoidAlgebra.single e r) = _
    rw [evalTen_tmul_single]
    congr 1
    unfold normAt
    rw [LinearMap.sum_apply]
    refine Finset.sum_nbij' (fun γ => γ⁻¹) (fun ε => ε⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro γ hγ
      simp only [Set.Finite.mem_toFinset, transp, Set.mem_ofPred_eq] at hγ
      simp only [Set.Finite.mem_toFinset, fiberE, Set.mem_ofPred_eq]
      rw [inv_smul_eq_iff]; exact hγ.symm
    · intro ε hε
      simp only [Set.Finite.mem_toFinset, fiberE, Set.mem_ofPred_eq] at hε
      simp only [Set.Finite.mem_toFinset, transp, Set.mem_ofPred_eq]
      rw [← hε, inv_smul_smul]
    · intro γ _; simp
    · intro ε _; simp
    · intro γ _; simp


section U2

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

theorem SS_eq_sum (F : IntegralGL → M) (c : PE) :
    SS F c = c.coeff.sum (fun e r => r • ∑ ε ∈ (fiberE_finite e).toFinset, F ε) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp [SS_zero]
  | add a b ha hb =>
    rw [SS_add, ha, hb, MonoidAlgebra.coeff_add]
    exact (Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])).symm
  | single e r =>
    rw [SS_single, MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

omit [Module ℚ M] in
theorem fiber_sum_translate (F : IntegralGL → M) (u : IntegralGL) (e : OTE) (hu : u • p0 = e) :
    ∑ ε ∈ (fiberE_finite e).toFinset, F ε = ∑ σ ∈ (fiberE_finite p0).toFinset, F (u * σ) := by
  refine Finset.sum_nbij' (fun ε => u⁻¹ * ε) (fun σ => u * σ) ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    simp only [Set.Finite.mem_toFinset, fiberE, Set.mem_ofPred_eq] at hε ⊢
    rw [mul_smul, hε, ← hu, inv_smul_smul]
  · intro σ hσ
    simp only [Set.Finite.mem_toFinset, fiberE, Set.mem_ofPred_eq] at hσ ⊢
    rw [mul_smul, hσ, hu]
  · intro ε _; simp
  · intro σ _; simp
  · intro ε _; simp

theorem swap_sub_eq_sum (c : PE) : c - swapMap.hom c = c.coeff.sum (fun e r => r • EeL e) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, MonoidAlgebra.coeff_add]
    rw [show a + b - (swapMap.hom a + swapMap.hom b) = (a - swapMap.hom a) + (b - swapMap.hom b) by abel, ha, hb]
    exact (Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])).symm
  | single e r =>
    rw [swapMap_single, MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    unfold EeL
    rw [smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem fiber_sum_p0 (N : Rep ℚ IntegralGL) (B : N) (hB : ∀ s : MulAction.stabilizer IntegralGL p0, N.ρ s B = B) :
    ∑ σ ∈ (fiberE_finite p0).toFinset, N.ρ σ B = (nP : ℚ) • B := by
  rw [← normStab_p_of_inv N B hB]
  unfold normStab normAt
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext σ
  simp only [Set.Finite.mem_toFinset, fiberE, transp, Set.mem_ofPred_eq]

theorem fiber_sum_eq (N : Rep ℚ IntegralGL) (B : N)
    (hB : ∀ s : MulAction.stabilizer IntegralGL p0, N.ρ s B = B) (u : IntegralGL) (e : OTE) (hu : u • p0 = e) :
    ∑ ε ∈ (fiberE_finite e).toFinset, N.ρ ε B = (nP : ℚ) • N.ρ u B := by
  rw [fiber_sum_translate (fun ε => N.ρ ε B) u e hu]
  simp only [map_mul, Module.End.mul_apply]
  rw [← map_sum, fiber_sum_p0 N B hB, map_smul]

/-- The antisymmetric edge element as an element of `P1`. -/
def EeP (e : OTE) : P1 := ⟨EeL e, EeL_mem e⟩

theorem EeP_ρ (γ : IntegralGL) (e : OTE) : P1.ρ γ (EeP e) = EeP (γ • e) :=
  Subtype.ext (EeL_ρ γ e)

theorem E0_eq : (E0 : P1) = EeP p0 := rfl

/-- **U2**: an equivariant map out of `P1` is determined by its value at `E₀`:
`2 nP Φ(c) = ∑_ε c(ε p₀) ρ(ε) Φ(E₀)`. -/
theorem phi_formula (N : Rep ℚ IntegralGL) (Φ : P1 →ₗ[ℚ] N)
    (hΦ : ∀ (γ : IntegralGL) (x : P1), Φ (P1.ρ γ x) = N.ρ γ (Φ x)) (c : P1) :
    ((2 * nP : ℚ)) • Φ c = SS (fun ε => N.ρ ε (Φ E0)) (c : PE) := by
  have hB : ∀ s : MulAction.stabilizer IntegralGL p0, N.ρ s (Φ E0) = Φ E0 := by
    intro s
    rw [← hΦ]
    congr 1
    rw [E0_eq, EeP_ρ, show (s : IntegralGL) • p0 = p0 from s.2]
  let Φt : PE →ₗ[ℚ] N := Φ ∘ₗ retrP1.hom.toLinearMap
  have h1 : Φt (c : PE) = Φ c := by
    have := congrArg (fun m => m.hom c) inclP1_retrP1
    change retrP1.hom (inclP1.hom c) = c at this
    change Φ (retrP1.hom (c : PE)) = Φ c
    exact congrArg Φ this
  have h2 : ∀ e : OTE, Φt (EeL e) = Φ (EeP e) := by
    intro e
    change Φ (retrP1.hom (EeL e)) = _
    congr 1
    apply Subtype.ext
    change antiLin (EeL e) = EeL e
    rw [antiLin_apply, (eq_neg_of_add_eq_zero_left (mem_antiSub.mp (EeL_mem e)) : swapMap.hom (EeL e) = -EeL e)]
    module
  have h3 : (2 : ℚ) • (c : PE) = (c : PE).coeff.sum (fun e r => r • EeL e) := by
    rw [← swap_sub_eq_sum, (eq_neg_of_add_eq_zero_left (mem_antiSub.mp c.2) : swapMap.hom (c : PE) = -(c : PE))]
    module
  have h4 : (2 : ℚ) • Φ c = (c : PE).coeff.sum (fun e r => r • Φ (EeP e)) := by
    rw [← h1, ← map_smul, h3, map_finsuppSum]
    refine Finsupp.sum_congr fun e _ => ?_
    rw [map_smul, h2]
  rw [SS_eq_sum, mul_comm, mul_smul, h4, Finsupp.smul_sum]
  refine Finsupp.sum_congr fun e _ => ?_
  obtain ⟨u, hu⟩ := ote_transitive e
  rw [fiber_sum_eq N (Φ E0) hB u e hu, smul_comm]
  congr 2
  rw [← hΦ, E0_eq, EeP_ρ, hu]

end U2

end Basic

end TernaryPeriodPolynomials.Argument.HeckeNormalization
