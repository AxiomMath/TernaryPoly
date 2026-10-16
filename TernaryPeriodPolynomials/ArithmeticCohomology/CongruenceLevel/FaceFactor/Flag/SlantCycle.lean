module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Slant
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantMu

@[expose] public section


/-!
# The shuffle slant `Sh₁ σ` as a bar `3`-chain of a flag group, its cycle property and the calibration of `λ`

Formalized by Claude Sonnet 5.5.

`LetterLift P B`: a group `B` with an injective homomorphism `ι : B →* G` into the group `G` of a pair model `P` (`G = N ⋊ L`) which contains the letters `nl a`, `ll σ`.
`sh1Chain` is `Sh([e₁|e₂]; σ)` (three placements of the letter `σ`), `nuSh = Sh₁ σ = sh1Chain e₁ e₂ σ - sh1Chain e₂ e₁ σ`; `chainEval_nuSh_dTwo` is the dual of `∂Sh₁σ = ν^σ - ν`,
`nuSh_sub_isCycle`: if `m` is a chain with `∂m = ν^σ - ν` then `Sh₁σ - m` is a cycle of `B`, and `calibrate`: for `(≥1)`-cocycles `Θ`, `Θ₁` of `B`
`⟨Θ₁, Sh₁σ⟩ · λ[Θ] = ⟨Θ, Sh₁σ⟩ · λ[Θ₁]` (`H³(B)` is one-dimensional, `exists_chainEval_eq_mul_lam`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FlagH3

/-- A group `B` embedded in the group `G` of a pair model, containing the letters `nl a`, `ll σ`. -/
structure LetterLift {G M L : Type} [Group G] [AddCommGroup M] [Group L] (P : PairModel G M L) (B : Type) [Group B] (σ : L) where
  ι : B →* G
  inj : Function.Injective ι
  nlB : M → B
  llB : B
  hnl : ∀ a, ι (nlB a) = P.nl a
  hll : ι llB = P.ll σ

namespace LetterLift

variable {G M L B : Type} [Group G] [AddCommGroup M] [Group L] [Group B] {P : PairModel G M L} {σ : L} (Lt : LetterLift P B σ)

theorem nlB_add (a b : M) : Lt.nlB a * Lt.nlB b = Lt.nlB (a + b) := by
  apply Lt.inj
  rw [map_mul, Lt.hnl, Lt.hnl, Lt.hnl, P.nl_mul_nl]

theorem llB_nlB (x : M) : Lt.llB * Lt.nlB (P.ψ σ⁻¹ x) = Lt.nlB x * Lt.llB := by
  apply Lt.inj
  rw [map_mul, map_mul, Lt.hll, Lt.hnl, Lt.hnl, P.ll_mul_nl', P.nl_mul_ll, P.ψ_ψ_inv]

/-- `Sh([e₁|e₂]; σ)`: the three placements of the `L`-letter `σ` in `[e₁|e₂]`, with the `N`-letters after `σ` conjugated by `σ⁻¹`. -/
def sh1Chain (e₁ e₂ : M) : (Fin 3 → B) →₀ ℚ :=
  Finsupp.single ![Lt.llB, Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] 1 -
    Finsupp.single ![Lt.nlB e₁, Lt.llB, Lt.nlB (P.ψ σ⁻¹ e₂)] 1 + Finsupp.single ![Lt.nlB e₁, Lt.nlB e₂, Lt.llB] 1

/-- The slant `Sh₁ σ = Sh(ν; σ)` with `ν = [e₁|e₂] - [e₂|e₁]`. -/
def nuSh (e₁ e₂ : M) : (Fin 3 → B) →₀ ℚ := Lt.sh1Chain e₁ e₂ - Lt.sh1Chain e₂ e₁

theorem chainEval_sh1Chain_dTwo (α : (Fin 2 → B) → ℚ) (e₁ e₂ : M) :
    chainEval (Lt.sh1Chain e₁ e₂) (dTwo α) =
      α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB e₁, Lt.nlB e₂] +
        α ![Lt.llB, Lt.nlB (P.ψ σ⁻¹ e₁ + P.ψ σ⁻¹ e₂)] - α ![Lt.llB, Lt.nlB (P.ψ σ⁻¹ e₁)] -
        α ![Lt.llB, Lt.nlB (P.ψ σ⁻¹ e₂)] + α ![Lt.nlB e₁, Lt.llB] + α ![Lt.nlB e₂, Lt.llB] -
        α ![Lt.nlB (e₁ + e₂), Lt.llB] := by
  unfold sh1Chain
  rw [chainEval_add, chainEval_sub, chainEval_single, chainEval_single, chainEval_single]
  simp only [dTwo_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Lt.llB_nlB, Lt.nlB_add, one_mul]
  ring

theorem chainEval_nuSh_dTwo (α : (Fin 2 → B) → ℚ) (e₁ e₂ : M) :
    chainEval (Lt.nuSh e₁ e₂) (dTwo α) =
      (α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB (P.ψ σ⁻¹ e₂), Lt.nlB (P.ψ σ⁻¹ e₁)]) -
        (α ![Lt.nlB e₁, Lt.nlB e₂] - α ![Lt.nlB e₂, Lt.nlB e₁]) := by
  unfold nuSh
  rw [chainEval_sub, chainEval_sh1Chain_dTwo, chainEval_sh1Chain_dTwo, add_comm (P.ψ σ⁻¹ e₂), add_comm e₂ e₁]
  ring

/-- If `m` has boundary `ν^σ - ν` (dually), then `Sh₁ σ - m` is a bar `3`-cycle of `B`. -/
theorem nuSh_sub_isCycle (e₁ e₂ : M) (m : (Fin 3 → B) →₀ ℚ)
    (hm : ∀ α : (Fin 2 → B) → ℚ, chainEval m (dTwo α) =
      (α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB (P.ψ σ⁻¹ e₂), Lt.nlB (P.ψ σ⁻¹ e₁)]) -
        (α ![Lt.nlB e₁, Lt.nlB e₂] - α ![Lt.nlB e₂, Lt.nlB e₁])) :
    IsCycle (Lt.nuSh e₁ e₂ - m) := by
  intro α
  rw [chainEval_sub, chainEval_nuSh_dTwo, hm, sub_self]

/-- **Calibration**: for `(≥1)`-cocycles `Θ₁`, `Θ` of a flag group `B` (vanishing on all triples of `N`-letters), `⟨Θ₁, Sh₁σ⟩ λ[Θ] = ⟨Θ, Sh₁σ⟩ λ[Θ₁]`. -/
theorem calibrate (D : FlagCohomDatum B) (e₁ e₂ : M) (m : (Fin 3 → B) →₀ ℚ)
    (hm : ∀ α : (Fin 2 → B) → ℚ, chainEval m (dTwo α) =
      (α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB (P.ψ σ⁻¹ e₂), Lt.nlB (P.ψ σ⁻¹ e₁)]) -
        (α ![Lt.nlB e₁, Lt.nlB e₂] - α ![Lt.nlB e₂, Lt.nlB e₁]))
    (hmsupp : ∀ x ∈ m.support, ∃ a b c, x = ![Lt.nlB a, Lt.nlB b, Lt.nlB c])
    (Θ₁ Θ : (Fin 3 → B) → ℚ) (h₁ : dThree Θ₁ = 0) (h : dThree Θ = 0)
    (z₁ : ∀ a b c, Θ₁ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0) (z : ∀ a b c, Θ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0) :
    chainEval (Lt.nuSh e₁ e₂) Θ₁ * D.lam (cocycleClass Θ h) = chainEval (Lt.nuSh e₁ e₂) Θ * D.lam (cocycleClass Θ₁ h₁) := by
  obtain ⟨μ, hμ⟩ := exists_chainEval_eq_mul_lam D _ (Lt.nuSh_sub_isCycle e₁ e₂ m hm)
  have hv : ∀ (Ψ : (Fin 3 → B) → ℚ), (∀ a b c, Ψ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0) → chainEval m Ψ = 0 := by
    intro Ψ hΨ
    unfold chainEval
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨a, b, c, rfl⟩ := hmsupp x hx
    show m _ * Ψ _ = 0
    rw [hΨ a b c, mul_zero]
  have e1 := hμ Θ₁ h₁
  have e2 := hμ Θ h
  rw [chainEval_sub, hv Θ₁ z₁, sub_zero] at e1
  rw [chainEval_sub, hv Θ z, sub_zero] at e2
  rw [e1, e2]
  ring

/-- **The value of `λ`**: if a test cocycle `Θ₁` has `⟨Θ₁, Sh₁σ⟩ = c₁ t` and `λ[Θ₁] = c₂ t` with `t ≠ 0`, `c₁ ≠ 0`, then `λ[Θ] = (c₂ / c₁) ⟨Θ, Sh₁σ⟩` for every `(≥1)`-cocycle `Θ`. -/
theorem lam_eq (D : FlagCohomDatum B) (e₁ e₂ : M) (m : (Fin 3 → B) →₀ ℚ)
    (hm : ∀ α : (Fin 2 → B) → ℚ, chainEval m (dTwo α) =
      (α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB (P.ψ σ⁻¹ e₂), Lt.nlB (P.ψ σ⁻¹ e₁)]) -
        (α ![Lt.nlB e₁, Lt.nlB e₂] - α ![Lt.nlB e₂, Lt.nlB e₁]))
    (hmsupp : ∀ x ∈ m.support, ∃ a b c, x = ![Lt.nlB a, Lt.nlB b, Lt.nlB c])
    (Θ₁ : (Fin 3 → B) → ℚ) (h₁ : dThree Θ₁ = 0) (z₁ : ∀ a b c, Θ₁ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0)
    (c₁ c₂ t : ℚ) (hc₁ : c₁ ≠ 0) (ht : t ≠ 0)
    (hν : chainEval (Lt.nuSh e₁ e₂) Θ₁ = c₁ * t) (hl : D.lam (cocycleClass Θ₁ h₁) = c₂ * t)
    (Θ : (Fin 3 → B) → ℚ) (h : dThree Θ = 0) (z : ∀ a b c, Θ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0) :
    D.lam (cocycleClass Θ h) = (c₂ / c₁) * chainEval (Lt.nuSh e₁ e₂) Θ := by
  have := Lt.calibrate D e₁ e₂ m hm hmsupp Θ₁ Θ h₁ h z₁ z
  rw [hν, hl] at this
  rw [div_mul_eq_mul_div, eq_div_iff hc₁]
  apply mul_right_cancel₀ ht
  linear_combination this

/-- Evaluation of the slant on a cochain of the form `u(x₀) β(x₁, x₂)` with `u` vanishing on `N`-letters. -/
theorem chainEval_nuSh_cup (e₁ e₂ : M) (u : B → ℚ) (β : B → B → ℚ) (hu : ∀ a, u (Lt.nlB a) = 0) :
    chainEval (Lt.nuSh e₁ e₂) (fun x => u (x 0) * β (x 1) (x 2)) =
      u (Lt.llB) * (β (Lt.nlB (P.ψ σ⁻¹ e₁)) (Lt.nlB (P.ψ σ⁻¹ e₂)) - β (Lt.nlB (P.ψ σ⁻¹ e₂)) (Lt.nlB (P.ψ σ⁻¹ e₁))) := by
  unfold nuSh sh1Chain
  simp only [chainEval_sub, chainEval_add, chainEval_single, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hu]
  ring

/-- The slant of a cochain pulled back along `ι` is the slant of the `G`-cochain. -/
theorem chainEval_sh1Chain_comp (e₁ e₂ : M) (Ψ : G → G → G → ℚ) :
    chainEval (Lt.sh1Chain e₁ e₂) (fun x => Ψ (Lt.ι (x 0)) (Lt.ι (x 1)) (Lt.ι (x 2))) =
      Ψ (P.ll σ) (P.nl (P.ψ σ⁻¹ e₁)) (P.nl (P.ψ σ⁻¹ e₂)) - Ψ (P.nl e₁) (P.ll σ) (P.nl (P.ψ σ⁻¹ e₂)) +
        Ψ (P.nl e₁) (P.nl e₂) (P.ll σ) := by
  unfold sh1Chain
  simp only [chainEval_sub, chainEval_add, chainEval_single, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Lt.hnl, Lt.hll]
  ring

/-- The pure-`N` chain pushed into `B`. -/
def pushChain (m : (M × M × M) →₀ ℚ) : (Fin 3 → B) →₀ ℚ :=
  Finsupp.mapDomain (fun v : M × M × M => ![Lt.nlB v.1, Lt.nlB v.2.1, Lt.nlB v.2.2]) m

/-- The pairing of a `2`-cochain with a `2`-chain of `N`-letters. -/
def evN (α : (Fin 2 → B) → ℚ) : ((M × M) →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun v => α ![Lt.nlB v.1, Lt.nlB v.2]

theorem chainEval_pushChain (α : (Fin 2 → B) → ℚ) (m : (M × M × M) →₀ ℚ) :
    chainEval (Lt.pushChain m) (dTwo α) = Lt.evN α (torusBd3 M m) := by
  induction m using Finsupp.induction_linear with
  | zero => simp [pushChain, chainEval]
  | add f g hf hg =>
    unfold pushChain at *
    rw [Finsupp.mapDomain_add, chainEval_add, hf, hg, map_add, map_add]
  | single v c =>
    unfold pushChain
    rw [Finsupp.mapDomain_single, chainEval_single]
    simp only [torusBd3, evN, Finsupp.linearCombination_single, map_smul, map_add, map_sub, smul_eq_mul,
      dTwo_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Lt.nlB_add]
    ring

theorem evN_nuChain (α : (Fin 2 → B) → ℚ) (a b : M) :
    Lt.evN α (nuChain a b) = α ![Lt.nlB a, Lt.nlB b] - α ![Lt.nlB b, Lt.nlB a] := by
  simp [evN, nuChain, Finsupp.linearCombination_single, map_sub]

theorem pushChain_hm (e₁ e₂ : M) (m : (M × M × M) →₀ ℚ)
    (hm : torusBd3 M m = nuChain (P.ψ σ⁻¹ e₁) (P.ψ σ⁻¹ e₂) - nuChain e₁ e₂) (α : (Fin 2 → B) → ℚ) :
    chainEval (Lt.pushChain m) (dTwo α) =
      (α ![Lt.nlB (P.ψ σ⁻¹ e₁), Lt.nlB (P.ψ σ⁻¹ e₂)] - α ![Lt.nlB (P.ψ σ⁻¹ e₂), Lt.nlB (P.ψ σ⁻¹ e₁)]) -
        (α ![Lt.nlB e₁, Lt.nlB e₂] - α ![Lt.nlB e₂, Lt.nlB e₁]) := by
  rw [chainEval_pushChain, hm, map_sub, evN_nuChain, evN_nuChain]

open scoped Classical in
theorem pushChain_supp (m : (M × M × M) →₀ ℚ) :
    ∀ x ∈ (Lt.pushChain m).support, ∃ a b c, x = ![Lt.nlB a, Lt.nlB b, Lt.nlB c] := by
  intro x hx
  have := Finsupp.mapDomain_support hx
  rw [Finset.mem_image] at this
  obtain ⟨v, -, rfl⟩ := this
  exact ⟨v.1, v.2.1, v.2.2, rfl⟩

/-- `lam_eq` with the homotopy hypothesis in the form produced by `hμ_of_torus` (S7). -/
theorem lam_eq_torus (D : FlagCohomDatum B) (e₁ e₂ : M) (m₀ : (M × M × M) →₀ ℚ)
    (hm₀ : torusBd3 M m₀ = nuChain (P.ψ σ⁻¹ e₁) (P.ψ σ⁻¹ e₂) - nuChain e₁ e₂)
    (Θ₁ : (Fin 3 → B) → ℚ) (h₁ : dThree Θ₁ = 0) (z₁ : ∀ a b c, Θ₁ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0)
    (c₁ c₂ t : ℚ) (hc₁ : c₁ ≠ 0) (ht : t ≠ 0)
    (hν : chainEval (Lt.nuSh e₁ e₂) Θ₁ = c₁ * t) (hl : D.lam (cocycleClass Θ₁ h₁) = c₂ * t)
    (Θ : (Fin 3 → B) → ℚ) (h : dThree Θ = 0) (z : ∀ a b c, Θ ![Lt.nlB a, Lt.nlB b, Lt.nlB c] = 0) :
    D.lam (cocycleClass Θ h) = (c₂ / c₁) * chainEval (Lt.nuSh e₁ e₂) Θ :=
  Lt.lam_eq D e₁ e₂ (Lt.pushChain m₀) (Lt.pushChain_hm e₁ e₂ m₀ hm₀) (Lt.pushChain_supp m₀) Θ₁ h₁ z₁ c₁ c₂ t hc₁ ht hν hl Θ h z

end LetterLift

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
