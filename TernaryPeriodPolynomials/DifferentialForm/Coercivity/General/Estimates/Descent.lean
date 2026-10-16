module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Average
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DetTwist

@[expose] public section


/-! # General coercivity, Tier B: descent of a primitive from a normal subgroup of finite index

If `Γ' ⊴ Γ` has finite index and `ω` is a smooth `Γ`-(twisted-)equivariant form which has a smooth
`Γ'`-equivariant primitive `η`, then the average of the translates of `η` over the finite group
`Γ / Γ'` is a smooth `Γ`-(twisted-)equivariant primitive of `ω`.  The twist is by a multiplicative
character `χ : GL₃(ℝ) → ℝ` (for the determinant twists `χ = det^{-e}`, which are trivial on
`SL₃`), so that the neat normal cover `Γ'` can be taken to carry the untwisted equivariance.  This is
the "finite-group averaging descends a primitive from a neat normal cover" of the proof of
Proposition C.1.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothLocalDeRham
open Set Filter
open scoped ContDiff


variable {n k : ℕ}

theorem fv_smul_zero (c : ℝ) : c • (0 : FormValue n k) = 0 :=
  ContinuousAlternatingMap.ext fun v => by
    rw [ContinuousAlternatingMap.smul_apply]; exact smul_zero c

theorem fv_smul_smul (a b : ℝ) (A : FormValue n k) : a • b • A = (a * b) • A :=
  ContinuousAlternatingMap.ext fun v => by
    rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.smul_apply]; exact smul_smul a b (A v)

theorem fv_one_smul (A : FormValue n k) : (1 : ℝ) • A = A :=
  ContinuousAlternatingMap.ext fun v => by
    rw [ContinuousAlternatingMap.smul_apply]; exact one_smul ℝ (A v)

/-- The determinant character `g ↦ det(g)^{-e}`. -/
def detChar (e : ℤ) : RealGL →* ℝ :=
  (Units.coeHom ℝ).comp ((zpowGroupHom (-e)).comp Matrix.GeneralLinearGroup.det)

theorem detChar_apply (e : ℤ) (g : RealGL) : detChar e g = g.val.det ^ (-e) := by
  simp [detChar]

theorem detChar_of_det_one (e : ℤ) {g : RealGL} (hg : g.val.det = 1) : detChar e g = 1 := by
  rw [detChar_apply, hg, one_zpow]

/-- The normalized pullback twisted by the character `χ`: the pullback for the representation
`χ(g) • ρ(g)`. -/
def twPull (χ : RealGL →* ℝ) (n k : ℕ) (g : RealGL) (w : Coordinates → FormValue n k) :
    Coordinates → FormValue n k :=
  (χ g)⁻¹ • actPull n k g w

theorem twPull_apply (χ : RealGL →* ℝ) (g : RealGL) (w : Coordinates → FormValue n k)
    (x : Coordinates) : twPull χ n k g w x = (χ g)⁻¹ • actPull n k g w x := rfl

theorem twPull_of_notMem (χ : RealGL →* ℝ) (g : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∉ positiveCoordinates) : twPull χ n k g w x = 0 := by
  rw [twPull_apply, actPull_of_notMem n k g w hx]
  exact fv_smul_zero _

theorem twPull_mul (χ : RealGL →* ℝ) (g h : RealGL) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    twPull χ n k g (twPull χ n k h w) x = twPull χ n k (h * g) w x := by
  rw [twPull_apply, twPull_apply, twPull, actPull_smul n k g _ _ hx, actPull_mul n k g h w hx]
  have e1 : (χ g)⁻¹ • (χ h)⁻¹ • actPull n k (h * g) w x =
      ((χ g)⁻¹ * (χ h)⁻¹) • actPull n k (h * g) w x := fv_smul_smul _ _ _
  have e2 : (χ g)⁻¹ * (χ h)⁻¹ = (χ (h * g))⁻¹ := by
    rw [map_mul, mul_inv, mul_comm]
  exact e1.trans (congrArg (fun y : ℝ => (y • actPull n k (h * g) w x : FormValue n k)) e2)

theorem twPull_one_eq (g : RealGL) (w : Coordinates → FormValue n k) :
    twPull (1 : RealGL →* ℝ) n k g w = actPull n k g w := by
  funext x
  change ((1 : RealGL →* ℝ) g)⁻¹ • actPull n k g w x = _
  rw [MonoidHom.one_apply, inv_one]
  exact fv_one_smul _

theorem contDiffOn_twPull (χ : RealGL →* ℝ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (twPull χ n k g w) positiveCoordinates := by
  let : IsBoundedSMul ℝ (FormValue n k) :=
    @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
  exact (contDiffOn_actPull n k g hw).const_smul ((χ g)⁻¹)

theorem extDeriv_twPull (χ : RealGL →* ℝ) (g : RealGL) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    extDeriv (twPull χ n k g w) x = twPull χ n (k + 1) g (extDeriv w) x := by
  rw [twPull, extDeriv_smul, twPull_apply]
  show (χ g)⁻¹ • extDeriv (actPull n k g w) x = _
  rw [extDeriv_actPull n k g hw hx]

/-! ### Linearity of the twisted pullback on finite sums -/

theorem fv_smul_add (c : ℝ) (A B : FormValue n k) : c • (A + B) = c • A + c • B :=
  ContinuousAlternatingMap.ext fun v => by
    rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.smul_apply]; exact smul_add c (A v) (B v)

theorem twPull_add (χ : RealGL →* ℝ) (g : RealGL) (w z : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    twPull χ n k g (w + z) x = twPull χ n k g w x + twPull χ n k g z x := by
  rw [twPull_apply, actPull_add n k g _ _ hx]
  exact fv_smul_add _ _ _

theorem twPull_zero (χ : RealGL →* ℝ) (g : RealGL) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    twPull χ n k g (0 : Coordinates → FormValue n k) x = 0 := by
  have h := twPull_add χ g (0 : Coordinates → FormValue n k) 0 hx
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem twPull_sum (χ : RealGL →* ℝ) (g : RealGL) {ι : Type*} (s : Finset ι)
    (f : ι → Coordinates → FormValue n k) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    twPull χ n k g (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, twPull χ n k g (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact twPull_zero χ g hx
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have e : (fun y => f j y + ∑ i ∈ s, f i y) = f j + (fun y => ∑ i ∈ s, f i y) := rfl
    rw [e, twPull_add χ g _ _ hx, ih]

theorem twPull_smul (χ : RealGL →* ℝ) (g : RealGL) (c : ℝ) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    twPull χ n k g (c • w) x = c • twPull χ n k g w x := by
  rw [twPull_apply, twPull_apply, actPull_smul n k g c w hx, fv_smul_smul, fv_smul_smul, mul_comm]

theorem twPull_congr (χ : RealGL →* ℝ) (g : RealGL) {w z : Coordinates → FormValue n k}
    (hwz : ∀ y ∈ positiveCoordinates, w y = z y) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    twPull χ n k g w x = twPull χ n k g z x := by
  rw [twPull_apply, twPull_apply, actPull_apply n k g w hx, actPull_apply n k g z hx,
    hwz _ (coordinateAction_mem g x hx)]

theorem funext_of_pos {M : Type*} [Zero M] {f g : Coordinates → M}
    (h : ∀ x ∈ positiveCoordinates, f x = g x) (hf : ∀ x ∉ positiveCoordinates, f x = 0)
    (hg : ∀ x ∉ positiveCoordinates, g x = 0) : f = g := by
  funext x
  by_cases hx : x ∈ positiveCoordinates
  · exact h x hx
  · rw [hf x hx, hg x hx]

theorem extDeriv_sum_at {ι : Type*} (s : Finset ι) (f : ι → Coordinates → FormValue n k)
    (hf : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) positiveCoordinates) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    extDeriv (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, extDeriv (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := extDeriv_add (𝕜 := ℝ) (x := x) (ω₁ := fun _ : Coordinates => (0 : FormValue n k))
      (ω₂ := fun _ : Coordinates => (0 : FormValue n k)) (differentiableAt_const _)
      (differentiableAt_const _)
    have e : ((fun _ : Coordinates => (0 : FormValue n k)) + fun _ => 0) =
        fun _ : Coordinates => (0 : FormValue n k) := funext fun _ => add_zero _
    rw [e] at h
    exact left_eq_add.mp h
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hd : ∀ i ∈ insert j s, DifferentiableAt ℝ (f i) x := fun i hi =>
      (((hf i hi).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
    have hs : DifferentiableAt ℝ (fun y => ∑ i ∈ s, f i y) x := by
      have : ContDiffOn ℝ ∞ (fun y => ∑ i ∈ s, f i y) positiveCoordinates :=
        ContDiffOn.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      exact (this.contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    have e : (fun y => f j y + ∑ i ∈ s, f i y) = f j + (fun y => ∑ i ∈ s, f i y) := rfl
    rw [e, extDeriv_add (hd j (Finset.mem_insert_self j s)) hs,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-! ### Descent -/

section Descent

variable (χ : RealGL →* ℝ) {Γ' Γ : Subgroup RealGL}

/-- Translates of a `Γ'`-invariant form by elements in the same coset of `Γ' ∩ Γ` agree. -/
theorem twPull_inv_congr {η : Coordinates → FormValue n k}
    (hη' : ∀ γ ∈ Γ', ∀ x ∈ positiveCoordinates, twPull χ n k γ η x = η x)
    (a b : Γ) (hab : a⁻¹ * b ∈ Γ'.subgroupOf Γ) :
    twPull χ n k ((a⁻¹ : Γ) : RealGL) η = twPull χ n k ((b⁻¹ : Γ) : RealGL) η := by
  have h1 : (((a⁻¹ * b : Γ)) : RealGL) ∈ Γ' := Subgroup.mem_subgroupOf.mp hab
  have hmem : (((a⁻¹ * b)⁻¹ : Γ) : RealGL) ∈ Γ' := by
    rw [Subgroup.coe_inv]
    exact Γ'.inv_mem h1
  have hbΓ : (b⁻¹ : Γ) = (a⁻¹ * b)⁻¹ * a⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hb : ((b⁻¹ : Γ) : RealGL) = (((a⁻¹ * b)⁻¹ : Γ) : RealGL) * ((a⁻¹ : Γ) : RealGL) := by
    rw [hbΓ, Subgroup.coe_mul]
  refine funext_of_pos (fun x hx => ?_) (fun x hx => twPull_of_notMem χ _ _ hx)
    (fun x hx => twPull_of_notMem χ _ _ hx)
  have e1 := twPull_mul χ ((a⁻¹ : Γ) : RealGL) (((a⁻¹ * b)⁻¹ : Γ) : RealGL) η hx
  have e2 : twPull χ n k ((a⁻¹ : Γ) : RealGL) η x =
      twPull χ n k ((a⁻¹ : Γ) : RealGL) (twPull χ n k (((a⁻¹ * b)⁻¹ : Γ) : RealGL) η) x :=
    twPull_congr χ _ (fun y hy => (hη' _ hmem y hy).symm) hx
  exact (e2.trans e1).trans (congrArg (fun r => twPull χ n k r η x) hb.symm)

/-- **Descent of a primitive.**  Let `Γ' ∩ Γ` be a normal subgroup of finite index of `Γ`.  If `ζ`
is a smooth `Γ`-equivariant (for the `χ`-twisted action) `(k+1)`-form and `η` is a smooth
`Γ'`-equivariant form with `dη = ζ`, then there is a smooth `Γ`-equivariant `η'` with `dη' = ζ`
(the average of the translates of `η` over `Γ / (Γ' ∩ Γ)`); it vanishes outside the positive
coordinates when `η` does. -/
theorem exists_descent_primitive [(Γ'.subgroupOf Γ).Normal] [Finite (Γ ⧸ Γ'.subgroupOf Γ)]
    {η : Coordinates → FormValue n k} {ζ : Coordinates → FormValue n (k + 1)}
    (hη : ContDiffOn ℝ ∞ η positiveCoordinates)
    (hη' : ∀ γ ∈ Γ', ∀ x ∈ positiveCoordinates, twPull χ n k γ η x = η x)
    (hζ : ∀ γ ∈ Γ, ∀ x ∈ positiveCoordinates, twPull χ n (k + 1) γ ζ x = ζ x)
    (hd : ∀ x ∈ positiveCoordinates, extDeriv η x = ζ x) :
    ∃ η'' : Coordinates → FormValue n k, ContDiffOn ℝ ∞ η'' positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η'' x = 0) ∧
      (∀ γ ∈ Γ, ∀ x ∈ positiveCoordinates, twPull χ n k γ η'' x = η'' x) ∧
      ∀ x ∈ positiveCoordinates, extDeriv η'' x = ζ x := by
  classical
  have : Fintype (Γ ⧸ Γ'.subgroupOf Γ) := Fintype.ofFinite _
  let Ψ : Γ ⧸ Γ'.subgroupOf Γ → Coordinates → FormValue n k := fun q =>
    Quotient.liftOn' q (fun γ : Γ => twPull χ n k ((γ⁻¹ : Γ) : RealGL) η)
      (fun a b hab => twPull_inv_congr χ hη' a b ((QuotientGroup.leftRel_apply).mp hab))
  have hΨ : ∀ γ : Γ, Ψ (γ : Γ ⧸ Γ'.subgroupOf Γ) = twPull χ n k ((γ⁻¹ : Γ) : RealGL) η :=
    fun _ => rfl
  have hΨ0 : ∀ q, ∀ x ∉ positiveCoordinates, Ψ q x = 0 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => exact fun x hx => by rw [hΨ]; exact twPull_of_notMem χ _ _ hx
  have hΨs : ∀ q, ContDiffOn ℝ ∞ (Ψ q) positiveCoordinates := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => rw [hΨ]; exact contDiffOn_twPull χ _ hη
  have hΨd : ∀ q, ∀ x ∈ positiveCoordinates, extDeriv (Ψ q) x = ζ x := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ =>
      intro x hx
      rw [hΨ, extDeriv_twPull χ _ hη hx]
      rw [twPull_congr χ _ (w := extDeriv η) (z := ζ) hd hx]
      exact hζ _ (γ⁻¹).2 x hx
  have hΨmul : ∀ (δ : Γ) (q : Γ ⧸ Γ'.subgroupOf Γ), ∀ x ∈ positiveCoordinates,
      twPull χ n k (δ : RealGL) (Ψ q) x = Ψ ((δ⁻¹ : Γ) * q) x := by
    intro δ q
    induction q using QuotientGroup.induction_on with
    | H γ =>
      intro x hx
      rw [hΨ, twPull_mul χ _ _ η hx]
      have : ((δ⁻¹ : Γ) * (γ : Γ ⧸ Γ'.subgroupOf Γ)) = ((δ⁻¹ * γ : Γ) : Γ ⧸ Γ'.subgroupOf Γ) :=
        rfl
      rw [this, hΨ]
      congr 2
  let S : Coordinates → FormValue n k := fun y => ∑ q, Ψ q y
  let m : ℝ := (Fintype.card (Γ ⧸ Γ'.subgroupOf Γ) : ℝ)⁻¹
  refine ⟨m • S, ?_, ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ S positiveCoordinates := ContDiffOn.sum (fun q _ => hΨs q)
    let : IsBoundedSMul ℝ (FormValue n k) :=
      @NormedSpace.toIsBoundedSMul ℝ (FormValue n k) _ _ inferInstance
    exact hS.const_smul m
  · intro x hx
    have h0 : S x = 0 := Finset.sum_eq_zero (fun q _ => hΨ0 q x hx)
    exact (congrArg (fun y : FormValue n k => (m • y : FormValue n k)) h0).trans (fv_smul_zero _)
  · intro δ hδ x hx
    have hS : twPull χ n k δ S x = S x := by
      have h1 := twPull_sum χ δ Finset.univ Ψ hx
      refine h1.trans ?_
      calc ∑ q, twPull χ n k δ (Ψ q) x = ∑ q, Ψ ((⟨δ, hδ⟩ : Γ)⁻¹ * q) x :=
            Finset.sum_congr rfl fun q _ => hΨmul ⟨δ, hδ⟩ q x hx
        _ = ∑ q, Ψ q x :=
            Equiv.sum_comp (Equiv.mulLeft (((⟨δ, hδ⟩ : Γ)⁻¹ : Γ) : Γ ⧸ Γ'.subgroupOf Γ))
              (fun q => Ψ q x)
    exact (twPull_smul χ δ m S hx).trans
      (congrArg (fun y : FormValue n k => (m • y : FormValue n k)) hS)
  · intro x hx
    rw [extDeriv_smul]
    have h1 := extDeriv_sum_at Finset.univ Ψ (fun q _ => hΨs q) hx
    have h2 : extDeriv S x = (Fintype.card (Γ ⧸ Γ'.subgroupOf Γ) : ℝ) • ζ x := by
      refine h1.trans ?_
      rw [Finset.sum_congr rfl (fun q _ => hΨd q x hx), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℝ]
    show m • extDeriv S x = ζ x
    rw [h2, fv_smul_smul]
    have hc : (Fintype.card (Γ ⧸ Γ'.subgroupOf Γ) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [show m * (Fintype.card (Γ ⧸ Γ'.subgroupOf Γ) : ℝ) = 1 from inv_mul_cancel₀ hc]
    exact fv_one_smul _

/-- Equivariance for the `χ`-twisted action: `w = χ(γ)⁻¹ • γ*w` on the positive coordinates. -/
def IsTwEquivariant (χ : RealGL →* ℝ) (Γ : Subgroup RealGL) (n k : ℕ)
    (w : Coordinates → FormValue n k) : Prop :=
  ∀ γ ∈ Γ, ∀ x ∈ positiveCoordinates, twPull χ n k γ w x = w x

theorem isEquivariant_iff_actPull {w : Coordinates → FormValue n k} :
    IsEquivariant Γ n k w ↔ ∀ γ ∈ Γ, ∀ x ∈ positiveCoordinates, actPull n k γ w x = w x := by
  rw [isEquivariant_iff]
  constructor
  · intro h γ hγ x hx
    exact actPull_eq_of_equivariantAt n k γ hx (h ⟨γ, hγ⟩ x hx)
  · intro h γ x hx
    exact equivariantAt_of_actPull_eq n k γ hx (h γ γ.2 x hx)

theorem isTwEquivariant_one_iff {w : Coordinates → FormValue n k} :
    IsTwEquivariant 1 Γ n k w ↔ IsEquivariant Γ n k w := by
  rw [isEquivariant_iff_actPull]
  simp only [IsTwEquivariant, twPull_one_eq]

end Descent

section Corollaries

variable {Γ' Γ : Subgroup RealGL}

/-- **Descent of a primitive (untwisted).**  A smooth `Γ'`-equivariant primitive of a smooth
`Γ`-equivariant form descends to a smooth `Γ`-equivariant primitive when `Γ' ∩ Γ` is normal of
finite index in `Γ`. -/
theorem exists_equivariant_primitive_of_normal [(Γ'.subgroupOf Γ).Normal]
    [Finite (Γ ⧸ Γ'.subgroupOf Γ)] {η : Coordinates → FormValue n k}
    {ζ : Coordinates → FormValue n (k + 1)} (hη : ContDiffOn ℝ ∞ η positiveCoordinates)
    (hη' : IsEquivariant Γ' n k η) (hζ : IsEquivariant Γ n (k + 1) ζ)
    (hd : ∀ x ∈ positiveCoordinates, extDeriv η x = ζ x) :
    ∃ η'' : Coordinates → FormValue n k, ContDiffOn ℝ ∞ η'' positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η'' x = 0) ∧ IsEquivariant Γ n k η'' ∧
      ∀ x ∈ positiveCoordinates, extDeriv η'' x = ζ x := by
  have h1 : ∀ γ ∈ Γ', ∀ x ∈ positiveCoordinates, twPull (1 : RealGL →* ℝ) n k γ η x = η x := by
    intro γ hγ x hx
    rw [twPull_one_eq]
    exact isEquivariant_iff_actPull.mp hη' γ hγ x hx
  have h2 : ∀ γ ∈ Γ, ∀ x ∈ positiveCoordinates, twPull (1 : RealGL →* ℝ) n (k + 1) γ ζ x = ζ x := by
    intro γ hγ x hx
    rw [twPull_one_eq]
    exact isEquivariant_iff_actPull.mp hζ γ hγ x hx
  obtain ⟨η'', h3, h4, h5, h6⟩ := exists_descent_primitive (1 : RealGL →* ℝ) hη h1 h2 hd
  exact ⟨η'', h3, h4, isTwEquivariant_one_iff.mp h5, h6⟩

/-- **Descent of a primitive across a determinant twist.**  A smooth equivariant primitive for a
normal subgroup `Γ' ∩ Γ` of finite index, with trivial determinant, descends to a primitive that
is equivariant for the `det^{-e}`-twisted coefficient action of `Γ`. -/
theorem exists_twisted_primitive_of_normal [(Γ'.subgroupOf Γ).Normal]
    [Finite (Γ ⧸ Γ'.subgroupOf Γ)] (e : ℤ) (hdet : ∀ γ ∈ Γ', γ.val.det = 1)
    {η : Coordinates → FormValue n k} {ζ : Coordinates → FormValue n (k + 1)}
    (hη : ContDiffOn ℝ ∞ η positiveCoordinates) (hη' : IsEquivariant Γ' n k η)
    (hζ : IsTwEquivariant (detChar e) Γ n (k + 1) ζ)
    (hd : ∀ x ∈ positiveCoordinates, extDeriv η x = ζ x) :
    ∃ η'' : Coordinates → FormValue n k, ContDiffOn ℝ ∞ η'' positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η'' x = 0) ∧ IsTwEquivariant (detChar e) Γ n k η'' ∧
      ∀ x ∈ positiveCoordinates, extDeriv η'' x = ζ x := by
  have h1 : ∀ γ ∈ Γ', ∀ x ∈ positiveCoordinates, twPull (detChar e) n k γ η x = η x := by
    intro γ hγ x hx
    have : twPull (detChar e) n k γ η = twPull (1 : RealGL →* ℝ) n k γ η := by
      funext y
      simp only [twPull, detChar_of_det_one e (hdet γ hγ), MonoidHom.one_apply]
    rw [this, twPull_one_eq]
    exact isEquivariant_iff_actPull.mp hη' γ hγ x hx
  exact exists_descent_primitive (detChar e) hη h1 hζ hd

end Corollaries


end TernaryPeriodPolynomials.Argument.GeneralCoercivity
