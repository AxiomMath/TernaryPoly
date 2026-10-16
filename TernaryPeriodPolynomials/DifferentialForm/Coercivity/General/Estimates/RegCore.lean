module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.RegOperators

@[expose] public section


/-! # General coercivity, Tier B: admissible regularisers for every compact set

For every compact set `Q` of the orbit space the regularisers `r_j` built from adapted cutoffs form a
`FriedrichsCore`; hence the Friedrichs step gives Gaffney's lemma for elements supported over `Q`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n : ℕ} [hΓ : Fact (Admissible Γ)] {Q : Set (OrbitSpace Γ)}

omit hΓ in
/-- A local operator preserves the support condition over a closed set. -/
theorem suppIn_map {p q : ℕ} (hQ : IsClosed Q) (D : CForm Γ n p → CForm Γ n q)
    (hloc : ∀ (a : CForm Γ n p) (x : Coordinates), x ∈ positiveCoordinates →
      CForm.fn a =ᶠ[𝓝 x] 0 → CForm.fn (D a) x = 0) {a : CForm Γ n p} (ha : a ∈ SuppIn Q n p) :
    D a ∈ SuppIn Q n q := by
  intro x hx hne
  by_contra hxQ
  apply hne
  apply hloc a x hx
  have hcont : ContinuousAt (coordProj Γ) x :=
    continuousOn_coordProj.continuousAt (isOpen_positiveCoordinates.mem_nhds hx)
  have hev : ∀ᶠ y in 𝓝 x, coordProj Γ y ∈ Qᶜ := hcont.eventually (hQ.isOpen_compl.mem_nhds hxQ)
  filter_upwards [hev, isOpen_positiveCoordinates.mem_nhds hx] with y hy hyΩ
  by_contra h0
  exact hy (ha y hyΩ h0)

/-- The exterior derivative on equivariant forms, as an operator datum. -/
def dOp (R : RegData Γ Q) (hQ : IsClosed Q) (k : ℕ) : OpData (n := n) R (k + 1) (k + 2) where
  F := dDatum (n := n) (k + 1) R.C.θ_compact.isCompact R.C.θ_pos
  Dform := CForm.d Γ n (k + 1)
  hint := fun g hg => hΓ.out.d_avgForm hg
  hfn := fun a x hx => CForm.d_apply a hx
  hsupp := fun a ha => suppIn_map hQ (CForm.d Γ n (k + 1)) (fun a x hx h => by
    rw [CForm.d_apply a hx]
    have hx' : x ∉ tsupport (CForm.fn a) := (notMem_tsupport_iff_eventuallyEq.mpr h)
    exact image_eq_zero_of_notMem_tsupport (f := extDeriv (CForm.fn a))
      (fun hh => hx' (tsupport_extDeriv_subset n (k + 1) (CForm.fn a) hh))) ha

/-- The codifferential on equivariant forms, as an operator datum. -/
def deltaOp (R : RegData Γ Q) (hQ : IsClosed Q) (k : ℕ) : OpData (n := n) R (k + 1) k where
  F := deltaDatum (n := n) k R.C.θ_compact.isCompact R.C.θ_pos
  Dform := CForm.delta Γ n k
  hint := fun g hg => hΓ.out.delta_avgForm hg
  hfn := fun a x hx => CForm.delta_apply hΓ.out a hx
  hsupp := fun a ha => suppIn_map hQ (CForm.delta Γ n k) (fun a x hx h => by
    rw [CForm.delta_apply hΓ.out a hx]
    have hx' : x ∉ tsupport (CForm.fn a) := (notMem_tsupport_iff_eventuallyEq.mpr h)
    exact image_eq_zero_of_notMem_tsupport (f := localAdjoint n k (CForm.fn a))
      (fun hh => hx' (tsupport_localAdjoint n k (CForm.fn a) hh))) ha

section Core

variable (R : RegData Γ Q) (hQ : IsClosed Q) (k : ℕ)

include hQ

theorem fixed_d_field (j : ℕ) : ∃ Kj : ℝ, 0 ≤ Kj ∧ ∀ a : CForm Γ n (k + 1),
    ‖incl Γ n (k + 2) (CForm.d Γ n (k + 1) ((R.regFamily (n := n) (k + 1)).r j a))‖ ≤
      Kj * ‖incl Γ n (k + 1) a‖ := by
  have hc : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hK := (dOp (n := n) R hQ k).exists_normSq_fixed_le hc
  exact ⟨Real.sqrt hK.choose, Real.sqrt_nonneg _, fun a =>
    norm_incl_le_of_normSq_le hK.choose_spec.1 _ _ (hK.choose_spec.2 a)⟩

theorem fixed_δ_field (j : ℕ) : ∃ Kj : ℝ, 0 ≤ Kj ∧ ∀ a : CForm Γ n (k + 1),
    ‖incl Γ n k (CForm.delta Γ n k ((R.regFamily (n := n) (k + 1)).r j a))‖ ≤
      Kj * ‖incl Γ n (k + 1) a‖ := by
  have hc : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hK := (deltaOp (n := n) R hQ k).exists_normSq_fixed_le hc
  exact ⟨Real.sqrt hK.choose, Real.sqrt_nonneg _, fun a =>
    norm_incl_le_of_normSq_le hK.choose_spec.1 _ _ (hK.choose_spec.2 a)⟩

theorem commD_field : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (j : ℕ) (a : CForm Γ n (k + 1)),
    ‖incl Γ n (k + 2) (commD (R.regFamily (n := n) (k + 1)) (R.regFamily (n := n) (k + 2)) j a)‖ ≤
      Kc * ‖incl Γ n (k + 1) a‖ := by
  have hK := (dOp (n := n) R hQ k).exists_normSq_comm_le
  exact ⟨Real.sqrt hK.choose, Real.sqrt_nonneg _, fun j a =>
    norm_incl_le_of_normSq_le hK.choose_spec.1 _ _
      (hK.choose_spec.2 (by positivity : (0 : ℝ) < (j : ℝ) + 1) a)⟩

theorem commδ_field : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (j : ℕ) (a : CForm Γ n (k + 1)),
    ‖incl Γ n k (commδ (R.regFamily (n := n) k) (R.regFamily (n := n) (k + 1)) j a)‖ ≤
      Kc * ‖incl Γ n (k + 1) a‖ := by
  have hK := (deltaOp (n := n) R hQ k).exists_normSq_comm_le
  exact ⟨Real.sqrt hK.choose, Real.sqrt_nonneg _, fun j a =>
    norm_incl_le_of_normSq_le hK.choose_spec.1 _ _
      (hK.choose_spec.2 (by positivity : (0 : ℝ) < (j : ℝ) + 1) a)⟩

theorem commD_conv_field {a : CForm Γ n (k + 1)} (ha : a ∈ SuppIn Q n (k + 1)) :
    Tendsto (fun j => incl Γ n (k + 2) (commD (R.regFamily (n := n) (k + 1))
      (R.regFamily (n := n) (k + 2)) j a)) atTop (𝓝 0) :=
  (dOp (n := n) R hQ k).comm_tendsto ha

theorem commδ_conv_field {a : CForm Γ n (k + 1)} (ha : a ∈ SuppIn Q n (k + 1)) :
    Tendsto (fun j => incl Γ n k (commδ (R.regFamily (n := n) k)
      (R.regFamily (n := n) (k + 1)) j a)) atTop (𝓝 0) :=
  (deltaOp (n := n) R hQ k).comm_tendsto ha

omit hQ in
theorem conv1_field {a : CForm Γ n (k + 1)} (ha : a ∈ SuppIn Q n (k + 1)) :
    Tendsto (fun j => incl Γ n (k + 1) ((R.regFamily (n := n) (k + 1)).r j a)) atTop
      (𝓝 (incl Γ n (k + 1) a)) := by
  have h := R.regSeq_tendsto (k + 1) a
  have e : R.avgCut (k + 1) a = a := R.avg_cut_eq_self (k + 1) ha
  exact h.mono_right (le_of_eq (congrArg 𝓝 (congrArg (incl Γ n (k + 1)) e)))

end Core

/-- Admissible regularisers for every closed set `Q`. -/
def friedrichsCore (R : RegData Γ Q) (hQ : IsClosed Q) (k : ℕ) : FriedrichsCore Γ n k Q where
  F0 := R.regFamily k
  F1 := R.regFamily (k + 1)
  F2 := R.regFamily (k + 2)
  T0 := R.regFamily_hasTranspose k
  T2 := R.regFamily_hasTranspose (k + 2)
  conv1 := fun _ ha => conv1_field R k ha
  fixed_d := fixed_d_field R hQ k
  fixed_δ := fixed_δ_field R hQ k
  commD_bound := commD_field R hQ k
  commD_conv := fun _ ha => commD_conv_field R hQ k ha
  commδ_bound := commδ_field R hQ k
  commδ_conv := fun _ ha => commδ_conv_field R hQ k ha

/-- **Gaffney's lemma for elements supported over a compact set** of the orbit space. -/
theorem compactGaffneyAt (k : ℕ) : CompactGaffneyAt Γ n k := by
  have : T2Space (OrbitSpace Γ) := hΓ.out.t2
  refine compactGaffneyAt_of_cores k (fun Q hQ => ?_)
  obtain ⟨R⟩ := RegData.exists (Γ := Γ) hQ
  exact ⟨friedrichsCore R hQ.isClosed k⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
