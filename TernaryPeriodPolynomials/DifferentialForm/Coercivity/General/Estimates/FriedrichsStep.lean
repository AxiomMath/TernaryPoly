module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.CutoffStep
public import TernaryPeriodPolynomials.Analysis.Bounded.WeakCommutatorTransport
public import TernaryPeriodPolynomials.Analysis.DenseRegularizerApproximation

@[expose] public section


/-! # General coercivity, Tier B: the abstract Friedrichs step

The abstract Friedrichs argument in the `L²` completions.  A family `r_j` of regularisers of the
compactly supported forms in the degrees `k, k+1, k+2` is *admissible for `Q`* when it is uniformly
bounded, convergent, has transposes, has bounded `d r_j` and `δ r_j`, and has commutators with `d`
and `δ` that are uniformly bounded and strongly null on the forms supported over `Q`.  Then every
element of the maximal graph supported over `Q` lies in the joint graph closure.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric

variable {Γ : Subgroup RealGL} [hΓ : Fact (Admissible Γ)] {n : ℕ}

/-- A uniformly bounded, strongly convergent family of regularisers in one degree. -/
structure RegFamily (Γ : Subgroup RealGL) [Fact (Admissible Γ)] (n p : ℕ) where
  r : ℕ → CForm Γ n p →ₗ[ℝ] CForm Γ n p
  K : ℝ
  K_nonneg : 0 ≤ K
  bound : ∀ j a, ‖incl Γ n p (r j a)‖ ≤ K * ‖incl Γ n p a‖
  conv : ∀ a, ∃ b, Tendsto (fun j => incl Γ n p (r j a)) atTop (𝓝 b)

/-- Every member of the family has an `L²`-transpose on the compactly supported forms. -/
def RegFamily.HasTranspose {p : ℕ} (F : RegFamily Γ n p) : Prop :=
  ∀ j, ∃ τ : CForm Γ n p → CForm Γ n p, ∀ a b,
    inner ℝ (incl Γ n p (F.r j a)) (incl Γ n p b) = inner ℝ (incl Γ n p a) (incl Γ n p (τ b))

/-- The commutator `d r_j - r_j d`. -/
def commD {k : ℕ} (F1 : RegFamily Γ n (k + 1)) (F2 : RegFamily Γ n (k + 2)) (j : ℕ) :
    CForm Γ n (k + 1) →ₗ[ℝ] CForm Γ n (k + 2) :=
  (CForm.d Γ n (k + 1)).comp (F1.r j) + (-1 : ℝ) • (F2.r j).comp (CForm.d Γ n (k + 1))

/-- The commutator `δ r_j - r_j δ`. -/
def commδ {k : ℕ} (F0 : RegFamily Γ n k) (F1 : RegFamily Γ n (k + 1)) (j : ℕ) :
    CForm Γ n (k + 1) →ₗ[ℝ] CForm Γ n k :=
  (CForm.delta Γ n k).comp (F1.r j) + (-1 : ℝ) • (F0.r j).comp (CForm.delta Γ n k)

/-- The data of regularisers admissible for forms supported over `Q`. -/
structure FriedrichsCore (Γ : Subgroup RealGL) [Fact (Admissible Γ)] (n k : ℕ)
    (Q : Set (OrbitSpace Γ)) where
  F0 : RegFamily Γ n k
  F1 : RegFamily Γ n (k + 1)
  F2 : RegFamily Γ n (k + 2)
  T0 : F0.HasTranspose
  T2 : F2.HasTranspose
  conv1 : ∀ a ∈ SuppIn Q n (k + 1),
    Tendsto (fun j => incl Γ n (k + 1) (F1.r j a)) atTop (𝓝 (incl Γ n (k + 1) a))
  fixed_d : ∀ j, ∃ Kj : ℝ, 0 ≤ Kj ∧ ∀ a,
    ‖incl Γ n (k + 2) (CForm.d Γ n (k + 1) (F1.r j a))‖ ≤ Kj * ‖incl Γ n (k + 1) a‖
  fixed_δ : ∀ j, ∃ Kj : ℝ, 0 ≤ Kj ∧ ∀ a,
    ‖incl Γ n k (CForm.delta Γ n k (F1.r j a))‖ ≤ Kj * ‖incl Γ n (k + 1) a‖
  commD_bound : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ j a,
    ‖incl Γ n (k + 2) (commD F1 F2 j a)‖ ≤ Kc * ‖incl Γ n (k + 1) a‖
  commD_conv : ∀ a ∈ SuppIn Q n (k + 1),
    Tendsto (fun j => incl Γ n (k + 2) (commD F1 F2 j a)) atTop (𝓝 0)
  commδ_bound : ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ j a,
    ‖incl Γ n k (commδ F0 F1 j a)‖ ≤ Kc * ‖incl Γ n (k + 1) a‖
  commδ_conv : ∀ a ∈ SuppIn Q n (k + 1),
    Tendsto (fun j => incl Γ n k (commδ F0 F1 j a)) atTop (𝓝 0)

/-- A uniformly bounded sequence of operators converging on a set converges on its closure. -/
theorem tendsto_of_mem_closure {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ℕ → E →L[ℝ] F) (f : E →L[ℝ] F) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) {D : Set E}
    (hconv : ∀ x ∈ D, Tendsto (fun j => T j x) atTop (𝓝 (f x))) {x : E} (hx : x ∈ closure D) :
    Tendsto (fun j => T j x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * (C + ‖f‖ + 1)) := by positivity
  obtain ⟨x', hx'D, hx'⟩ := Metric.mem_closure_iff.mp hx _ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hconv x' hx'D) (ε / 3) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have h1 : dist (T j x) (T j x') ≤ C * (ε / (3 * (C + ‖f‖ + 1))) := by
    rw [dist_eq_norm, ← map_sub]
    refine ((T j).le_opNorm _).trans ?_
    have : ‖x - x'‖ ≤ ε / (3 * (C + ‖f‖ + 1)) := by
      rw [← dist_eq_norm]
      exact hx'.le
    exact mul_le_mul (hT j) this (norm_nonneg _) hC
  have h2 : dist (f x') (f x) ≤ ‖f‖ * (ε / (3 * (C + ‖f‖ + 1))) := by
    rw [dist_eq_norm, ← map_sub]
    refine (f.le_opNorm _).trans ?_
    have : ‖x' - x‖ ≤ ε / (3 * (C + ‖f‖ + 1)) := by
      rw [← dist_eq_norm, dist_comm]
      exact hx'.le
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have h3 := hN j hj
  have h4 : (C + ‖f‖) * (ε / (3 * (C + ‖f‖ + 1))) ≤ ε / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [norm_nonneg f]
  calc dist (T j x) (f x) ≤ dist (T j x) (T j x') + dist (T j x') (f x') + dist (f x') (f x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by nlinarith

theorem cancel_sub_smul' {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V) :
    a - (a + (-1 : ℝ) • b) = b := by
  rw [neg_one_smul]
  abel

section Ops

variable {k : ℕ} {Q : Set (OrbitSpace Γ)} (Z : FriedrichsCore Γ n k Q)

/-- The bounded extensions of the regularisers to the completions. -/
def FriedrichsCore.R0 (j : ℕ) : Hilbert Γ n k →L[ℝ] Hilbert Γ n k :=
  hext Γ n k k (Z.F0.r j) Z.F0.K (Z.F0.bound j)

def FriedrichsCore.R1 (j : ℕ) : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n (k + 1) :=
  hext Γ n (k + 1) (k + 1) (Z.F1.r j) Z.F1.K (Z.F1.bound j)

def FriedrichsCore.R2 (j : ℕ) : Hilbert Γ n (k + 2) →L[ℝ] Hilbert Γ n (k + 2) :=
  hext Γ n (k + 2) (k + 2) (Z.F2.r j) Z.F2.K (Z.F2.bound j)

/-- The constants of the fixed-scale bounds. -/
def FriedrichsCore.Kd (j : ℕ) : ℝ := (Z.fixed_d j).choose

def FriedrichsCore.Kδ (j : ℕ) : ℝ := (Z.fixed_δ j).choose

def FriedrichsCore.Kcd : ℝ := Z.commD_bound.choose

def FriedrichsCore.Kcδ : ℝ := Z.commδ_bound.choose

theorem FriedrichsCore.Kd_nonneg (j : ℕ) : 0 ≤ Z.Kd j := (Z.fixed_d j).choose_spec.1
theorem FriedrichsCore.Kδ_nonneg (j : ℕ) : 0 ≤ Z.Kδ j := (Z.fixed_δ j).choose_spec.1
theorem FriedrichsCore.Kcd_nonneg : 0 ≤ Z.Kcd := Z.commD_bound.choose_spec.1
theorem FriedrichsCore.Kcδ_nonneg : 0 ≤ Z.Kcδ := Z.commδ_bound.choose_spec.1

/-- The extension of `d r_j`. -/
def FriedrichsCore.Vd (j : ℕ) : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n (k + 2) :=
  hext Γ n (k + 1) (k + 2) ((CForm.d Γ n (k + 1)).comp (Z.F1.r j)) (Z.Kd j)
    (Z.fixed_d j).choose_spec.2

/-- The extension of `δ r_j`. -/
def FriedrichsCore.Vδ (j : ℕ) : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n k :=
  hext Γ n (k + 1) k ((CForm.delta Γ n k).comp (Z.F1.r j)) (Z.Kδ j) (Z.fixed_δ j).choose_spec.2

/-- The extension of the commutator `d r_j - r_j d`. -/
def FriedrichsCore.Cd (j : ℕ) : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n (k + 2) :=
  hext Γ n (k + 1) (k + 2) (commD Z.F1 Z.F2 j) Z.Kcd (Z.commD_bound.choose_spec.2 j)

/-- The extension of the commutator `δ r_j - r_j δ`. -/
def FriedrichsCore.Cδ (j : ℕ) : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n k :=
  hext Γ n (k + 1) k (commδ Z.F0 Z.F1 j) Z.Kcδ (Z.commδ_bound.choose_spec.2 j)

theorem FriedrichsCore.Vd_incl (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Vd j (incl Γ n (k + 1) a) = incl Γ n (k + 2) (CForm.d Γ n (k + 1) (Z.F1.r j a)) :=
  hext_incl ((CForm.d Γ n (k + 1)).comp (Z.F1.r j)) (Z.Kd j) (Z.fixed_d j).choose_spec.2 a

theorem FriedrichsCore.Vδ_incl (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Vδ j (incl Γ n (k + 1) a) = incl Γ n k (CForm.delta Γ n k (Z.F1.r j a)) :=
  hext_incl ((CForm.delta Γ n k).comp (Z.F1.r j)) (Z.Kδ j) (Z.fixed_δ j).choose_spec.2 a

theorem FriedrichsCore.R0_incl (j : ℕ) (a : CForm Γ n k) :
    Z.R0 j (incl Γ n k a) = incl Γ n k (Z.F0.r j a) :=
  hext_incl (Z.F0.r j) Z.F0.K (Z.F0.bound j) a

theorem FriedrichsCore.R1_incl (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.R1 j (incl Γ n (k + 1) a) = incl Γ n (k + 1) (Z.F1.r j a) :=
  hext_incl (Z.F1.r j) Z.F1.K (Z.F1.bound j) a

theorem FriedrichsCore.R2_incl (j : ℕ) (a : CForm Γ n (k + 2)) :
    Z.R2 j (incl Γ n (k + 2) a) = incl Γ n (k + 2) (Z.F2.r j a) :=
  hext_incl (Z.F2.r j) Z.F2.K (Z.F2.bound j) a

theorem FriedrichsCore.Cd_incl (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Cd j (incl Γ n (k + 1) a) = incl Γ n (k + 2) (CForm.d Γ n (k + 1) (Z.F1.r j a)) +
      (-1 : ℝ) • incl Γ n (k + 2) (Z.F2.r j (CForm.d Γ n (k + 1) a)) :=
  (hext_incl (commD Z.F1 Z.F2 j) Z.Kcd (Z.commD_bound.choose_spec.2 j) a).trans
    ((map_add (incl Γ n (k + 2)) _ _).trans
      (congrArg₂ (· + ·) rfl (map_smul (incl Γ n (k + 2)) _ _)))

theorem FriedrichsCore.Cδ_incl (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Cδ j (incl Γ n (k + 1) a) = incl Γ n k (CForm.delta Γ n k (Z.F1.r j a)) +
      (-1 : ℝ) • incl Γ n k (Z.F0.r j (CForm.delta Γ n k a)) :=
  (hext_incl (commδ Z.F0 Z.F1 j) Z.Kcδ (Z.commδ_bound.choose_spec.2 j) a).trans
    ((map_add (incl Γ n k) _ _).trans (congrArg₂ (· + ·) rfl (map_smul (incl Γ n k) _ _)))

/-- The transposes. -/
def FriedrichsCore.tau0 (j : ℕ) : CForm Γ n k → CForm Γ n k := Classical.choose (Z.T0 j)

def FriedrichsCore.tau2 (j : ℕ) : CForm Γ n (k + 2) → CForm Γ n (k + 2) :=
  Classical.choose (Z.T2 j)

theorem FriedrichsCore.tau0_spec (j : ℕ) (a b : CForm Γ n k) :
    inner ℝ (incl Γ n k (Z.F0.r j a)) (incl Γ n k b) =
      inner ℝ (incl Γ n k a) (incl Γ n k (Z.tau0 j b)) :=
  Classical.choose_spec (Z.T0 j) a b

theorem FriedrichsCore.tau2_spec (j : ℕ) (a b : CForm Γ n (k + 2)) :
    inner ℝ (incl Γ n (k + 2) (Z.F2.r j a)) (incl Γ n (k + 2) b) =
      inner ℝ (incl Γ n (k + 2) a) (incl Γ n (k + 2) (Z.tau2 j b)) :=
  Classical.choose_spec (Z.T2 j) a b

theorem FriedrichsCore.transport_d (j : ℕ) {u : Hilbert Γ n (k + 1)} {v : Hilbert Γ n (k + 2)}
    (hv : (u, v) ∈ (maxD Γ n (k + 1)).graph) : Z.Vd j u = Z.R2 j v + Z.Cd j u := by
  have hcore : ∀ a : CForm Γ n (k + 1), Z.Vd j (incl Γ n (k + 1) a) - Z.Cd j (incl Γ n (k + 1) a) =
      Z.R2 j (incl Γ n (k + 2) (CForm.d Γ n (k + 1) a)) := fun a =>
    (congrArg₂ (· - ·) (Z.Vd_incl j a) (Z.Cd_incl j a)).trans
      ((cancel_sub_smul' _ _).trans (Z.R2_incl j _).symm)
  have htr : ∀ (y : Hilbert Γ n (k + 2)) (b : CForm Γ n (k + 2)),
      inner ℝ (Z.R2 j y) (incl Γ n (k + 2) b) = inner ℝ y (incl Γ n (k + 2) (Z.tau2 j b)) :=
    fun y b => inner_hext_incl (Z.F2.r j) (Z.F2.bound j) (Z.tau2 j) (Z.tau2_spec j) y b
  have hw := (mem_maxD_graph_iff Γ n (k + 1) u v).mp hv
  exact TernaryPoly.BoundedWeakCommutatorTransport.transport (incl Γ n (k + 1)) (incl Γ n (k + 2))
    (incl_dense Γ n (k + 1)) (incl_dense Γ n (k + 2)) (CForm.d Γ n (k + 1))
    (CForm.delta Γ n (k + 1)) (Z.tau2 j) (Z.R2 j) (Z.Vd j) (Z.Cd j)
    (fun a b => inner_incl_d Γ n (k + 1) a b) htr hcore u v hw

theorem FriedrichsCore.transport_δ (j : ℕ) {u : Hilbert Γ n (k + 1)} {w : Hilbert Γ n k}
    (hw : (u, w) ∈ (maxDelta Γ n k).graph) : Z.Vδ j u = Z.R0 j w + Z.Cδ j u := by
  have hcore : ∀ a : CForm Γ n (k + 1), Z.Vδ j (incl Γ n (k + 1) a) - Z.Cδ j (incl Γ n (k + 1) a) =
      Z.R0 j (incl Γ n k (CForm.delta Γ n k a)) := fun a =>
    (congrArg₂ (· - ·) (Z.Vδ_incl j a) (Z.Cδ_incl j a)).trans
      ((cancel_sub_smul' _ _).trans (Z.R0_incl j _).symm)
  have htr : ∀ (y : Hilbert Γ n k) (b : CForm Γ n k),
      inner ℝ (Z.R0 j y) (incl Γ n k b) = inner ℝ y (incl Γ n k (Z.tau0 j b)) :=
    fun y b => inner_hext_incl (Z.F0.r j) (Z.F0.bound j) (Z.tau0 j) (Z.tau0_spec j) y b
  have hw' := (mem_maxDelta_graph_iff Γ n k u w).mp hw
  exact TernaryPoly.BoundedWeakCommutatorTransport.transport (incl Γ n (k + 1)) (incl Γ n k)
    (incl_dense Γ n (k + 1)) (incl_dense Γ n k) (CForm.delta Γ n k)
    (CForm.d Γ n k) (Z.tau0 j) (Z.R0 j) (Z.Vδ j) (Z.Cδ j)
    (fun a b => (real_inner_comm _ _).trans ((inner_incl_d Γ n k b a).symm.trans
      (real_inner_comm _ _))) htr hcore u w hw'

theorem FriedrichsCore.Cd_incl' (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Cd j (incl Γ n (k + 1) a) = incl Γ n (k + 2) (commD Z.F1 Z.F2 j a) :=
  hext_incl (commD Z.F1 Z.F2 j) Z.Kcd (Z.commD_bound.choose_spec.2 j) a

theorem FriedrichsCore.Cδ_incl' (j : ℕ) (a : CForm Γ n (k + 1)) :
    Z.Cδ j (incl Γ n (k + 1) a) = incl Γ n k (commδ Z.F0 Z.F1 j a) :=
  hext_incl (commδ Z.F0 Z.F1 j) Z.Kcδ (Z.commδ_bound.choose_spec.2 j) a

theorem FriedrichsCore.mem_joint_j (j : ℕ) (x : Hilbert Γ n (k + 1)) :
    (Z.R1 j x, Z.Vd j x, Z.Vδ j x) ∈ jointGraph Γ n k := by
  have h := DenseRegularizerApproximation.exists_simultaneous_sequence (incl Γ n (k + 1))
    (incl_dense Γ n (k + 1)) (Z.F1.r j)
    (fun v => incl Γ n (k + 2) (CForm.d Γ n (k + 1) v))
    (fun v => incl Γ n k (CForm.delta Γ n k v)) (Z.R1 j) (Z.Vd j) (Z.Vδ j)
    (fun v => Z.R1_incl j v) (fun v => Z.Vd_incl j v) (fun v => Z.Vδ_incl j v) x
  obtain ⟨u, hx, hy, hz⟩ := h
  exact JointEmbeddedGraphClosure.mem_of_sequence (incl Γ n (k + 1))
    ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))) ((incl Γ n k).comp (CForm.delta Γ n k))
    u _ _ _ hx hy hz

end Ops

section Joint

variable {k : ℕ}

theorem jointGraph_mem_maxD {x : Hilbert Γ n (k + 1)} {y : Hilbert Γ n (k + 2)}
    {z : Hilbert Γ n k} (h : (x, y, z) ∈ jointGraph Γ n k) :
    (x, y) ∈ (maxD Γ n (k + 1)).graph := by
  refine (mem_maxD_graph_iff Γ n (k + 1) x y).mpr (fun b => ?_)
  have hclosed : IsClosed {p : Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k |
      inner ℝ p.2.1 (incl Γ n (k + 2) b) = inner ℝ p.1 (incl Γ n (k + 1)
        (CForm.delta Γ n (k + 1) b))} :=
    isClosed_eq (continuous_snd.fst.inner continuous_const)
      (continuous_fst.inner continuous_const)
  have hrange : ((LinearMap.range ((incl Γ n (k + 1)).prod
      ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))
        |>.prod ((incl Γ n k).comp (CForm.delta Γ n k))))  : Submodule ℝ _) :
      Set (Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k)) ⊆
      {p | inner ℝ p.2.1 (incl Γ n (k + 2) b) = inner ℝ p.1 (incl Γ n (k + 1)
        (CForm.delta Γ n (k + 1) b))} := by
    rintro _ ⟨a, rfl⟩
    exact inner_incl_d Γ n (k + 1) a b
  have hmem : (x, y, z) ∈ closure ((LinearMap.range ((incl Γ n (k + 1)).prod
      ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))
        |>.prod ((incl Γ n k).comp (CForm.delta Γ n k))))  : Submodule ℝ _) :
      Set (Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact h
  exact closure_minimal hrange hclosed hmem

theorem jointGraph_mem_maxDelta {x : Hilbert Γ n (k + 1)} {y : Hilbert Γ n (k + 2)}
    {z : Hilbert Γ n k} (h : (x, y, z) ∈ jointGraph Γ n k) :
    (x, z) ∈ (maxDelta Γ n k).graph := by
  refine (mem_maxDelta_graph_iff Γ n k x z).mpr (fun b => ?_)
  have hclosed : IsClosed {p : Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k |
      inner ℝ p.2.2 (incl Γ n k b) = inner ℝ p.1 (incl Γ n (k + 1) (CForm.d Γ n k b))} :=
    isClosed_eq (continuous_snd.snd.inner continuous_const)
      (continuous_fst.inner continuous_const)
  have hrange : ((LinearMap.range ((incl Γ n (k + 1)).prod
      ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))
        |>.prod ((incl Γ n k).comp (CForm.delta Γ n k))))  : Submodule ℝ _) :
      Set (Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k)) ⊆
      {p | inner ℝ p.2.2 (incl Γ n k b) = inner ℝ p.1 (incl Γ n (k + 1) (CForm.d Γ n k b))} := by
    rintro _ ⟨a, rfl⟩
    exact (real_inner_comm _ _).trans ((inner_incl_d Γ n k b a).symm.trans (real_inner_comm _ _))
  have hmem : (x, y, z) ∈ closure ((LinearMap.range ((incl Γ n (k + 1)).prod
      ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))
        |>.prod ((incl Γ n k).comp (CForm.delta Γ n k))))  : Submodule ℝ _) :
      Set (Hilbert Γ n (k + 1) × Hilbert Γ n (k + 2) × Hilbert Γ n k)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact h
  exact closure_minimal hrange hclosed hmem

theorem graph_eq_of_mem {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ.[ℝ] F) {x : E} {y y' : F}
    (h : (x, y) ∈ T.graph) (h' : (x, y') ∈ T.graph) : y = y' := by
  have := T.graph.sub_mem h h'
  rw [Prod.mk_sub_mk, sub_self] at this
  exact sub_eq_zero.mp (T.graph_fst_eq_zero_snd this rfl)

end Joint

section Limits

variable {k : ℕ} {Q : Set (OrbitSpace Γ)} (Z : FriedrichsCore Γ n k Q)

theorem FriedrichsCore.exists_lim_R2 (v : Hilbert Γ n (k + 2)) :
    ∃ v' : Hilbert Γ n (k + 2), Tendsto (fun j => Z.R2 j v) atTop (𝓝 v') := by
  have hD : Dense (Set.range (incl Γ n (k + 2))) := incl_dense Γ n (k + 2)
  have hb : ∀ j, ‖Z.R2 j‖ ≤ Z.F2.K := fun j =>
    opNorm_hext_le (Z.F2.r j) Z.F2.K_nonneg (Z.F2.bound j)
  have hconv : ∀ x ∈ Set.range (incl Γ n (k + 2)),
      ∃ y, Tendsto (fun j => Z.R2 j x) atTop (𝓝 y) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(Z.F2.conv a).choose, (tendsto_congr (fun j => Z.R2_incl j a)).mpr
      (Z.F2.conv a).choose_spec⟩
  exact exists_tendsto_of_dense (fun j => Z.R2 j) Z.F2.K_nonneg hb hD hconv v

theorem FriedrichsCore.exists_lim_R0 (w : Hilbert Γ n k) :
    ∃ w' : Hilbert Γ n k, Tendsto (fun j => Z.R0 j w) atTop (𝓝 w') := by
  have hD : Dense (Set.range (incl Γ n k)) := incl_dense Γ n k
  have hb : ∀ j, ‖Z.R0 j‖ ≤ Z.F0.K := fun j =>
    opNorm_hext_le (Z.F0.r j) Z.F0.K_nonneg (Z.F0.bound j)
  have hconv : ∀ x ∈ Set.range (incl Γ n k),
      ∃ y, Tendsto (fun j => Z.R0 j x) atTop (𝓝 y) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(Z.F0.conv a).choose, (tendsto_congr (fun j => Z.R0_incl j a)).mpr
      (Z.F0.conv a).choose_spec⟩
  exact exists_tendsto_of_dense (fun j => Z.R0 j) Z.F0.K_nonneg hb hD hconv w

theorem FriedrichsCore.tendsto_R1 {u : Hilbert Γ n (k + 1)}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1))) :
    Tendsto (fun j => Z.R1 j u) atTop (𝓝 u) := by
  have := tendsto_of_mem_closure (fun j => Z.R1 j) (ContinuousLinearMap.id ℝ _) Z.F1.K_nonneg
    (fun j => opNorm_hext_le (Z.F1.r j) Z.F1.K_nonneg (Z.F1.bound j))
    (D := incl Γ n (k + 1) '' SuppIn Q n (k + 1))
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact (tendsto_congr (fun j => Z.R1_incl j a)).mpr (Z.conv1 a ha)) hu
  exact this

theorem FriedrichsCore.tendsto_Cd {u : Hilbert Γ n (k + 1)}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1))) :
    Tendsto (fun j => Z.Cd j u) atTop (𝓝 0) := by
  have := tendsto_of_mem_closure (fun j => Z.Cd j)
    (0 : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n (k + 2))
    Z.Kcd_nonneg (fun j => opNorm_hext_le (commD Z.F1 Z.F2 j) Z.Kcd_nonneg
      (Z.commD_bound.choose_spec.2 j))
    (D := incl Γ n (k + 1) '' SuppIn Q n (k + 1))
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact (tendsto_congr (fun j => Z.Cd_incl' j a)).mpr (Z.commD_conv a ha)) hu
  exact this

theorem FriedrichsCore.tendsto_Cδ {u : Hilbert Γ n (k + 1)}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1))) :
    Tendsto (fun j => Z.Cδ j u) atTop (𝓝 0) := by
  have := tendsto_of_mem_closure (fun j => Z.Cδ j)
    (0 : Hilbert Γ n (k + 1) →L[ℝ] Hilbert Γ n k)
    Z.Kcδ_nonneg (fun j => opNorm_hext_le (commδ Z.F0 Z.F1 j) Z.Kcδ_nonneg
      (Z.commδ_bound.choose_spec.2 j))
    (D := incl Γ n (k + 1) '' SuppIn Q n (k + 1))
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact (tendsto_congr (fun j => Z.Cδ_incl' j a)).mpr (Z.commδ_conv a ha)) hu
  exact this

theorem FriedrichsCore.tendsto_Vd {u : Hilbert Γ n (k + 1)} {v v' : Hilbert Γ n (k + 2)}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)))
    (hv : (u, v) ∈ (maxD Γ n (k + 1)).graph) (hv' : Tendsto (fun j => Z.R2 j v) atTop (𝓝 v')) :
    Tendsto (fun j => Z.Vd j u) atTop (𝓝 v') := by
  have h1 := hv'.add (Z.tendsto_Cd hu)
  have h2 : Tendsto (fun j => Z.R2 j v + Z.Cd j u) atTop (𝓝 v') :=
    h1.mono_right (le_of_eq (congrArg 𝓝 (add_zero v')))
  exact (tendsto_congr (fun j => Z.transport_d j hv)).mpr h2

theorem FriedrichsCore.tendsto_Vδ {u : Hilbert Γ n (k + 1)} {w w' : Hilbert Γ n k}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)))
    (hw : (u, w) ∈ (maxDelta Γ n k).graph) (hw' : Tendsto (fun j => Z.R0 j w) atTop (𝓝 w')) :
    Tendsto (fun j => Z.Vδ j u) atTop (𝓝 w') := by
  have h1 := hw'.add (Z.tendsto_Cδ hu)
  have h2 : Tendsto (fun j => Z.R0 j w + Z.Cδ j u) atTop (𝓝 w') :=
    h1.mono_right (le_of_eq (congrArg 𝓝 (add_zero w')))
  exact (tendsto_congr (fun j => Z.transport_δ j hw)).mpr h2

end Limits

theorem FriedrichsCore.joint_limit {k : ℕ} {Q : Set (OrbitSpace Γ)}
    (Z : FriedrichsCore Γ n k Q) {u : Hilbert Γ n (k + 1)} {v v' : Hilbert Γ n (k + 2)}
    {w w' : Hilbert Γ n k} (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)))
    (hv : (u, v) ∈ (maxD Γ n (k + 1)).graph) (hw : (u, w) ∈ (maxDelta Γ n k).graph)
    (hv' : Tendsto (fun j => Z.R2 j v) atTop (𝓝 v'))
    (hw' : Tendsto (fun j => Z.R0 j w) atTop (𝓝 w')) : (u, v', w') ∈ jointGraph Γ n k :=
  JointEmbeddedGraphClosure.mem_of_limits (incl Γ n (k + 1))
    ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))) ((incl Γ n k).comp (CForm.delta Γ n k))
    (fun j => Z.R1 j u) (fun j => Z.Vd j u) (fun j => Z.Vδ j u)
    (fun j => Z.mem_joint_j j u) u v' w' (Z.tendsto_R1 hu) (Z.tendsto_Vd hu hv hv')
    (Z.tendsto_Vδ hu hw hw')

theorem FriedrichsCore.mem_joint_of_limits {k : ℕ} {Q : Set (OrbitSpace Γ)}
    (Z : FriedrichsCore Γ n k Q) {u : Hilbert Γ n (k + 1)} {v v' : Hilbert Γ n (k + 2)}
    {w w' : Hilbert Γ n k} (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)))
    (hv : (u, v) ∈ (maxD Γ n (k + 1)).graph) (hw : (u, w) ∈ (maxDelta Γ n k).graph)
    (hv' : Tendsto (fun j => Z.R2 j v) atTop (𝓝 v'))
    (hw' : Tendsto (fun j => Z.R0 j w) atTop (𝓝 w')) : (u, v, w) ∈ jointGraph Γ n k := by
  have hJ := Z.joint_limit hu hv hw hv' hw'
  have e1 : v = v' := graph_eq_of_mem (maxD Γ n (k + 1)) hv (jointGraph_mem_maxD hJ)
  have e2 : w = w' := graph_eq_of_mem (maxDelta Γ n k) hw (jointGraph_mem_maxDelta hJ)
  subst e1
  subst e2
  exact hJ

/-- **The Friedrichs step**: an element of the maximal graph supported over `Q` lies in the joint
graph closure, given admissible regularisers. -/
theorem FriedrichsCore.mem_joint {k : ℕ} {Q : Set (OrbitSpace Γ)} (Z : FriedrichsCore Γ n k Q)
    {u : Hilbert Γ n (k + 1)} {v : Hilbert Γ n (k + 2)} {w : Hilbert Γ n k}
    (hu : u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)))
    (hv : (u, v) ∈ (maxD Γ n (k + 1)).graph) (hw : (u, w) ∈ (maxDelta Γ n k).graph) :
    (u, v, w) ∈ jointGraph Γ n k :=
  Z.mem_joint_of_limits hu hv hw (Z.exists_lim_R2 v).choose_spec (Z.exists_lim_R0 w).choose_spec

/-- Compactly supported Gaffney from admissible regularisers for every compact set. -/
theorem compactGaffneyAt_of_cores (k : ℕ)
    (h : ∀ Q : Set (OrbitSpace Γ), IsCompact Q → Nonempty (FriedrichsCore Γ n k Q)) :
    CompactGaffneyAt Γ n k := fun Q hQ _ _ _ hu hv hw =>
  (Classical.choice (h Q hQ)).mem_joint hu hv hw

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
