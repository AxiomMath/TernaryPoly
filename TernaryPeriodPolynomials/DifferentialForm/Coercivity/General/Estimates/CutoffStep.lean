module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Extend
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Commutator
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hodge

@[expose] public section


/-! # General coercivity, Tier B: the cutoff step of Gaffney's lemma

For a smooth `Γ`-invariant multiplier `c` with values in `[0,1]` and gradient bounded by `B`, the
Hilbert-space extension `Mc` of multiplication, the commutator `Ec = [d, c]` and the adjoint
commutator `Fc = [c, δ]` are bounded, and `x ↦ c x` preserves the maximal operators:
`(x, y) ∈ maxD ⇒ (c x, c y + Ec x) ∈ maxD`, `(x, z) ∈ maxδ ⇒ (c x, c z - Fc x) ∈ maxδ`.  A sequence of
such multipliers exhausting the orbit space with gradient bounds tending to zero reduces Gaffney's
lemma to elements supported over a compact subset of the orbit space.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.PolynomialFormMetric

variable {Γ : Subgroup RealGL} [hΓ : Fact (Admissible Γ)] {n m : ℕ}

/-- A uniformly bounded sequence of operators converging on a dense set converges to the
continuous limit everywhere. -/
theorem tendsto_of_dense_bounded {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ℕ → E →L[ℝ] F) (f : E →L[ℝ] F) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) {D : Set E} (hD : Dense D)
    (hconv : ∀ x ∈ D, Tendsto (fun j => T j x) atTop (𝓝 (f x))) (x : E) :
    Tendsto (fun j => T j x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (3 * (C + ‖f‖ + 1)) := by positivity
  obtain ⟨x', hx'D, hx'⟩ := Metric.mem_closure_iff.mp (hD x) _ hδ
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

namespace InvMult

variable (c : InvMult Γ)

/-- The adjoint commutator `c δ - δ c` of multiplication with the codifferential. -/
def commAdj (n m : ℕ) : CForm Γ n (m + 1) →ₗ[ℝ] CForm Γ n m :=
  c.mulMap.comp (CForm.delta Γ n m) + (-1 : ℝ) • (CForm.delta Γ n m).comp c.mulMap

theorem l2Form_commCore (a : CForm Γ n m) (b : CForm Γ n (m + 1)) :
    l2Form Γ n (m + 1) (c.commCore n m a) b = l2Form Γ n m a (c.commAdj n m b) := by
  have e1 : c.commCore n m a = CForm.d Γ n m (c.mulMap a) + (-1 : ℝ) • c.mulMap (CForm.d Γ n m a) :=
    rfl
  have e2 : c.commAdj n m b = c.mulMap (CForm.delta Γ n m b) + (-1 : ℝ) • CForm.delta Γ n m (c.mulMap b) :=
    rfl
  have h1 : l2Form Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) b =
      l2Form Γ n m a (c.mulMap (CForm.delta Γ n m b)) :=
    (hΓ.out.l2Form_d (c.mulMap a) b).trans (c.l2Form_mulMap a (CForm.delta Γ n m b))
  have h2 : l2Form Γ n (m + 1) (c.mulMap (CForm.d Γ n m a)) b =
      l2Form Γ n m a (CForm.delta Γ n m (c.mulMap b)) :=
    (c.l2Form_mulMap (CForm.d Γ n m a) b).trans (hΓ.out.l2Form_d a (c.mulMap b))
  have t1 : ∀ u v : CForm Γ n (m + 1), l2Form Γ n (m + 1) (u + v) b =
      l2Form Γ n (m + 1) u b + l2Form Γ n (m + 1) v b :=
    fun u v => LinearMap.map_add₂ (l2Form Γ n (m + 1)) u v b
  have t2 : ∀ (r : ℝ) (u : CForm Γ n (m + 1)), l2Form Γ n (m + 1) (r • u) b =
      r * l2Form Γ n (m + 1) u b :=
    fun r u => LinearMap.map_smul₂ (l2Form Γ n (m + 1)) r u b
  have t3 : ∀ u v : CForm Γ n m, l2Form Γ n m a (u + v) = l2Form Γ n m a u + l2Form Γ n m a v :=
    fun u v => map_add (l2Form Γ n m a) u v
  have t4 : ∀ (r : ℝ) (u : CForm Γ n m), l2Form Γ n m a (r • u) = r * l2Form Γ n m a u :=
    fun r u => map_smul (l2Form Γ n m a) r u
  have s1 : l2Form Γ n (m + 1) (c.commCore n m a) b =
      l2Form Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) b +
        (-1 : ℝ) * l2Form Γ n (m + 1) (c.mulMap (CForm.d Γ n m a)) b :=
    (congrArg (fun u => l2Form Γ n (m + 1) u b) e1).trans
      ((t1 _ _).trans (congrArg (fun r : ℝ => l2Form Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) b + r)
        (t2 _ _)))
  have s2 : l2Form Γ n m a (c.commAdj n m b) =
      l2Form Γ n m a (c.mulMap (CForm.delta Γ n m b)) +
        (-1 : ℝ) * l2Form Γ n m a (CForm.delta Γ n m (c.mulMap b)) :=
    (congrArg (fun u => l2Form Γ n m a u) e2).trans
      ((t3 _ _).trans (congrArg (fun r : ℝ => l2Form Γ n m a (c.mulMap (CForm.delta Γ n m b)) + r)
        (t4 _ _)))
  exact s1.trans ((congrArg₂ (fun x y : ℝ => x + (-1 : ℝ) * y) h1 h2).trans s2.symm)

theorem aux_le_of_sq_le {u N β D : ℝ} (hD : 0 ≤ D) (hu : u ^ 2 ≤ N * β) (hN : N ≤ D * u)
    (hu0 : 0 ≤ u) (hβ : 0 ≤ β) : u ≤ D * β := by
  by_cases h0 : u = 0
  · rw [h0]
    exact mul_nonneg hD hβ
  · have hpos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h0)
    have h4 : u * u ≤ u * (D * β) := by
      calc u * u = u ^ 2 := (sq u).symm
        _ ≤ N * β := hu
        _ ≤ (D * u) * β := mul_le_mul_of_nonneg_right hN hβ
        _ = u * (D * β) := by ring
    exact le_of_mul_le_mul_left h4 hpos

/-- The constant of `exists_normSq_commCore_le`. -/
def commConst (n m : ℕ) : ℝ := Classical.choose (InvMult.exists_normSq_commCore_le n m)

theorem commConst_nonneg (n m : ℕ) : 0 ≤ commConst n m :=
  (Classical.choose_spec (InvMult.exists_normSq_commCore_le n m)).1

/-- The operator-norm constant of the commutator with a multiplier of slope `B`. -/
def Dc (n m : ℕ) (B : ℝ) : ℝ := Real.sqrt (commConst n m) * B

theorem Dc_nonneg (n m : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ Dc n m B :=
  mul_nonneg (Real.sqrt_nonneg _) hB

theorem norm_incl_mulMap_le (a : CForm Γ n m) :
    ‖incl Γ n m (c.mulMap a)‖ ≤ 1 * ‖incl Γ n m a‖ := by
  have h : ‖incl Γ n m (c.mulMap a)‖ ^ 2 ≤ ‖incl Γ n m a‖ ^ 2 :=
    (norm_incl_sq Γ n m (c.mulMap a)).trans_le
      ((c.normSq_mulMap_le a).trans_eq (norm_incl_sq Γ n m a).symm)
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h).trans_eq (one_mul _).symm

theorem Dc_sq (n m : ℕ) (B : ℝ) : Dc n m B ^ 2 = commConst n m * B ^ 2 := by
  unfold Dc
  rw [mul_pow, Real.sq_sqrt (commConst_nonneg n m)]

theorem norm_incl_commCore_le {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (a : CForm Γ n m) :
    ‖incl Γ n (m + 1) (c.commCore n m a)‖ ≤ Dc n m B * ‖incl Γ n m a‖ := by
  have h := (Classical.choose_spec (InvMult.exists_normSq_commCore_le n m)).2 Γ c B hB hs a
  have e : (Dc n m B * ‖incl Γ n m a‖) ^ 2 = commConst n m * B ^ 2 * normSq a :=
    (mul_pow _ _ _).trans (congrArg₂ (· * ·) (Dc_sq n m B) (norm_incl_sq Γ n m a))
  have h2 : ‖incl Γ n (m + 1) (c.commCore n m a)‖ ^ 2 ≤ (Dc n m B * ‖incl Γ n m a‖) ^ 2 :=
    (norm_incl_sq Γ n (m + 1) (c.commCore n m a)).trans_le (h.trans_eq e.symm)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Dc_nonneg n m hB) (norm_nonneg _))).mp h2

theorem inner_incl_commCore (a : CForm Γ n m) (b : CForm Γ n (m + 1)) :
    inner ℝ (incl Γ n (m + 1) (c.commCore n m a)) (incl Γ n (m + 1) b) =
      inner ℝ (incl Γ n m a) (incl Γ n m (c.commAdj n m b)) :=
  (inner_incl Γ n (m + 1) _ _).trans ((c.l2Form_commCore a b).trans (inner_incl Γ n m _ _).symm)

theorem norm_incl_commAdj_le {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (b : CForm Γ n (m + 1)) :
    ‖incl Γ n m (c.commAdj n m b)‖ ≤ Dc n m B * ‖incl Γ n (m + 1) b‖ := by
  have h1 : ‖incl Γ n m (c.commAdj n m b)‖ ^ 2 =
      inner ℝ (incl Γ n (m + 1) (c.commCore n m (c.commAdj n m b))) (incl Γ n (m + 1) b) :=
    (real_inner_self_eq_norm_sq (incl Γ n m (c.commAdj n m b))).symm.trans
      (c.inner_incl_commCore (c.commAdj n m b) b).symm
  exact aux_le_of_sq_le (Dc_nonneg n m hB) (h1.trans_le (real_inner_le_norm _ _))
    (c.norm_incl_commCore_le hB hs (c.commAdj n m b)) (norm_nonneg _) (norm_nonneg _)

/-! ### The bounded operators on the completions -/

theorem cancel_add_smul {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V) :
    a + (b + (-1 : ℝ) • a) = b := by
  rw [neg_one_smul]
  abel

theorem cancel_sub_smul {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V) :
    a - (a + (-1 : ℝ) • b) = b := by
  rw [neg_one_smul]
  abel

variable (n) in
/-- Multiplication by `c` on the completion. -/
def Mh (p : ℕ) : Hilbert Γ n p →L[ℝ] Hilbert Γ n p :=
  hext Γ n p p c.mulMap 1 c.norm_incl_mulMap_le

variable (n) in
/-- The commutator `[d, c]` on the completion. -/
def Eh {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (m : ℕ) : Hilbert Γ n m →L[ℝ] Hilbert Γ n (m + 1) :=
  hext Γ n m (m + 1) (c.commCore n m) (Dc n m B) (c.norm_incl_commCore_le hB hs)

variable (n) in
/-- The adjoint commutator `[c, δ]` on the completion. -/
def Fh {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (m : ℕ) : Hilbert Γ n (m + 1) →L[ℝ] Hilbert Γ n m :=
  hext Γ n (m + 1) m (c.commAdj n m) (Dc n m B) (c.norm_incl_commAdj_le hB hs)

theorem Mh_incl (p : ℕ) (a : CForm Γ n p) :
    c.Mh n p (incl Γ n p a) = incl Γ n p (c.mulMap a) :=
  hext_incl c.mulMap 1 c.norm_incl_mulMap_le a

theorem inner_incl_mulMap (a b : CForm Γ n m) :
    inner ℝ (incl Γ n m (c.mulMap a)) (incl Γ n m b) =
      inner ℝ (incl Γ n m a) (incl Γ n m (c.mulMap b)) :=
  (inner_incl Γ n m _ _).trans ((c.l2Form_mulMap a b).trans (inner_incl Γ n m _ _).symm)

theorem inner_Mh (x : Hilbert Γ n m) (b : CForm Γ n m) :
    inner ℝ (c.Mh n m x) (incl Γ n m b) = inner ℝ x (incl Γ n m (c.mulMap b)) :=
  inner_hext_incl c.mulMap c.norm_incl_mulMap_le c.mulMap c.inner_incl_mulMap x b

theorem inner_Eh {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (x : Hilbert Γ n m)
    (b : CForm Γ n (m + 1)) :
    inner ℝ (c.Eh n hB hs m x) (incl Γ n (m + 1) b) = inner ℝ x (incl Γ n m (c.commAdj n m b)) :=
  inner_hext_incl (c.commCore n m) (c.norm_incl_commCore_le hB hs) (c.commAdj n m)
    c.inner_incl_commCore x b

theorem inner_Fh {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) (x : Hilbert Γ n (m + 1))
    (a : CForm Γ n m) :
    inner ℝ (c.Fh n hB hs m x) (incl Γ n m a) = inner ℝ x (incl Γ n (m + 1) (c.commCore n m a)) :=
  inner_hext_incl (c.commAdj n m) (c.norm_incl_commAdj_le hB hs) (c.commCore n m)
    (fun b a => ((real_inner_comm _ _).trans ((c.inner_incl_commCore a b).symm.trans
      (real_inner_comm _ _)))) x a

/-- Multiplication by `c` preserves the maximal differential, up to the commutator. -/
theorem maxD_mul {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) {x : Hilbert Γ n m}
    {y : Hilbert Γ n (m + 1)} (h : (x, y) ∈ (maxD Γ n m).graph) :
    (c.Mh n m x, c.Mh n (m + 1) y + c.Eh n hB hs m x) ∈ (maxD Γ n m).graph := by
  refine (mem_maxD_graph_iff Γ n m _ _).mpr (fun b => ?_)
  have w := (mem_maxD_graph_iff Γ n m x y).mp h (c.mulMap b)
  have key : incl Γ n m (CForm.delta Γ n m (c.mulMap b)) + incl Γ n m (c.commAdj n m b) =
      incl Γ n m (c.mulMap (CForm.delta Γ n m b)) := by
    have e : c.commAdj n m b = c.mulMap (CForm.delta Γ n m b) +
        (-1 : ℝ) • CForm.delta Γ n m (c.mulMap b) := rfl
    have e2 : incl Γ n m (c.commAdj n m b) = incl Γ n m (c.mulMap (CForm.delta Γ n m b)) +
        (-1 : ℝ) • incl Γ n m (CForm.delta Γ n m (c.mulMap b)) :=
      (congrArg (incl Γ n m) e).trans
        ((map_add (incl Γ n m) _ _).trans (congrArg₂ (· + ·) rfl (map_smul (incl Γ n m) _ _)))
    exact (congrArg (fun z => incl Γ n m (CForm.delta Γ n m (c.mulMap b)) + z) e2).trans
      (cancel_add_smul _ _)
  calc inner ℝ (c.Mh n (m + 1) y + c.Eh n hB hs m x) (incl Γ n (m + 1) b)
      = inner ℝ (c.Mh n (m + 1) y) (incl Γ n (m + 1) b) +
          inner ℝ (c.Eh n hB hs m x) (incl Γ n (m + 1) b) := inner_add_left _ _ _
    _ = inner ℝ y (incl Γ n (m + 1) (c.mulMap b)) +
          inner ℝ x (incl Γ n m (c.commAdj n m b)) :=
        congrArg₂ (· + ·) (c.inner_Mh y b) (c.inner_Eh hB hs x b)
    _ = inner ℝ x (incl Γ n m (CForm.delta Γ n m (c.mulMap b))) +
          inner ℝ x (incl Γ n m (c.commAdj n m b)) := congrArg (· + _) w
    _ = inner ℝ x (incl Γ n m (CForm.delta Γ n m (c.mulMap b)) +
          incl Γ n m (c.commAdj n m b)) := (inner_add_right _ _ _).symm
    _ = inner ℝ x (incl Γ n m (c.mulMap (CForm.delta Γ n m b))) := congrArg (inner ℝ x) key
    _ = inner ℝ (c.Mh n m x) (incl Γ n m (CForm.delta Γ n m b)) := (c.inner_Mh x (CForm.delta Γ n m b)).symm

/-- Multiplication by `c` preserves the maximal codifferential, up to the commutator. -/
theorem maxDelta_mul {B : ℝ} (hB : 0 ≤ B) (hs : c.Slope B) {x : Hilbert Γ n (m + 1)}
    {z : Hilbert Γ n m} (h : (x, z) ∈ (maxDelta Γ n m).graph) :
    (c.Mh n (m + 1) x, c.Mh n m z - c.Fh n hB hs m x) ∈ (maxDelta Γ n m).graph := by
  refine (mem_maxDelta_graph_iff Γ n m _ _).mpr (fun a => ?_)
  have w := (mem_maxDelta_graph_iff Γ n m x z).mp h (c.mulMap a)
  have key : incl Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) -
      incl Γ n (m + 1) (c.commCore n m a) = incl Γ n (m + 1) (c.mulMap (CForm.d Γ n m a)) := by
    have e : c.commCore n m a = CForm.d Γ n m (c.mulMap a) +
        (-1 : ℝ) • c.mulMap (CForm.d Γ n m a) := rfl
    have e2 : incl Γ n (m + 1) (c.commCore n m a) = incl Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) +
        (-1 : ℝ) • incl Γ n (m + 1) (c.mulMap (CForm.d Γ n m a)) :=
      (congrArg (incl Γ n (m + 1)) e).trans
        ((map_add (incl Γ n (m + 1)) _ _).trans (congrArg₂ (· + ·) rfl (map_smul (incl Γ n (m + 1)) _ _)))
    exact (congrArg (fun z => incl Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) - z) e2).trans
      (cancel_sub_smul _ _)
  calc inner ℝ (c.Mh n m z - c.Fh n hB hs m x) (incl Γ n m a)
      = inner ℝ (c.Mh n m z) (incl Γ n m a) - inner ℝ (c.Fh n hB hs m x) (incl Γ n m a) :=
        inner_sub_left (c.Mh n m z) (c.Fh n hB hs m x) (incl Γ n m a)
    _ = inner ℝ z (incl Γ n m (c.mulMap a)) -
          inner ℝ x (incl Γ n (m + 1) (c.commCore n m a)) :=
        congrArg₂ (· - ·) (c.inner_Mh z a) (c.inner_Fh hB hs x a)
    _ = inner ℝ x (incl Γ n (m + 1) (CForm.d Γ n m (c.mulMap a))) -
          inner ℝ x (incl Γ n (m + 1) (c.commCore n m a)) := congrArg (· - _) w
    _ = inner ℝ x (incl Γ n (m + 1) (CForm.d Γ n m (c.mulMap a)) -
          incl Γ n (m + 1) (c.commCore n m a)) := (inner_sub_right _ _ _).symm
    _ = inner ℝ x (incl Γ n (m + 1) (c.mulMap (CForm.d Γ n m a))) := congrArg (inner ℝ x) key
    _ = inner ℝ (c.Mh n (m + 1) x) (incl Γ n (m + 1) (CForm.d Γ n m a)) :=
        (c.inner_Mh x (CForm.d Γ n m a)).symm

end InvMult

/-! ### The reduction of Gaffney's lemma to compactly supported elements -/

/-- Compactly supported equivariant forms vanishing outside the preimage of `Q`. -/
def SuppIn (Q : Set (OrbitSpace Γ)) (n k : ℕ) : Set (CForm Γ n k) :=
  {a | ∀ x ∈ positiveCoordinates, CForm.fn a x ≠ 0 → coordProj Γ x ∈ Q}

variable (Γ n) in
/-- Gaffney's lemma for elements supported over a compact subset of the orbit space. -/
def CompactGaffneyAt (k : ℕ) : Prop :=
  ∀ Q : Set (OrbitSpace Γ), IsCompact Q → ∀ (u : Hilbert Γ n (k + 1)) (v : Hilbert Γ n (k + 2))
    (w : Hilbert Γ n k), u ∈ closure (incl Γ n (k + 1) '' SuppIn Q n (k + 1)) →
      (u, v) ∈ (maxD Γ n (k + 1)).graph → (u, w) ∈ (maxDelta Γ n k).graph →
        (u, v, w) ∈ jointGraph Γ n k

/-- Invariant cutoffs exhausting the orbit space with gradients tending to zero. -/
structure CutoffSeq (Γ : Subgroup RealGL) where
  c : ℕ → InvMult Γ
  B : ℝ
  B_nonneg : 0 ≤ B
  slope : ∀ j : ℕ, (c j).Slope (B / ((j : ℝ) + 1))
  Q : ℕ → Set (OrbitSpace Γ)
  Q_compact : ∀ j : ℕ, IsCompact (Q j)
  support_sub : ∀ (j : ℕ), ∀ x ∈ positiveCoordinates, (c j).toFun x ≠ 0 → coordProj Γ x ∈ Q j
  eventually_one : ∀ K : Set (OrbitSpace Γ), IsCompact K → ∀ᶠ j : ℕ in atTop,
    ∀ x ∈ positiveCoordinates, coordProj Γ x ∈ K → (c j).toFun x = 1

namespace InvMult

variable (c : InvMult Γ)

theorem zero_smul_formValue (f : FormValue n m) : (0 : ℝ) • f = 0 :=
  ContinuousAlternatingMap.ext (fun v => zero_smul ℝ (f v))

theorem one_smul_formValue (f : FormValue n m) : (1 : ℝ) • f = f :=
  ContinuousAlternatingMap.ext (fun v => one_smul ℝ (f v))

omit hΓ in
theorem mulMap_eq_self (a : CForm Γ n m)
    (h : ∀ x ∈ positiveCoordinates, CForm.fn a x ≠ 0 → c.toFun x = 1) : c.mulMap a = a := by
  apply CForm.ext
  intro x hx
  by_cases h0 : CForm.fn a x = 0
  · exact (c.fn_mulMap a hx).trans
      ((congrArg (fun z : FormValue n m => c.toFun x • z) h0).trans
        ((smul_zero (A := FormValue n m) (c.toFun x)).trans h0.symm))
  · exact (c.fn_mulMap a hx).trans
      ((congrArg (fun r : ℝ => r • CForm.fn a x) (h x hx h0)).trans (one_smul_formValue _))

omit hΓ in
theorem mulMap_mem_suppIn {Q : Set (OrbitSpace Γ)}
    (hQ : ∀ x ∈ positiveCoordinates, c.toFun x ≠ 0 → coordProj Γ x ∈ Q) (a : CForm Γ n m) :
    c.mulMap a ∈ SuppIn Q n m := by
  intro x hx hne
  apply hQ x hx
  intro h0
  apply hne
  exact (c.fn_mulMap a hx).trans ((congrArg (fun r : ℝ => r • CForm.fn a x) h0).trans
    (zero_smul_formValue _))

end InvMult

namespace CutoffSeq

variable (S : CutoffSeq Γ)

theorem tendsto_Mh (p : ℕ) (x : Hilbert Γ n p) :
    Tendsto (fun j => (S.c j).Mh n p x) atTop (𝓝 x) := by
  have h := tendsto_of_dense_bounded (fun j => (S.c j).Mh n p) (ContinuousLinearMap.id ℝ _)
    zero_le_one (fun j => opNorm_hext_le (S.c j).mulMap zero_le_one (S.c j).norm_incl_mulMap_le)
    (incl_dense Γ n p) ?_ x
  · exact h
  · rintro _ ⟨a, rfl⟩
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [S.eventually_one _ (CForm.compact a)] with j hj
    have h1 : (S.c j).mulMap a = a := (S.c j).mulMap_eq_self a
      (fun x hx hne => hj x hx (subset_closure ⟨x, hne, rfl⟩))
    exact ((congrArg (incl Γ n p) h1).symm.trans ((S.c j).Mh_incl p a).symm)

end CutoffSeq

theorem tendsto_zero_of_le_div {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) (A : ℝ)
    (h : ∀ j : ℕ, ‖f j‖ ≤ A / ((j : ℝ) + 1)) : Tendsto f atTop (𝓝 0) := by
  refine squeeze_zero_norm h ?_
  have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A
  rw [mul_zero] at h1
  exact h1.congr (fun j => mul_one_div A _)

theorem InvMult.Mh_mem_closure (c : InvMult Γ) (n : ℕ) {Q : Set (OrbitSpace Γ)}
    (hQ : ∀ x ∈ positiveCoordinates, c.toFun x ≠ 0 → coordProj Γ x ∈ Q) (p : ℕ)
    (x : Hilbert Γ n p) :
    c.Mh n p x ∈ closure (incl Γ n p '' SuppIn Q n p) := by
  have hc : IsClosed {z : Hilbert Γ n p | c.Mh n p z ∈ closure (incl Γ n p '' SuppIn Q n p)} :=
    isClosed_closure.preimage (c.Mh n p).continuous
  refine DenseRange.induction_on (incl_dense Γ n p) x
    (p := fun z : Hilbert Γ n p => c.Mh n p z ∈ closure (incl Γ n p '' SuppIn Q n p)) hc ?_
  intro a
  have e : c.Mh n p (incl Γ n p a) = incl Γ n p (c.mulMap a) := c.Mh_incl p a
  exact Set.mem_of_eq_of_mem e (subset_closure ⟨c.mulMap a, c.mulMap_mem_suppIn hQ a, rfl⟩)

theorem InvMult.Dc_div_mul (n m : ℕ) (B : ℝ) (j : ℕ) (t : ℝ) :
    InvMult.Dc n m (B / ((j : ℝ) + 1)) * t = InvMult.Dc n m B * t / ((j : ℝ) + 1) := by
  unfold InvMult.Dc
  ring

/-- **Gaffney's lemma from its compactly supported form**, given exhausting invariant cutoffs. -/
theorem gaffneyAt_of_compact (S : CutoffSeq Γ) (k : ℕ) (h : CompactGaffneyAt Γ n k) :
    GaffneyAt Γ n k := by
  intro x y z hy hz
  have hB : ∀ j : ℕ, 0 ≤ S.B / ((j : ℝ) + 1) := fun j => div_nonneg S.B_nonneg (by positivity)
  have hmem : ∀ j : ℕ, ((S.c j).Mh n (k + 1) x, (S.c j).Mh n (k + 2) y +
      (S.c j).Eh n (hB j) (S.slope j) (k + 1) x, (S.c j).Mh n k z -
      (S.c j).Fh n (hB j) (S.slope j) k x) ∈ jointGraph Γ n k := by
    intro j
    have a1 := (S.c j).Mh_mem_closure n (S.support_sub j) (k + 1) x
    have a2 : ((S.c j).Mh n (k + 1) x, (S.c j).Mh n (k + 2) y +
        (S.c j).Eh n (hB j) (S.slope j) (k + 1) x) ∈ (maxD Γ n (k + 1)).graph :=
      (S.c j).maxD_mul (hB j) (S.slope j) hy
    have a3 := (S.c j).maxDelta_mul (hB j) (S.slope j) hz
    exact h (S.Q j) (S.Q_compact j) _ _ _ a1 a2 a3
  have hE : Tendsto (fun j : ℕ => (S.c j).Eh n (hB j) (S.slope j) (k + 1) x) atTop (𝓝 0) := by
    refine tendsto_zero_of_le_div _ (InvMult.Dc n (k + 1) S.B * ‖x‖) (fun j => ?_)
    exact (norm_hext_le ((S.c j).commCore n (k + 1))
      ((S.c j).norm_incl_commCore_le (hB j) (S.slope j)) x).trans_eq
      (InvMult.Dc_div_mul n (k + 1) S.B j ‖x‖)
  have hF : Tendsto (fun j : ℕ => (S.c j).Fh n (hB j) (S.slope j) k x) atTop (𝓝 0) := by
    refine tendsto_zero_of_le_div _ (InvMult.Dc n k S.B * ‖x‖) (fun j => ?_)
    exact (norm_hext_le ((S.c j).commAdj n k)
      ((S.c j).norm_incl_commAdj_le (hB j) (S.slope j)) x).trans_eq
      (InvMult.Dc_div_mul n k S.B j ‖x‖)
  have hu := S.tendsto_Mh (k + 1) x
  have hv0 := (S.tendsto_Mh (k + 2) y).add hE
  have hw0 := (S.tendsto_Mh k z).sub hF
  have hv : Tendsto (fun j : ℕ => (S.c j).Mh n (k + 2) y +
      (S.c j).Eh n (hB j) (S.slope j) (k + 1) x) atTop (𝓝 y) :=
    hv0.mono_right (le_of_eq (congrArg 𝓝 (add_zero y)))
  have hw : Tendsto (fun j : ℕ => (S.c j).Mh n k z -
      (S.c j).Fh n (hB j) (S.slope j) k x) atTop (𝓝 z) :=
    hw0.mono_right (le_of_eq (congrArg 𝓝 (sub_zero z)))
  exact JointEmbeddedGraphClosure.mem_of_limits (incl Γ n (k + 1))
    ((incl Γ n (k + 2)).comp (CForm.d Γ n (k + 1))) ((incl Γ n k).comp (CForm.delta Γ n k))
    _ _ _ hmem x y z hu hv hw

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
