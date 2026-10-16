module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Coefficient
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Value

@[expose] public section


/-!
# The real entry as the frame coefficient of the actual seed form

Appendix C.5 (`ar:sec:real`) of the paper computes
the archimedean entry of the intertwining integral `(Tφ)(g) = ∫ φ(w₀⁻¹u(s,t)g) ds dt`
(`ar:eq:intertwiner`) on the invariant-frame coefficient
`ω̃(g)(Y₁, Y₂) = ρ(g)⁻¹ ω_{g SO(3)}(dL_g Y₁, dL_g Y₂)` (`ar:sec:constantterms`) of the seed
`ω_h = h(τ) 𝓑ⁿ (du₁ - τ du₂) ∧ dτ` (`ar:eq:seed`) for the lowest-weight vector `h(τ) = (τ + i)^{-k}`,
`k = n + 3`, at the line-radical tangent `v₂ = E₁₃` and the binary tangent `x₀ = E₂₃`, read at
`X = Z = 0, Y = 1`.

This module carries out that computation for the seed `seedForm`:

* a point `g SO(3)` is described by its Gram matrix `g gᵀ`, whose plane horospherical coordinates
  `(u₁, u₂, Re τ, Im τ, t)` are `gramChart` (built from the `gramPlaneU`, `gramPlaneTau`);
  the tangent vector `dL_g V` is the derivative of the chart along `ε ↦ g (1 + εV)`;
* `frameCoefficient ω g V W = ρ(g)⁻¹ (ω(dL_g V, dL_g W))`, with `ρ = SeedC3.rho` the paper's
  action `ρ(g) q = det(g)⁻¹ q(g⁻¹𝐗)` and `ρ(g)⁻¹ = ρ(g⁻¹)` (`rho_inv_rho`, `rho_rho_inv`);
* `seed_frameCoefficient_entryFrame`: at `L = w₀⁻¹u(s,t)`,
  `ω̃_h(L)(v₂, x₀) = -i r⁻³ h(τ) (aX + bY + (i/r)Z)ⁿ`, combining the tangent entry
  `(β ∧ dτ)(v₂, x₀) = -i/r³` (`real_entry_tangent`) with the transported coefficient
  (`RealEntryCoefficient.rho_entryFrame_inv_seedLinear`);
* `entryIntegral_eq_integral_seed_frameCoefficient`: `I_n = ∫_{ℝ²} ω̃_h(w₀⁻¹u(s,t))(v₂, x₀)|_{(0,1,0)} ds dt`,
  i.e. the `entryIntegral` is the real intertwining integral of the seed's frame coefficient.

This is the differential-form side of the archimedean entry. Relating it to the group-cochain
model of the library's constant-term map (`IsSourceCocycle`, the good-line real factor) needs a
form-to-cochain comparison that is not part of this module.

Written by Claude Opus 5.5.
-/

open MvPolynomial MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient

/-! ### `ρ(g)⁻¹ = ρ(g⁻¹)` -/

private theorem bind_rho_comp (g h : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C ((h i j : ℝ) : ℂ) * X j)
        (bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C ((g i j : ℝ) : ℂ) * X j) q) =
      bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C (((g * h) i j : ℝ) : ℂ) * X j) q := by
  rw [bind₁_bind₁]
  have hφ : (fun i : Fin 3 => bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C ((h i j : ℝ) : ℂ) * X j)
      (∑ j : Fin 3, C ((g i j : ℝ) : ℂ) * X j)) =
      (fun i : Fin 3 => ∑ j : Fin 3, C (((g * h) i j : ℝ) : ℂ) * X j) := by
    funext i
    rw [map_sum]
    simp only [map_mul, bind₁_C_right, bind₁_X_right]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_mul, map_add,
      map_mul]
    ring
  rw [hφ]

private theorem bind_rho_one (q : MvPolynomial (Fin 3) ℂ) :
    bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C (((1 : Matrix (Fin 3) (Fin 3) ℝ) i j : ℝ) : ℂ) * X j) q =
      q := by
  have h : (fun i : Fin 3 => ∑ j : Fin 3, C (((1 : Matrix (Fin 3) (Fin 3) ℝ) i j : ℝ) : ℂ) * X j) =
      X := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_three, Matrix.one_apply]
  rw [h, bind₁_X_left, AlgHom.id_apply]

private theorem rho_comp (g h : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (SeedC3.rho h q) =
      C (((g.det⁻¹ * h.det⁻¹ : ℝ)) : ℂ) *
        bind₁ (fun i : Fin 3 => ∑ j : Fin 3, C (((h⁻¹ * g⁻¹) i j : ℝ) : ℂ) * X j) q := by
  unfold SeedC3.rho
  rw [map_mul, bind₁_C_right, bind_rho_comp, ← mul_assoc, ← C_mul]
  push_cast
  rfl

/-- `ρ` is multiplicative: `ρ(g h) = ρ(g) ρ(h)`. -/
theorem rho_mul (g h : Matrix (Fin 3) (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho (g * h) q = SeedC3.rho g (SeedC3.rho h q) := by
  rw [rho_comp]
  unfold SeedC3.rho
  rw [Matrix.mul_inv_rev, Matrix.det_mul, mul_inv]

/-- `ρ(1) = 1`. -/
theorem rho_one (q : MvPolynomial (Fin 3) ℂ) : SeedC3.rho 1 q = q := by
  unfold SeedC3.rho
  rw [inv_one, bind_rho_one, Matrix.det_one, inv_one]
  simp

/-- `ρ(g) ρ(g⁻¹) = 1`. -/
theorem rho_rho_inv (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g (SeedC3.rho g⁻¹ q) = q := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  rw [rho_comp, Matrix.nonsing_inv_nonsing_inv g hu, Matrix.mul_nonsing_inv g hu, bind_rho_one,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, inv_mul_cancel₀ hg]
  simp

/-- `ρ(g⁻¹) ρ(g) = 1`. -/
theorem rho_inv_rho (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det ≠ 0) (q : MvPolynomial (Fin 3) ℂ) :
    SeedC3.rho g⁻¹ (SeedC3.rho g q) = q := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  rw [rho_comp, Matrix.nonsing_inv_nonsing_inv g hu, Matrix.nonsing_inv_mul g hu, bind_rho_one,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, mul_inv_cancel₀ hg]
  simp

/-! ### The frame coefficient of a polynomial-valued two-form -/

/-- The plane horospherical coordinates `(u₁, u₂, Re τ, Im τ, t)` of the point whose Gram matrix
is `G = p pᵀ`, for `p = [[A, t u], [0, t]]`: `u = G_{{1,2},3}/G₃₃`, `τ = gramPlaneTau G`,
`t = √G₃₃`. -/
def gramChart (G : Matrix (Fin 3) (Fin 3) ℝ) : Fin 5 → ℝ :=
  ![(gramPlaneU G).1, (gramPlaneU G).2, (gramPlaneTau G).re, (gramPlaneTau G).im,
    Real.sqrt (gramNormal G)]

/-- The Gram matrix of `g (1 + εV)`. -/
def gramCurve (g V : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  g * (1 + ε • V) * (1 + ε • V).transpose * g.transpose

/-- The plane coordinates of the tangent vector `dL_g V` at `g SO(3)`. -/
def chartTangent (g V : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 5) : ℝ :=
  deriv (fun ε => gramChart (gramCurve g V ε) a) 0

/-- `ω_{g SO(3)}(dL_g V, dL_g W)` for a two-form given by its coefficient matrix in plane
coordinates. -/
def frameValue (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (g V W : Matrix (Fin 3) (Fin 3) ℝ) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    C ((chartTangent g V a * chartTangent g W b : ℝ) : ℂ) * ω (gramChart (g * g.transpose)) a b

/-- The invariant-frame coefficient `ω̃(g)(V, W) = ρ(g)⁻¹ ω_{g SO(3)}(dL_g V, dL_g W)`. -/
def frameCoefficient (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (g V W : Matrix (Fin 3) (Fin 3) ℝ) : MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho g⁻¹ (frameValue ω g V W)

/-- The local holomorphic lowest-weight vector `h(τ) = (τ + i)^{-k}`, `k = n + 3`. -/
def lowestWeightVector (n : ℕ) (τ : ℂ) : ℂ := (τ + Complex.I) ^ (-((n : ℤ) + 3))

/-- `β(dL_g V) = du₁(V) - τ du₂(V)`. -/
def frameBeta (g V : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  (chartTangent g V 0 : ℂ) - gramPlaneTau (g * g.transpose) * (chartTangent g V 1 : ℂ)

/-- `dτ(dL_g V) = d(Re τ)(V) + i d(Im τ)(V)`. -/
def frameDTau (g V : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  (chartTangent g V 2 : ℂ) + Complex.I * (chartTangent g V 3 : ℂ)

private theorem seedTau_gramChart (G : Matrix (Fin 3) (Fin 3) ℝ) :
    seedTau (gramChart G) = gramPlaneTau G := by
  simp only [seedTau, gramChart, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_cons]
  rw [mul_comm]
  exact Complex.re_add_im _

/-- **The seed on a pair of frame tangents.** `ω_h(dL_g V, dL_g W) = h(τ) 𝓑ⁿ (β(V) dτ(W) - β(W) dτ(V))`. -/
theorem frameValue_seedForm (n : ℕ) (h : ℂ → ℂ) (g V W : Matrix (Fin 3) (Fin 3) ℝ) :
    frameValue (seedForm n h) g V W =
      C (h (gramPlaneTau (g * g.transpose)) *
          (frameBeta g V * frameDTau g W - frameBeta g W * frameDTau g V)) *
        seedLinear (gramChart (g * g.transpose)) ^ n := by
  have hterm : ∀ a b : Fin 5,
      C ((chartTangent g V a * chartTangent g W b : ℝ) : ℂ) *
          seedForm n h (gramChart (g * g.transpose)) a b =
        C (h (gramPlaneTau (g * g.transpose)) *
            (((chartTangent g V a * chartTangent g W b : ℝ) : ℂ) *
              (seedBeta (gramChart (g * g.transpose)) a * seedDTau b -
                seedBeta (gramChart (g * g.transpose)) b * seedDTau a))) *
          seedLinear (gramChart (g * g.transpose)) ^ n := by
    intro a b
    rw [seedForm, seedTau_gramChart, ← mul_assoc, ← C_mul]
    congr 2
    ring
  simp only [frameValue, hterm, ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum]
  congr 3
  simp only [Fin.sum_univ_five, seedBeta, seedDTau, frameBeta, frameDTau, seedTau_gramChart,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-! ### Evaluation at `L = w₀⁻¹ u(s,t)` -/

private theorem gramCurve_entryFrame (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    gramCurve (entryFrame s t) V = entryCurve s t V := rfl

private theorem entryFrame_gram (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    entryFrame s t * (entryFrame s t).transpose = entryCurve s t V 0 :=
  (entryCurve_const s t V).symm

private theorem deriv_ofReal_comp' (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hg : ¬ DifferentiableAt ℝ (fun y => (f y : ℂ)) x := by
      intro hg
      apply hf
      have := Complex.differentiable_re.differentiableAt.comp x hg
      simpa [Function.comp_def] using this
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg,
      Complex.ofReal_zero]

private theorem frameBeta_entryFrame (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) :
    frameBeta (entryFrame s t) V = entryBeta s t V := by
  rw [frameBeta, entryBeta, entryFrame_gram s t V]
  simp only [deriv_ofReal_comp']
  rfl

private theorem frameDTau_entryFrame (s t : ℝ) (V : Matrix (Fin 3) (Fin 3) ℝ) {d : ℂ}
    (hd : HasDerivAt (fun ε : ℝ => gramPlaneTau (entryCurve s t V ε)) d 0) :
    frameDTau (entryFrame s t) V = entryDTau s t V := by
  have hre : HasDerivAt (fun ε : ℝ => (gramPlaneTau (entryCurve s t V ε)).re) d.re 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    rw [Complex.reCLM_apply] at h
    exact h
  have him : HasDerivAt (fun ε : ℝ => (gramPlaneTau (entryCurve s t V ε)).im) d.im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    rw [Complex.imCLM_apply] at h
    exact h
  have h2 : chartTangent (entryFrame s t) V 2 = d.re := by
    rw [chartTangent, gramCurve_entryFrame]
    exact hre.deriv
  have h3 : chartTangent (entryFrame s t) V 3 = d.im := by
    rw [chartTangent, gramCurve_entryFrame]
    exact him.deriv
  rw [frameDTau, h2, h3, entryDTau, hd.deriv, mul_comm Complex.I, Complex.re_add_im]

/-- `(β ∧ dτ)(dL_L v₂, dL_L x₀) = -i/r³` in the frame of `L = w₀⁻¹u(s,t)`. -/
theorem frame_wedge_entryFrame (s t : ℝ) :
    frameBeta (entryFrame s t) (Matrix.single 0 2 1) * frameDTau (entryFrame s t) (Matrix.single 1 2 1) -
        frameBeta (entryFrame s t) (Matrix.single 1 2 1) *
          frameDTau (entryFrame s t) (Matrix.single 0 2 1) =
      -Complex.I / (entryRadius (s, t) : ℂ) ^ 3 := by
  rw [frameBeta_entryFrame, frameBeta_entryFrame,
    frameDTau_entryFrame s t _ (entryDTau_x0_hasDerivAt s t),
    frameDTau_entryFrame s t _ (entryDTau_v2_hasDerivAt s t)]
  exact (real_entry_tangent s t).2.2.2.2

private theorem entryFrame_det (s t : ℝ) : (entryFrame s t).det = 1 := by
  simp [entryFrame, Matrix.det_fin_three]

private theorem rho_entryFrame_inv_mul (s t : ℝ) (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) (n : ℕ) :
    SeedC3.rho (entryFrame s t)⁻¹ (C c * q ^ n) = C c * SeedC3.rho (entryFrame s t)⁻¹ q ^ n := by
  rw [rho_entryFrame_inv, rho_entryFrame_inv, map_mul, map_pow, bind₁_C_right]

/-- **The seed's frame coefficient at `L = w₀⁻¹u(s,t)`** (Appendix C.5): for the lowest-weight
vector `h(τ) = (τ + i)^{-k}`,
`ρ(L)⁻¹ ω_h(dL_L v₂, dL_L x₀) = -i r⁻³ h(τ) (aX + bY + (i/r)Z)ⁿ` with `τ = entryTau (s, t)`,
`a = entryCoefficientA (s, t)`, `b = entryCoefficient (s, t)`. -/
theorem seed_frameCoefficient_entryFrame (n : ℕ) (s t : ℝ) :
    frameCoefficient (seedForm n (lowestWeightVector n)) (entryFrame s t)
        (Matrix.single 0 2 1) (Matrix.single 1 2 1) =
      C (-Complex.I / (entryRadius (s, t) : ℂ) ^ 3 * lowestWeightVector n (entryTau (s, t))) *
        (C (entryCoefficientA (s, t)) * X 0 + C (entryCoefficient (s, t)) * X 1 +
          C (Complex.I / (entryRadius (s, t) : ℂ)) * X 2) ^ n := by
  obtain ⟨hU, hT, -⟩ := real_entry_tangent s t
  rw [frameCoefficient, frameValue_seedForm, frame_wedge_entryFrame, rho_entryFrame_inv_mul,
    rho_entryFrame_inv_seedLinear s t]
  · rw [entryFrame_gram s t 0, hT]
    ring_nf
  · rw [entryFrame_gram s t 0]
    rfl
  · rw [seedTau_gramChart, entryFrame_gram s t 0, hT]

/-- The `Y`-coordinate (`X = Z = 0`, `Y = 1`) of the seed's frame coefficient at `L` is
`-i r⁻³ h(τ) bⁿ`, the integrand of `I_n`. -/
theorem seed_frameCoefficient_entryFrame_eval (n : ℕ) (st : ℝ × ℝ) :
    eval ![0, 1, 0] (frameCoefficient (seedForm n (lowestWeightVector n)) (entryFrame st.1 st.2)
        (Matrix.single 0 2 1) (Matrix.single 1 2 1)) =
      -Complex.I * entryIntegrand n st := by
  rw [seed_frameCoefficient_entryFrame]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
    zero_add, add_zero, mul_one]
  rw [entryIntegrand, lowestWeightVector]
  simp only [Prod.mk.eta, zpow_neg, zpow_ofNat]
  ring

/-- **The real entry is the intertwining integral of the seed.** The `I_n = -i ∫_{ℝ²} r⁻³ h(τ) bⁿ ds dt` is `∫_{ℝ²} ω̃_h(w₀⁻¹u(s,t))(v₂, x₀)|_{X = Z = 0, Y = 1} ds dt`,
the real factor `∫ φ(w₀⁻¹u(s,t)) ds dt` of `ar:eq:intertwiner` at `g = 1` on the invariant-frame
coefficient of the seed `ω_h`, `h(τ) = (τ + i)^{-k}`. -/
theorem entryIntegral_eq_integral_seed_frameCoefficient (n : ℕ) :
    entryIntegral n =
      ∫ st : ℝ × ℝ, eval ![0, 1, 0]
        (frameCoefficient (seedForm n (lowestWeightVector n)) (entryFrame st.1 st.2)
          (Matrix.single 0 2 1) (Matrix.single 1 2 1)) := by
  simp only [seed_frameCoefficient_entryFrame_eval]
  rw [integral_const_mul, entryIntegral]

end TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
