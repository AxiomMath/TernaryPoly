module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.RegBasic
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hodge

@[expose] public section


/-! # General coercivity, Tier B: the current of an `L²` element

An element `u` of the `L²` completion `Hilbert Γ n k` defines a distribution on the positive
coordinates, `T_u(g) = ⟪u, Π g⟫` for compactly supported smooth forms `g`, where `Π g = ∑_γ γ* g`
is the average over `Γ`.  This current is invariant under `Γ`, locally bounded for the plain
coordinate `L²` norm and, when `u` has weak differential `ω`, satisfies the weak equation
`T_u (δ g) = ∫ ⟪ω, g⟫`.  No function representing `u` is ever constructed.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Set MeasureTheory Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
  TernaryPoly.SmoothLocalDeRham TernaryPoly.PolynomialFormCoordinates
  TernaryPoly.SymmetricSpaceRiemannian
open scoped ContDiff

variable {Γ : Subgroup RealGL} {n k : ℕ} [hΓ : Fact (Admissible Γ)]

/-- The current `g ↦ ⟪u, Π g⟫` of an element of the `L²` completion. -/
def currentFun (u : Hilbert Γ n k) : Cc n k →ₗ[ℝ] ℝ :=
  (innerSL ℝ u).toLinearMap.comp ((incl Γ n k).comp (avg hΓ.out))

theorem currentFun_apply (u : Hilbert Γ n k) (g : Cc n k) :
    currentFun u g = inner ℝ u (incl Γ n k (avg hΓ.out g)) := rfl

omit hΓ in
theorem actSum_actPull (γ : Γ) {g : Coordinates → FormValue n k} {x : Coordinates}
    (hx : x ∈ positiveCoordinates) :
    actSum Γ n k (actPull n k (γ : RealGL) g) x = actSum Γ n k g x := by
  unfold actSum
  have h1 : ∀ γ' : Γ, actPull n k (γ' : RealGL) (actPull n k (γ : RealGL) g) x =
      actPull n k ((γ * γ' : Γ) : RealGL) g x := fun γ' =>
    actPull_mul n k (γ' : RealGL) (γ : RealGL) g hx
  simp only [h1]
  exact finsum_comp_equiv (Equiv.mulLeft γ) (f := fun γ : Γ => actPull n k (γ : RealGL) g x)

theorem avg_actPull (γ : Γ) (g : Cc n k) :
    avg hΓ.out (⟨actPull n k (γ : RealGL) g.1, actPull_mem_Cc n k (γ : RealGL) g.2⟩ : Cc n k) =
      avg hΓ.out g := by
  apply CForm.ext
  intro x hx
  exact (fn_avg hΓ.out _ hx).trans ((actSum_actPull γ hx).trans (fn_avg hΓ.out g hx).symm)

/-- The current is invariant under the group. -/
theorem currentFun_invariant (u : Hilbert Γ n k) (γ : Γ) (g : Cc n k) :
    currentFun u (⟨actPull n k (γ : RealGL) g.1, actPull_mem_Cc n k (γ : RealGL) g.2⟩ : Cc n k) =
      currentFun u g :=
  congrArg (fun a : CForm Γ n k => inner ℝ u (incl Γ n k a)) (avg_actPull γ g)

theorem aux_chain2 {w c I N A D : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) (h2 : w ≤ A * c)
    (h3 : c ≤ D * I) : N * w ≤ N * A * D * I := by
  calc N * w ≤ N * (A * c) := mul_le_mul_of_nonneg_left h2 hN
    _ ≤ N * (A * (D * I)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hA) hN
    _ = N * A * D * I := by ring

theorem aux_sqrt_le {x M I : ℝ} (hM : 0 ≤ M) (h : x ^ 2 ≤ M * I) : x ≤ Real.sqrt M * Real.sqrt I := by
  rw [← Real.sqrt_mul hM]
  exact Real.le_sqrt_of_sq_le h

/-- The current is bounded on forms supported in a fixed compact set by the plain `L²` norm. -/
theorem currentFun_bound (u : Hilbert Γ n k) {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Cc n k, tsupport g.1 ⊆ K →
      |currentFun u g| ≤ C * Real.sqrt (∫ x, ‖g.1 x‖ ^ 2) := by
  classical
  have h := hΓ.out
  obtain ⟨A, hA, hAK⟩ := exists_wL2_comp n k hK hKp
  have hD : 0 ≤ (Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hN : 0 ≤ ((h.overlap_finite hK hKp).toFinset.card : ℝ) := Nat.cast_nonneg _
  refine ⟨‖u‖ * Real.sqrt (((h.overlap_finite hK hKp).toFinset.card : ℝ) * A *
    ((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2)),
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), fun g hg => ?_⟩
  have h1 := h.normSq_avgForm_le_of_subset g.2 hK hKp hg
  have h2 := (hAK g.1 g.2.1 g.2.2.1 hg).1
  have h3 := compL2_le_integral g.2.1.continuous g.2.2.1
  have h4 : ‖incl Γ n k (avg h g)‖ ^ 2 ≤ (((h.overlap_finite hK hKp).toFinset.card : ℝ) * A *
      ((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖ ^ 2)) *
        ∫ x, ‖g.1 x‖ ^ 2 :=
    (norm_incl_sq Γ n k (avg h g)).trans_le (h1.trans (aux_chain2 hN hA h2 h3))
  have h5 := aux_sqrt_le (mul_nonneg (mul_nonneg hN hA) hD) h4
  have h6 : |currentFun u g| ≤ ‖u‖ * ‖incl Γ n k (avg h g)‖ :=
    abs_real_inner_le_norm u (incl Γ n k (avg h g))
  exact h6.trans ((mul_le_mul_of_nonneg_left h5 (norm_nonneg _)).trans_eq (by ring))

/-- The weak equation: if `d u = ω` weakly, then `T_u (δ g) = ⟪ω, g⟫`. -/
theorem currentFun_weak (u : Hilbert Γ n k) (ζ : CForm Γ n (k + 1))
    (hu : (u, incl Γ n (k + 1) ζ) ∈ (maxD Γ n k).graph) (g : Cc n (k + 1)) :
    currentFun u (⟨localAdjoint n k g.1, localAdjoint_mem_Cc g.2⟩ : Cc n k) =
      ∫ x, coordinateDensity x * formPairing n (k + 1) x (CForm.fn ζ x) (g.1 x) := by
  have h := hΓ.out
  have hw := (mem_maxD_graph_iff Γ n k u (incl Γ n (k + 1) ζ)).mp hu (avg h g)
  have e1 : avg h (⟨localAdjoint n k g.1, localAdjoint_mem_Cc g.2⟩ : Cc n k) =
      CForm.delta Γ n k (avg h g) := (h.delta_avgForm g.2).symm
  have e2 : currentFun u (⟨localAdjoint n k g.1, localAdjoint_mem_Cc g.2⟩ : Cc n k) =
      inner ℝ (incl Γ n (k + 1) ζ) (incl Γ n (k + 1) (avg h g)) :=
    (congrArg (fun a : CForm Γ n k => inner ℝ u (incl Γ n k a)) e1).trans hw.symm
  have h1 : l2Form Γ n (k + 1) (avg h g) ζ = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n (k + 1) x (g.1 x) (CForm.fn ζ x) := h.l2Form_avg g.2 ζ
  have h2 : (∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n (k + 1) x (g.1 x) (CForm.fn ζ x)) = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n (k + 1) x (CForm.fn ζ x) (g.1 x) :=
    setIntegral_congr_fun isOpen_positiveCoordinates.measurableSet (fun x hx => by
      rw [formPairing_symm n (k + 1) x hx])
  have h3 : localIntegral n (k + 1) (CForm.fn ζ) g.1 = ∫ x in positiveCoordinates,
      coordinateDensity x * formPairing n (k + 1) x (CForm.fn ζ x) (g.1 x) :=
    localIntegral_eq_setIntegral n (k + 1) _ _ (fun x hx => CForm.outside ζ hx)
  exact (e2.trans ((inner_incl Γ n (k + 1) ζ (avg h g)).trans
    ((l2Form_comm ζ (avg h g)).trans (h1.trans (h2.trans h3.symm)))))

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
