module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.PairingCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.OrbitPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2

@[expose] public section


/-!
# Torus averaging and the pairing criterion

Let `Θ : ℝ × ℝ → (Fin 3 → GL₃(ℚ)) → V` be a continuous family of homogeneous 2-cocycles with
values in a finite-dimensional representation `V`, whose coordinates integrate to zero over the
unit square.  If all grid averages of `Θ` differ from `Θ 0` by an equivariant coboundary, then
`Θ 0` is an equivariant coboundary.  The proof pairs the inhomogeneous restriction of `Θ 0` with
finitely supported dual 2-cycles, evaluates the pairing as a Riemann sum, and concludes with the
pairing criterion for `H²`.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous MeasureTheory
open TernaryPeriodPolynomials.FlagExactness

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

section Aux

variable {G : Type} [Group G] (A : Rep ℂ G)

private theorem pairing₂_add_aux (f g : G × G → A) (chain : DualChains₂ A) :
    pairing₂ A (f + g) chain = pairing₂ A f chain + pairing₂ A g chain := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb]
    ring
  | single pair μ =>
    rw [pairing₂_single, pairing₂_single, pairing₂_single, Pi.add_apply, map_add]

private theorem pairing₂_eq_sum_aux (f : G × G → A) (chain : DualChains₂ A) :
    pairing₂ A f chain = ∑ pair ∈ chain.support, chain pair (f pair) := by
  rw [pairing₂, Finsupp.lsum_apply, Finsupp.sum]
  rfl

end Aux

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- **Torus averaging and the pairing criterion**, with continuity of the family stated through
the coordinates `μ (Θ r y)` of linear functionals `μ`; no topology on `V` is needed. -/
theorem isCoboundary_of_torus_average_of_functional_continuous [FiniteDimensional ℂ V]
    (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → V)
    (hcoc : ∀ r, IsCocycle₂ (Θ r))
    (hcont : ∀ (y : Fin 3 → RationalGL3) (μ : V →ₗ[ℂ] ℂ), Continuous fun r => μ (Θ r y))
    (hzero : ∀ (y : Fin 3 → RationalGL3) (μ : V →ₗ[ℂ] ℂ),
      ∫ r in Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, μ (Θ r y) = 0)
    (hΘ0 : Equivariant Γ ρ (Θ 0))
    (hgrid : ∀ K : ℕ, 0 < K → IsCoboundary Γ ρ (gridAverage Θ K - Θ 0))
    (riemann : ∀ φ : ℝ × ℝ → ℂ, Continuous φ → Filter.Tendsto
      (fun K : ℕ => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        φ ((a : ℝ) / K, (b : ℝ) / K)) Filter.atTop
        (nhds (∫ p in Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p))) :
    IsCoboundary Γ ρ (Θ 0) := by
  classical
  set A := SphericalDetection.Helpers.subgroupCoefficientRep Γ ρ
  have : FiniteDimensional ℂ A := ‹FiniteDimensional ℂ V›
  let θ : ℝ × ℝ → Γ × Γ → A := fun r p => Θ r ![1, p.1.val, p.1.val * p.2.val]
  have key : ∀ chain : DualChains₂ A, dualBoundary A chain = 0 → pairing₂ A (θ 0) chain = 0 := by
    intro chain hcycle
    let μ : Γ × Γ → (V →ₗ[ℂ] ℂ) := fun pair => chain pair
    let φ : ℝ × ℝ → ℂ := fun r => pairing₂ A (θ r) chain
    have hφ : φ = fun r => ∑ pair ∈ chain.support,
        μ pair (Θ r ![1, pair.1.val, pair.1.val * pair.2.val]) :=
      funext fun r => pairing₂_eq_sum_aux A (θ r) chain
    have hcontφ : Continuous φ := by
      rw [hφ]
      exact continuous_finsetSum _ (fun pair _ => hcont _ (μ pair))
    have hint : ∫ r in Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ r = 0 := by
      rw [hφ, integral_finsetSum]
      · exact Finset.sum_eq_zero (fun pair _ => hzero _ (μ pair))
      · intro pair _
        exact ((hcont _ (μ pair)).continuousOn).integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc)
    have hgridpair : ∀ K : ℕ, 0 < K → (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K,
        ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) = pairing₂ A (θ 0) chain := by
      intro K hK
      obtain ⟨P, hPeq, hP⟩ := hgrid K hK
      let τ : Γ → A := fun g => P ![1, g.val]
      have hfun : (fun p : Γ × Γ => gridAverage Θ K ![1, p.1.val, p.1.val * p.2.val]) =
          (groupCohomology.d₁₂ A).hom τ + θ 0 := by
        funext p
        have h1 : gridAverage Θ K ![1, p.1.val, p.1.val * p.2.val] -
            Θ 0 ![1, p.1.val, p.1.val * p.2.val] =
            P ![p.1.val, p.1.val * p.2.val] - P ![1, p.1.val * p.2.val] +
              P ![1, p.1.val] := congrFun hP ![1, p.1.val, p.1.val * p.2.val]
        have h2 : P ![p.1.val, p.1.val * p.2.val] = ρ p.1.val (P ![1, p.2.val]) := by
          have := hPeq p.1.val p.1.2 ![1, p.2.val]
          have e : (fun i => p.1.val * (![1, p.2.val] : Fin 2 → RationalGL3) i) =
              ![p.1.val, p.1.val * p.2.val] := by
            funext i; fin_cases i <;> first | rfl | simp
          rw [e] at this
          exact this
        rw [Pi.add_apply, groupCohomology.d₁₂_hom_apply]
        show _ = ρ p.1.val (P ![1, p.2.val]) - P ![1, (p.1 * p.2).val] + P ![1, p.1.val] +
          Θ 0 ![1, p.1.val, p.1.val * p.2.val]
        rw [Subgroup.coe_mul, ← h2]
        linear_combination (norm := abel) h1
      have hpair : pairing₂ A (fun p : Γ × Γ =>
          gridAverage Θ K ![1, p.1.val, p.1.val * p.2.val]) chain = pairing₂ A (θ 0) chain := by
        have e : pairing₂ A (fun p : Γ × Γ =>
            gridAverage Θ K ![1, p.1.val, p.1.val * p.2.val]) chain =
            pairing₂ A ((groupCohomology.d₁₂ A).hom τ + θ 0) chain :=
          congrArg (fun f => pairing₂ A f chain) hfun
        rw [e, pairing₂_add_aux, pairing₂_d₁₂, hcycle, map_zero, zero_add]
      have hL : pairing₂ A (fun p : Γ × Γ =>
          gridAverage Θ K ![1, p.1.val, p.1.val * p.2.val]) chain =
          ∑ pair ∈ chain.support,
            μ pair (gridAverage Θ K ![1, pair.1.val, pair.1.val * pair.2.val]) :=
        pairing₂_eq_sum_aux A _ chain
      have hR : ∀ r, φ r = ∑ pair ∈ chain.support,
          μ pair (Θ r ![1, pair.1.val, pair.1.val * pair.2.val]) := fun r => congrFun hφ r
      rw [← hpair, hL]
      simp only [hR, gridAverage, map_smul, map_sum, smul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact ((Finset.sum_comm).trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm)).symm
    have hlim := riemann φ hcontφ
    rw [hint] at hlim
    have hev : (fun K : ℕ => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        φ ((a : ℝ) / K, (b : ℝ) / K)) =ᶠ[Filter.atTop] fun _ => pairing₂ A (θ 0) chain := by
      filter_upwards [Filter.eventually_gt_atTop 0] with K hK
      exact hgridpair K hK
    exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hev)
  obtain ⟨τ, hτ⟩ := mem_coboundaries₂_of_pairing A (θ 0) key
  let Kc : cochains Γ ρ 2 := ⟨Θ 0, fun γ x => hΘ0 γ.val γ.2 x⟩
  obtain ⟨P, hP⟩ := exists_primitive_of_inhomogeneous Γ ρ Kc (fun x => hcoc 0 x) τ
    (fun a b => by
      have := congrFun hτ (a, b)
      rw [groupCohomology.d₁₂_hom_apply] at this
      exact this.symm)
  exact ⟨P.val, fun γ hγ x => P.property ⟨γ, hγ⟩ x, funext fun x => (hP x).symm⟩

/-- **Torus averaging and the pairing criterion.** If `Θ` is a continuous family of homogeneous
2-cocycles with vanishing coordinate integrals over the unit square, and every grid average
of `Θ` differs from `Θ 0` by an equivariant coboundary, then `Θ 0` is an equivariant
coboundary.  Here `V` carries a Hausdorff vector-space topology; the topology plays no role
beyond turning continuity of `r ↦ Θ r y` into continuity of its linear coordinates. -/
theorem isCoboundary_of_torus_average [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → V)
    (hcoc : ∀ r, IsCocycle₂ (Θ r))
    (hcont : ∀ y, Continuous fun r => Θ r y)
    (hzero : ∀ (y : Fin 3 → RationalGL3) (μ : V →ₗ[ℂ] ℂ),
      ∫ r in Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, μ (Θ r y) = 0)
    (hΘ0 : Equivariant Γ ρ (Θ 0))
    (_hgridEq : ∀ K : ℕ, 0 < K → Equivariant Γ ρ (gridAverage Θ K))
    (hgrid : ∀ K : ℕ, 0 < K → IsCoboundary Γ ρ (gridAverage Θ K - Θ 0))
    (riemann : ∀ φ : ℝ × ℝ → ℂ, Continuous φ → Filter.Tendsto
      (fun K : ℕ => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        φ ((a : ℝ) / K, (b : ℝ) / K)) Filter.atTop
        (nhds (∫ p in Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p))) :
    IsCoboundary Γ ρ (Θ 0) :=
  isCoboundary_of_torus_average_of_functional_continuous Γ ρ Θ hcoc
    (fun y μ => (LinearMap.continuous_of_finiteDimensional μ).comp (hcont y)) hzero hΘ0
    hgrid riemann

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
