module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.AssemblyCore
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Assembly
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupportForm
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.L2.Final
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.LevelTwo
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.TorsionFree
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESLevelOne

@[expose] public section


/-!
# Eichler–Shimura spanning at every principal congruence level

For a finite-index subgroup `Λ ⊆ SL(2, ℤ)` with `-1 ∉ Λ`, every parabolic class of
`H¹(Λ, Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period classes of cusp
forms of weight `n + 3` (`esSpan_of_neg_one_not_mem`). The proof:

* a parabolic cocycle has an equivariant smooth primitive `Φ₁` whose differential is supported
  compactly modulo `Λ` (`CompactSupport.exists_compactSupport_primitive_matrix`);
* the `L²` Hodge projection of `dΦ₁` gives a smooth closed and co-closed equivariant representative
  `a dx + b dy`, whose `dz` and `dz̄` parts are `F(z)(zX₁ - X₀)^{n+1}` and the conjugate of
  `G(z)(zX₁ - X₀)^{n+1}` for cusp forms `F`, `G` (`SymFrame.ES_assembly_core`);
* its primitive `Φ₀` transforms by a cocycle cohomologous to the original one
  (`L2.HodgeDatum.coboundary_of_projection`);
* `Φ₀` is the sum of the holomorphic and antiholomorphic Eichler primitives of `F` and `G` up to a
  constant (`Assembly.eq_periodPrim_add_const`), so the class is in the span
  (`Assembly.mem_span_of_periods`).

At the principal congruence subgroups (`esSpan_gamma`): `Γ(1) = SL(2, ℤ)` is
`SeedC3S4c.esSpan_top`; for `N ≥ 3`, `-1 ∉ Γ(N)`; for `N = 2` and `n` even the cohomology vanishes
(`CentralSign`), and for `n` odd one passes through the index-two subgroup `Γ'(2)`, which does not
contain `-1` (`LevelTwo.esSpan_gamma2_of_prime`).

Written by Claude Opus 5.5 and Claude Sonnet 5.5.
-/

open Complex MvPolynomial
open scoped MatrixGroups ContDiff
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U)
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition (mob)
open TernaryPeriodPolynomials.Argument.ESFoundations.L2 (Weights)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.ESFinal

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.BinCoeff
open TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
open TernaryPeriodPolynomials.Argument.ESFoundations.Assembly

/-- **Eichler–Shimura spanning** for a finite-index subgroup of `SL(2, ℤ)` not containing `-1`. -/
theorem esSpan_of_neg_one_not_mem {Λ : Subgroup SL(2, ℤ)} [Λ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∉ Λ) (n : ℕ) : ESSpan Λ n := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨Φ₁, hΦ₁, hΦ₁eq, K, hK, hKU, h0⟩ :=
    CompactSupport.exists_compactSupport_primitive_matrix hneg (rhoW Λ n) (cocycleW c)
      (cocycleW_mul c) (fun γ hγ => cocycleW_parabolic hc γ hγ)
  let W : Weights Λ := Classical.arbitrary _
  have hcoc : ∀ δ : Λ, ∀ z ∈ U, Φ₁ (mob (δ : SL(2, ℤ)) z) =
      (hodgeDatumSym (n + 1) Λ).ρ δ (Φ₁ z) + cocycleW c δ := hΦ₁eq
  obtain ⟨a', b', F, G, ha, hb, hcl, -, hE, -, hae, hcoef⟩ :=
    ES_assembly_core hneg n W (cocycleW c) hΦ₁ hcoc hK hKU h0
  obtain ⟨Φ₀, c₀, hΦ₀, hΦ₀eq, w, hw⟩ :=
    (hodgeDatumSym (n + 1) Λ).coboundary_of_projection W (cocycleW c) hΦ₁ hcoc hK hKU h0 ha hb
      hcl hE hae
  refine mem_span_of_periods c F G Φ₀ c₀ hΦ₀eq ⟨w, hw⟩ ?_
  refine eq_periodPrim_add_const F G Φ₀ (fun z => WithLp.toLp 2 (coefA a' b' z))
    (fun z => WithLp.toLp 2 (coefB a' b' z)) (fun z hz => ⟨_, hΦ₀ z hz, fun v => ?_⟩)
    (fun z hz i => (hcoef z hz i).1) (fun z hz i => (hcoef z hz i).2)
  exact formOf_apply_wd a' b' z v

/-- **Eichler–Shimura spanning at every principal congruence subgroup `Γ(N)`, `N > 0`.** -/
theorem esSpan_gamma (N n : ℕ) (hN : 0 < N) : ESSpan (CongruenceSubgroup.Gamma N) n := by
  have : NeZero N := ⟨hN.ne'⟩
  rcases (show N = 1 ∨ N = 2 ∨ 3 ≤ N by omega) with rfl | rfl | h3
  · rw [CongruenceSubgroup.Gamma_one_top]
    exact esSpan_top n
  · rcases Nat.even_or_odd n with he | ho
    · exact CentralSign.esSpan_of_neg_one_mem_of_even LevelTwo.neg_one_mem_Gamma2 he
    · exact LevelTwo.esSpan_gamma2_of_prime ho
        (esSpan_of_neg_one_not_mem LevelTwo.neg_one_not_mem_gammaTwoPrime n)
  · exact esSpan_of_neg_one_not_mem (neg_one_not_mem_Gamma h3) n

end TernaryPeriodPolynomials.Argument.ESFoundations.ESFinal
