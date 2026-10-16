module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.RepChange
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFaces
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeUniq

@[expose] public section


open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

/-!
# `r_P ℰ_Q^∨(η) = T^∨η` in the face representatives, conditional on canonicity of `T`

Formalized by Claude Sonnet 5.5.
Hypothesis (explicit): `ClassicalLineConstantTerm N n hn`.

`DualRepChange.dualE_eq_dualEJ` identifies the dual class `dualE u'` (series cusps `LineFaces.rep j`) with `dualEJ u` (cusps `ȷ(planeFaceRepr x)`) for a tuple `u` built from `u'`
by the Levi change of cusp (`CuspChangeB`).  Vanishing of line/plane restrictions is a property of the face (the `rPlane_zero_of_rel`, `rLine_zero_of_rel`), so the canonical statement
`dual_rP_eq_dualT_of_canonical` for the `ȷ`-representatives transfers to the representatives `LineFaces.rep` / `planeFaceRepr`:

* `dualRP_eq_zero_of_dualS_eq_zero`: a tuple with zero dual seed vector has zero plane coordinate;
* `dual_rP_eq_dualT_of_canonical_reps`: a single linear `T^∨ : ⨁_j 𝒞_Q(E^∨) → PDmod` with `dualRP (dualEH u') = T^∨ (dualS u')` for every `u'` (and `dualRQ = dualS`, the `dualRQ_dualEH`), whose values are cuspidal at every plane cusp (`dualRP_mem_dualCuspidalP`);
* `dual_rP_eq_dualT_of_canonical_literal`: the same for the literal contragredient (`dualRQL`, `dualRPL`, `ΦQ`, `ΦP`, `isoHd`).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Vanishing of the plane coordinate**: if the dual global class of a tuple (S7's `dualE`, representatives `LineFaces.rep j`) has zero line coordinate, its plane coordinate vanishes
(conditional on canonicity of `T`). -/
theorem dualRP_eq_zero_of_dualS_eq_zero (hN : 3 ≤ N) (hn : 4 ≤ n)
    (hT : ClassicalLineConstantTerm N n hn) (u' : DualTuple N n) (h0 : dualS u' = 0) :
    dualRP hn (dualEH hn u') = 0 := by
  obtain ⟨u, hu⟩ := dualE_eq_dualEJ N n hn u'
  have hC : (dualEH hn u').1 = jPullC N n (classCG N n hn u) := hu.trans (dualEJ_eq N n hn u)
  set c := classCG N n hn u with hc
  -- (a) the line coordinate vanishes
  have hQ : ∀ j : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNQAt N j.rep) (gammaNQAt_le_N N j.rep)
      (jPullC N n c) = 0 := by
    intro j
    rw [← hC, ← dualRQ_apply hN hn (dualEH hn u') j, dualRQ_dualEH hN hn u', h0]
    rfl
  -- (b) the plane restriction of the plane-side class at `ȷ(j.rep)` vanishes
  have hP : ∀ j : LineFaces N, rPlane N n (jmath j.rep) c = 0 := by
    intro j
    have e := jPullC_res N n (gammaNQAt_le_N N j.rep) (gammaNPAt_le N (jmath j.rep)) (jmath_Q_to_P j.rep) c
    rw [hQ j] at e
    exact (map_eq_zero_iff _ (pullQPC_bijective j.rep).1).1 e.symm
  have hP' : ∀ x : PlaneFaces N, rPlane N n (planeFaceRepr x) c = 0 := by
    intro x
    have := rPlane_zero_of_rel (N := N) (n := n)
      ((planeFaceSetoid N).iseqv.symm (rel_tau N ((jFaceEquiv N).symm x))) c (hP ((jFaceEquiv N).symm x))
    rwa [show tauFace N ((jFaceEquiv N).symm x) = x from (jFaceEquiv N).apply_symm_apply x] at this
  -- (c) the canonical statement of the dual constant terms
  obtain ⟨Td, hTd⟩ := dual_rP_eq_dualT_of_canonical N n hN hn hT
  let η : ∀ x : PlaneFaces N, QDJ N n x := fun x =>
    ⟨dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) + dualSeedConjC N n (u x true) (jmath (planeFaceRepr x)),
      (mem_dualCuspidalQ_iff_seeds N n (jmath (planeFaceRepr x)) _).2 ⟨_, _, rfl⟩⟩
  obtain ⟨h1, h2, -⟩ := hTd u η (fun x => rfl)
  have hη : η = 0 := by
    funext x
    apply Subtype.ext
    have e2 : resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
        (gammaNQAt_le_N N (jmath (planeFaceRepr x))) (dualEJ N n hn u) =
        pullQP' N n (planeFaceRepr x) (rPlane N n (planeFaceRepr x) c) := by
      rw [dualEJ_eq]
      exact resToC_dual_Q N n (planeFaceRepr x) c
    rw [← h1 x, e2, hP' x]
    exact (pullQP' N n (planeFaceRepr x)).map_zero
  have hL : ∀ l : LineFaces N, rLine N n l.rep c = 0 := by
    intro l
    have e2 : resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath l.rep)) (gammaNPAt_le N (jmath l.rep))
        (dualEJ N n hn u) = pullPQ' N n l.rep (rLine N n l.rep c) := by
      rw [dualEJ_eq]
      exact resToC_dual_P N n l.rep c
    have hTd0 : Td η l = 0 := by rw [hη, map_zero]; rfl
    rw [h2 l, hTd0] at e2
    exact (map_eq_zero_iff _ (pullPQ'_bijective N n l.rep).1).1 e2.symm
  have hL' : ∀ y : PlaneFaces N, rLine N n (jmath (planeFaceRepr y)) c = 0 := by
    intro y
    exact rLine_zero_of_rel (N := N) (n := n)
      ((lineFaceSetoid N).iseqv.symm (LineFaces.rel_rep (N := N) (jmath (planeFaceRepr y)))) c (hL (sigmaFace N y))
  -- (d) the plane coordinate of S7's class at `planeFaceRepr y`
  apply DFinsupp.ext
  intro y
  rw [dualRP_apply, hC]
  refine (jPullC_res N n (gammaNPAt_le N (planeFaceRepr y)) (gammaNQAt_le_N N (jmath (planeFaceRepr y)))
    (jmath_P_to_Q (planeFaceRepr y)) c).trans ?_
  have : resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNQAt N (jmath (planeFaceRepr y)))
      (gammaNQAt_le_N N (jmath (planeFaceRepr y))) c = 0 := hL' y
  rw [this, map_zero]
  rfl



/-- The plane coordinate of S7's dual class of a tuple is cuspidal at every plane cusp `planeFaceRepr y`. -/
theorem dualRP_mem_dualCuspidalP (hN : 3 ≤ N) (hn : 4 ≤ n) (u' : DualTuple N n) (y : PlaneFaces N) :
    (dualRP hn (dualEH hn u')) y ∈ dualCuspidalP N n (planeFaceRepr y) := by
  obtain ⟨u, hu⟩ := dualE_eq_dualEJ N n hn u'
  have hC : (dualEH hn u').1 = jPullC N n (classCG N n hn u) := hu.trans (dualEJ_eq N n hn u)
  rw [dualRP_apply, hC]
  refine Eq.mpr (congrArg (· ∈ _) (jPullC_res N n (gammaNPAt_le N (planeFaceRepr y))
    (gammaNQAt_le_N N (jmath (planeFaceRepr y))) (jmath_P_to_Q (planeFaceRepr y)) (classCG N n hn u))) ?_
  exact Submodule.mem_map_of_mem
    (zeroFlags_line_mixed N n hN _ (classicalPlaneConstantTerms N n hN hn u).1 (jmath (planeFaceRepr y)))

/-- **`r_P ℰ_Q^∨(η) = T^∨ η` for S7's `dualE`/`dualRP` (representatives `LineFaces.rep j`), conditional on canonicity of `T`** (`ClassicalLineConstantTerm`): there is a single linear map
`T^∨ : ⨁_j 𝒞_Q(E^∨) → ⨁_y H²(Γ_{y⁻¹Py}, E^∨)` with `r_Q ℰ^∨(u') = η'` (S7's `dualRQ_dualEH`), `r_P ℰ^∨(u') = T^∨ η'` for every tuple `u'` with dual seed vector `η'`, and `T^∨ η'`
cuspidal at every plane cusp. -/
theorem dual_rP_eq_dualT_of_canonical_reps (hN : 3 ≤ N) (hn : 4 ≤ n) (hT : ClassicalLineConstantTerm N n hn) :
    ∃ Td' : (⨁ i : LineFaces N, QDi N n i) →ₗ[ℂ] PDmod N n,
      (∀ η' y, (Td' η') y ∈ dualCuspidalP N n (planeFaceRepr y)) ∧
      ∀ u' : DualTuple N n, dualRQ hN hn (dualEH hn u') = dualS u' ∧ dualRP hn (dualEH hn u') = Td' (dualS u') := by
  let S : DualTuple N n →ₗ[ℂ] ⨁ i : LineFaces N, QDi N n i := dualS
  let A : DualTuple N n →ₗ[ℂ] PDmod N n := dualRP hn ∘ₗ dualEH hn
  have hker : LinearMap.ker S ≤ LinearMap.ker A := fun u' hu' =>
    dualRP_eq_zero_of_dualS_eq_zero N n hN hn hT u' hu'
  let e := S.quotKerEquivOfSurjective dualS_surjective
  let Td' : (⨁ i : LineFaces N, QDi N n i) →ₗ[ℂ] PDmod N n := ((LinearMap.ker S).liftQ A hker) ∘ₗ e.symm.toLinearMap
  have hApp : ∀ u' : DualTuple N n, Td' (S u') = A u' := by
    intro u'
    have : e.symm (S u') = Submodule.Quotient.mk u' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [Td', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨Td', fun η' y => ?_, fun u' => ⟨dualRQ_dualEH hN hn u', (hApp u').symm⟩⟩
  obtain ⟨u', rfl⟩ := dualS_surjective η'
  rw [show dualS u' = S u' from rfl, hApp u']
  exact dualRP_mem_dualCuspidalP N n hN hn u' y



theorem ΦQ_injective : Function.Injective (ΦQ (N := N) (n := n)) :=
  (DirectSum.lmap_injective _).2 fun i _a _b hab =>
    Subtype.ext ((toLiteral_bijective (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n).1 (congrArg Subtype.val hab))

/-- **The same for the literal contragredient `E*`** (S7/S4: `dualRQL`, `dualRPL`, `isoHd`, `ΦQ`, `ΦP`): conditional on canonicity of `T`, a single linear `T^∨_{lit}` with
`r_P ℰ^∨(u') = T^∨_{lit} η'` for every tuple `u'` with literal dual seed vector `η' = ΦQ (dualS u')`. -/
theorem dual_rP_eq_dualT_of_canonical_literal (hN : 3 ≤ N) (hn : 4 ≤ n) (hT : ClassicalLineConstantTerm N n hn) :
    ∃ TdL : (⨁ i : LineFaces N, QDiL N n i) →ₗ[ℂ] PDL N n,
      ∀ u' : DualTuple N n, dualRQL hN hn (isoHd hn (dualEH hn u')) = ΦQ (dualS u') ∧
        dualRPL hn (isoHd hn (dualEH hn u')) = TdL (ΦQ (dualS u')) := by
  obtain ⟨Td', -, hTd'⟩ := dual_rP_eq_dualT_of_canonical_reps N n hN hn hT
  let eΦ := LinearEquiv.ofBijective (ΦQ (N := N) (n := n)) ⟨ΦQ_injective N n, ΦQ_surjective⟩
  refine ⟨ΦP ∘ₗ Td' ∘ₗ eΦ.symm.toLinearMap, fun u' => ⟨?_, ?_⟩⟩
  · have e : dualRQL hN hn (isoHd hn (dualEH hn u')) = ΦQ (dualRQ hN hn (dualEH hn u')) := by
      unfold dualRQL
      simp
    rw [e, (hTd' u').1]
  · have e : dualRPL hn (isoHd hn (dualEH hn u')) = ΦP (dualRP hn (dualEH hn u')) := by
      unfold dualRPL
      simp
    rw [e, (hTd' u').2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ΦQ (dualS u') = eΦ (dualS u') from rfl, LinearEquiv.symm_apply_apply]

end TernaryPeriodPolynomials.Argument.EisensteinDual
