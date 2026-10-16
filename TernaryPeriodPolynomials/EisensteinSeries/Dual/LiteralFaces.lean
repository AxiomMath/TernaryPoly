module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralGlobal

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups DirectSum

/-!
# `dualEisenstein` for the literal contragredient `E_n^*`

Formalized by Claude Sonnet 5.5.

the `dualEisenstein_gammaN` is stated for the classes of `H²(Γ(N), E^∨)`.  the Stokes lemma (`GammaNStokes.gamma6_stokes_En`) uses the literal contragredient, so
here the same obligation is transported along the isomorphisms `toLiteral` (face level) / `toLiteralG` (global):

* `QDiL i = 𝒞_Q(E*)` at the line face `i` (`dualCuspidalQLiteral`), `PDL` the literal plane groups, `HdLit` the literal dual classes;
* `dualRQL`, `dualRPL`: the line and plane restrictions of literal dual classes, with `dualRQL_apply`, `dualRPL_apply`: they are the `twoCohomologyRestriction (Subgroup.inclusion …)`;
* `dualEisenstein_gammaN_literal`: for `3 ≤ N`, `4 ≤ n` there is a linear `Td` such that every `η ∈ ⨁ 𝒞_Q(E*)` is the line coordinate of a literal dual series class with plane coordinate `Td η`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open GeneralEisenstein TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.SphericalDetection.Helpers (twoCohomologyRestriction)

variable {N n : ℕ}

theorem toLiteral_eq_mapId (S : Subgroup SL(3, ℤ)) (hS : S ≤ gammaN N) :
    toLiteral S hS n = mapId ((dualRhoC N n).comp (Subgroup.inclusion hS)) ((dualRepC (gammaN N) n).comp (Subgroup.inclusion hS))
      (dualIso n).toLinearMap (fun s v => dualIso_equivariant_G N n (Subgroup.inclusion hS s) v) := rfl


open scoped Classical

section Lit

variable [NeZero N]

/-- The literal dual mixed cuspidal groups of the line faces. -/
abbrev QDiL (N n : ℕ) [NeZero N] (i : LineFaces N) := ↥(dualCuspidalQLiteral N n i.rep)

/-- The literal plane groups of the plane faces. -/
abbrev PDL (N n : ℕ) [NeZero N] := ⨁ x : PlaneFaces N, groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp
  (Subgroup.inclusion (gammaNPAt_le N (planeFaceRepr x)))))

/-- `toLiteral` restricted to the cuspidal group of a line face. -/
def toLitQ (i : LineFaces N) : QDi N n i →ₗ[ℂ] QDiL N n i :=
  ((toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n).domRestrict (dualCuspidalQ N n i.rep)).codRestrict
    (dualCuspidalQLiteral N n i.rep) (fun x => Submodule.mem_map_of_mem x.2)

theorem toLitQ_surjective (i : LineFaces N) : Function.Surjective (toLitQ (N := N) (n := n) i) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The comparison `⨁ 𝒞_Q(E^∨) → ⨁ 𝒞_Q(E*)`. -/
def ΦQ : (⨁ i : LineFaces N, QDi N n i) →ₗ[ℂ] ⨁ i : LineFaces N, QDiL N n i := DirectSum.lmap (fun i => toLitQ i)

theorem ΦQ_surjective : Function.Surjective (ΦQ (N := N) (n := n)) :=
  (DirectSum.lmap_surjective _).2 toLitQ_surjective

/-- The comparison of the plane groups. -/
def ΦP : PDmod N n →ₗ[ℂ] PDL N n :=
  DirectSum.lmap (fun x => toLiteral (gammaNPAt N (planeFaceRepr x)) (gammaNPAt_le N (planeFaceRepr x)) n)

/-- `toLiteralG` is an isomorphism `Hd ≃ HdLit`. -/
def isoHd (hn : 4 ≤ n) : Hd (N := N) (n := n) hn ≃ₗ[ℂ] HdLit (N := N) hn :=
  LinearEquiv.ofBijective
    ((toLiteralG N n ∘ₗ (Hd (N := N) (n := n) hn).subtype).codRestrict (HdLit (N := N) hn)
      (fun c => by obtain ⟨u, hu⟩ := c.2; exact ⟨u, congrArg (toLiteralG N n) hu⟩))
    ⟨fun a b hab => Subtype.ext ((toLiteralG_bijective N n).1 (congrArg Subtype.val hab)), by
      rintro ⟨y, u, rfl⟩
      exact ⟨⟨dualE hn u, LinearMap.mem_range_self _ u⟩, rfl⟩⟩

theorem isoHd_apply (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) : (isoHd hn c).1 = toLiteralG N n c.1 := rfl

/-- The line restriction of the literal dual classes into `⨁ 𝒞_Q(E*)`. -/
def dualRQL (hN : 3 ≤ N) (hn : 4 ≤ n) : HdLit (N := N) hn →ₗ[ℂ] ⨁ i : LineFaces N, QDiL N n i :=
  ΦQ ∘ₗ dualRQ hN hn ∘ₗ (isoHd hn).symm.toLinearMap

/-- The plane restriction of the literal dual classes. -/
def dualRPL (hn : 4 ≤ n) : HdLit (N := N) hn →ₗ[ℂ] PDL N n :=
  ΦP ∘ₗ dualRP hn ∘ₗ (isoHd hn).symm.toLinearMap

theorem dualRQ_apply (hN : 3 ≤ N) (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) (i : LineFaces N) :
    ((dualRQ hN hn c) i : groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N i.rep))))) =
      resLine i c.1 := by
  change ((∑ j : LineFaces N, DirectSum.lof ℂ (LineFaces N) (fun i => QDi N n i) j _) i : QDi N n i).1 = _
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · intro j _ hj
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
  · simp

/-- **The line coordinate of a literal dual class is S1's restriction** `twoCohomologyRestriction (Subgroup.inclusion …)`. -/
theorem dualRQL_apply (hN : 3 ≤ N) (hn : 4 ≤ n) (c' : HdLit (N := N) hn) (i : LineFaces N) :
    ((dualRQL hN hn c' i : QDiL N n i) : groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp
        (Subgroup.inclusion (gammaNQAt_le_N N i.rep))))) =
      twoCohomologyRestriction (Subgroup.inclusion (gammaNQAt_le_N N i.rep)) (Rep.of (dualRepC (gammaN N) n)) c'.1 := by
  obtain ⟨c, rfl⟩ := (isoHd hn).surjective c'
  have e : dualRQL hN hn (isoHd hn c) = ΦQ (dualRQ hN hn c) := by
    unfold dualRQL
    simp
  rw [e]
  have e2 : ((ΦQ (dualRQ hN hn c)) i : QDiL N n i).1 =
      toLiteral (gammaNQAt N i.rep) (gammaNQAt_le_N N i.rep) n ((dualRQ hN hn c i).1) := rfl
  rw [e2, dualRQ_apply, isoHd_apply, ← toLiteralG_res]
  rfl

theorem dualRP_apply (hn : 4 ≤ n) (c : Hd (N := N) (n := n) hn) (x : PlaneFaces N) :
    (dualRP hn c) x = resToC N n (ρ := dualRhoC N n) (gammaNPAt N (planeFaceRepr x)) (gammaNPAt_le N (planeFaceRepr x)) c.1 := by
  unfold dualRP
  rw [LinearMap.sum_apply, DFinsupp.finsetSum_apply, Finset.sum_eq_single x]
  · simp [DirectSum.lof_eq_of]
  · intro y _ hy
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy)]
  · simp

/-- **The plane coordinate of a literal dual class is S1's restriction.** -/
theorem dualRPL_apply (hn : 4 ≤ n) (c' : HdLit (N := N) hn) (x : PlaneFaces N) :
    (dualRPL hn c') x =
      twoCohomologyRestriction (Subgroup.inclusion (gammaNPAt_le N (planeFaceRepr x))) (Rep.of (dualRepC (gammaN N) n)) c'.1 := by
  obtain ⟨c, rfl⟩ := (isoHd hn).surjective c'
  have e : dualRPL hn (isoHd hn c) = ΦP (dualRP hn c) := by
    unfold dualRPL
    simp
  rw [e]
  have e2 : (ΦP (dualRP hn c)) x =
      toLiteral (gammaNPAt N (planeFaceRepr x)) (gammaNPAt_le N (planeFaceRepr x)) n ((dualRP hn c) x) := rfl
  rw [e2, dualRP_apply, isoHd_apply, ← toLiteralG_res]
  rfl

open TernaryPeriodPolynomials.Argument.FormClassK in
/-- **`dualEisenstein` of S1's `GammaNC5FaceObligations` for the literal contragredient** (`3 ≤ N`, `4 ≤ n`): with `Hd := HdLit` (literal classes generated by the dual series, all with zero flag
restrictions: `HdLit_zeroFlags`), `QDi i := 𝒞_Q(E*)` (`dualCuspidalQLiteral`), `PD := ⨁ H²(Γ_{P'}, E*)` and the restrictions `twoCohomologyRestriction (Subgroup.inclusion …)` (`dualRQL_apply`, `dualRPL_apply`),
there is a linear `Td` such that every `η` is the line coordinate of a literal dual series class whose plane coordinate is `Td η`. -/
theorem dualEisenstein_gammaN_literal (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ Td : (⨁ i : LineFaces N, QDiL N n i) →ₗ[ℂ] PDL N n,
      ∀ η : ⨁ i : LineFaces N, QDiL N n i, ∃ c' : HdLit (N := N) hn, dualRQL hN hn c' = η ∧ dualRPL hn c' = Td η := by
  refine dualEisenstein_of_section (dualRPL hn) (dualRQL hN hn) ((isoHd hn).toLinearMap ∘ₗ dualEH hn)
    (ΦQ ∘ₗ dualS) ?_ ((ΦQ_surjective (N := N) (n := n)).comp dualS_surjective)
  intro u
  have e : dualRQL hN hn (isoHd hn (dualEH hn u)) = ΦQ (dualRQ hN hn (dualEH hn u)) := by
    unfold dualRQL
    simp
  change dualRQL hN hn (isoHd hn (dualEH hn u)) = ΦQ (dualS u)
  rw [e, dualRQ_dualEH hN hn u]

end Lit

end TernaryPeriodPolynomials.Argument.EisensteinDual
