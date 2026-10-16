module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSection
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinCuspTerm

@[expose] public section


/-!
# Linearity of the classical series class in the cusp forms, and `dualEisenstein` by a linear section

Formalized by Claude Sonnet 5.5.

* `classCG_add`, `classCG_smul`: the summed class `classCG` is additive and homogeneous for the twisted scalar action of `TwTuple` (conjugate-linear on the antiholomorphic seed), assembled from the `eisensteinAtClassC_add` and `eisensteinAtClassC_cmul` (`Statements.EisensteinCuspTerm`).
* `SeedLinearity`: the remaining half of `ClassicalLinearity` (additivity and homogeneity of `seedBoundary`; the L3 seed side, NOT proved here), and `ClassicalLinearity.of_seed`.
* `dualEisenstein_of_section`: the `dualEisenstein` field of `GammaNC5Obligations` by the same linear-section argument, abstractly (dual classes `Hd`, restrictions `rPd`, `rQd`, parameters `U` with
  `E : U → Hd`, `S : U → QD`, `rQd ∘ E = S` (the `dual_rQ_at`) and `S` surjective): no unfolding.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem classCG_term_add (hn : 4 ≤ n) (b : Bool) (x : PlaneFaces N)
    (f g : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f + g) (planeFaceRepr x) b hn) =
      EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (planeFaceRepr x) b hn) +
      EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n g (planeFaceRepr x) b hn) :=
  Statements.EisensteinClass.eisensteinAtClassC_add (gammaN N) n (leviGroup N) b (CuspData.ofSL (planeFaceRepr x)) hn
    (leviInCusp_gammaN N _) f g

theorem classCG_term_smul (hn : 4 ≤ n) (b : Bool) (x : PlaneFaces N) (a : ℂ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (a • f) (planeFaceRepr x) b hn) =
      cx b a • EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f (planeFaceRepr x) b hn) :=
  Statements.EisensteinClass.eisensteinAtClassC_cmul (gammaN N) n (leviGroup N) b (CuspData.ofSL (planeFaceRepr x)) hn
    (leviInCusp_gammaN N _) a f

theorem classCG_add (hn : 4 ≤ n) (f g : TwTuple N n) :
    classCG N n hn (f + g) = classCG N n hn f + classCG N n hn g := by
  unfold classCG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Finset.sum_congr rfl fun b _ => classCG_term_add N n hn b x (f x b) (g x b)).trans
    Finset.sum_add_distrib

theorem classCG_smul (hn : 4 ≤ n) (a : ℂ) (f : TwTuple N n) :
    classCG N n hn (a • f) = a • classCG N n hn f := by
  unfold classCG
  refine (Finset.sum_congr rfl fun x _ => ?_).trans (Finset.smul_sum).symm
  refine (Finset.sum_congr rfl fun b _ => ?_).trans (Finset.smul_sum).symm
  have h := classCG_term_smul N n hn b x (if b then star a else a) (f x b)
  have hc : cx b (if b then star a else a) = a := by cases b <;> simp [cx]
  rw [hc] at h
  exact h

/-- **The seed side of `ClassicalLinearity`**: additivity and (twisted) homogeneity of the seed vector in the cusp forms (S6's L3, seed side). -/
structure SeedLinearity : Prop where
  seed_add : ∀ f g : TwTuple N n, seedBoundary N n (f + g) = seedBoundary N n f + seedBoundary N n g
  seed_smul : ∀ (a : ℂ) (f : TwTuple N n), seedBoundary N n (a • f) = a • seedBoundary N n f

/-- **`ClassicalLinearity` from the seed-side linearity alone**: the series side is S6's `eisensteinAtClassC_add/_cmul`
(`classCG_add`, `classCG_smul`). -/
theorem ClassicalLinearity.of_seed (hn : 4 ≤ n) (hs : SeedLinearity N n) : ClassicalLinearity N n hn where
  class_add := classCG_add N n hn
  class_smul := classCG_smul N n hn
  seed_add := hs.seed_add
  seed_smul := hs.seed_smul

/-- **`dualEisenstein` by a linear section** (abstract form).  Let `Hd` be the admissible dual global classes with restriction maps `rQd : Hd → QD`, `rPd : Hd → PD`,
let `U` be a module of parameters (tuples of cusp forms for the dual series, with the twisted scalar action) with a linear map `E : U → Hd` (the dual
series class) and a linear map `S : U → QD` (the seed vector), with `rQd (E u) = S u` (the dual constant term `r_Q ℰ_Q^∨ = η`, S4's `dual_rQ_at`) and `S` surjective
(Eichler-Shimura spanning for the dual coefficients).  Then there is a linear map `Td : QD → PD` such that every `η` is the line coordinate of a dual class
whose plane coordinate is `Td η`.  No unfolding is used; `Td` depends on the chosen section. -/
theorem dualEisenstein_of_section {QD PD Hd U : Type*} [AddCommGroup QD] [Module ℂ QD] [AddCommGroup PD] [Module ℂ PD]
    [AddCommGroup Hd] [Module ℂ Hd] [AddCommGroup U] [Module ℂ U]
    (rPd : Hd →ₗ[ℂ] PD) (rQd : Hd →ₗ[ℂ] QD) (E : U →ₗ[ℂ] Hd) (S : U →ₗ[ℂ] QD)
    (hconst : ∀ u, rQd (E u) = S u) (hsurj : Function.Surjective S) :
    ∃ Td : QD →ₗ[ℂ] PD, ∀ η : QD, ∃ c' : Hd, rQd c' = η ∧ rPd c' = Td η := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective S (LinearMap.range_eq_top.2 hsurj)
  refine ⟨rPd ∘ₗ E ∘ₗ s, fun η => ⟨E (s η), ?_, rfl⟩⟩
  rw [hconst]
  exact LinearMap.congr_fun hs η

end TernaryPeriodPolynomials.Argument.FormClassK
