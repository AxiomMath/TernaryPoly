module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AutomorphicSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Parity

@[expose] public section


/-!
# The direct route to the `n + 3` branch of `inner_bad_line_cuspidal_span`

An inner bad-line class `a` is compared with an element of the automorphic line span through their
edge classes in `H¹(Γ₁'(3), Sym^{n+1})`; no Hecke eigencharacters (and no matching of them with the
pair characters of the cuspidal data) are involved:

* `InnerEdgeRealized n`: the bad-line Shapiro coordinate of every inner bad-line class has zero
  radical restriction, and its edge class is `(n + 1)` times the period class of a cusp form of
  weight `n + 3` for `Γ₁(3)` (Eichler–Shimura surjectivity onto the parabolic classes, and the
  identification of the edge of the local classes of the inner classes with the parabolic class of
  Sol).
* `PeriodsRealized n`: every period class `levelPeriodMap (n + 1) 0 f` is realized, up to the factor
  `n + 1`, as the edge of the bad-line coordinate of an element of the automorphic line span which
  vanishes at the good cusp (cuspidal data attached to the weight `-(n + 3)` level-three vectors
  of the cuspidal constituents, their Eichler cocycles and line sources).

`inner_bad_line_of_direct` proves the goal from the two statements: the edge map is injective on
the radical kernel and a class of the line stratum is determined by its two Shapiro coordinates.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.DirectRoute

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle (S)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

variable {n : ℕ}

/-- The classes of the period space `S_{n+3}(Γ₁(3))` realized by the automorphic line span: the
period class of `f` (times `n + 1`) is the edge of the bad-line coordinate of an element of the
automorphic line span vanishing at the good line cusp. -/
def periodRealized (n : ℕ) (hn : 0 < n) : Submodule ℂ (S (n + 1)) where
  carrier := {f | ∃ b ∈ automorphicLineSpan n,
    cuspRes n trivialCharacter .line true b = 0 ∧
      ∃ y : badLineLocalRadicalKernel n,
        y.1 = cuspRes n trivialCharacter .line false b ∧
          badLineEdge n hn y = ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 f}
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem _, map_zero _, 0, ?_, ?_⟩
    · simp; rfl
    · simp; rfl
  add_mem' := by
    rintro f g ⟨b, hb, hbgood, y, hy, hyedge⟩ ⟨c, hc, hcgood, z, hz, hzedge⟩
    refine ⟨b + c, Submodule.add_mem _ hb hc, ?_, y + z, ?_, ?_⟩
    · rw [map_add, hbgood, hcgood, add_zero]
    · have h := congrArg₂ (· + ·) hy hz
      rw [map_add]
      exact h
    · rw [map_add, hyedge, hzedge, map_add, smul_add]; rfl
  smul_mem' := by
    rintro r f ⟨b, hb, hbgood, y, hy, hyedge⟩
    refine ⟨r • b, Submodule.smul_mem _ r hb, ?_, r • y, ?_, ?_⟩
    · rw [map_smul, hbgood, smul_zero]
    · have h := congrArg (fun x => r • x) hy
      rw [map_smul]
      exact h
    · rw [map_smul, hyedge, map_smul, smul_comm]; rfl

/-- **Input (cuspidal supply).**  Every period class is realized by the automorphic line span:
the span of the cusp forms of the level-three weight vectors of the cohomological constituents of
the model is everything (so `periodRealized` is the whole space). -/
def PeriodsRealized (n : ℕ) (hn : 0 < n) : Prop :=
  periodRealized n hn = ⊤

/-- **Input (classical side).**  The bad-line coordinate of every inner bad-line class lies in
the radical kernel and its edge class is `(n + 1)` times the period class of a cusp form.
Owners: D and PI (Eichler–Shimura), Sol (`innerBadLineParabolicMap`). -/
def InnerEdgeRealized (n : ℕ) (hn : 0 < n) : Prop :=
  ∀ a ∈ innerBadLineClasses n,
    ∃ y : badLineLocalRadicalKernel n,
      y.1 = cuspRes n trivialCharacter .line false a ∧
        ∃ f : S (n + 1), badLineEdge n hn y = ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 f

/-- **The direct route.**  An inner bad-line class vanishing at the good cusp lies in the automorphic
line span as soon as the period classes are realized and the edge classes of the inner classes are
period classes. -/
theorem inner_bad_line_of_direct (hn : 0 < n) (hES : InnerEdgeRealized n hn)
    (hP : PeriodsRealized n hn) :
    ∀ a : StratumH2 n trivialCharacter .line, VanishesOnGood n trivialCharacter .line a →
      InnerBoundary n trivialCharacter .line a → a ∈ automorphicLineSpan n := by
  intro a good inner
  have ha : a ∈ innerBadLineClasses n := (mem_innerBadLineClasses_iff n a).mpr ⟨good, inner⟩
  obtain ⟨y, hy, f, hyf⟩ := hES a ha
  have hf : f ∈ periodRealized n hn := by
    rw [hP]
    exact Submodule.mem_top
  obtain ⟨b, hb, hbgood, z, hz, hzf⟩ := hf
  have hyz : z = y := badLineEdge_injective n hn (hzf.trans hyf.symm)
  have hgood : cuspRes n trivialCharacter .line true a = 0 :=
    (vanishesOnGood_iff_fixedPointH2 a).mp good (cuspFlag .line true)
      ((cuspFlag_good_iff .line true).mpr rfl)
  have hzero : a - b = 0 := by
    refine (eq_zero_iff_cuspRes .line (a - b)).mpr ⟨?_, ?_⟩
    · rw [map_sub, hgood, hbgood, sub_zero]
    · rw [map_sub, ← hy, ← hz, hyz]
      exact sub_self _
  have hab : a = b := sub_eq_zero.mp hzero
  rw [hab]
  exact hb

/-- The two inputs of the direct route, for the degree `n + 3` of the `n + 3` branch. -/
def DirectInputs (n : ℕ) : Prop :=
  InnerEdgeRealized (n + 3) (Nat.succ_pos _) ∧ PeriodsRealized (n + 3) (Nat.succ_pos _)

/-- **The goal at the `n + 3` branch of `inner_bad_line_cuspidal_span`.** -/
theorem inner_bad_line_n_plus_three (h : DirectInputs n)
    (a : StratumH2 (n + 3) trivialCharacter .line)
    (good : VanishesOnGood (n + 3) trivialCharacter .line a)
    (inner : InnerBoundary (n + 3) trivialCharacter .line a) :
    a ∈ automorphicLineSpan (n + 3) :=
  inner_bad_line_of_direct (Nat.succ_pos _) h.1 h.2 a good inner

end TernaryPeriodPolynomials.Automorphic.DirectRoute
