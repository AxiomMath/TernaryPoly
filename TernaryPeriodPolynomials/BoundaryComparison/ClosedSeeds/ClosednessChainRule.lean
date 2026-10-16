module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`), chain-rule helpers for the "hard" cases: a complex
function differentiable at `seedTau p`, composed with `seedTau` along coordinate `2` or `3`, is
real-differentiable along that coordinate, with derivative the original complex derivative value
(coordinate `2`, slope `1`) or `Complex.I` times it (coordinate `3`, slope `Complex.I`) — the
Cauchy–Riemann relation in disguise, since `seedTau p = (p 2 : ℂ) + Complex.I * (p 3 : ℂ)`.
Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


namespace TernaryPeriodPolynomials.Argument

theorem seedTau_update2 (p : Fin 5 → ℝ) (s : ℝ) :
    seedTau (Function.update p 2 s) = (s : ℂ) + Complex.I * (p 3 : ℂ) := by
  simp [seedTau]

theorem seedTau_update3 (p : Fin 5 → ℝ) (s : ℝ) :
    seedTau (Function.update p 3 s) = (p 2 : ℂ) + Complex.I * (s : ℂ) := by
  simp [seedTau]

/-- Chain rule through `seedTau` along coordinate `2` (slope `1`). -/
theorem hasDerivAt_comp_seedTau_two (p : Fin 5 → ℝ) (F : ℂ → ℂ) (F' : ℂ)
    (hF : HasDerivAt F F' (seedTau p)) :
    HasDerivAt (fun s : ℝ => F (seedTau (Function.update p 2 s))) F' (p 2) := by
  have hinner : HasDerivAt (fun z : ℂ => z + Complex.I * (p 3 : ℂ)) 1 (p 2 : ℂ) :=
    (hasDerivAt_id (p 2 : ℂ)).add_const _
  have hg : HasDerivAt F F' ((p 2 : ℂ) + Complex.I * (p 3 : ℂ)) := hF
  have hcomp := hg.comp (p 2 : ℂ) hinner
  simp only [mul_one] at hcomp
  have hreal := hcomp.comp_ofReal
  simp only [seedTau_update2]
  exact hreal

/-- Chain rule through `seedTau` along coordinate `3` (slope `Complex.I`). -/
theorem hasDerivAt_comp_seedTau_three (p : Fin 5 → ℝ) (F : ℂ → ℂ) (F' : ℂ)
    (hF : HasDerivAt F F' (seedTau p)) :
    HasDerivAt (fun s : ℝ => F (seedTau (Function.update p 3 s))) (F' * Complex.I) (p 3) := by
  have hinner : HasDerivAt (fun z : ℂ => (p 2 : ℂ) + Complex.I * z) Complex.I (p 3 : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (p 3 : ℂ) := by
      simpa using (hasDerivAt_id (p 3 : ℂ)).const_mul Complex.I
    simpa using h1.const_add (p 2 : ℂ)
  have hg : HasDerivAt F F' ((p 2 : ℂ) + Complex.I * (p 3 : ℂ)) := hF
  have hcomp := hg.comp (p 3 : ℂ) hinner
  have hreal := hcomp.comp_ofReal
  simp only [seedTau_update3]
  exact hreal

end TernaryPeriodPolynomials.Argument
