module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.InnerBadLineSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.InnerEdgeAuxMain

@[expose] public section


/-!
# The classical input `InnerEdgeRealized` of the direct route

The bad-line Shapiro coordinate of every inner bad-line class has zero radical restriction and its
edge class is `(n + 1)` times the period class of a cusp form of weight `n + 3` for `Γ₁(3)`.  The
proof (`InnerEdgeAuxMain`) identifies `badLineEdge` of the local class with Sol's parabolic class of
the inner class, shows that Sol's parabolic condition implies the (`InnerEdgeAux`), and applies Eichler–Shimura surjectivity onto the parabolic classes.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Period.InnerEdge

/-- **The classical side of the direct route.**  The bad-line coordinate of every inner bad-line
class lies in the radical kernel and its edge class is `(n + 1)` times the period class of a cusp
form of weight `n + 3`. -/
theorem innerEdgeRealized (n : ℕ) (hn : 0 < n) : DirectRoute.InnerEdgeRealized n hn :=
  InnerEdgeAux.innerEdgeRealized_aux n hn

end TernaryPeriodPolynomials.Automorphic.Period.InnerEdge
