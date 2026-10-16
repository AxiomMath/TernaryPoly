module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Quotient

@[expose] public section


/-!
# The Hecke operators preserve the parabolic classes of `Γ₁'(3)`

Let `T_p = levelHecke m e p hp3` be the Hecke operator of `Γ₁'(3) diag(1, p) Γ₁'(3)` on
`H¹(Γ₁'(3), Sym^m ⊗ det^e)` in the crossed-homomorphism model, `p ≠ 3` prime.  The parabolic
classes (those whose crossed homomorphisms take coboundary values at `T = [[1,1],[0,1]]` and at
`L = [[1,0],[3,1]]`) are the common kernel of the two boundary functionals
`β_∞ [z] = z(T)(1, 0)` and `β_0 [z] = z(L)(0, 1)`, and `T_p` multiplies each functional by a scalar
(`β_∞ ∘ T_p = q_∞ β_∞`, `β_0 ∘ T_p = q_0 β_0`).  Hence `T_p` maps the parabolic classes into
themselves, and restricts to an endomorphism `parabolicHecke` of the parabolic subspace on which the
parabolic cup pairing is defined.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke)

/-- **The level-three Hecke operator maps parabolic classes to parabolic classes.**  A class is
parabolic iff both boundary functionals vanish on it, and each functional is an eigenfunctional of
`T_p`. -/
theorem levelHecke_mem_parabolicCrossedH1 (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    {x : CrossedH1 (levelRep m e)} (hx : x ∈ parabolicCrossedH1 (levelRep m e)) :
    levelHecke m e p hp3 x ∈ parabolicCrossedH1 (levelRep m e) := by
  rw [parabolicCrossedH1_eq (levelRep m e)] at hx
  rw [parabolicCrossedH1_eq (levelRep m e)]
  rw [TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryFunctional.mem_parabolicH1_iff
    m e x] at hx
  rw [TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryFunctional.mem_parabolicH1_iff
    m e (levelHecke m e p hp3 x)]
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryHecke.betaInf_levelHecke
      m e p hp3 x, h1, mul_zero]
  · rw [TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryZeroHecke.betaZero_levelHecke
      m e p hp3 x, h2, mul_zero]

/-- **The Hecke operator `T_p` on the parabolic classes** of `H¹(Γ₁'(3), Sym^m ⊗ det^e)`. -/
def parabolicHecke (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    Module.End ℂ (parabolicCrossedH1 (levelRep m e)) :=
  (levelHecke m e p hp3).restrict
    (fun _ hx => levelHecke_mem_parabolicCrossedH1 m e p hp3 hx)

/-- The parabolic Hecke operator is the restriction of the Hecke operator on all classes. -/
theorem parabolicHecke_coe (m : ℕ) (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : parabolicCrossedH1 (levelRep m e)) :
    ((parabolicHecke m e p hp3 x : parabolicCrossedH1 (levelRep m e)) : CrossedH1 (levelRep m e)) =
      levelHecke m e p hp3 (x : CrossedH1 (levelRep m e)) := rfl

/-- The parabolic Hecke operators commute with each other when the Hecke operators on all classes
do. -/
theorem parabolicHecke_comm (m : ℕ) (e : ℤ) (p q : Nat.Primes) (hp3 : p.val ≠ 3)
    (hq3 : q.val ≠ 3)
    (h : Commute (levelHecke m e p hp3) (levelHecke m e q hq3)) :
    Commute (parabolicHecke m e p hp3) (parabolicHecke m e q hq3) := by
  have key : parabolicHecke m e p hp3 * parabolicHecke m e q hq3 =
      parabolicHecke m e q hq3 * parabolicHecke m e p hp3 :=
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h.eq (x : CrossedH1 (levelRep m e)))
  exact key

end TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
