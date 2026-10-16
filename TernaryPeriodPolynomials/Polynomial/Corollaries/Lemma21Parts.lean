module

public import TernaryPeriodPolynomials.Polynomial.Restriction
public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Proofs feeding `TernaryPeriodPolynomials.solution_homogeneous_symmetric_alternating_parts`: homogeneous components and the
symmetric/alternating decomposition of a solution are themselves solutions. -/


open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument

section HomogeneousComponent

variable {R : Type*} [CommRing R]

private theorem homogeneous_vec3' {a b c : MvPolynomial (Fin 3) R}
    (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    ∀ i : Fin 3, (![a, b, c] i).IsHomogeneous 1 := by
  intro i; fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Homogeneous components of a solution are solutions, over every commutative ring. -/
theorem Solution.homogeneousComponent {f : MvPolynomial (Fin 3) R} (hf : Solution f) (n : ℕ) :
    Solution (MvPolynomial.homogeneousComponent n f) := by
  have h0 := isHomogeneous_X R (0 : Fin 3)
  have h1 := isHomogeneous_X R (1 : Fin 3)
  have h2 := isHomogeneous_X R (2 : Fin 3)
  constructor
  · have h := congrArg (MvPolynomial.homogeneousComponent n) hf.cyclic
    rwa [TernaryPoly.homogeneousComponent_bind₁_linear _
      (homogeneous_vec3' h1 h2 h0)] at h
  · have h := congrArg (MvPolynomial.homogeneousComponent n) hf.norm
    simpa only [map_add, map_zero,
      TernaryPoly.homogeneousComponent_bind₁_linear _ (homogeneous_vec3' h1.neg (h0.sub h1) h2),
      TernaryPoly.homogeneousComponent_bind₁_linear _ (homogeneous_vec3' (h1.sub h0) h0.neg h2)]
      using h

end HomogeneousComponent

section SwapSolution

variable {R : Type*} [CommRing R]

/-- Collapse a composed pair of variable substitutions on `Fin 3`, given the pointwise identity
of the composite vector. -/
private theorem bind₁_comp_eq {g h k : Fin 3 → Ternary R}
    (e : (fun i => bind₁ g (h i)) = k) (p : Ternary R) :
    bind₁ g (bind₁ h p) = bind₁ k p := by
  rw [bind₁_bind₁]
  exact congrArg (fun v : Fin 3 → Ternary R => bind₁ v p) e

/-- Swapping the first two variables sends a solution to a solution, over every commutative
ring. -/
theorem Solution.swap01 {f : Ternary R} (hf : Solution f) :
    Solution (bind₁ ![X 1, X 0, X 2] f) := by
  have hcc : bind₁ (![X 2, X 0, X 1] : Fin 3 → Ternary R) f = f := by
    have expand := bind₁_comp_eq
      (g := (![X 1, X 2, X 0] : Fin 3 → Ternary R)) (h := (![X 1, X 2, X 0] : Fin 3 → Ternary R))
      (k := (![X 2, X 0, X 1] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    rw [← expand, hf.cyclic, hf.cyclic]
  have hB : bind₁ (![X 2, X 1, X 0] : Fin 3 → Ternary R) f =
      bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R) f := by
    have expand := bind₁_comp_eq
      (g := (![X 1, X 0, X 2] : Fin 3 → Ternary R)) (h := (![X 2, X 0, X 1] : Fin 3 → Ternary R))
      (k := (![X 2, X 1, X 0] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    rw [← expand, hcc]
  constructor
  · have expand := bind₁_comp_eq
      (g := (![X 1, X 2, X 0] : Fin 3 → Ternary R)) (h := (![X 1, X 0, X 2] : Fin 3 → Ternary R))
      (k := (![X 2, X 1, X 0] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    rw [expand, hB]
  · have g1 := bind₁_comp_eq
      (g := (![-X 1, X 0 - X 1, X 2] : Fin 3 → Ternary R))
      (h := (![X 1, X 0, X 2] : Fin 3 → Ternary R))
      (k := (![X 0 - X 1, -X 1, X 2] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    have g2 := bind₁_comp_eq
      (g := (![X 1 - X 0, -X 0, X 2] : Fin 3 → Ternary R))
      (h := (![X 1, X 0, X 2] : Fin 3 → Ternary R))
      (k := (![-X 0, X 1 - X 0, X 2] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    have h1 := bind₁_comp_eq
      (g := (![X 1, X 0, X 2] : Fin 3 → Ternary R))
      (h := (![-X 1, X 0 - X 1, X 2] : Fin 3 → Ternary R))
      (k := (![-X 0, X 1 - X 0, X 2] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    have h2 := bind₁_comp_eq
      (g := (![X 1, X 0, X 2] : Fin 3 → Ternary R))
      (h := (![X 1 - X 0, -X 0, X 2] : Fin 3 → Ternary R))
      (k := (![X 0 - X 1, -X 1, X 2] : Fin 3 → Ternary R))
      (by funext i; fin_cases i <;> simp [bind₁_X_right]) f
    have hnorm := congrArg (bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary R)) hf.norm
    simp only [map_add, map_zero, h1, h2] at hnorm
    rw [g1, g2]
    linear_combination hnorm

/-- The symmetric part `(f + Sf)/2` of a solution is a solution, over any field where `2 ≠ 0`. -/
theorem Solution.symmPart {F : Type*} [Field F] {f : Ternary F} (hf : Solution f) :
    Solution ((2 : F)⁻¹ • (f + bind₁ ![X 1, X 0, X 2] f)) :=
  (solutions F).smul_mem _ ((solutions F).add_mem hf (Solution.swap01 hf))

/-- The alternating part `(f - Sf)/2` of a solution is a solution, over any field where
`2 ≠ 0`. -/
theorem Solution.altPart {F : Type*} [Field F] {f : Ternary F} (hf : Solution f) :
    Solution ((2 : F)⁻¹ • (f - bind₁ ![X 1, X 0, X 2] f)) :=
  (solutions F).smul_mem _ ((solutions F).sub_mem hf (Solution.swap01 hf))

end SwapSolution

end TernaryPeriodPolynomials.Argument
