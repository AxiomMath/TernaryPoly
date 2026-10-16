module

public import TernaryPeriodPolynomials.Building.Integer.Exactness

@[expose] public section


/-! Top exactness for finitely supported square chains on the whole integer grid.
A boundary coefficient gives the row recurrence. The finite-strip filling is
also a left inverse to the square boundary, which proves injectivity directly. -/

noncomputable section
namespace TernaryPoly.IntegerGridTopInjective

open IntegerGridExactness

/-- At a vertical edge, a square contributes its left neighbor coefficient minus its own. -/
theorem squareBoundary_vertical_coefficient (p : Vertex) (x y : ℤ) :
    squareBoundary p ((x, y), 1) =
      Finsupp.single p (1 : ℚ) (x - 1, y) - Finsupp.single p (1 : ℚ) (x, y) := by
  classical
  rcases p with ⟨px, py⟩
  have hx : px + 1 = x ↔ px = x - 1 := by omega
  simp [squareBoundary, horizontal, vertical, Finsupp.single_apply, Prod.mk.injEq, hx]

/-- The actual vertical boundary coefficient is the difference of adjacent square coefficients. -/
theorem boundary₂_vertical_coefficient (z : C₂) (x y : ℤ) :
    boundary₂ z ((x, y), 1) = z (x - 1, y) - z (x, y) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, sub_self]
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply, ha, hb]
    abel
  | single p q =>
    rw [boundary₂_single, Finsupp.smul_apply, smul_eq_mul,
      squareBoundary_vertical_coefficient]
    simp only [Finsupp.single_apply, mul_sub, mul_ite, mul_one, mul_zero]

/-- A zero square boundary forces neighboring coefficients in each horizontal row to agree. -/
theorem coefficient_add_one_eq_of_boundary₂_eq_zero (z : C₂) (hz : boundary₂ z = 0)
    (x y : ℤ) : z (x + 1, y) = z (x, y) := by
  have h := boundary₂_vertical_coefficient z (x + 1) y
  rw [hz, Finsupp.zero_apply] at h
  have hs : z (x, y) - z (x + 1, y) = 0 := by simpa using h.symm
  exact (sub_eq_zero.mp hs).symm

/-- The existing finite-strip filling of a horizontal edge is its negative strip. -/
theorem filling_horizontal (p : Vertex) : filling (horizontal p) = -strip p := by
  simp [horizontal, filling_single, edgeFilling]

/-- The chosen filling of a vertical edge contains no squares. -/
theorem filling_vertical (p : Vertex) : filling (vertical p) = 0 := by
  simp [vertical, filling_single, edgeFilling]

/-- The two horizontal strips telescope to recover one literal unit square. -/
theorem filling_squareBoundary (p : Vertex) : filling (squareBoundary p) = square p := by
  rw [squareBoundary, map_sub, map_sub, map_add,
    filling_horizontal, filling_vertical, filling_horizontal, filling_vertical,
    add_zero, sub_zero]
  change -signedSum (fun j => square (p.1, j)) p.2 -
    -signedSum (fun j => square (p.1, j)) (p.2 + 1) = square p
  rw [signedSum_add_one]
  abel

/-- On every finite square chain, strip filling is a genuine left inverse to the boundary. -/
theorem filling_boundary₂ (z : C₂) : filling (boundary₂ z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single p q =>
    rw [boundary₂_single, map_smul, filling_squareBoundary,
      square, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The actual boundary on finitely supported chains of the infinite square grid is injective. -/
theorem boundary₂_injective : Function.Injective boundary₂ :=
  (show Function.LeftInverse filling boundary₂ from filling_boundary₂).injective

/-- A finite square chain with zero boundary is zero. -/
theorem eq_zero_of_boundary₂_eq_zero (z : C₂) (hz : boundary₂ z = 0) : z = 0 :=
  boundary₂_injective (hz.trans (map_zero boundary₂).symm)

/-- Top exactness: there are no nonzero finite two-cycles in the whole integer grid. -/
theorem ker_boundary₂_eq_bot : LinearMap.ker boundary₂ = ⊥ :=
  LinearMap.ker_eq_bot.mpr boundary₂_injective

end TernaryPoly.IntegerGridTopInjective
