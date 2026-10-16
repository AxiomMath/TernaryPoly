module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatAffine
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatChambers

@[expose] public section


/-!
# The compactified diagonal flat as a singular 2-chain

`flatChain` is the alternating sum of the six chamber squares, each cut along the diagonal from its
Borel corner into two affine triangles. `d_flatChain`: its boundary is the hexagon of twelve arcs
`hexBoundary`, since the interior diagonals and the walls between adjacent chambers cancel.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory AlgebraicTopology
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SymmetricSpaceRationalGluing

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

/-! ### The flat as a singular 2-chain -/

/-- The corner `(0,0)` of a chamber square. -/
def pv : ℝ × ℝ := (0, 0)
/-- The midpoint of the plane-side arc of a chamber square, where `t₁ = 1`, `t₂ = 0`. -/
def pa : ℝ × ℝ := (1, 0)
/-- The centre `(1,1)` of the flat, common to the six chambers. -/
def pO : ℝ × ℝ := (1, 1)
/-- The midpoint of the line-side arc of a chamber square, where `t₁ = 0`, `t₂ = 1`. -/
def pb : ℝ × ℝ := (0, 1)

theorem seg_wall_one {X : TopCat.{0}} (f g : C(ℝ × ℝ, X)) (h : ∀ u : ℝ, f (1, u) = g (1, u)) :
    seg f pa pO = seg g pa pO := by
  unfold seg affSimplex
  congr 1
  apply ContinuousMap.ext
  intro z
  have hz := z.total_fin_two
  have e : affineMap 1 ![pa, pO] z = (1, z.weights 1) := by
    simp only [affineMap, ContinuousMap.coe_mk, pa, pO]
    ext <;> simp
  change f (affineMap 1 ![pa, pO] z) = g (affineMap 1 ![pa, pO] z)
  rw [e]
  exact h _

theorem seg_wall_two {X : TopCat.{0}} (f g : C(ℝ × ℝ, X)) (h : ∀ u : ℝ, f (u, 1) = g (u, 1)) :
    seg f pO pb = seg g pO pb := by
  unfold seg affSimplex
  congr 1
  apply ContinuousMap.ext
  intro z
  have hz := z.total_fin_two
  have e : affineMap 1 ![pO, pb] z = (z.weights 0, 1) := by
    simp only [affineMap, ContinuousMap.coe_mk, pO, pb]
    ext <;> simp
  change f (affineMap 1 ![pO, pb] z) = g (affineMap 1 ![pO, pb] z)
  rw [e]
  exact h _

/-- The chamber square, as two affine triangles with common diagonal `pv → pO`. -/
def sqChain {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) : (underlyingChains X).X 2 :=
  sing X (tri f pv pa pO) + sing X (tri f pv pO pb)

theorem d_sqChain {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) :
    ((underlyingChains X).d 2 1).hom (sqChain f) =
      sing X (seg f pv pa) + sing X (seg f pa pO) + sing X (seg f pO pb) - sing X (seg f pv pb) := by
  unfold sqChain
  rw [map_add, d_tri, d_tri]
  abel

/-- The `k`-th chamber map. -/
abbrev fk (k : ℕ) : C(ℝ × ℝ, TopCat.of Glued) := chamber (hexW k)

/-- The compactified diagonal flat: six chamber squares with alternating orientation. -/
def flatChain : (underlyingChains (TopCat.of Glued)).X 2 :=
  sqChain (fk 0) - sqChain (fk 1) + sqChain (fk 2) - sqChain (fk 3) + sqChain (fk 4) -
    sqChain (fk 5)

/-- The twelve arcs of the boundary hexagon of the flat. -/
def hexBoundary : (underlyingChains (TopCat.of Glued)).X 1 :=
  (sing _ (seg (fk 0) pv pa) - sing _ (seg (fk 0) pv pb)) -
    (sing _ (seg (fk 1) pv pa) - sing _ (seg (fk 1) pv pb)) +
    (sing _ (seg (fk 2) pv pa) - sing _ (seg (fk 2) pv pb)) -
    (sing _ (seg (fk 3) pv pa) - sing _ (seg (fk 3) pv pb)) +
    (sing _ (seg (fk 4) pv pa) - sing _ (seg (fk 4) pv pb)) -
    (sing _ (seg (fk 5) pv pa) - sing _ (seg (fk 5) pv pb))

theorem fk_wall_a (k : ℕ) (hk : Even k) : seg (fk (k + 1)) pa pO = seg (fk k) pa pO :=
  seg_wall_one _ _ (fun u => by
    rw [fk, fk, hexW_succ_even k hk]
    exact chamber_wall_one _ u)

theorem fk_wall_b (k : ℕ) (hk : ¬ Even k) : seg (fk (k + 1)) pO pb = seg (fk k) pO pb :=
  seg_wall_two _ _ (fun u => by
    rw [fk, fk, hexW_succ_odd k hk]
    exact chamber_wall_two _ u)

theorem fk_six : fk 6 = fk 0 := by
  rw [fk, fk, hexW_six]

/-- **The boundary of the compactified flat is the hexagon of twelve arcs**: the interior walls and
diagonals cancel. -/
theorem d_flatChain :
    ((underlyingChains (TopCat.of Glued)).d 2 1).hom flatChain = hexBoundary := by
  have e0 := fk_wall_a 0 (by decide)
  have e2 := fk_wall_a 2 (by decide)
  have e4 := fk_wall_a 4 (by decide)
  have e1 := fk_wall_b 1 (by decide)
  have e3 := fk_wall_b 3 (by decide)
  have e5 := fk_wall_b 5 (by decide)
  rw [fk_six] at e5
  simp only [flatChain, hexBoundary, map_add, map_sub, d_sqChain]
  rw [e0, e2, e4, e1, e3, e5]
  abel



end TernaryPeriodPolynomials.Argument.Lemma33
