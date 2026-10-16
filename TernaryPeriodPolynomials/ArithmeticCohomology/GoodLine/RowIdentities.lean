module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Matrices

@[expose] public section


/-!
# The stabilizer of the good line `ℚ e₃` in `K†`

Formalized by Claude Sonnet 5.5.  Paper: "the stabilizer of the good line in `K†` is
`{[[D,0],[3u,1]] : D ∈ GL₂(ℤ), u ∈ ℤ^{1×2}}`".

`goodLine_stabilizer_explicit`: for `g ∈ GL₃(ℤ)`, `g ∈ K†` and `g` stabilizes `ℚ e₃` iff `g = [[D, 0], [3(a,b), 1]]` with `D ∈ GL₂(ℤ)` (an integral matrix with unit determinant), `a, b ∈ ℤ`.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerMatrices

/-- **The good-line stabilizer in `K†`**. -/
theorem goodLine_stabilizer_explicit (g : IntegralGL) :
    (g ∈ K3 ∧ Stabilizes g (coordinateSubspace {2})) ↔
      ∃ (D : Mat2) (a b : ℤ), IsUnit D.det ∧
        g.val = !![D 0 0, D 0 1, 0; D 1 0, D 1 1, 0; 3 * a, 3 * b, 1] := by
  rw [stabilizes_coordinate_iff, mem_K3_iff]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, hs⟩
    have e02 : g.val 0 2 = 0 := hs 0 (by decide) 2 (by decide)
    have e12 : g.val 1 2 = 0 := hs 1 (by decide) 2 (by decide)
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h1
    have hd : IsUnit (g.val.det) := det_isUnit g
    have he : g.val.det = (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * g.val 2 2 := by
      rw [Matrix.det_fin_three, e02, e12]
      ring
    rw [he] at hd
    have hs22 : IsSign (g.val 2 2) := Int.isUnit_iff.mp (unit_of_mul_right hd)
    have h22 : g.val 2 2 = 1 := sign_eq_one_of_residue hs22 h2
    refine ⟨!![g.val 0 0, g.val 0 1; g.val 1 0, g.val 1 1], a, b, ?_, ?_⟩
    · have := unit_of_mul_left hd
      simpa [Matrix.det_fin_two] using this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [e02, e12, h22, ha, hb]
  · rintro ⟨D, a, b, hD, hg⟩
    have e : ∀ i j, g.val i j = (!![D 0 0, D 0 1, 0; D 1 0, D 1 1, 0; 3 * a, 3 * b, 1] : Mat) i j :=
      fun i j => by rw [hg]
    have h3 : (3 : ZMod 3) = 0 := by decide
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [e 2 0]; simp [h3]
    · rw [e 2 1]; simp [h3]
    · rw [e 2 2]; simp
    · intro i hi j hj
      have hj2 : j = 2 := by simpa using hj
      have hi2 : i ≠ 2 := by simpa using hi
      subst hj2
      rw [e]
      fin_cases i <;> simp_all

end TernaryPeriodPolynomials.Argument.Identities
