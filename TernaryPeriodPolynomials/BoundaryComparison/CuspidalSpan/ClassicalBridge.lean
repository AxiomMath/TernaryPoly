module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ReynoldsAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


/-!
# Bridging `cuspAt` (integral-adelic) with `cuspFiniteRationalSlash` (rational-adelic)

Step (ii) of `CuspidalSupply.lean`'s hypothesis `h` needs to relate the eight
`cuspAt cusp (γ i)` translates used by `ReynoldsAverage.lean`'s `reynoldsAverage` to the
classical slash action, so that `AxiomCodeEvenLevelThree/WtModular.lean`'s
`levelThree_slash_eqWt` can be applied. This file supplies that bridge: `γ i` is literally
the image, under the integral-adelic embedding, of an explicit `SL₂(ℤ)` matrix `M i` with the
same entries, and `cuspAt cusp (γ i)` agrees with `cuspFiniteRationalSlash cusp (mapGL ℚ (M i))`
because both are `cuspSmoothAction cusp` applied to the *same* finite-adelic group element
(`integralEmbedding` and `algebraMap ℚ FiniteAdeles` agree on the image of `ℤ`).

The matrix-level identity (`bridge_eq`) is the `equality` sub-proof inside
`SphericalDetection/BinaryScalarModularity.lean`'s `cuspSpherical_specialLinear_fixed`,
re-derived standalone (that file does not export it as its own lemma).
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers (cuspFiniteRationalSlash)

/-- The eight `SL₂(ℤ)` matrices underlying `ReynoldsCosets.lean`'s `γ` (same entries as the
`ofIntDetOne a b c d` calls defining `γ`). -/
def M : Fin 8 → SpecialLinearGroup (Fin 2) ℤ
  | 0 => ⟨!![1, 0; 0, 1], by simp [Matrix.det_fin_two]⟩
  | 1 => ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩
  | 2 => ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  | 3 => ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  | 4 => ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  | 5 => ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  | 6 => ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two]⟩
  | 7 => ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

/-- **The matrix bridge.** Mapping an integer `SL₂` matrix to the finite adeles factors through
either `ℤ →ₐ IntegralAdeles →ₐ FiniteAdeles`-style route; `integralEmbedding` and
`algebraMap ℚ FiniteAdeles ∘ algebraMap ℤ ℚ` agree on integers, so the two routes to
`GL₂(FiniteAdeles)`/`GL₂(IntegralAdeles)` land on the same element after a further embedding.
Re-derivation of the `equality` step inside
`SphericalDetection.BinaryScalarModularity.cuspSpherical_specialLinear_fixed`. -/
theorem bridge_eq (κ : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ κ) =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles κ) := by
  apply Units.ext
  funext row column
  simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
    SpecialLinearGroup.map_apply_coe]
  change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (κ.val row column)) =
    integralEmbedding (algebraMap ℤ IntegralAdeles (κ.val row column))
  simp

/-- Entrywise formula for `mapGL`'s coe, for an *abstract* `g`.








-/
theorem mapGL_entries (g : SpecialLinearGroup (Fin 2) ℤ) (row column : Fin 2) :
    (SpecialLinearGroup.mapGL IntegralAdeles g : Matrix (Fin 2) (Fin 2) IntegralAdeles) row column
      = algebraMap ℤ IntegralAdeles (g.val row column) := by
  simp only [SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]

/-- **Generic form of `gamma_eq_mapGL`.** `ofIntDetOne` lands exactly on the image, under `mapGL`,
of *any* `SL₂(ℤ)` matrix `g` whose entries are the given `a b c d`. Taking `g` as a bound variable
(as in `mapGL_entries` above) sidesteps the issue entirely; callers discharge `hg` by `rfl`. -/
theorem ofIntDetOne_eq_mapGL (a b c d : ℤ) (h : a * d - b * c = 1)
    (g : SpecialLinearGroup (Fin 2) ℤ) (hg : g.val = !![a, b; c, d]) :
    ofIntDetOne a b c d h = SpecialLinearGroup.mapGL IntegralAdeles g := by
  apply Units.ext
  funext row column
  rw [mapGL_entries, hg]
  simp only [ofIntDetOne, GeneralLinearGroup.val_mk'']
  fin_cases row <;> fin_cases column <;> simp

/-- **`γ i` is the image of `M i`.** -/
theorem gamma_eq_mapGL (i : Fin 8) :
    γ i = SpecialLinearGroup.mapGL IntegralAdeles (M i) := by
  fin_cases i
  · exact ofIntDetOne_eq_mapGL 1 0 0 1 (by norm_num) (M 0) rfl
  · exact ofIntDetOne_eq_mapGL (-1) 0 0 (-1) (by norm_num) (M 1) rfl
  · exact ofIntDetOne_eq_mapGL 0 (-1) 1 0 (by norm_num) (M 2) rfl
  · exact ofIntDetOne_eq_mapGL 0 1 (-1) 0 (by norm_num) (M 3) rfl
  · exact ofIntDetOne_eq_mapGL 1 0 1 1 (by norm_num) (M 4) rfl
  · exact ofIntDetOne_eq_mapGL 0 (-1) 1 (-1) (by norm_num) (M 5) rfl
  · exact ofIntDetOne_eq_mapGL 1 0 (-1) 1 (by norm_num) (M 6) rfl
  · exact ofIntDetOne_eq_mapGL 0 1 (-1) (-1) (by norm_num) (M 7) rfl

/-- **The bridge, in `cuspAt`/`cuspFiniteRationalSlash` form.** -/
theorem cuspAt_eq_rationalSlash (cusp : CuspidalRepresentation) (v : cusp.smooth) (i : Fin 8) :
    cuspAt cusp (γ i) v = cuspFiniteRationalSlash cusp (SpecialLinearGroup.mapGL ℚ (M i)) v := by
  apply Subtype.ext
  show cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (γ i)⁻¹)) v.val =
    cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (SpecialLinearGroup.mapGL ℚ (M i))⁻¹)) v.val
  rw [gamma_eq_mapGL i, GeneralLinearGroup.map_inv, ← bridge_eq, ← GeneralLinearGroup.map_inv]

end TernaryPeriodPolynomials.Argument.CuspidalSpan
