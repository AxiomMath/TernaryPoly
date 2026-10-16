module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.HeckeHom
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.CompositeOdd
public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Basic
public import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section


/-!
# The analytic period Hecke dictionary

Paper: Appendix A.3, the paragraph
after `eq:Hecke-formula`'s proof: "It remains to check that this binary
correspondence has the standard analytic Hecke normalization on period polynomials.  Put `d = n+1`,
and let `h` be a cusp form of weight `d+2`.  For a matrix `g = (a b; c e)` of positive determinant
`m`, the fractional-linear action gives `((gzY-X) | g) = m(zY-X)/(cz+e)`, `d(gz) = m dz/(cz+e)^2`.
Hence the differential `h(z)(zY-X)^d dz` transforms with the usual weight `d+2` Hecke factor.  The
homological correspondence above is the standard Hecke operator on the period polynomial of `h`."

This file proves the clauses of that paragraph for the library's literal objects:

* `mobius_linear`, `mobius_hasDerivAt`: the two displayed identities, with `(X', Y') = g (X, Y)`
  (`substX`, `substY`) the linear substitution of the polynomial coefficients; for `g` of positive
  determinant `m` and `cz + e ≠ 0`,
  `(gz) Y' - X' = m (zY - X)/(cz + e)` and `d/dw (gw) = m/(cz+e)^2`.
* `slash_differential`: hence, for every `f : ℍ → ℂ`, the pull-back of the differential
  `f(gz) (gz Y' - X')^d d(gz)` is `(f ∣[d+2] g)(z) (zY - X)^d dz`, with `∣[d+2]` Mathlib's weight
  `d + 2` slash action (the usual weight `d+2` Hecke factor `m^{d+1} (cz+e)^{-(d+2)}`).
* `periodIntegrand_hecke_sum`: the differential of the standard prime Hecke operator `T_p h` of weight
  `d + 2` is the sum, over the `p + 1` upper representatives `g_i` of `diag(1,p)`, of the transformed
  differentials of `h`.
* `binary_hecke_twist`: for the binary Hom model, the prime correspondence with determinant exponent
  `e + 2` is `p^2` times the one with exponent `e` (every representative has determinant `p`).
* `hecke_dictionary_cusp`: the paper's normalization (determinant exponent `+1 = -1 + 2` on both
  the ternary and the binary side), on every modular symbol `c` of the binary Steinberg module: if the
  complexified binary residue coordinate of `F` is the odd cusp symbol of a cusp form `f` of weight
  `d + 2` (`d = n + 1`), then
  `p^d · res(T₃(p,1)|_res F)(c) = p² · φ_{T_p f}(c) + p^{d+2} · φ_f(c)`, i.e.
  `T₃(p,1)|_res = p · (p^{1-d} T_p) + p² I`: the binary correspondence `T₂(p)` of
  `eq:Hecke-formula` acts on the period symbols of `f` as `p^{1-d}` times the analytic prime Hecke
  operator `T_p` (the literal analytic normalization; `φ_f = oddHom f` is the library's analytic modular
  symbol, whose endpoints are the limits of the Eichler integral of the differential
  `f(z)(zY-X)^d dz`).

The remaining ingredients are in the library: `TernaryPoly.BinaryCuspSymbol.full_hecke` (the analytic
symbol of `T_p f` is `p^{d+1}` times the sum of the adjugate-representative transfers of the symbol of
`f`), `oddHom_hecke`, `BinaryCuspPeriod.periodMap_hecke`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane Matrix
open scoped MatrixGroups ModularForm

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel.AnalyticHecke

open TernaryPoly TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspHeckeEndomorphism

/-- The first coordinate `X' = aX + bY` of the linear substitution `(X', Y')ᵀ = g (X, Y)ᵀ`. -/
def substX (g : GL (Fin 2) ℝ) (X Y : ℂ) : ℂ := g 0 0 * X + g 0 1 * Y

/-- The second coordinate `Y' = cX + eY` of the linear substitution `(X', Y')ᵀ = g (X, Y)ᵀ`. -/
def substY (g : GL (Fin 2) ℝ) (X Y : ℂ) : ℂ := g 1 0 * X + g 1 1 * Y

theorem det_cast (g : GL (Fin 2) ℝ) :
    (g.det.val : ℂ) = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  push_cast; ring

/-- **`((gzY - X) | g) = m (zY - X)/(cz + e)`**: with `(X', Y') = g (X, Y)`,
`(gz) Y' - X' = m (zY - X)/(cz + e)`. -/
theorem mobius_linear (g : GL (Fin 2) ℝ) {w : ℂ} (hw : denom g w ≠ 0) (X Y : ℂ) :
    (num g w / denom g w) * substY g X Y - substX g X Y =
      (g.det.val : ℂ) * (w * Y - X) / denom g w := by
  rw [det_cast, eq_div_iff hw, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
    mul_div_cancel_right₀ _ hw]
  unfold num denom substX substY
  ring

/-- **`d(gz) = m dz/(cz + e)²`**: the derivative of `w ↦ (aw + b)/(cw + e)`. -/
theorem mobius_hasDerivAt (g : GL (Fin 2) ℝ) {w : ℂ} (hw : denom g w ≠ 0) :
    HasDerivAt (fun u : ℂ => num g u / denom g u) ((g.det.val : ℂ) / (denom g w) ^ 2) w := by
  have h1 : HasDerivAt (fun u : ℂ => num g u) (g 0 0 : ℂ) w := by
    unfold num
    simpa using ((hasDerivAt_id w).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)
  have h2 : HasDerivAt (fun u : ℂ => denom g u) (g 1 0 : ℂ) w := by
    unfold denom
    simpa using ((hasDerivAt_id w).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)
  refine (h1.fun_div h2 hw).congr_deriv ?_
  rw [det_cast]; unfold num denom; ring

/-- **The differential `h(z)(zY - X)^d dz` transforms with the usual weight `d + 2` Hecke factor**: for `g` of positive determinant `m`, the transported differential
`f(gz) (gz Y' - X')^d · m/(cz+e)²` is `(f ∣[d+2] g)(z) (zY - X)^d`, where `f ∣[d+2] g` is
Mathlib's weight `d + 2` slash action, `m^{d+1} (cz+e)^{-(d+2)} f(gz)`. -/
theorem slash_differential (d : ℕ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (z : ℍ)
    (X Y : ℂ) :
    (f ∣[(d : ℤ) + 2] g) z * ((z : ℂ) * Y - X) ^ d =
      f (g • z) * (((g • z : ℍ) : ℂ) * substY g X Y - substX g X Y) ^ d *
        ((g.det.val : ℂ) / (denom g z) ^ 2) := by
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  rw [ModularForm.slash_apply, UpperHalfPlane.coe_smul_of_det_pos hg z, mobius_linear g hD,
    abs_of_pos hg]
  have hs : ∀ w : ℂ, σ g w = w := by
    intro w; rw [σ, ite_eq_left hg]; rfl
  rw [hs]
  have h2 : ((g.det.val : ℝ) : ℂ) ^ ((d : ℤ) + 2 - 1) = (g.det.val : ℂ) ^ (d + 1) := by
    have : ((d : ℤ) + 2 - 1) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]
  have h3 : (denom g z) ^ (-((d : ℤ) + 2)) = ((denom g z) ^ (d + 2))⁻¹ := by
    rw [_root_.zpow_neg]; congr 1
  rw [h2, h3, div_pow, mul_pow]
  field_simp
  ring

/-- **The standard prime Hecke operator acts on the period differential through the `p + 1`
upper representatives.**  For a level-one cusp form `f` of weight `d + 2` and the standard
operator `T_p` (`BinaryCuspHeckeEndomorphism.T`, `p^{d+1} f(pz) + p^{-1} ∑_b f((z+b)/p)`), the
differential `(T_p f)(z) (zy - x)^d` is the sum over the representatives `g_i` (`diag(p,1)` and
`(1 b; 0 p)`) of the transported differentials `f(g_i z) (g_i z Y_i - X_i)^d d(g_i z)`,
`(X_i, Y_i) = g_i (x, y)`. -/
theorem periodIntegrand_hecke_sum (d p : ℕ) [Fact p.Prime] (f : Forms d) (x y : ℂ) (z : ℍ) :
    periodIntegrand (T d p f) x y (z : ℂ) =
      ∑ i : BinaryRationalHeckePrime.PrimeIndex p,
        f (realify (upper p i) • z) *
          (((realify (upper p i) • z : ℍ) : ℂ) * substY (realify (upper p i)) x y -
            substX (realify (upper p i)) x y) ^ d *
          (((realify (upper p i)).det.val : ℂ) / (denom (realify (upper p i)) z) ^ 2) := by
  rw [periodIntegrand, UpperHalfPlane.ofComplex_apply, T_apply, ← slashSum_eq_primeOperator,
    slashSum, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ =>
    slash_differential d f (realify (upper p i)) (real_upper_det_pos p i) z x y


open BinaryModularSymbol BinaryModularSymbolCoefficients in
/-- **The binary prime correspondence with determinant exponent `e + 2` is `p²` times the one with
exponent `e`** (every upper/lower representative of `diag(p,1)` has determinant `p`; the integral Hom
spaces for `e` and `e + 2` coincide, `mem_lift_binary`). -/
theorem binary_hecke_twist (d p : ℕ) [Fact p.Prime] (e : ℤ)
    (G : BinaryModularSymbol.Hom (homogeneousAction d e)) :
    (BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
        (homogeneousAction d (e + 2)) ⟨G.val, mem_lift_binary d e G⟩).val =
      (p : ℚ) ^ 2 • (BinaryRationalHecke.rationalHecke
        (BinaryRationalHeckePrime.primeDiagonal p) (homogeneousAction d e) G).val := by
  rw [BinaryRationalHeckePrime.rationalHecke_prime, BinaryRationalHeckePrime.rationalHecke_prime,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro c
  simp only [LinearMap.smul_apply, BinaryModularSymbol.homAction_apply]
  rw [AppendixBResidue.homogeneousAction_twist, det_primeRepresentative]
  simp

open TernaryPoly.BinaryCuspSymbol TernaryPoly.OrdinaryResidueParabolic in
/-- **The analytic period Hecke dictionary, in the paper's normalization.**
Let `f` be a level-one cusp form of weight `d + 2`, `d = n + 1`, with analytic modular symbol
`φ_f = oddHom f` (endpoints: limits of the Eichler integral of the differential
`f(z)(zY - X)^d dz`), and let `F` be a literal residue class whose complexified binary residue
coordinate `κ(Sh F) = toBinaryHom n F` is `φ_f`.  Then for every modular symbol `c` of the binary
Steinberg module, with the determinant exponent `+1 = -1 + 2` on both the ternary operator `T₃(p,1)`
(`diag(p,1,1)`) and the binary operator,
`p^d · res_H(T₃(p,1) F)(c) = p² · φ_{T_p f}(c) + p^{d+2} · φ_f(c)`,
i.e. `T₃(p,1)|_res = p · (p^{1-d} T_p) + p² I`.  The binary correspondence `T₂(p)` of
`eq:Hecke-formula` is `p^{1-d}` times the analytic weight-`d+2` Hecke operator `T_p` on period
symbols: the standard analytic Hecke operator up to this explicit scalar.  The scalar depends on the
determinant exponent `e` of the binary coefficient system: `T₂^{(e)}(p) = p^{e-d} T_p` on these
symbols (`binary_hecke_twist` and `oddHom_hecke`), so the two operators agree literally only for
`e = d`; the factor is irrelevant for eigenspaces and Hecke stability. -/
theorem hecke_dictionary_cusp (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (f : Forms (n + 1))
    (hF : rationalFunctionHom (n + 1) (OrdinaryResidueSymbol.toBinaryHom n F) = oddHom f)
    (c : BinaryModularSymbol.St) :
    (p : ℚ) ^ (n + 1) • rationalEvaluate
        (zeroCoordinate n
          ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
            (SinglePole.residueAction n (-1 + 2))
            (⟨F.val, mem_lift_ternary n (-1) F⟩ :
              OrdinaryFullCoefficient.ResidueHom n (-1 + 2))).val
            (OrdinaryPlaneEdge.binaryCone c))).val =
      (p : ℚ) ^ 2 • (oddHom (T (n + 1) p f)).val c + (p : ℚ) ^ (n + 3) • (oddHom f).val c := by
  rw [hecke_transfer_lifted n p F c]
  have h1 := congrArg (fun H : BinaryModularSymbol.St →ₗ[ℚ]
      BinaryModularSymbolCoefficients.HomogeneousPoly (n + 1) => H c)
    (binary_hecke_twist (n + 1) p (-1) (OrdinaryResidueSymbol.toBinaryHom n F))
  simp only [LinearMap.smul_apply] at h1
  rw [h1]
  simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]
  have h2 := congrArg (fun H : FunctionHom => H.val c)
    (rationalFunctionHom_hecke (n + 1) p (OrdinaryResidueSymbol.toBinaryHom n F))
  simp only [rationalFunctionHom_apply] at h2
  have h3 := congrArg (fun H : FunctionHom => H.val c) (oddHom_hecke f p)
  simp only [Submodule.coe_smul, LinearMap.smul_apply] at h3
  rw [hF] at h2
  have h4 : rationalEvaluate ((OrdinaryResidueSymbol.toBinaryHom n F).val c).val =
      (oddHom f).val c := by
    simpa only [rationalFunctionHom_apply] using congrArg (fun H : FunctionHom => H.val c) hF
  rw [← h2, h4, h3]
  module


open TernaryPoly.BinaryCuspSymbol TernaryPoly.OrdinaryResidueParabolic in
/-- **`hecke_dictionary_cusp` from the period hypothesis.**  The same statement when the hypothesis
is that the complexified residue coordinate `res_H F` of the standard edge is the period
`periodMap f` of the cusp form `f` (the form in which `composite_is_odd_period` is stated). -/
theorem hecke_dictionary_cusp_of_period (n p : ℕ) [Fact p.Prime] (hd : Even (n + 1))
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (f : Forms (n + 1))
    (h : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F) = periodMap (n + 1) hd f)
    (c : BinaryModularSymbol.St) :
    (p : ℚ) ^ (n + 1) • rationalEvaluate
        (zeroCoordinate n
          ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
            (SinglePole.residueAction n (-1 + 2))
            (⟨F.val, mem_lift_ternary n (-1) F⟩ :
              OrdinaryFullCoefficient.ResidueHom n (-1 + 2))).val
            (OrdinaryPlaneEdge.binaryCone c))).val =
      (p : ℚ) ^ 2 • (oddHom (T (n + 1) p f)).val c + (p : ℚ) ^ (n + 3) • (oddHom f).val c :=
  hecke_dictionary_cusp n p F f
    (AppendixBResidue.composite_is_odd_period n hd F f h).1 c

end TernaryPeriodPolynomials.Argument.FiberModel.AnalyticHecke
