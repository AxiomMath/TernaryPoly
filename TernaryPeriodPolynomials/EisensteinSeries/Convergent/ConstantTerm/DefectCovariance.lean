module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectCovariance

@[expose] public section


/-!
# Covariance of the defect (convergent)

Real covariance, rational left and finite right invariance of the defect, and the shift, Levi and periodicity properties of its translation family.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.DefectCovariance` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
/-- The real image of a rational matrix, written out in full. -/
local notation:max "ratReal[" g "]" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g

variable {n : ℕ}
section Defect
variable (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
  (c : SourceSpace.sourceCocycles D .plane)
theorem defectFamily_eq_value (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r y =
      defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
        (translationArgument side q K r) := rfl

theorem sideSource_isSourceCocycle (side : Side) :
    IsSourceCocycle D side (sideSource large D hol c side).val :=
  (sideSource large D hol c side).property

/-- Real covariance of the defect `Φ`: the Eisenstein part by
`EndpointEisensteinCocycle.sourceValue_real_covariant`, the source part by `IsSourceCocycle`. -/
theorem defectValue_real_covariant (side : Side) (h : RealGL3) (x : Fin 3 → RealGL3)
    (a : AdelicGL) :
    defectValue large D hol c side (fun i => h * x i) a =
      realCoefficientComponent n D.chi h (defectValue large D hol c side x (a * atInfinity h)) := by
  have hs := sideSource_isSourceCocycle large D hol c side
  simp only [defectValue, eisensteinValue]
  rw [EndpointEisensteinCocycle.sourceValue_real_covariant D hol large c h x a,
    hs.2.2.1 h x a, map_sub]

/-- Left invariance of `Φ` under the rational points of the parabolic of the side. -/
theorem defectValue_rational_left (side : Side) (p : RationalGL3) (hp : p ∈ parabolic side)
    (x : Fin 3 → RealGL3) (a : AdelicGL) :
    defectValue large D hol c side x (rationalGroup p * a) =
      defectValue large D hol c side x a := by
  have hs := sideSource_isSourceCocycle large D hol c side
  simp only [defectValue, eisensteinValue, GlobalEisensteinCocycle.sourceValueAtReal]
  rw [PolynomialEisenstein.polynomialValue_rational,
    RationalComparison.source_parabolicInvariant D RationalNorm.rational_norm side _ hs p hp x a]

/-- Right invariance of `Φ` under the finite level. -/
theorem defectValue_finite_right (side : Side) (k : finiteLevel) (x : Fin 3 → RealGL3)
    (a : AdelicGL) :
    defectValue large D hol c side x (a * atFinite k.val) =
      defectValue large D hol c side x a := by
  have hs := sideSource_isSourceCocycle large D hol c side
  simp only [defectValue, eisensteinValue, GlobalEisensteinCocycle.sourceValueAtReal]
  rw [PolynomialEisenstein.polynomialValue_finite D hol _ k a,
    Comparison.source_finiteInvariant D side _ hs k x a]

/-- Absorption: a left factor in the rational parabolic and a right factor in the rational
level (through `rationalFinite`) do not change `Φ`. -/
theorem defectValue_absorb (side : Side) (p : RationalGL3) (hp : p ∈ parabolic side)
    (k : RationalGL3) (hk : k ∈ rationalLevel) (x : Fin 3 → RealGL3) (B : AdelicGL) :
    defectValue large D hol c side x (rationalGroup p * B * atFinite (rationalFinite k)) =
      defectValue large D hol c side x B := by
  have hfin : rationalFinite k ∈ finiteLevel := Comparison.rationalLevel_finiteLevel ⟨k, hk⟩
  have h1 := defectValue_finite_right large D hol c side ⟨rationalFinite k, hfin⟩ x
    (rationalGroup p * B)
  have h2 := defectValue_rational_left large D hol c side p hp x B
  exact h1.trans h2

/-- Moving a rational element `g` through the vertices of the defect family produces `ρ g`
and the right translation of the adelic argument by the real image of `g`. -/
theorem defectFamily_mul_vertices (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (g : RationalGL3) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r (fun i => g * y i) =
      rationalCoefficientComponent n D.chi g
        (defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
          (translationArgument side q K r * atInfinity (ratReal[g]))) := by
  have h := defectValue_real_covariant large D hol c side (ratReal[g])
    (GlobalEisensteinCocycle.realVertices y) (translationArgument side q K r)
  rw [defectFamily_eq_value, realVertices_leftMul]
  exact h

/-- **Shift.**  For `h = q u(K w) q⁻¹`, `Θ_r(h y) = ρ h (Θ_{r+w}(y))`.  Computation: real
covariance gives `ρ h (Φ y (A_r * atInfinity h))`, and `A_r * atInfinity h = A_{r+w}`
(`translationArgument_shift`). -/
theorem defectFamily_shift (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r
        (fun i => (q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹) * y i) =
      rationalCoefficientComponent n D.chi
        (q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹)
        (defectFamily large D hol c side q K (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y) := by
  rw [defectFamily_mul_vertices, translationArgument_shift, defectFamily_eq_value]

/-- **Levi covariance.**  Let `γ ∈ rationalLevel` with `p := q⁻¹ γ q` in the rational
parabolic of the side, and suppose `(ι p)⁻¹ u(K r) (ι p) = u(K r')` in `GL₃(ℝ)`, `ι` the real
image.  Then `Θ_r(γ y) = ρ γ (Θ_{r'}(y))`.  The adelic identity used is
`A_r * atInfinity (ι γ) = rationalGroup p * A_{r'} * atFinite (rationalFinite γ⁻¹)`
(`translationArgument_levi` with `q p q⁻¹ = γ`): the left factor is removed by left
invariance, the right one lies in the finite level since `γ⁻¹ ∈ rationalLevel`. -/
theorem defectFamily_levi (side : Side) (q : RationalGL3) (K : ℕ) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel) (hp : q⁻¹ * γ * q ∈ parabolic side) (r r' : ℝ × ℝ)
    (hr : (ratReal[q⁻¹ * γ * q])⁻¹ * sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) *
        ratReal[q⁻¹ * γ * q] = sideUnipotent side ((K : ℝ) * r'.1) ((K : ℝ) * r'.2))
    (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r (fun i => γ * y i) =
      rationalCoefficientComponent n D.chi γ (defectFamily large D hol c side q K r' y) := by
  have hcore := translationArgument_levi side q (q⁻¹ * γ * q) K r r' hr
  rw [show q * (q⁻¹ * γ * q) * q⁻¹ = γ by group] at hcore
  rw [defectFamily_mul_vertices, hcore,
    defectValue_absorb large D hol c side (q⁻¹ * γ * q) hp γ⁻¹ (rationalLevel.inv_mem hγ),
    defectFamily_eq_value]

/-- **Periodicity.**  If `ν := q u(K w) q⁻¹` lies in `rationalLevel`, then
`Θ_{r+w} = Θ_r`.  Computation: `A_{r+w} = A_r * atInfinity (ι ν)` (shift) and
`A_r * atInfinity (ι ν) = rationalGroup u * A_r * atFinite (rationalFinite ν⁻¹)` (Levi with
`p = u(K w)`, `r' = r`, since the radical is abelian), with `u(K w)` in the parabolic. -/
theorem defectFamily_periodic (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ)
    (hw : q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹ ∈ rationalLevel)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y =
      defectFamily large D hol c side q K r y := by
  have hcomm : (ratReal[sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)])⁻¹ *
      sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) *
        ratReal[sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)] =
      sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) := by
    rw [map_sideUnipotent_scaled, mul_assoc,
      sideUnipotent_comm side ((K : ℝ) * r.1) ((K : ℝ) * r.2) ((K : ℝ) * (w.1 : ℝ))
        ((K : ℝ) * (w.2 : ℝ)),
      inv_mul_cancel_left]
  have hshift := translationArgument_shift side q K w r
  have hlevi := translationArgument_levi side q
    (sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)) K r r hcomm
  rw [defectFamily_eq_value, defectFamily_eq_value, ← hshift, hlevi]
  exact defectValue_absorb large D hol c side _ (sideUnipotent_mem_parabolic side _ _) _
    (rationalLevel.inv_mem hw) _ _

/-- Periodicity along the integral lattice (`ℓ ∈ ℤ²`, scaled by `K`). -/
theorem defectFamily_periodic_int (side : Side) (q : RationalGL3) (K : ℕ) (ℓ : ℤ × ℤ)
    (hℓ : q * sideUnipotent side ((K : ℚ) * (ℓ.1 : ℚ)) ((K : ℚ) * (ℓ.2 : ℚ)) * q⁻¹ ∈
      rationalLevel)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y =
      defectFamily large D hol c side q K r y := by
  have h := defectFamily_periodic large D hol c side q K ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) hℓ r y
  simpa only [Rat.cast_intCast] using h

/-- **Equivariance under the radical elements of the level.**  If `μ = q u(K w) q⁻¹` lies in
`rationalLevel`, then `Θ_r(μ y) = ρ μ (Θ_r(y))` (shift followed by periodicity). -/
theorem defectFamily_radical_equivariant (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ)
    (hw : q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹ ∈ rationalLevel)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r
        (fun i => (q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹) * y i) =
      rationalCoefficientComponent n D.chi
        (q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹)
        (defectFamily large D hol c side q K r y) := by
  rw [defectFamily_shift large D hol c side q K w r y,
    defectFamily_periodic large D hol c side q K w hw r y]

end Defect


end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
