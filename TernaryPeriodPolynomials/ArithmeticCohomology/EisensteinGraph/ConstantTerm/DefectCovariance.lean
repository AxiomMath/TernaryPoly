module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PlaneDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.Decomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Comparison

@[expose] public section


/-!
# Covariance of the defect translation family

Fix a plane source cocycle `c`, a side, a rational flag representative `q` and a scale `K`.
Write `A_r := atInfinity (u(K r)) * rationalGroup q⁻¹` for the adelic argument of the defect
translation family `Θ_r(y) = Φ(y)(A_r)`, `Φ := defectValue`, `ρ := rationalCoefficientComponent`.

The adelic algebra of this file consists of three identities between adelic arguments, each
proved by comparing the real and the finite projections:

* shift: `A_r * atInfinity (q u(K w) q⁻¹) = A_{r+w}`;
* Levi: `A_r * atInfinity (q p q⁻¹) = rationalGroup p * A_{r'} * atFinite (rationalFinite
  (q p q⁻¹)⁻¹)` whenever `p⁻¹ u(K r) p = u(K r')` in the real group;
* the radical is abelian, so `p = u(K w)` falls under the Levi case with `r' = r`.

The analytic input is only the real covariance of `Φ`, its left invariance under the rational
points of the parabolic, and its right invariance under the finite level.
Together they give the shift formula, the Levi covariance and the periodicity of `Θ`.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The real image of a rational matrix, written out in full. -/
local notation:max "ratReal[" g "]" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g

variable {n : ℕ}

/-! ## The radical -/

theorem sideUnipotent_comm (side : Side) {R : Type*} [CommRing R] (s t s' t' : R) :
    sideUnipotent side s t * sideUnipotent side s' t' =
      sideUnipotent side s' t' * sideUnipotent side s t := by
  rw [← sideUnipotent_add, ← sideUnipotent_add, add_comm s s', add_comm t t']

theorem sideUnipotent_scaled_add (side : Side) (K a b a' b' : ℝ) :
    sideUnipotent side (K * (a + a')) (K * (b + b')) =
      sideUnipotent side (K * a) (K * b) * sideUnipotent side (K * a') (K * b') := by
  rw [mul_add, mul_add]
  exact sideUnipotent_add side _ _ _ _

/-- The rational radical lies in the rational parabolic of its side. -/
theorem sideUnipotent_mem_parabolic (side : Side) (s t : ℚ) :
    sideUnipotent side s t ∈ parabolic side := by
  cases side
  · show InPlaneParabolic (planeUnipotent s t)
    exact ⟨rfl, rfl⟩
  · show InLineParabolic (lineUnipotent s t)
    exact ⟨rfl, rfl⟩

theorem map_sideUnipotent_cast (side : Side) (a b : ℚ) :
    ratReal[sideUnipotent side a b] = sideUnipotent side (a : ℝ) (b : ℝ) := by
  have e : ∀ x : ℚ, algebraMap ℚ ℝ x = (x : ℝ) := fun x => eq_ratCast _ x
  cases side
  · have h := PlaneDecomposition.map_planeUnipotent (algebraMap ℚ ℝ) a b
    simp only [e] at h
    simpa only [sideUnipotent] using h
  · have h := LineDecomposition.map_lineUnipotent (algebraMap ℚ ℝ) a b
    simp only [e] at h
    simpa only [sideUnipotent] using h

theorem map_sideUnipotent_scaled (side : Side) (K : ℕ) (w : ℚ × ℚ) :
    ratReal[sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2)] =
      sideUnipotent side ((K : ℝ) * (w.1 : ℝ)) ((K : ℝ) * (w.2 : ℝ)) := by
  rw [map_sideUnipotent_cast]
  simp only [Rat.cast_mul, Rat.cast_natCast]

/-! ## The adelic argument of the translation family -/

/-- The adelic argument `atInfinity (u(K r)) * rationalGroup q⁻¹` of `defectFamily`. -/
def translationArgument (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ) : AdelicGL :=
  atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) * rationalGroup q⁻¹

theorem translationArgument_mk (side : Side) (q : RationalGL3) (K : ℕ) (a b : ℝ) :
    translationArgument side q K (a, b) =
      atInfinity (sideUnipotent side ((K : ℝ) * a) ((K : ℝ) * b)) * rationalGroup q⁻¹ := rfl

/-- Shift identity: right multiplication of `A_r` by the real image of
`h = q u(K w) q⁻¹` is the translation `r ↦ r + w`.  Computed on real and finite parts:
real part `u(K r) · q⁻¹ · (q u(K w) q⁻¹) = u(K r) u(K w) · q⁻¹`, finite part `rationalFinite q⁻¹`
on both sides (the archimedean element has trivial finite part). -/
theorem translationArgument_shift (side : Side) (q : RationalGL3) (K : ℕ) (w : ℚ × ℚ)
    (r : ℝ × ℝ) :
    translationArgument side q K r *
        atInfinity (ratReal[q * sideUnipotent side ((K : ℚ) * w.1) ((K : ℚ) * w.2) * q⁻¹]) =
      translationArgument side q K (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) := by
  have hU := sideUnipotent_scaled_add side (K : ℝ) r.1 r.2 (w.1 : ℝ) (w.2 : ℝ)
  rw [translationArgument_mk side q K (r.1 + (w.1 : ℝ)) (r.2 + (w.2 : ℝ))]
  apply InducedContinuity.adelic_ext
  · simp only [translationArgument, map_mul, map_inv, InducedContinuity.realGroup_atInfinity,
      GeneralEisenstein.Adelic.realGroup_rational, map_sideUnipotent_scaled, hU]
    group
  · simp only [translationArgument, map_mul, map_inv, InducedContinuity.finiteGroup_atInfinity,
      GeneralEisenstein.Adelic.finiteGroup_rational]
    group

/-- Levi identity.  For `p : GL₃(ℚ)` with `p⁻¹ u(K r) p = u(K r')` in `GL₃(ℝ)` and
`γ = q p q⁻¹`,
`A_r * atInfinity γ = rationalGroup p * A_{r'} * atFinite (rationalFinite γ⁻¹)`.
Computed on projections.  Real: `u(K r) q⁻¹ (q p q⁻¹) = p u(K r') q⁻¹`, because
`u(K r) p = p u(K r')`.  Finite: `rationalFinite q⁻¹ = rationalFinite p · rationalFinite q⁻¹ ·
rationalFinite (q p q⁻¹)⁻¹`. -/
theorem translationArgument_levi (side : Side) (q p : RationalGL3) (K : ℕ) (r r' : ℝ × ℝ)
    (hr : (ratReal[p])⁻¹ * sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) * ratReal[p] =
      sideUnipotent side ((K : ℝ) * r'.1) ((K : ℝ) * r'.2)) :
    translationArgument side q K r * atInfinity (ratReal[q * p * q⁻¹]) =
      rationalGroup p * translationArgument side q K r' *
        atFinite (rationalFinite (q * p * q⁻¹)⁻¹) := by
  apply InducedContinuity.adelic_ext
  · simp only [translationArgument, map_mul, map_inv, InducedContinuity.realGroup_atInfinity,
      InducedContinuity.realGroup_atFinite, GeneralEisenstein.Adelic.realGroup_rational]
    rw [← hr]
    group
  · simp only [translationArgument, map_mul, map_inv, InducedContinuity.finiteGroup_atInfinity,
      InducedContinuity.finiteGroup_atFinite, GeneralEisenstein.Adelic.finiteGroup_rational]
    group

/-! ## Analytic inputs for the defect -/

section Defect

variable (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
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

theorem rationalCoefficientComponent_eq (χ : RankOneCharacter) (g : RationalGL3) :
    rationalCoefficientComponent n χ g = realCoefficientComponent n χ (ratReal[g]) := rfl

theorem realVertices_leftMul (g : RationalGL3) (y : Fin 3 → RationalGL3) :
    GlobalEisensteinCocycle.realVertices (fun i => g * y i) =
      fun i => ratReal[g] * GlobalEisensteinCocycle.realVertices y i := by
  funext i
  simp [GlobalEisensteinCocycle.realVertices, map_mul]

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

/-! ## The three properties of the translation family -/

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

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
