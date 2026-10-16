module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceInduced
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceIdentity

@[expose] public section


/-!
# The good-plane source at the good-plane cusp point

The good-plane cusp point is `rationalGroup (planeFrameQ true)⁻¹`, where
`planeFrameQ true = rational goodPlaneFrame` is the rational permutation matrix `w` swapping `e₂`
and `e₃` (`Separation.planeFrameQ`).  Its finite part is the finite good-plane frame
`goodPlaneFrameF` (`rationalFinite_goodPlane`), at which the good-plane cell vector is the
level-three vector itself (`goodPlaneVector_frame`), so the finite twist disappears
(`gp_twist_frame`):

* `goodPlaneSourceAt_frame`: if `finiteGroup g = goodPlaneFrameF` then
  `goodPlaneSourceAt D E y g x = ρ(g_∞)⁻¹ ((l(b(g_∞ y₂)) - l(b(g_∞ y₁)))
    (α(A(g_∞ y₁)) x - α(A(g_∞ y₀)) x))`.
* `goodPlaneSource_cusp_real` (the exact statement the detection argument uses): for real vertices
  `y`, with `W` the real image of the rational frame `planeFrameQ true`,
  `goodPlaneSource D E y (rationalGroup (planeFrameQ true)⁻¹) =
     ρ(W) (identityPlaneCup n D.chi E.α (fun i => W⁻¹ * y i))`.
* `goodPlaneSource_rational_cusp`: for rational vertices `x i` (the shape entering `Evaluates`),
  `goodPlaneSource D E (ratReal ∘ x) (rationalGroup (planeFrameQ true)⁻¹) =
     ρ(W) (identityPlaneCup n D.chi E.α (fun i => ratReal ((planeFrameQ true)⁻¹ * x i)))`.

Here `identityPlaneCup n χ α z := (l(b(z₂)) - l(b(z₁))) (α(A(z₁)) 1 - α(A(z₀)) 1)` is, with
`α = E.α`, exactly the right-hand side of SC's `planeSource_rational_identity` (identity-plane
value) at the vertices `z`, so the value at the good-plane cusp point is `ρ(W)` applied to SC's
identity-plane value at the rational vertices `(planeFrameQ true)⁻¹ * x i`, with the vector data
of the level-three Levi cocycle `E` in place of the spherical one.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Separation (planeFrameQ rationalFinite_goodPlane)

namespace TernaryPeriodPolynomials.LevelThreeSource

section Frame

variable {n : ℕ}

/-- **The good-plane source at an adele whose finite part is the good-plane frame.** -/
theorem goodPlaneSourceAt_frame (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (hg : finiteGroup g = goodPlaneFrameF) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y g x =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        ((planeRadical n D.chi (iwP (realGroup g * y 2)) -
            planeRadical n D.chi (iwP (realGroup g * y 1)))
          (E.α (iwA (realGroup g * y 1)) x - E.α (iwA (realGroup g * y 0)) x)) := by
  unfold goodPlaneSourceAt
  rw [smul_sub, gp_twist_frame D E hχ g hg, gp_twist_frame D E hχ g hg]

/-- The identity-plane expression of SC (`planeSource_rational_identity`) for an arbitrary Levi
cocycle `α`: the difference of the radicals of the Iwasawa factors of the vertices applied to the
difference of the Levi cocycles of the `GL₂` blocks, at the trivial `GL₂` adele. -/
def identityPlaneCup (n : ℕ) (χ : RankOneCharacter)
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (z : Fin 3 → RealGL3) : HomogeneousPoly n :=
  (planeRadical n χ (iwP (z 2)) - planeRadical n χ (iwP (z 1)))
    (α (iwA (z 1)) 1 - α (iwA (z 0)) 1)

/-- SC's identity-plane value of the spherical plane source is `identityPlaneCup`. -/
theorem planeSource_rational_identity_eq_cup (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    planeSource D E (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (1 : RationalGL3)⁻¹) =
      identityPlaneCup n D.chi E.α (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) :=
  planeSource_rational_identity D E hχ x

end Frame

section Cusp

variable {n : ℕ}

theorem rationalFinite_planeFrameQ_true : rationalFinite (planeFrameQ true) = goodPlaneFrameF :=
  rationalFinite_goodPlane

/-- The finite part of the good-plane cusp point is the finite good-plane frame. -/
theorem finiteGroup_goodPlaneCusp :
    finiteGroup (rationalGroup (planeFrameQ true)⁻¹) = goodPlaneFrameF := by
  rw [finiteGroup_rational, map_inv rationalFinite, rationalFinite_planeFrameQ_true,
    goodPlaneFrameF_inv]

/-- The real part of the good-plane cusp point. -/
theorem realGroup_goodPlaneCusp :
    realGroup (rationalGroup (planeFrameQ true)⁻¹) =
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeFrameQ true))⁻¹ := by
  rw [realGroup_rational, _root_.map_inv]

/-- **The good-plane source at the good-plane cusp point and real vertices.** -/
theorem goodPlaneSource_cusp_real (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (y : Fin 3 → RealGL3) :
    goodPlaneSource D E y (rationalGroup (planeFrameQ true)⁻¹) =
      realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeFrameQ true))
        (identityPlaneCup n D.chi E.α
          (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeFrameQ true))⁻¹ * y i)) := by
  have h := goodPlaneSourceAt_frame D E hχ _ finiteGroup_goodPlaneCusp y 1
  rw [realGroup_goodPlaneCusp, _root_.inv_inv] at h
  exact h

/-- **The good-plane source at the good-plane cusp point and rational vertices**, as it enters the
evaluation `Evaluates` of a source cocycle at the good-plane flag. -/
theorem goodPlaneSource_rational_cusp (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (x : Fin 3 → RationalGL3) :
    goodPlaneSource D E (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i))
        (rationalGroup (planeFrameQ true)⁻¹) =
      realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeFrameQ true))
        (identityPlaneCup n D.chi E.α
          (fun i => GeneralLinearGroup.map (algebraMap ℚ ℝ) ((planeFrameQ true)⁻¹ * x i))) := by
  rw [goodPlaneSource_cusp_real D E hχ]
  simp only [map_mul, _root_.map_inv]

end Cusp

end TernaryPeriodPolynomials.LevelThreeSource
