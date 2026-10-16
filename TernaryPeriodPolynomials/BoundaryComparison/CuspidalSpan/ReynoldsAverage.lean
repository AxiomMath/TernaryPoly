module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ReynoldsCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SmoothVectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TensorAction

@[expose] public section


/-!
# The Reynolds averaging operator over the eight `PlaneLeviLevel` cosets

Step (i) of `CuspidalSupply.lean`'s hypothesis `h`. Given a
cuspidal datum `cusp : CuspidalRepresentation` and a vector `v : cusp.smooth` fixed by every
`PlaneLeviLevel` element of `GL₂(ℤ̂)`, the Reynolds average over the eight coset representatives
of `ReynoldsCosets.lean`,

  `w := (1/8 : ℂ) • ∑ i : Fin 8, v ⋆ (γ i)`,

is fixed by *all* of `GL₂(ℤ̂)` (`reynoldsAverage_fixed`). The right action `v ⋆ κ := cuspAt cusp κ v`
is `cusp.π` through the finite-adelic embedding `integralEmbedding`, with the inverse baked in so
that `cuspAt cusp` composes as a right action (`cuspAt_mul`).

The fixedness argument is a permutation argument: for
`k : GL₂(ℤ̂)`, the covering lemma `exists_unique_coset` applied to `γ i * k` gives, for each `i`, a
unique `σ i` and a Levi-level witness with `γ i * k = (γ i * k * (γ (σ i))⁻¹) * γ (σ i)`; `σ` is
injective (hence bijective, `Fin 8` being finite) because the eight `γ i` already lie in
*distinct* `PlaneLeviLevel`-cosets; re-indexing the finite sum along `σ` then shows `w ⋆ k = w`.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (cuspSmoothAction)
open TernaryPeriodPolynomials.Automorphic.SmoothVectors (combineGL_mul)

/-- The right action of `GL₂(ℤ̂)` on a cuspidal datum's smooth vectors through the finite-adelic
embedding: `v ⋆ κ := cuspAt cusp κ v`. The inverse is baked in so that `cuspAt cusp` composes as a
*right* action (`cuspAt_mul`), matching the convention of `cuspFiniteRationalSlash`. -/
def cuspAt (cusp : CuspidalRepresentation) (κ : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    Module.End ℂ cusp.smooth :=
  cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding κ⁻¹))

/-- `atFinite` turns products into products: it is the finite-place half of the monoid hom
`combineGL 1 ·`. -/
theorem atFinite_mul (A B : BinaryFiniteGL) : atFinite (A * B) = atFinite A * atFinite B := by
  show combineGL 1 (A * B) = combineGL 1 A * combineGL 1 B
  rw [combineGL_mul, one_mul]

/-- **`cuspAt` is a right action**: `v ⋆ (κμ) = (v⋆κ)⋆μ`. -/
theorem cuspAt_mul (cusp : CuspidalRepresentation)
    (κ μ : GeneralLinearGroup (Fin 2) IntegralAdeles) (v : cusp.smooth) :
    cuspAt cusp (κ * μ) v = cuspAt cusp μ (cuspAt cusp κ v) := by
  apply Subtype.ext
  show cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (κ * μ)⁻¹)) v.val =
    cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding μ⁻¹))
      (cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding κ⁻¹)) v.val)
  rw [_root_.mul_inv_rev, GeneralLinearGroup.map_mul, atFinite_mul, map_mul, Module.End.mul_apply]

/-- The Reynolds average of a vector over the eight coset representatives of `ReynoldsCosets.lean`. -/
def reynoldsAverage (cusp : CuspidalRepresentation) (v : cusp.smooth) : cusp.smooth :=
  (8⁻¹ : ℂ) • ∑ i : Fin 8, cuspAt cusp (γ i) v

/-- **The Reynolds average of a Levi-level-fixed vector is fixed by all of `GL₂(ℤ̂)`.** -/
theorem reynoldsAverage_fixed (cusp : CuspidalRepresentation) (v : cusp.smooth)
    (leviFixed : ∀ κ : GeneralLinearGroup (Fin 2) IntegralAdeles, PlaneLeviLevel κ →
      cuspAt cusp κ v = v) (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    cuspAt cusp k (reynoldsAverage cusp v) = reynoldsAverage cusp v := by
  classical
  choose σ hσ using fun i : Fin 8 => exists_unique_coset (γ i * k)
  have hA : ∀ A B : GeneralLinearGroup (Fin 2) IntegralAdeles,
      PlaneLeviLevel (A * B⁻¹) ↔ bottomRow3 (red A) = bottomRow3 (red B) := by
    intro A B
    rw [planeLeviLevel_iff, red_mul, red_inv, bottomRow3_eq_iff]
  have hcancel : ∀ g h c : GeneralLinearGroup (Fin 2) (ZMod 3),
      bottomRow3 (g * c) = bottomRow3 (h * c) → bottomRow3 g = bottomRow3 h := by
    intro g h c heq
    have h1 : bottomRow3 ((g * c) * (h * c)⁻¹) = ((0 : ZMod 3), (1 : ZMod 3)) :=
      (bottomRow3_eq_iff (g * c) (h * c)).mpr heq
    have h2 : (g * c) * (h * c)⁻¹ = g * h⁻¹ := by group
    rw [h2] at h1
    exact (bottomRow3_eq_iff g h).mp h1
  have hinj : Function.Injective σ := by
    intro i j hij
    have hi := (hA (γ i * k) (γ (σ i))).mp (hσ i).1
    have hj := (hA (γ j * k) (γ (σ j))).mp (hσ j).1
    rw [hij] at hi
    rw [red_mul] at hi hj
    have hc := hcancel (red (γ i)) (red (γ j)) (red k) (hi.trans hj.symm)
    rw [bottomRow3_gamma, bottomRow3_gamma] at hc
    exact row_injective i j hc
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  have hstep : ∀ i : Fin 8, cuspAt cusp (γ i * k) v = cuspAt cusp (γ (σ i)) v := by
    intro i
    have heq : γ i * k = (γ i * k * (γ (σ i))⁻¹) * γ (σ i) := by group
    rw [heq, cuspAt_mul, leviFixed _ (hσ i).1]
  have step3 : (∑ i : Fin 8, cuspAt cusp k (cuspAt cusp (γ i) v)) =
      ∑ i : Fin 8, cuspAt cusp (γ i) v :=
    (Finset.sum_congr rfl (fun i _ => (cuspAt_mul cusp (γ i) k v).symm.trans (hstep i))).trans
      (hbij.sum_comp (fun j => cuspAt cusp (γ j) v))
  unfold reynoldsAverage
  rw [map_smul, map_sum, step3]

end TernaryPeriodPolynomials.Argument.CuspidalSpan
