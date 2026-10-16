module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineFrame

@[expose] public section


/-!
# The orientation convention of the literal Stokes lemma

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair` ("The two internal orientation characters multiply to the face orientation. All determinant and reflection
actions are retained before taking finite-group invariants"), Lemma `ar:lem:stokes` ("The orientations are included in the two pairings"), and the mapping cone of its proof
`d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)`.

**The convention used in Lean.**

1. *Pairing of one face.*  `canAt` is `facePairingCan` on the Hochschild-Serre edges of the restrictions at the conjugating frame `h`: the Koszul pairing of the radical lattice `ℤ² = N_R` for its standard basis (orientation `e₁ ∧ e₂`)
   times the cup form of the modular curve for the standard orientation of the Farey tree (`cupForm`), both transported to the face `h⁻¹ R h` by the integral conjugator `h ∈ SL₃(ℤ)`.
   The text says the face orientation is the product of the two internal characters (radical, base).  The theorems below show this product is *trivial* on the whole integral stabilizer of the face, including the reflections
   (`line_internal_characters`, `plane_internal_characters`: `det φ_q = det A_G = a`, `a² = 1`; the `FaceDescent.line_characters_multiply` is the same computation on the tangent space of the symmetric space), so
   the transported orientation does not depend on the chosen conjugator (`frameInvarianceLine`, `frameInvariancePlane`), and conjugation by `SL₃(ℤ)` preserves the orientation of the symmetric space.  Hence the canonical orientation of every face of type `R` is the
   boundary orientation of that face multiplied by ONE sign `s_R ∈ {±1}` depending only on the type `R ∈ {P, Q}`.
2. *Relative sign of the two types.*  The two types of faces meet along the flag stratum `F_B`; in the paper's cone the corner enters with `+` for the plane component and `-` for the line component
   (`α|_{F_B} - β|_{F_B}`).  The Lean Stokes identity is derived from exactly this cone (the `lineFacePairM`, `planeFacePairM` are the cone pairings; S2 computed `lineFacePairM = c · can6`, `planeFacePairM = -c · can6P`,
   `κ_P = -κ_L`).  So with the face orientation signs `ε_P = +1` (plane), `ε_Q = -1` (line) of the cone differential, `ε_P ∑_P ⟨ , ⟩ + ε_Q ∑_Q ⟨ , ⟩ = 0`.
3. *What the text does not fix.*  The absolute sign (a global reversal of the orientation of the symmetric space multiplies both `ε_R` by `-1`) is a convention; the statement is invariant under it.  What is not formalised is the comparison of
   `canAt` with an integral over the geometric Borel-Serre boundary (`s_R` per type): the Lean content is the combinatorial/cohomological identity for the cone, with the face orientations of the cone differential.

`orientation_signs_forced`: the relative sign is not a free choice: if some other signs `(ε_P', ε_Q')` also make the identity true for all classes, and `∑_P` is nonzero for some classes, then `ε_P' + ε_Q' = 0`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.FrameInvariance

/-- **The internal orientation characters of a line face**: for `q ∈ Q(ℚ) ∩ SL₃(ℤ)` with first column `(a, 0, 0)ᵗ`, the radical (Koszul) character `det φ_q` and the base (cup-form) character `det A_G` both equal `a`, and `a² = 1`: their product,
the face orientation character, is trivial. -/
theorem line_internal_characters {q : SL(3, ℤ)} (hq : q ∈ lineBorel) :
    radDet (phiQ hq).toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 ∧
      (AG hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 ∧
      (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by
  refine ⟨radDet_phiQ hq, ?_, lineBorel_a_sq hq⟩
  have hm := congrArg Matrix.det (botRight_inv_mul q hq).2
  rw [Matrix.det_mul, Matrix.det_one] at hm
  have hd := lineBorel_detA hq
  rw [← Matrix.det_fin_two] at hd
  rw [hd] at hm
  have h2 := lineBorel_a_sq hq
  rw [AG_val]
  linear_combination (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * hm - (botRight q⁻¹).det * h2

/-- **The internal orientation characters of a plane face**: `det φ_q = det A_G = d`, `d² = 1`. -/
theorem plane_internal_characters {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    radDet (phiPQ hq).toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ∧
      (AGP hq).val.det = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 ∧
      (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := by
  refine ⟨radDet_phiPQ hq, ?_, planeBorel_d_sq hq⟩
  rw [AGP_val, Matrix.det_fin_two]
  have hd := planeBorel_detA (planeBorel.inv_mem hq)
  rw [inv_d hq] at hd
  exact hd

variable {N n : ℕ} [NeZero N]

/-- **The relative sign of the two kinds of faces is forced**: if `ε_P' ∑_P + ε_Q' ∑_Q = 0` for all classes of `Γ(N)` with zero flag restrictions, and the plane sum is nonzero for some pair of classes, then
`ε_P' + ε_Q' = 0` (given the literal Stokes lemma `∑_P = ∑_Q` at level `N`). -/
theorem orientation_signs_forced (hN : 3 ≤ N) (hS : StokesGammaNLiteral N n hN) (εP εQ : ℂ)
    (h : ∀ (c₀ : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c₀)
      (c₀' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c₀'),
      εP * ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' +
        εQ * ∑ i : LineFaces N, canAtClass N i.rep n hN c₀ hz c₀' hz' = 0)
    (c₀ : groupCohomology.H2 (gammaNRepAll N n)) (hz : ZeroFlags N n c₀)
    (c₀' : groupCohomology.H2 (gammaNRepAllDual N n)) (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c₀')
    (hne : ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' ≠ 0) : εP + εQ = 0 := by
  have h1 := hS c₀ hz c₀' hz'
  have h2 := h c₀ hz c₀' hz'
  simp only [planeFaceOrientationSign, lineFaceOrientationSign, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at h1
  have h3 : (εP + εQ) * ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' = 0 := by
    have e : ∑ i : LineFaces N, canAtClass N i.rep n hN c₀ hz c₀' hz' =
        ∑ j : PlaneFaces N, canAtClassP N (planeFaceRepr j) n hN c₀ hz c₀' hz' := by linear_combination -h1
    rw [e] at h2
    linear_combination h2
  exact (mul_eq_zero.1 h3).resolve_right hne

end TernaryPeriodPolynomials.Argument
