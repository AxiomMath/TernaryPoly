module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.Analytic.RadiusLiminf
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


/-!
# Schur's lemma for irreducible unitary representations on Hilbert space

A bounded self-adjoint operator commuting with a family of operators that has no
nontrivial closed invariant subspace is a real scalar. The proof uses the continuous
functional calculus: two distinct spectral points would split the space by the kernel of
`cfc f A` for a continuous `f` vanishing near one point but not the other.

This is the input that makes Hecke and central operators act by scalars on irreducible
`CuspidalRepresentation`s.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.RepresentationTheory

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  refine ⟨⟨1, 0, fun h => hv ?_⟩⟩
  simpa using congrArg (fun F : H →L[ℂ] H => F v) h

/-- Two distinct spectral points are impossible for a self-adjoint operator commuting with an
irreducible family. -/
theorem no_two_spectral_points [Nontrivial H] (S : Set (H →L[ℂ] H))
    (irr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ T ∈ S, ∀ v ∈ W, T v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ T ∈ S, Commute A T)
    {a b : ℝ} (ha : a ∈ spectrum ℝ A) (hb : b ∈ spectrum ℝ A) (hab : a < b) : False := by
  have := nontrivial_endomorphisms (H := H)
  set c : ℝ := (a + b) / 2 with hcdef
  let f : ℝ → ℝ := fun x => max (x - c) 0
  let g : ℝ → ℝ := fun x => max (c - x) 0
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  set P := cfc f A with hP
  set Q := cfc g A with hQ
  have hfg : (fun x => f x * g x) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hx : c ≤ x
    · have : g x = 0 := max_eq_right (by linarith)
      simp [this]
    · have : f x = 0 := max_eq_right (by linarith)
      simp [this]
  have hPQ : P * Q = 0 := by
    rw [hP, hQ, ← cfc_mul f g A hf.continuousOn hg.continuousOn, hfg, cfc_const_zero]
  have hspecP : spectrum ℝ P = f '' spectrum ℝ A := cfc_map_spectrum f A
  have hspecQ : spectrum ℝ Q = g '' spectrum ℝ A := cfc_map_spectrum g A
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : f b ∈ spectrum ℝ P := hspecP ▸ ⟨b, hb, rfl⟩
    rw [h0, spectrum.zero_eq] at hmem
    have : f b = 0 := hmem
    have hpos : 0 < f b := lt_max_of_lt_left (by rw [hcdef]; linarith)
    linarith
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hmem : g a ∈ spectrum ℝ Q := hspecQ ▸ ⟨a, ha, rfl⟩
    rw [h0, spectrum.zero_eq] at hmem
    have : g a = 0 := hmem
    have hpos : 0 < g a := lt_max_of_lt_left (by rw [hcdef]; linarith)
    linarith
  have hcomm : ∀ T ∈ S, Commute P T := fun T hT =>
    Commute.cfc_real (hc T hT) f
  let W : Submodule ℂ H := LinearMap.ker (P : H →ₗ[ℂ] H)
  have hWc : IsClosed (W : Set H) := ContinuousLinearMap.isClosed_ker P
  have hWi : ∀ T ∈ S, ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    have hv' : P v = 0 := hv
    change P (T v) = 0
    have := congrArg (fun F : H →L[ℂ] H => F v) (hcomm T hT).eq
    change P (T v) = T (P v) at this
    rw [this, hv', map_zero]
  rcases irr W hWc hWi with hbot | htop
  · apply hQ0
    ext v
    have hmem : Q v ∈ W := by
      change P (Q v) = 0
      have := congrArg (fun F : H →L[ℂ] H => F v) hPQ
      simpa using this
    rw [hbot] at hmem
    simpa using hmem
  · apply hP0
    ext v
    have hmem : v ∈ W := by rw [htop]; trivial
    exact hmem

/-- **Schur's lemma, self-adjoint form.** -/
theorem selfAdjoint_eq_scalar [Nontrivial H] (S : Set (H →L[ℂ] H))
    (irr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ T ∈ S, ∀ v ∈ W, T v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ T ∈ S, Commute A T) :
    ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by
  have := nontrivial_endomorphisms (H := H)
  obtain ⟨a, ha⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hall : ∀ b ∈ spectrum ℝ A, b = a := by
    intro b hb
    rcases lt_trichotomy a b with h | h | h
    · exact (no_two_spectral_points S irr A hA hc ha hb h).elim
    · exact h.symm
    · exact (no_two_spectral_points S irr A hA hc hb ha h).elim
  refine ⟨a, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id' ℝ A).symm
    _ = cfc (fun _ : ℝ => a) A := cfc_congr (fun x hx => hall x hx)
    _ = algebraMap ℝ (H →L[ℂ] H) a := cfc_const a A

/-- **Schur's lemma.** A bounded operator commuting with a `star`-closed irreducible family of
operators is a complex scalar. -/
theorem eq_scalar_of_commute [Nontrivial H] (S : Set (H →L[ℂ] H))
    (hstar : ∀ T ∈ S, star T ∈ S)
    (irr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ T ∈ S, ∀ v ∈ W, T v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (A : H →L[ℂ] H) (hc : ∀ T ∈ S, Commute A T) :
    ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
  have hcs : ∀ T ∈ S, Commute (star A) T := by
    intro T hT
    have h := (hc (star T) (hstar T hT)).star_star
    simpa using h
  have hre : ∀ T ∈ S, Commute ((realPart A : H →L[ℂ] H)) T := by
    intro T hT
    rw [realPart_apply_coe]
    exact ((hc T hT).add_left (hcs T hT)).smul_left _
  have him : ∀ T ∈ S, Commute ((imaginaryPart A : H →L[ℂ] H)) T := by
    intro T hT
    rw [imaginaryPart_apply_coe]
    exact (((hc T hT).sub_left (hcs T hT)).smul_left (2⁻¹ : ℝ)).smul_left (-Complex.I)
  obtain ⟨r₁, h₁⟩ := selfAdjoint_eq_scalar S irr _ (realPart A).property hre
  obtain ⟨r₂, h₂⟩ := selfAdjoint_eq_scalar S irr _ (imaginaryPart A).property him
  refine ⟨(r₁ : ℂ) + Complex.I * r₂, ?_⟩
  have hdecomp := realPart_add_I_smul_imaginaryPart A
  have e1 : ∀ r : ℝ, algebraMap ℝ (H →L[ℂ] H) r = (r : ℂ) • (1 : H →L[ℂ] H) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [← hdecomp, h₁, h₂, e1, e1, smul_smul, ← add_smul]

/-- The unitary operator `π g` of a cuspidal representation, as a bounded operator. -/
def cuspOperator (σ : GeneralEisenstein.CuspidalRepresentation)
    (g : GeneralEisenstein.BinaryAdelicGL) : σ.H →L[ℂ] σ.H :=
  LinearMap.mkContinuous (σ.π g) 1 (fun v => by rw [σ.unitary, one_mul])

theorem cuspOperator_apply (σ : GeneralEisenstein.CuspidalRepresentation)
    (g : GeneralEisenstein.BinaryAdelicGL) (v : σ.H) : cuspOperator σ g v = σ.π g v := rfl

theorem cuspOperator_inner (σ : GeneralEisenstein.CuspidalRepresentation)
    (g : GeneralEisenstein.BinaryAdelicGL) (v w : σ.H) :
    inner ℂ (σ.π g v) (σ.π g w) = inner ℂ v w := by
  let L : σ.H →ₗᵢ[ℂ] σ.H := ⟨σ.π g, fun v => σ.unitary g v⟩
  exact L.inner_map_map v w

theorem cuspOperator_star (σ : GeneralEisenstein.CuspidalRepresentation)
    (g : GeneralEisenstein.BinaryAdelicGL) :
    star (cuspOperator σ g) = cuspOperator σ g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [cuspOperator_apply, cuspOperator_apply]
  have hx : σ.π g (σ.π g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc inner ℂ (σ.π g⁻¹ x) y = inner ℂ (σ.π g (σ.π g⁻¹ x)) (σ.π g y) :=
        (cuspOperator_inner σ g _ _).symm
    _ = inner ℂ x (σ.π g y) := by rw [hx]

/-- **Schur's lemma for cuspidal representations.** Every bounded operator commuting with all
`π g` is a scalar. -/
theorem cuspidal_schur (σ : GeneralEisenstein.CuspidalRepresentation) (A : σ.H →L[ℂ] σ.H)
    (hA : ∀ g v, A (σ.π g v) = σ.π g (A v)) : ∃ z : ℂ, ∀ v, A v = z • v := by
  have := σ.nontrivial
  obtain ⟨z, hz⟩ := eq_scalar_of_commute (Set.range (cuspOperator σ))
    (by rintro _ ⟨g, rfl⟩; exact ⟨g⁻¹, (cuspOperator_star σ g).symm⟩)
    (by
      intro W hW hinv
      exact σ.irreducible W hW (fun g v hv => hinv _ ⟨g, rfl⟩ v hv))
    A (by
      rintro _ ⟨g, rfl⟩
      ext v
      exact hA g v)
  exact ⟨z, fun v => by rw [hz]; simp⟩

end TernaryPeriodPolynomials.RepresentationTheory
