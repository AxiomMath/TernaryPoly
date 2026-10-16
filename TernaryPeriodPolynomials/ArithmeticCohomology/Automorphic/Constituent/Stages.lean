module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Setting
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RotationTypes
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Differentiation

@[expose] public section


/-!
# Finite rotation types of the cuspidal constituents of the Bergman model

A smooth vector of a cuspidal constituent that is fixed by the congruence subgroup
`finiteCongruence` and on which the rotations act through the character `fourier index` is a
vector `F` of the Bergman space whose rotation `realRep (rotGL θ) F` is `exp (index θ i) F`.  By the
phase computation of `coeffPlus_realRep_rot` and `coeffMinus_realRep_rot`, all its Taylor
coefficients vanish except the single one with `k + 2 m = index` (upper half plane) or
`-(k + 2 m) = index` (lower half plane), and these two coefficients are fixed by the congruence
subgroup.  Hence `F` is determined by a vector of the finite dimensional space of fixed vectors of
the model, and the space of such `F` is finite dimensional (`Piece.finiteTypes`).  By
`continuousStages_of_finite_types` this gives `ContinuousStages` (`Piece.stages`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors (IsOpenCompact)
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility (cyclicSpan)
open TernaryPeriodPolynomials.Regularity
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
  (fixedMode mem_fixedMode_iff continuousStages_of_finite_types)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
  (finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle
  (rotation complexMatrix)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
  (rotation_val_exp)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

namespace Stages

/-! ### Rotations and characters of the circle -/

/-- The matrix of the complex number `exp (θ i)` is the rotation of angle `θ`. -/
theorem complexMatrix_exp (θ : ℝ) :
    complexMatrix (Complex.exp ((θ : ℂ) * Complex.I)) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexMatrix]

/-- The rotation of the circle parameter `x` is the rotation matrix of angle `2 π x`. -/
theorem rotation_coe (x : ℝ) : rotation (x : AddCircle (1 : ℝ)) = rotGL (2 * Real.pi * x) :=
  Units.ext (by rw [rotation_val_exp, rotGL_val]; exact complexMatrix_exp _)

/-- The character `fourier index` at the parameter `x` is `exp (index · 2 π x · i)`. -/
theorem fourier_coe_eq (index : ℤ) (x : ℝ) :
    fourier index (x : AddCircle (1 : ℝ)) =
      Complex.exp ((index : ℂ) * ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- A vector of the Bergman space on which the circle rotates through `fourier index`, in the
coordinates of the rotation angle. -/
theorem realRep_rot_of_eigen {k : ℕ} (M : FiniteModel k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E)
    (hint : ∀ g w, ι (D.π g w) = bergmanRep M g (ι w)) {index : ℤ} {w : D.H}
    (h : ∀ p : AddCircle (1 : ℝ), D.π (atInfinity (rotation p)) w = fourier index p • w)
    (θ : ℝ) :
    realRep k M.E (rotGL θ) (ι w) = Complex.exp ((index : ℂ) * θ * Complex.I) • ι w := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 := congrArg ι (h ((θ / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)))
  rw [hint, bergmanRep_atInfinity, map_smul, rotation_coe, fourier_coe_eq,
    show 2 * Real.pi * (θ / (2 * Real.pi)) = θ by field_simp] at h2
  exact h2

/-! ### Vanishing of the coefficients -/

/-- If two distinct integer frequencies act identically on `a`, then `a = 0`. -/
theorem eq_zero_of_exp_smul_eq {E : Type*} [AddCommGroup E] [Module ℂ E] {a : E} {p q : ℤ}
    (hpq : p ≠ q)
    (h : ∀ θ : ℝ, Complex.exp ((p : ℂ) * θ * Complex.I) • a =
      Complex.exp ((q : ℂ) * θ * Complex.I) • a) : a = 0 := by
  have hne : (p : ℂ) - q ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hpq)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((p : ℂ) - q) * (θ : ℂ) = (Real.pi : ℂ) :=
    ⟨Real.pi / ((p : ℝ) - q), by push_cast; field_simp⟩
  refine eq_zero_of_exp_eq_neg ?_ (h θ)
  have hsplit : (p : ℂ) * θ * Complex.I = (q : ℂ) * θ * Complex.I + Real.pi * Complex.I := by
    linear_combination Complex.I * hθ
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

section Coefficients

variable {k : ℕ} {M : FiniteModel k} {F : BergmanSpace k M.E} {index : ℤ}

/-- The upper coefficients of a rotation eigenvector vanish away from the frequency `index`. -/
theorem coeffPlus_eq_zero_of_rot
    (hrot : ∀ θ : ℝ, realRep k M.E (rotGL θ) F = Complex.exp ((index : ℂ) * θ * Complex.I) • F)
    {n : ℕ} (hn : (k : ℤ) + 2 * n ≠ index) : coeffPlus F n = 0 := by
  refine eq_zero_of_exp_smul_eq hn (fun θ => ?_)
  have h := congrArg (fun G => coeffPlus G n) (hrot θ)
  simp only [coeffPlus_realRep_rot, coeffPlus_smul] at h
  rw [show (((k : ℤ) + 2 * (n : ℤ) : ℤ) : ℂ) = (k : ℂ) + 2 * n by simp]
  exact h

/-- The lower coefficients of a rotation eigenvector vanish away from the frequency `index`. -/
theorem coeffMinus_eq_zero_of_rot
    (hrot : ∀ θ : ℝ, realRep k M.E (rotGL θ) F = Complex.exp ((index : ℂ) * θ * Complex.I) • F)
    {n : ℕ} (hn : -((k : ℤ) + 2 * n) ≠ index) : coeffMinus F n = 0 := by
  refine eq_zero_of_exp_smul_eq hn (fun θ => ?_)
  have h := congrArg (fun G => coeffMinus G n) (hrot θ)
  simp only [coeffMinus_realRep_rot, coeffMinus_smul] at h
  rw [show ((-((k : ℤ) + 2 * (n : ℤ)) : ℤ) : ℂ) * θ * Complex.I =
    -(((k : ℂ) + 2 * n) * θ) * Complex.I by push_cast; ring]
  exact h

/-- The upper coefficients of a vector fixed by `K` are fixed by `K`. -/
theorem coeffPlus_mem_fixed {K : Subgroup BinaryFiniteGL}
    (hF : ∀ u : K, finRep k M.σ M.unitary u.val F = F) (n : ℕ) :
    coeffPlus F n ∈ fixedSubmodule M.σ K := fun u => by
  rw [← coeffPlus_finRep M.σ M.unitary u.val F n, hF u]

/-- The lower coefficients of a vector fixed by `K` are fixed by `K`. -/
theorem coeffMinus_mem_fixed {K : Subgroup BinaryFiniteGL}
    (hF : ∀ u : K, finRep k M.σ M.unitary u.val F = F) (n : ℕ) :
    coeffMinus F n ∈ fixedSubmodule M.σ K := fun u => by
  rw [← coeffMinus_finRep M.σ M.unitary u.val F n, hF u]

end Coefficients

/-- The upper coefficients of zero vanish. -/
theorem coeffPlus_zero_eq {k : ℕ} (M : FiniteModel k) (hk : 2 ≤ k) (n : ℕ) :
    coeffPlus (0 : BergmanSpace k M.E) n = 0 :=
  (coeffPlusL_apply hk n 0).symm.trans (map_zero _)

/-- The lower coefficients of zero vanish. -/
theorem coeffMinus_zero_eq {k : ℕ} (M : FiniteModel k) (hk : 2 ≤ k) (n : ℕ) :
    coeffMinus (0 : BergmanSpace k M.E) n = 0 :=
  (coeffMinusL_apply hk n 0).symm.trans (map_zero _)

/-! ### The index of the only possibly nonvanishing coefficient -/

/-- Auxiliary existence statement defining `modeIndex`. -/
theorem exists_modeIndex (k : ℕ) (a : ℤ) :
    ∃ n : ℕ, (∃ m : ℕ, (k : ℤ) + 2 * m = a) → (k : ℤ) + 2 * n = a := by
  by_cases h : ∃ m : ℕ, (k : ℤ) + 2 * m = a
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, fun _ => hm⟩
  · exact ⟨0, fun h' => absurd h' h⟩

/-- The index `n` with `k + 2 n = a`, when there is one (and `0` otherwise). -/
def modeIndex (k : ℕ) (a : ℤ) : ℕ :=
  Classical.choose (exists_modeIndex k a)

/-- `modeIndex k a` is the only index `n` with `k + 2 n = a`. -/
theorem eq_modeIndex {k : ℕ} {a : ℤ} {n : ℕ} (h : (k : ℤ) + 2 * n = a) : n = modeIndex k a := by
  have h2 : (k : ℤ) + 2 * (modeIndex k a : ℕ) = a :=
    Classical.choose_spec (exists_modeIndex k a) ⟨n, h⟩
  omega

/-! ### The embedding of a fixed mode into the Bergman space -/

section Embedding

variable {k : ℕ}

/-- The embedding of the smooth vectors of `D` fixed by `K` into the Bergman space. -/
def modeEmbedding (M : FiniteModel k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E) (K : Subgroup BinaryFiniteGL) (index : ℤ) :
    fixedMode D K index →ₗ[ℂ] BergmanSpace k M.E :=
  ι ∘ₗ (D.smooth.subtype ∘ₗ (fixedMode D K index).subtype)

/-- The value of `modeEmbedding` on a vector. -/
theorem modeEmbedding_apply (M : FiniteModel k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E) (K : Subgroup BinaryFiniteGL) (index : ℤ)
    (w : fixedMode D K index) : modeEmbedding M D ι K index w = ι w.val.val :=
  rfl

/-- The image of a fixed mode is a rotation eigenvector. -/
theorem rot_modeEmbedding (M : FiniteModel k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E) (hint : ∀ g w, ι (D.π g w) = bergmanRep M g (ι w))
    {K : Subgroup BinaryFiniteGL} {index : ℤ} (w : fixedMode D K index) (θ : ℝ) :
    realRep k M.E (rotGL θ) (modeEmbedding M D ι K index w) =
      Complex.exp ((index : ℂ) * θ * Complex.I) • modeEmbedding M D ι K index w :=
  realRep_rot_of_eigen M D ι hint ((mem_fixedMode_iff D K index w.val).1 w.property).2 θ

/-- The image of a fixed mode is fixed by the finite group. -/
theorem finRep_modeEmbedding (M : FiniteModel k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E) (hint : ∀ g w, ι (D.π g w) = bergmanRep M g (ι w))
    {K : Subgroup BinaryFiniteGL} {index : ℤ} (w : fixedMode D K index) (u : K) :
    finRep k M.σ M.unitary u.val (modeEmbedding M D ι K index w) =
      modeEmbedding M D ι K index w := by
  have hmem : D.π (atFinite u.val) w.val.val = w.val.val :=
    ((mem_fixedMode_iff D K index w.val).1 w.property).1 u
  rw [← bergmanRep_atFinite M u.val, modeEmbedding_apply, ← hint, hmem]

/-- **Finite rotation types, abstractly.**  If a cuspidal representation `D` embeds equivariantly
and injectively in the Bergman space of a finite-adelic model, the smooth vectors fixed by an open
compact `K` with a given rotation character form a finite dimensional space. -/
theorem finiteDimensional_fixedMode (M : FiniteModel k) (hk : 2 ≤ k) (D : CuspidalRepresentation)
    (ι : D.H →ₗ[ℂ] BergmanSpace k M.E) (hι : Function.Injective ι)
    (hint : ∀ g w, ι (D.π g w) = bergmanRep M g (ι w)) {K : Subgroup BinaryFiniteGL}
    (hK : IsOpenCompact K) (index : ℤ) : FiniteDimensional ℂ (fixedMode D K index) := by
  have hfd : FiniteDimensional ℂ (fixedSubmodule M.σ K) := M.finiteDimensional K hK
  let L₁ : fixedMode D K index →ₗ[ℂ] fixedSubmodule M.σ K :=
    ((coeffPlusL hk (modeIndex k index)).toLinearMap ∘ₗ modeEmbedding M D ι K index).codRestrict _
      fun w => coeffPlus_mem_fixed (finRep_modeEmbedding M D ι hint w) (modeIndex k index)
  let L₂ : fixedMode D K index →ₗ[ℂ] fixedSubmodule M.σ K :=
    ((coeffMinusL hk (modeIndex k (-index))).toLinearMap ∘ₗ
      modeEmbedding M D ι K index).codRestrict _
      fun w => coeffMinus_mem_fixed (finRep_modeEmbedding M D ι hint w) (modeIndex k (-index))
  refine Module.Finite.of_injective (L₁.prod L₂) ?_
  rw [injective_iff_map_eq_zero]
  intro w hw
  have h1 : coeffPlus (modeEmbedding M D ι K index w) (modeIndex k index) = 0 :=
    congrArg Subtype.val (congrArg Prod.fst hw)
  have h2 : coeffMinus (modeEmbedding M D ι K index w) (modeIndex k (-index)) = 0 :=
    congrArg Subtype.val (congrArg Prod.snd hw)
  have hF : modeEmbedding M D ι K index w = 0 := by
    refine eq_of_coeff hk (fun n => ?_) (fun n => ?_)
    · rw [coeffPlus_zero_eq M hk]
      by_cases hn : (k : ℤ) + 2 * n = index
      · rw [eq_modeIndex hn]
        exact h1
      · exact coeffPlus_eq_zero_of_rot (rot_modeEmbedding M D ι hint w) hn
    · rw [coeffMinus_zero_eq M hk]
      by_cases hn : (k : ℤ) + 2 * n = -index
      · rw [eq_modeIndex hn]
        exact h2
      · exact coeffMinus_eq_zero_of_rot (rot_modeEmbedding M D ι hint w)
          (fun h => hn (by omega))
  have h0 : ι w.val.val = 0 := (modeEmbedding_apply M D ι K index w).symm.trans hF
  exact Subtype.ext (Subtype.ext (hι (h0.trans (map_zero ι).symm)))

end Embedding

end Stages

/-! ### The cuspidal constituents -/

/-- The inclusion of the cuspidal representation of a constituent into the Bergman space: the
closed cyclic span of `c.v` is a subspace. -/
def cuspInclusion {n : ℕ} (hn : 3 ≤ n) (c : Piece n) :
    (c.cusp hn).H →ₗ[ℂ] BergmanSpace (n + 3) (bergmanModel n).E :=
  (cyclicSpan (bergmanRep (bergmanModel n)) c.v).subtype

/-- The inclusion of a constituent is injective. -/
theorem cuspInclusion_injective {n : ℕ} (hn : 3 ≤ n) (c : Piece n) :
    Function.Injective (cuspInclusion hn c) :=
  Submodule.injective_subtype (cyclicSpan (bergmanRep (bergmanModel n)) c.v)

/-- The inclusion of a constituent intertwines the restricted representation with the Bergman
representation. -/
theorem cuspInclusion_intertwine {n : ℕ} (hn : 3 ≤ n) (c : Piece n) (g : BinaryAdelicGL)
    (w : (c.cusp hn).H) :
    cuspInclusion hn c ((c.cusp hn).π g w) =
      bergmanRep (bergmanModel n) g (cuspInclusion hn c w) :=
  rfl

/-- **Finite rotation types.**  For every integer `index`, the smooth vectors of the cuspidal
constituent `c` fixed by `finiteCongruence` on which the rotations act through `fourier index`
form a finite dimensional space. -/
theorem Piece.finiteTypes {n : ℕ} (hn : 3 ≤ n) (c : Piece n) (index : ℤ) :
    FiniteDimensional ℂ (fixedMode (c.cusp hn) finiteCongruence index) :=
  Stages.finiteDimensional_fixedMode (bergmanModel n) (by omega) (c.cusp hn)
    (cuspInclusion hn c) (cuspInclusion_injective hn c) (cuspInclusion_intertwine hn c)
    (And.intro finiteCongruence_isOpen finiteCongruence_isCompact) index

/-- **Continuity of the stages** for the cuspidal constituents of the Bergman model. -/
theorem Piece.stages {n : ℕ} (hn : 3 ≤ n) (c : Piece n) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages
      (c.cusp hn) :=
  continuousStages_of_finite_types _ (Piece.finiteTypes hn c)

end TernaryPeriodPolynomials.Automorphic.Constituent

end
