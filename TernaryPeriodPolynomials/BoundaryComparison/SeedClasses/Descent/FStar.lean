module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.EdgeConj
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Reflection

@[expose] public section


/-!
# The conjugate cusp form `f^*(τ) = \overline{f(-\bar τ)}` of level one (Lemma C.3, S4c)

For a level-one cusp form `f` of weight `n + 3`, `fStar f = f ∣ J` with `J = diag(-1, 1)` is again a
level-one cusp form of the same weight, with `fStar f τ = \overline{f(-\bar τ)}`
(`fStar_apply`): slash-invariance since `J` normalizes `SL₂(ℤ)` (`J_mul_mem`), holomorphy by
`MDifferentiable.slash`, and vanishing at the cusps since `J` fixes `∞` and permutes the cusps
(`fStar_zero_at_cusps`). Its normalized moment primitives are the primitives
`Gs_j' = \overline{f(-\bar z)} z^j` of the reflection lemma `modularCocycleReflection_classical`,
so the edge of the antiholomorphic seed of `fStar f` is the reflected holomorphic period class
(`seedConjEdge_fStar`).

Paper: Lemma C.3 (`ar:lem:seed`).

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup ComplexConjugate OnePoint
open GeneralEisenstein MvPolynomial CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The polynomial underlying a value of `modularBinaryRep`. -/
def bval (d : ℕ) (x : modularBinaryRep d (-1)) : MvPolynomial (Fin 2) ℂ :=
  (x : Binary.HomogeneousPoly d).1

theorem slash_J_eq (f : ℍ → ℂ) (k : ℤ) :
    f ∣[k] J = fun τ : ℍ ↦ conj (f <| ofComplex <| -(conj ↑τ)) := by
  simp [slash_def, J_smul]

/-- Conjugation of `SL₂(ℤ)` by `J = diag(-1, 1)`. -/
def jConj (s : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![s 0 0, -s 0 1; -s 1 0, s 1 1], by
    have := s.det_coe
    simp only [Matrix.det_fin_two] at this ⊢
    simp
    linarith⟩

theorem J_mul_mapGL_mul_J (s : SL(2, ℤ)) :
    J * mapGL ℝ s * J = mapGL ℝ (jConj s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, jConj, mapGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      first | rfl | (change _ = ((-_ : ℤ) : ℝ); push_cast; rfl)

theorem J_smul_infty : (J : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = ∞ := by
  rw [smul_infty_eq_self_iff]
  simp [J]

theorem J_mul_mem {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Lvl1) : J * γ * J ∈ Lvl1 := by
  obtain ⟨s, rfl⟩ := hγ
  exact ⟨jConj s, (J_mul_mapGL_mul_J s).symm⟩

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

theorem fStar_slash_invariant {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Lvl1) :
    (⇑f ∣[((n + 3 : ℕ) : ℤ)] J) ∣[((n + 3 : ℕ) : ℤ)] γ = ⇑f ∣[((n + 3 : ℕ) : ℤ)] J := by
  have h1 : J * γ = (J * γ * J) * J := by
    rw [mul_assoc (J * γ) J J, ← sq, J_sq, mul_one]
  rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f _ (J_mul_mem hγ)]

theorem fStar_zero_at_cusps {c : OnePoint ℝ} (hc : IsCusp c Lvl1) :
    c.IsZeroAt (⇑f ∣[((n + 3 : ℕ) : ℤ)] J) ((n + 3 : ℕ) : ℤ) := by
  intro g hg
  have hJc : IsCusp (J • c) Lvl1 := by
    obtain ⟨s, rfl⟩ := (isCusp_SL2Z_iff'.1 hc)
    refine isCusp_SL2Z_iff'.2 ⟨jConj s, ?_⟩
    rw [← J_mul_mapGL_mul_J, mul_smul, J_smul_infty, mul_smul]
  have h1 : J * g = (J * g * J) * J := by
    rw [mul_assoc (J * g) J J, ← sq, J_sq, mul_one]
  have h2 : (J * g * J) • (∞ : OnePoint ℝ) = J • c := by
    rw [mul_smul, mul_smul, J_smul_infty, hg]
  have h3 := CuspFormClass.zero_at_cusps f hJc (J * g * J) h2
  rw [← SlashAction.slash_mul, h1, SlashAction.slash_mul]
  exact h3.slash _ (by simp [J])

/-- **The conjugate cusp form** `f^*(τ) = \overline{f(-\bar τ)}`, a level-one cusp form of the same
weight. -/
def fStar : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ) where
  toFun := ⇑f ∣[((n + 3 : ℕ) : ℤ)] J
  slash_action_eq' _ hγ := fStar_slash_invariant f hγ
  holo' := (ModularFormClass.holo f).slash _ J
  zero_at_cusps' hc := fStar_zero_at_cusps f hc

theorem fStar_apply (τ : ℍ) :
    fStar f τ = conj (f (ofComplex (-(conj (τ : ℂ))))) := by
  change (⇑f ∣[((n + 3 : ℕ) : ℤ)] J) τ = _
  rw [slash_J_eq]

theorem fStar_cuspH {z : ℂ} (hz : 0 < z.im) :
    cuspH Lvl1 n (fStar f) z = conj (f (ofComplex (-(conj z)))) := by
  change fStar f (ofComplex z) = _
  rw [fStar_apply, ofComplex_apply_of_im_pos hz]

/-- The normalized moment primitives of `fStar f` are those of `\overline{f(-\bar z)} z^j`. -/
theorem momentPrim_fStar_hasDerivAt (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (momentPrim Lvl1 n (fStar f) j)
      (conj (f (ofComplex (-(conj z)))) * z ^ j) z := by
  have := momentPrim_hasDerivAt Lvl1 n (fStar f) j z hz
  rwa [fStar_cuspH f hz] at this

/-- **The edge of the antiholomorphic seed of `f^*`**, in terms of the reflected holomorphic
period cocycle of `f`: with `R` the library's parity reflection of `classicalBinaryCocycle f`,
the edge of `seedConjRelCocycle (fStar f)` is `-(n+1)⁻¹ (-1)^{n+1} [R c_f]`. -/
theorem seedConjEdge_fStar (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    (plusLeviCohomologyIso n).hom (plusEdgeS n
        (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedConjRelCocycle (fStar f)))) =
      (-(((n : ℂ) + 1)⁻¹ * (-1 : ℂ) ^ (n + 1))) • groupCohomology.H1π
        (modularBinaryRep (n + 1) (-1))
        (modularCocycleReflection (n + 1) (-1) (classicalBinaryCocycle f (n + 1) hw (-1))) := by
  set R := modularCocycleReflection (n + 1) (-1) (classicalBinaryCocycle f (n + 1) hw (-1)) with hR
  have hs : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  have := seedConjEdge_of (fStar f) (momentPrim Lvl1 n (fStar f)) (momentPrim_zero Lvl1 n (fStar f))
    (momentPrim_hasDerivAt Lvl1 n (fStar f))
    ((-(-1 : ℂ) ^ (n + 1)) • R) (fun m => by
      have h := modularCocycleReflection_classical f n hw (-1) (momentPrim Lvl1 n f)
        (momentPrim Lvl1 n (fStar f)) (momentPrim_zero Lvl1 n f)
        (momentPrim_zero Lvl1 n (fStar f)) (momentPrim_hasDerivAt Lvl1 n f)
        (fun j z hz => momentPrim_fStar_hasDerivAt f j z hz) m
      have h' : (R m : Binary.HomogeneousPoly (n + 1)).val =
          -(C ((-1 : ℂ) ^ (n + 1)) * MvPolynomial.map (starRingEnd ℂ)
            (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (mapGL ℝ m))) := h
      have hC : (C ((-1 : ℂ) ^ (n + 1)) : MvPolynomial (Fin 2) ℂ) * C ((-1 : ℂ) ^ (n + 1)) = 1 := by
        rw [← map_mul, hs, map_one]
      have h'' : bval (n + 1) (R m) =
          -(C ((-1 : ℂ) ^ (n + 1)) * MvPolynomial.map (starRingEnd ℂ)
            (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (mapGL ℝ m))) := h'
      have e : bval (n + 1) (((-(-1 : ℂ) ^ (n + 1)) • R) m) =
          C (-(-1 : ℂ) ^ (n + 1)) * bval (n + 1) (R m) :=
        smul_eq_C_mul _ _
      change bval (n + 1) (((-(-1 : ℂ) ^ (n + 1)) • R) m) = _
      rw [e, h'', map_neg]
      linear_combination (MvPolynomial.map (starRingEnd ℂ)
        (eichlerCocycle n (momentPrim Lvl1 n (fStar f)) (mapGL ℝ m))) * hC)
  rw [this, _root_.map_smul, smul_smul]
  congr 1
  ring

end

end TernaryPeriodPolynomials.Argument.SeedC3S4c
