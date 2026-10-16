module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BSL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaNTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspRegroup

@[expose] public section



/-!
# `BaseSumZero` from the cusp values of homomorphisms on `Γ(6) ≤ GL₂(ℤ)`

Formalized by Claude Sonnet 5.5.

`baseSumZero_of_cusp_values` translates the Farey-side statement about additive maps `φ : gammaNGL 6 → ℚ` and the generators `cuspSigma c` of the representative cusps
into the `BaseSumZero` (cusps of `Γ(6) ≤ SL₂(ℤ)` as classes of primitive vectors, positive generators `posParSL v`).
* `cuspSigma_eq_posParGL`: `cuspElt c · T⁶ · (cuspElt c)⁻¹ = posPar(first column of cuspElt c)` and `conj_posParGL`: `γ posPar(v) γ⁻¹ = posPar(γ v)` for `det γ = 1`; `posPar(-v) = posPar(v)`.
* `rel_of_orbit`, `orbit_of_rel`: `CuspRel v w` iff the lines of `v`, `w` lie in one `Γ(6)`-orbit.
* The map `i ↦` (representative of the orbit of the line of `c i`) is a bijection `I → (cuspReps).R`; an additive map to the abelian group `ℚ` is conjugation invariant.
-/

open CongruenceSubgroup Matrix
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- The positive parabolic generator as an element of `GL₂(ℤ)`. -/
def posParGL (v : Fin 2 → ℤ) : IntegralGL := Matrix.SpecialLinearGroup.toGL (posPar v)

theorem posParGL_val (v : Fin 2 → ℤ) :
    (posParGL v).val = !![1 - 6 * v 0 * v 1, 6 * v 0 ^ 2; -6 * v 1 ^ 2, 1 + 6 * v 0 * v 1] := by
  rfl

theorem posParGL_neg (v : Fin 2 → ℤ) : posParGL (-v) = posParGL v := by
  apply Units.ext
  rw [posParGL_val, posParGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation of the positive parabolic generator by a determinant-one matrix. -/
theorem conj_posParGL (γ : IntegralGL) (hγ : IsSL γ) (v : Fin 2 → ℤ) :
    γ * posParGL v * γ⁻¹ = posParGL (γ.val.mulVec v) := by
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    have := hγ
    unfold IsSL at this
    rw [Matrix.det_fin_two] at this
    exact this
  have key : γ * posParGL v = posParGL (γ.val.mulVec v) * γ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, posParGL_val, posParGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    · linear_combination (6 * (γ.val 0 0 * v 0 + γ.val 0 1 * v 1) * v 1) * hdet
    · linear_combination (-6 * v 0 * (γ.val 0 0 * v 0 + γ.val 0 1 * v 1)) * hdet
    · linear_combination (6 * v 1 * (γ.val 1 0 * v 0 + γ.val 1 1 * v 1)) * hdet
    · linear_combination (-6 * v 0 * (γ.val 1 0 * v 0 + γ.val 1 1 * v 1)) * hdet
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

theorem Tk_six_eq : Tk 6 = posParGL ![1, 0] := by
  apply eq_of_entries <;> simp [posParGL_val, Tk_00, Tk_01, Tk_10, Tk_11]

theorem cuspSigma_eq_posParGL (c : RationalLine2) :
    ((cuspSigma (N := 6) c : gammaNGL 6) : IntegralGL) = posParGL (fun i => (cuspElt c).val i 0) := by
  rw [cuspSigma_val]
  have h := conj_posParGL (cuspElt c) (cuspElt_sl c) ![1, 0]
  have hv : (cuspElt c).val.mulVec ![1, 0] = fun i => (cuspElt c).val i 0 := by
    funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv] at h
  have e6 : ((6 : ℕ) : ℤ) = 6 := by norm_num
  rw [e6, Tk_six_eq]
  exact h

theorem coprime_of_prim {v : IntegralVector} (h : Primitive v) : IsCoprime (v 0) (v 1) := by
  unfold Primitive content at h
  exact Int.isCoprime_iff_gcd_eq_one.mpr h

theorem prim_of_coprime (v : Prim2) : Primitive v.1 := by
  unfold Primitive content
  exact Int.isCoprime_iff_gcd_eq_one.mp v.2

/-- The cusp (rational line) of a primitive vector. -/
def lineP (v : Prim2) : RationalLine2 := lineOf v.1 (prim_of_coprime v)

theorem isGen_lineP (v : Prim2) : IsGen (lineP v) v.1 := isGen_lineOf _ _

theorem isGen_cuspElt (c : RationalLine2) : IsGen c (fun i => (cuspElt c).val i 0) := by
  have h := col_isGen (cuspElt c) 0
  have h0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  rw [h0, ← smul_cusp1, cuspElt_cusp1] at h
  exact h

theorem isGen_smul' (C : IntegralGL) {L : RationalLine2} {v : IntegralVector} (h : IsGen L v) :
    IsGen (C • L) (C.val.mulVec v) := by
  obtain ⟨g, hg⟩ := rationalLine_eq_augmentedLine L
  subst hg
  have h0 : IsGen (augmentedLine g 0) (fun i => g.val i 0) := col_isGen g 0
  have hC : IsGen (C • augmentedLine g 0) (fun i => (C * g).val i 0) := by
    rw [smul_augmentedLine]
    exact col_isGen (C * g) 0
  have hmul : (fun i => (C * g).val i 0) = C.val.mulVec (fun i => g.val i 0) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  rcases h0.eq_or_neg h with e | e
  · rw [e, ← hmul]; exact hC
  · rw [e, Matrix.mulVec_neg, ← hmul]; exact hC.neg

theorem rel_of_orbit (hN : 3 ≤ 6) (γ : gammaNGL 6) (v w : Prim2) (h : γ • lineP v = lineP w) : CuspRel v w := by
  have h1 : IsGen (γ • lineP v) (γ.1.val.mulVec v.1) := isGen_smul' γ.1 (isGen_lineP v)
  rw [h] at h1
  refine ⟨toSL hN γ, toSL_mem hN γ, ?_⟩
  rcases (h1.eq_or_neg (isGen_lineP w)) with e | e
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [e]; simp [toSL]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have e' : (γ.1.val.mulVec v.1) = -w.1 := by rw [e]; simp
    simpa [toSL] using e'

theorem orbit_of_rel (hN : 3 ≤ 6) (v w : Prim2) (h : CuspRel v w) : ∃ γ : gammaNGL 6, γ • lineP v = lineP w := by
  obtain ⟨γ, hγ, s, hs, e⟩ := h
  refine ⟨gammaEquiv hN ⟨γ, hγ⟩, ?_⟩
  have h1 : IsGen ((gammaEquiv hN ⟨γ, hγ⟩ : gammaNGL 6) • lineP v) ((gammaEquiv hN ⟨γ, hγ⟩ : gammaNGL 6).1.val.mulVec v.1) :=
    isGen_smul' _ (isGen_lineP v)
  have e' : (gammaEquiv hN ⟨γ, hγ⟩ : gammaNGL 6).1.val.mulVec v.1 = s • w.1 := e
  rw [e'] at h1
  refine (h1.line_eq_iff (isGen_lineP w)).mpr ?_
  rcases hs with rfl | rfl
  · left; simp
  · right; simp

/-- **`BaseSumZero` from the Farey-side core**: if every sum-zero vector of the representative cusps is the value
vector `(φ(σ_c))_c` of an additive map `φ` on `Γ(6) ≤ GL₂(ℤ)`, then the cusp values `φ(posParSL v)` of homomorphisms on
`Γ(6) ≤ SL₂(ℤ)` fill the sum-zero hyperplane over any bijective indexing of the cusps. -/
theorem baseSumZero_of_cusp_values
    (H : ∀ (x : (cuspReps (by norm_num : 3 ≤ 6)).R → ℚ), ∑ c, x c = 0 →
      ∃ φ : gammaNGL 6 → ℚ, (∀ g h, φ (g * h) = φ g + φ h) ∧
        ∀ c : (cuspReps (by norm_num : 3 ≤ 6)).R, φ (cuspSigma (c : RationalLine2)) = x c) :
    BaseSumZero := by
  classical
  intro I _ c hbij x hx
  have hN : 3 ≤ 6 := by norm_num
  have hr : ∀ i, ∃ r ∈ (cuspReps hN).R, ∃ γ : gammaNGL 6, γ • r = lineP (c i) := fun i => (cuspReps hN).cover _
  choose rr hrR γγ hγγ using hr
  let f : I → (cuspReps hN).R := fun i => ⟨rr i, hrR i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hij' : rr i = rr j := congrArg Subtype.val hij
    apply hbij.1
    apply Quotient.sound
    apply rel_of_orbit hN ((γγ j) * (γγ i)⁻¹) (c i) (c j)
    rw [mul_smul, ← hγγ i, inv_smul_smul, hij', hγγ j]
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨v, hv⟩ := exists_gen r
    let pv : Prim2 := ⟨v, coprime_of_prim hv.1⟩
    obtain ⟨i, hi⟩ := hbij.2 (Quotient.mk cuspSetoid pv)
    obtain ⟨γ, hγ⟩ := orbit_of_rel hN (c i) pv (Quotient.exact hi)
    have hl : lineP pv = r := ((isGen_lineP pv).line_eq_iff hv).mpr (Or.inl rfl)
    refine ⟨i, Subtype.ext ?_⟩
    apply (cuspReps hN).inj _ (hrR i) r hr (γ * γγ i)
    rw [mul_smul, hγγ i, hγ, hl]
  let e : I ≃ (cuspReps hN).R := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hsum : ∑ r : (cuspReps hN).R, x (e.symm r) = 0 := by
    rw [Equiv.sum_comp e.symm x]; exact hx
  obtain ⟨φ0, hadd, hval⟩ := H (fun r => x (e.symm r)) hsum
  have h1 : φ0 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    linarith
  have hinvv : ∀ g, φ0 g⁻¹ = - φ0 g := by
    intro g
    have := hadd g g⁻¹
    rw [mul_inv_cancel, h1] at this
    linarith
  have hconj : ∀ g s, φ0 (g * s * g⁻¹) = φ0 s := by
    intro g s
    rw [hadd, hadd, hinvv]; ring
  refine ⟨fun g => φ0 (gammaEquiv hN g), fun a b => by simp [hadd], fun i => ?_⟩
  have hkey : gammaEquiv hN (posParSL (c i).1) = γγ i * cuspSigma (N := 6) (rr i) * (γγ i)⁻¹ := by
    apply Subtype.ext
    change posParGL (c i).1 = ((γγ i : gammaNGL 6) : IntegralGL) * ((cuspSigma (N := 6) (rr i) : gammaNGL 6) : IntegralGL) *
      ((γγ i : gammaNGL 6) : IntegralGL)⁻¹
    rw [cuspSigma_eq_posParGL, conj_posParGL _ (gammaN_isSL hN (γγ i).2)]
    have h1 : IsGen (lineP (c i)) ((γγ i : gammaNGL 6).1.val.mulVec (fun j => (cuspElt (rr i)).val j 0)) := by
      rw [← hγγ i]; exact isGen_smul' _ (isGen_cuspElt (rr i))
    rcases h1.eq_or_neg (isGen_lineP (c i)) with e1 | e1
    · rw [e1]
    · rw [e1, posParGL_neg]
  change φ0 (gammaEquiv hN (posParSL (c i).1)) = x i
  rw [hkey, hconj]
  have h2 : e.symm (f i) = i := e.symm_apply_apply i
  have h3 := hval (f i)
  simp only [h2] at h3
  exact h3

end TernaryPeriodPolynomials.Argument.GammaNStokes
