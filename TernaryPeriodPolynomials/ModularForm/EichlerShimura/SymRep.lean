module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymFrame
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.EichlerClass

@[expose] public section


/-!
# The representation `Sym^m` in monomial coordinates and the equivariance of the Hodge frame

Foundation file of the unconditional Eichler--Shimura route.  A binary form `Σ v_i X₀^{m-i} X₁^i` of degree `m` is identified with its coefficient
vector `v : Fin (m+1) → ℂ` (`thetaPoly`, `coords`, `thetaPoly_coords`).  `symRepGL m g` is the
matrix of the substitution `P ↦ P ∘ adj(g)` (the adjugate substitution `invCoordPoly` of the
library) in these coordinates; it is multiplicative (`symRepGL_mul`). For a general `g ∈ GL₂(ℝ)` the
adjugate is `det(g) · g⁻¹`, so on forms of degree `m` this substitution is `det(g)^m` times
`P ↦ P ∘ g⁻¹`; the two agree when `det g = 1` (a sufficient condition, not a necessary one: for
`det g = -1` and even `m` the factor `det(g)^m` is also `1`), in particular for `g ∈ SL₂(ℤ)`, the
only case used downstream, where it is the action of `modularBinaryRep`.  The Hodge frame
`frameE m z` (columns: the coefficient vectors of `(zX₁ - X₀)^j (z̄X₁ - X₀)^{m-j}`, see
`frameE_eq_coords`) is equivariant:

  `symRepGL m g * frameE m z = frameE m w * diag ((cz+d)^j (cz̄+d)^{m-j})`,  `w = (az+b)/(cz+d)`

(`symRepGL_mul_frameE`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial Matrix
open TernaryPeriodPolynomials.Argument.SeedC3
  (invCoordPoly invCoord invCoord_mul eval_bind₁_invCoordPoly dnm)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame

variable (m : ℕ)

/-- The exponent vector of `X₀^{m-i} X₁^i`. -/
def expo (i : Fin (m + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m - (i : ℕ)) + Finsupp.single 1 (i : ℕ)

/-- The monomial `X₀^{m-i} X₁^i`. -/
def monoPoly (i : Fin (m + 1)) : MvPolynomial (Fin 2) ℂ := monomial (expo m i) 1

/-- The binary form with coefficient vector `v`. -/
def thetaPoly (v : Fin (m + 1) → ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ i : Fin (m + 1), C (v i) * monoPoly m i

/-- The coefficient vector of a binary form. -/
def coords (P : MvPolynomial (Fin 2) ℂ) : Fin (m + 1) → ℂ := fun i => P.coeff (expo m i)

theorem expo_apply_zero (i : Fin (m + 1)) : expo m i 0 = m - (i : ℕ) := by
  simp [expo]

theorem expo_apply_one (i : Fin (m + 1)) : expo m i 1 = (i : ℕ) := by
  simp [expo]

theorem expo_inj {i k : Fin (m + 1)} (h : expo m i = expo m k) : i = k := by
  have := congrArg (fun s => s 1) h
  simp only [expo_apply_one] at this
  exact Fin.ext this

theorem coords_thetaPoly (v : Fin (m + 1) → ℂ) : coords m (thetaPoly m v) = v := by
  funext k
  unfold coords thetaPoly monoPoly
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    have : expo m i ≠ expo m k := fun h => hik (expo_inj m h)
    simp [this]
  · simp

theorem thetaPoly_coords {P : MvPolynomial (Fin 2) ℂ} (hP : P.IsHomogeneous m) :
    thetaPoly m (coords m P) = P := by
  ext s
  unfold thetaPoly coords monoPoly
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases hs : s 0 + s 1 = m
  · have hi : (s 1) < m + 1 := by omega
    have hsi : expo m ⟨s 1, hi⟩ = s := by
      ext n
      fin_cases n
      · simp [expo]; omega
      · simp [expo]
    rw [Finset.sum_eq_single ⟨s 1, hi⟩]
    · simp [hsi]
    · intro i _ hik
      have : expo m i ≠ s := by
        intro h
        apply hik
        rw [← hsi] at h
        exact expo_inj m h
      simp [this]
    · simp
  · have h0 : P.coeff s = 0 := by
      by_contra hne
      apply hs
      have h1 := hP hne
      have h2 : (Finsupp.weight (1 : Fin 2 → ℕ)) s = s 0 + s 1 := by
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
        simp [Fin.sum_univ_two]
      omega
    rw [h0]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : expo m i ≠ s := by
      intro h
      apply hs
      rw [← h, expo_apply_zero, expo_apply_one]
      have := i.2
      omega
    simp [this]

theorem coords_add (P Q : MvPolynomial (Fin 2) ℂ) : coords m (P + Q) = coords m P + coords m Q := by
  funext i; simp [coords]

theorem coords_smul (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    coords m (C c * P) = c • coords m P := by
  funext i; simp [coords, coeff_C_mul]

theorem coords_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    coords m (∑ i ∈ s, f i) = ∑ i ∈ s, coords m (f i) := by
  funext k; simp [coords]

/-- Dehomogenisation `X₀ ↦ 1`, `X₁ ↦ t`. -/
def dehom : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval ![1, Polynomial.X]

theorem dehom_monoPoly (i : Fin (m + 1)) : dehom (monoPoly m i) = Polynomial.X ^ (i : ℕ) := by
  unfold monoPoly dehom expo
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two]

theorem coords_eq_dehom {P : MvPolynomial (Fin 2) ℂ} (hP : P.IsHomogeneous m) (i : Fin (m + 1)) :
    coords m P i = (dehom P).coeff i := by
  conv_rhs => rw [← thetaPoly_coords m hP]
  unfold thetaPoly
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp only [map_mul, dehom_monoPoly]
  have hC : ∀ c : ℂ, dehom (C c) = Polynomial.C c := fun c => by simp [dehom]
  simp only [hC, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : (i : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

/-- The binary form `(zX₁ - X₀)^j (z̄X₁ - X₀)^{m-j}`. -/
def ehom (z : ℂ) (j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (C z * X 1 - X 0) ^ j * (C (starRingEnd ℂ z) * X 1 - X 0) ^ (m - j)

theorem ehom_homogeneous (z : ℂ) {j : ℕ} (hj : j ≤ m) : (ehom m z j).IsHomogeneous m := by
  have h1 : (C z * X 1 - X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
    ((isHomogeneous_C_mul_X z 1)).sub (isHomogeneous_X ℂ 0)
  have h2 : (C (starRingEnd ℂ z) * X 1 - X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
    ((isHomogeneous_C_mul_X (starRingEnd ℂ z) 1)).sub (isHomogeneous_X ℂ 0)
  have := (h1.pow j).mul (h2.pow (m - j))
  unfold ehom
  have e : 1 * j + 1 * (m - j) = m := by omega
  rw [e] at this
  exact this

theorem dehom_ehom (z : ℂ) (j : ℕ) : dehom (ehom m z j) = epol m z j := by
  unfold ehom epol dehom
  simp

theorem frameE_eq_coords (z : ℂ) (i j : Fin (m + 1)) :
    frameE m z i j = coords m (ehom m z j) i := by
  rw [coords_eq_dehom m (ehom_homogeneous m z (by omega)), dehom_ehom]
  rfl

/-- The matrix, in monomial coordinates, of the adjugate substitution `P ↦ P ∘ adj(g)`
(`invCoordPoly`) on binary forms of degree `m`. It differs from `P ↦ P ∘ g⁻¹` by the factor
`det(g)^m`, so the two agree when `det g = 1` (a sufficient condition: `det g = -1` with even `m`
also gives `1`); for `g ∈ SL₂` it is `P ↦ P ∘ g⁻¹`. -/
def symRepGL (g : GL (Fin 2) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i' i => coords m (bind₁ (invCoordPoly g) (monoPoly m i)) i'

theorem weight_eq (s : Fin 2 →₀ ℕ) : Finsupp.weight (1 : Fin 2 → ℕ) s = s 0 + s 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

theorem isHomogeneous_monoPoly (i : Fin (m + 1)) : (monoPoly m i).IsHomogeneous m := by
  unfold monoPoly
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_weight_one]
  change (Finsupp.weight (1 : Fin 2 → ℕ)) (expo m i) = m
  rw [weight_eq, expo_apply_zero, expo_apply_one]
  have := i.2
  omega

theorem isHomogeneous_invCoordPoly (g : GL (Fin 2) ℝ) (i : Fin 2) :
    (invCoordPoly g i).IsHomogeneous 1 := by
  fin_cases i
  · have e : invCoordPoly g 0 = C (((g 1 1 : ℝ)) : ℂ) * X 0 + C (-(((g 0 1 : ℝ)) : ℂ)) * X 1 := by
      simp [invCoordPoly, sub_eq_add_neg]
    simp only [Fin.zero_eta]
    rw [e]
    exact (isHomogeneous_C_mul_X _ 0).add (isHomogeneous_C_mul_X _ 1)
  · have e : invCoordPoly g 1 = C (-(((g 1 0 : ℝ)) : ℂ)) * X 0 + C (((g 0 0 : ℝ)) : ℂ) * X 1 := by
      simp [invCoordPoly]
    simp only [Fin.mk_one]
    rw [e]
    exact (isHomogeneous_C_mul_X _ 0).add (isHomogeneous_C_mul_X _ 1)

theorem isHomogeneous_bind_inv (g : GL (Fin 2) ℝ) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsHomogeneous m) : (bind₁ (invCoordPoly g) P).IsHomogeneous m := by
  have := hP.aeval (invCoordPoly g) (isHomogeneous_invCoordPoly g)
  simpa [aeval_eq_bind₁] using this

/-- `symRepGL` acts on coordinate vectors as the adjugate substitution `bind₁ (invCoordPoly g)`
(equal to `P ↦ P ∘ g⁻¹` when `det g = 1`, a sufficient condition; in general the two differ by the
factor `det(g)^m`). -/
theorem symRepGL_mulVec (g : GL (Fin 2) ℝ) {P : MvPolynomial (Fin 2) ℂ} (hP : P.IsHomogeneous m) :
    symRepGL m g *ᵥ coords m P = coords m (bind₁ (invCoordPoly g) P) := by
  have hP' : P = ∑ i : Fin (m + 1), C (coords m P i) * monoPoly m i := (thetaPoly_coords m hP).symm
  conv_rhs => rw [hP']
  rw [map_sum]
  simp only [map_mul, bind₁_C_right]
  rw [coords_sum]
  simp only [coords_smul]
  funext k
  simp [symRepGL, Matrix.mulVec, dotProduct, mul_comm]

theorem bind_inv_mul (g h : GL (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    bind₁ (invCoordPoly (g * h)) P = bind₁ (invCoordPoly g) (bind₁ (invCoordPoly h) P) := by
  apply MvPolynomial.funext
  intro v
  simp only [eval_bind₁_invCoordPoly, invCoord_mul]

theorem symRepGL_mul (g h : GL (Fin 2) ℝ) : symRepGL m (g * h) = symRepGL m g * symRepGL m h := by
  ext i' i
  have hmono := isHomogeneous_monoPoly m i
  have hb := isHomogeneous_bind_inv m h hmono
  have h1 := congrFun (symRepGL_mulVec m g hb) i'
  have h2 : (symRepGL m g *ᵥ coords m (bind₁ (invCoordPoly h) (monoPoly m i))) i' =
      (symRepGL m g * symRepGL m h) i' i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, symRepGL, Matrix.of_apply]
  rw [← h2, h1, ← bind_inv_mul]
  rfl

theorem coords_monoPoly (i k : Fin (m + 1)) :
    coords m (monoPoly m i) k = if k = i then 1 else 0 := by
  unfold coords monoPoly
  rw [coeff_monomial]
  by_cases h : k = i
  · simp [h]
  · have : expo m i ≠ expo m k := fun e => h (expo_inj m e).symm
    simp [this, h]

theorem symRepGL_one : symRepGL m 1 = 1 := by
  ext i' i
  have hid : bind₁ (invCoordPoly (1 : GL (Fin 2) ℝ)) (monoPoly m i) = monoPoly m i := by
    have : invCoordPoly (1 : GL (Fin 2) ℝ) = fun j => X j := by
      funext j
      fin_cases j <;> simp [invCoordPoly]
    rw [this, bind₁_X_left, AlgHom.id_apply]
  simp only [symRepGL, Matrix.of_apply, hid, coords_monoPoly]
  by_cases h : i' = i
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

theorem bind_lin (g : GL (Fin 2) ℝ) (z w : ℂ)
    (hw : dnm g z * w = (g 0 0 : ℝ) * z + (g 0 1 : ℝ)) :
    bind₁ (invCoordPoly g) (C z * X 1 - X 0 : MvPolynomial (Fin 2) ℂ) =
      C (dnm g z) * (C w * X 1 - X 0) := by
  have hw' : (C (dnm g z) * C w : MvPolynomial (Fin 2) ℂ) =
      C (((g 0 0 : ℝ) : ℂ)) * C z + C (((g 0 1 : ℝ) : ℂ)) := by
    rw [← map_mul, ← map_mul, ← map_add, hw]
  have hd : (C (dnm g z) : MvPolynomial (Fin 2) ℂ) =
      C (((g 1 0 : ℝ) : ℂ)) * C z + C (((g 1 1 : ℝ) : ℂ)) := by
    simp [dnm]
  simp only [map_sub, map_mul, bind₁_C_right, bind₁_X_right]
  simp only [invCoordPoly, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hd] at hw' ⊢
  linear_combination (-(X 1 : MvPolynomial (Fin 2) ℂ)) * hw'

theorem bind_ehom (g : GL (Fin 2) ℝ) (z w : ℂ)
    (hw : dnm g z * w = (g 0 0 : ℝ) * z + (g 0 1 : ℝ))
    (hw' : dnm g (starRingEnd ℂ z) * starRingEnd ℂ w =
      (g 0 0 : ℝ) * starRingEnd ℂ z + (g 0 1 : ℝ)) (j : ℕ) :
    bind₁ (invCoordPoly g) (ehom m z j) =
      C (dnm g z ^ j * dnm g (starRingEnd ℂ z) ^ (m - j)) * ehom m w j := by
  unfold ehom
  rw [map_mul, map_pow, map_pow, bind_lin g z w hw, bind_lin g (starRingEnd ℂ z)
    (starRingEnd ℂ w) hw', map_mul, map_pow, map_pow]
  rw [mul_pow, mul_pow]
  ring

theorem symRepGL_mul_frameE (g : GL (Fin 2) ℝ) (z w : ℂ)
    (hw : dnm g z * w = (g 0 0 : ℝ) * z + (g 0 1 : ℝ))
    (hw' : dnm g (starRingEnd ℂ z) * starRingEnd ℂ w =
      (g 0 0 : ℝ) * starRingEnd ℂ z + (g 0 1 : ℝ)) :
    symRepGL m g * frameE m z = frameE m w *
      Matrix.diagonal (fun j : Fin (m + 1) =>
        dnm g z ^ (j : ℕ) * dnm g (starRingEnd ℂ z) ^ (m - j)) := by
  ext i j
  have hcol : (symRepGL m g *ᵥ (fun k => frameE m z k j)) i =
      (coords m (bind₁ (invCoordPoly g) (ehom m z j))) i := by
    have : (fun k => frameE m z k j) = coords m (ehom m z j) := by
      funext k; exact frameE_eq_coords m z k j
    rw [this, symRepGL_mulVec m g (ehom_homogeneous m z (by omega))]
  have h1 : (symRepGL m g * frameE m z) i j = (symRepGL m g *ᵥ (fun k => frameE m z k j)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, hcol, bind_ehom m g z w hw hw' j, coords_smul]
  simp [Matrix.mul_diagonal, frameE_eq_coords, mul_comm]

end TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
