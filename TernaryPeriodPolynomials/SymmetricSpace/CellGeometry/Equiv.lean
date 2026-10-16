module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Fiber
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Reduction
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.WellRounded

@[expose] public section


/-!
# Appendix B cell calculation: the `P_H`-equivariance of `i(w,C) = G(w,C)` as an action of `P_H`, and its link to `fiber_compat`

Formalized by Claude Sonnet 5.5.  Paper: "For `p = (η 0; u D)` ... `pᵗ G(w,C) p = G(w', C')` ... The map `i : (w,C) ↦ G(w,C)` ...
is `P_H`-equivariant.  ... The radical acts trivially on the residue fibre.  Quotienting its `ℝ²` coordinate by `ℤ²` gives the oriented torus ..."

* `phAct g (w, C) = (D⁻¹(u + ηw), DᵗCD)` for `g = (η 0; u D) ∈ P_H` (`η = lamHom g`, `u = uvec g`, `D = pi g`), a right action of `P_H` on `ℝ² × (binary forms)`
  (`phAct_one`, `phAct_mul` on positive definite `C`).
* `Gmat_phAct`: `gᵗ G(w,C) g = G(phAct g (w, C))` for every `g ∈ P_H` (the equivariance of `i`, stated for the group elements of `P_H` and not only for the matrix shape).
* `phAct_radPH`: the integral radical `U = ℤ²` acts by translation `w ↦ w + v` and trivially on `C`.
* `torusLinear_det`: the linear part `η D⁻¹` of the action on the fibre coordinate has determinant `deltaG eU g`, the Hochschild-Serre factor of `kappaLit`
  (`fiber_compat`): the orientation of the radical torus `ℝ²/ℤ²` is multiplied by exactly the determinant twist of the residue action (`fiber_compat_torus`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- The action of `g = (η 0; u D) ∈ P_H` on the fibre coordinate and the binary form: `(w, C) ↦ (D⁻¹(u + ηw), DᵗCD)`. -/
def phAct (g : PH) (x : Vec2 × Mat2) : Vec2 × Mat2 :=
  (castMat ((pi g)⁻¹).val *ᵥ (intVec (uvec g) + (((lamHom g : ℤˣ) : ℤ) : ℝ) • x.1),
    (castMat (pi g).val)ᵀ * x.2 * castMat (pi g).val)

/-- The real matrix of an element of `P_H`. -/
def phMat (g : PH) : Mat3 := g.1.val.map (Int.cast : ℤ → ℝ)

theorem phMat_eq_parab (g : PH) : phMat g = parab ((lamHom g : ℤˣ) : ℤ) (uvec g) (pi g).val := by
  unfold phMat
  rw [PH_matrix g]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parab]

/-- **Equivariance of `i`**: `gᵗ G(w,C) g = G(g · (w,C))` for every `g ∈ P_H` and symmetric `C`. -/
theorem Gmat_phAct {C : Mat2} (hC : Cᵀ = C) (g : PH) (w : Vec2) :
    (phMat g)ᵀ * Gmat w C * phMat g = Gmat (phAct g (w, C)).1 (phAct g (w, C)).2 := by
  have hDE : (pi g).val * ((pi g)⁻¹).val = 1 := Units.mul_inv (pi g)
  have hED : ((pi g)⁻¹).val * (pi g).val = 1 := Units.inv_mul (pi g)
  rw [phMat_eq_parab]
  refine Gmat_equivariant hC (pi g).val ((pi g)⁻¹).val hDE hED (uvec g) _ (lam_cases g) w _ ?_
  change castMat (pi g).val *ᵥ (castMat ((pi g)⁻¹).val *ᵥ (intVec (uvec g) + (((lamHom g : ℤˣ) : ℤ) : ℝ) • w)) = _
  rw [Matrix.mulVec_mulVec, ← castMat_mul, hDE, castMat_one, Matrix.one_mulVec]

theorem phAct_fst (g : PH) (x : Vec2 × Mat2) :
    (phAct g x).1 = castMat ((pi g)⁻¹).val *ᵥ intVec (uvec g) +
      (((lamHom g : ℤˣ) : ℤ) : ℝ) • (castMat ((pi g)⁻¹).val *ᵥ x.1) := by
  unfold phAct
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

theorem phAct_one (x : Vec2 × Mat2) : phAct 1 x = x := by
  have hu : uvec (1 : PH) = 0 := by
    funext i; simp [uvec]
  obtain ⟨w, C⟩ := x
  simp only [phAct, hu, map_one, inv_one, Units.val_one, castMat_one, Int.cast_one, one_smul]
  have h0 : intVec (0 : Fin 2 → ℤ) = 0 := by funext i; simp [intVec]
  simp [h0]

/-- **The action law** on positive definite forms: `(g h) · x = h · (g · x)` (a right action), a consequence of the equivariance and the injectivity of `i`. -/
theorem phAct_mul {C : Mat2} (hC : Cᵀ = C) (hpos : ∀ v : Vec2, v ≠ 0 → 0 < quad C v) (g h : PH) (w : Vec2) :
    phAct (g * h) (w, C) = phAct h (phAct g (w, C)) := by
  have hC1 : (phAct g (w, C)).2ᵀ = (phAct g (w, C)).2 := castMat_symm hC _
  have e1 := Gmat_phAct hC (g * h) w
  have e2 := Gmat_phAct hC g w
  have e3 := Gmat_phAct hC1 h (phAct g (w, C)).1
  have hmul : phMat (g * h) = phMat g * phMat h := by
    unfold phMat
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hposg : ∀ v : Vec2, v ≠ 0 → 0 < quad (phAct (g * h) (w, C)).2 v := by
    intro v hv
    have hDE : (pi (g * h)).val * ((pi (g * h))⁻¹).val = 1 := Units.mul_inv (pi (g * h))
    have hED : ((pi (g * h))⁻¹).val * (pi (g * h)).val = 1 := Units.inv_mul (pi (g * h))
    show 0 < quad ((castMat (pi (g * h)).val)ᵀ * C * castMat (pi (g * h)).val) v
    rw [quad_conj]
    apply hpos
    intro h0
    exact hv (castMat_mulVec_eq_zero hED h0)
  have key : Gmat (phAct (g * h) (w, C)).1 (phAct (g * h) (w, C)).2 =
      Gmat (phAct h (phAct g (w, C))).1 (phAct h (phAct g (w, C))).2 := by
    rw [← e1, ← e3, ← e2, hmul]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨hc, hw⟩ := Gmat_injective hposg key
  exact Prod.ext hw hc

/-- **The integral radical acts by translation of the fibre coordinate and trivially on the binary form**. -/
theorem phAct_radPH (v : Multiplicative (Fin 2 → ℤ)) (x : Vec2 × Mat2) :
    phAct (radPH v) x = (x.1 + intVec (Multiplicative.toAdd v), x.2) := by
  obtain ⟨w, C⟩ := x
  have hl : ((lamHom (radPH v) : ℤˣ) : ℤ) = 1 := by rw [lam_radPH]; rfl
  simp only [phAct, hl, pi_radPH, uvec_radPH, inv_one, Units.val_one, castMat_one, Int.cast_one, one_smul,
    Matrix.one_mulVec]
  refine Prod.ext ?_ ?_
  · simp [add_comm]
  · simp

/-- The linear part `η D⁻¹` of the action of `g ∈ P_H` on the fibre coordinate (rational matrix). -/
def torusLinear (g : PH) : Matrix (Fin 2) (Fin 2) ℚ :=
  (((lamHom g : ℤˣ) : ℤ) : ℚ) • ((pi g)⁻¹).val.map (Int.cast : ℤ → ℚ)

/-- **The orientation character of the radical torus is the determinant twist `deltaG`**: `det(η D⁻¹) = deltaG eU g` (the Hochschild-Serre factor of `kappaLit`). -/
theorem torusLinear_det (g : PH) : (torusLinear g).det = HochschildSerre.deltaG AppendixBResidue.eU g := by
  rw [deltaG_eq]
  unfold torusLinear
  have h1 : (((pi g)⁻¹).val.map (Int.cast : ℤ → ℚ)).det = ((((pi g)⁻¹).val.det : ℤ) : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) ((pi g)⁻¹).val
    simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.det_smul, h1]
  have hDE : (pi g).val * ((pi g)⁻¹).val = 1 := Units.mul_inv (pi g)
  have hd : (pi g).val.det * ((pi g)⁻¹).val.det = 1 := by rw [← Matrix.det_mul, hDE, Matrix.det_one]
  have hs : ((pi g)⁻¹).val.det = (pi g).val.det := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  have hl : (((lamHom g : ℤˣ) : ℤ) : ℚ) ^ Fintype.card (Fin 2) = 1 := by
    rcases lam_cases g with h | h <;> rw [h] <;> norm_num
  rw [hl, one_mul, hs]

/-- **The `P_H`-equivariant cell calculation and `fiber_compat`**: the determinant of the linear part of the action of `g` on the radical-torus coordinate is
exactly the scalar of `fiber_compat`, so `kappaLit` is the fibre integration of the cell calculation. -/
theorem fiber_compat_torus (n : ℕ) (g : PH) (a : (FibRep n).V) :
    fiberLin n ((torusLinear g).det • (FibRep n).ρ g a) =
      (Dplain (n + 1)).ρ (pibar (QuotientGroup.mk g)) (fiberLin n a) := by
  rw [torusLinear_det]
  exact fiber_compat n g a

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
