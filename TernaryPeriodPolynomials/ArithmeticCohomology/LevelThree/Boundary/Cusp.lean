module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Boundary.Hecke

@[expose] public section


/-!
# Values of cocycles at the cusp `0`

Tools for computing `β_0(T_p z)`, `β_0(z) = z(L)(0, 1)`:

* `levelElt a b c d`: the element `[[a,b],[c,d]]` of `Γ₁'(3)`
  (`ad - bc = 1`, `c ≡ 0`, `d ≡ 1 mod 3`);
* `eval_levelRep_of_det_one`: for a determinant-one `g ∈ Γ₁'(3)` and `g y = x`,
  `(g v)(x) = v(y)`;
* `ev01_cocycle_pow`: `β_0(z(L^n)) = n β_0(z)`;
* `eval_cusp_value`: if `δ γ = γ L^k`, `δ x = x`, `γ y = x` and `y = c (0, 1)`, then
  `z(δ)(x) = c^m k β_0(z)` -- the value of a cocycle on a parabolic element fixing `x` is
  determined by the class at the cusp `0`;
* `ev01_inv_none`, `ev01_inv_some`: the values at `(0, 1)` of `ρ(α_j)⁻¹ v`:
  `p^{-e} v(α_j (0, 1))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryCusp

open Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators ParabolicBounds FullBound
open LevelThreeCosets LevelThreeHeckeH1 LevelThreeBoundaryFunctional LevelThreeBoundaryHecke
open GeneralEisenstein

section Elements

theorem levelElt_mul_inv (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ) * !![d, -b; -c, a] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet

theorem levelElt_inv_mul (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; c, d] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet

/-- The matrix `[[a,b],[c,d]]` of determinant one, as an element of `GL₂(ℤ)`. -/
def levelEltGL (a b c d : ℤ) (hdet : a * d - b * c = 1) : GL (Fin 2) ℤ :=
  ⟨!![a, b; c, d], !![d, -b; -c, a], levelElt_mul_inv a b c d hdet,
    levelElt_inv_mul a b c d hdet⟩

theorem levelEltGL_coe (a b c d : ℤ) (hdet : a * d - b * c = 1) :
    (levelEltGL a b c d hdet : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := rfl

theorem levelEltGL_mem (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod 3) = 0)
    (hd : (d : ZMod 3) = 1) : levelEltGL a b c d hdet ∈ binaryArithmeticLevel := by
  apply (mem_binaryArithmeticLevel_iff _).mpr
  intro column
  fin_cases column
  · simpa [levelEltGL] using hc
  · simpa [levelEltGL] using hd

/-- **The element `[[a,b],[c,d]]` of `Γ₁'(3)`.** -/
def levelElt (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod 3) = 0)
    (hd : (d : ZMod 3) = 1) : binaryArithmeticLevel :=
  ⟨levelEltGL a b c d hdet, levelEltGL_mem a b c d hdet hc hd⟩

theorem levelElt_coe (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod 3) = 0)
    (hd : (d : ZMod 3) = 1) :
    ((levelElt a b c d hdet hc hd).val : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := rfl

theorem levelElt_det (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod 3) = 0)
    (hd : (d : ZMod 3) = 1) :
    ((levelElt a b c d hdet hc hd).val : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [levelElt_coe, Matrix.det_fin_two_of]
  exact hdet

end Elements

section Values

variable (m : ℕ) (e : ℤ)

/-- The integral matrix of an element of `Γ₁'(3)`. -/
abbrev matZ (g : binaryArithmeticLevel) : Matrix (Fin 2) (Fin 2) ℤ :=
  (g.val : Matrix (Fin 2) (Fin 2) ℤ)

/-- For a determinant-one `g ∈ Γ₁'(3)` with `g y = x`: `(g v)(x) = v(y)`. -/
theorem eval_levelRep_of_det_one (g : binaryArithmeticLevel) (hdet : (matZ g).det = 1)
    (v : Binary.HomogeneousPoly m) (x y : Fin 2 → ℂ)
    (hxy : ∀ i, ∑ j, (((matZ g i j : ℤ)) : ℂ) * y j = x i) :
    eval x (levelRep m e g v : Binary.HomogeneousPoly m).val = eval y v.val := by
  have hdetC : ((GeneralLinearGroup.det (binaryIntegralComplex g.val) : ℂˣ) : ℂ) = 1 := by
    rw [GeneralLinearGroup.val_det_apply]
    have hd := RingHom.map_det (Int.castRingHom ℂ) (matZ g)
    change (RingHom.mapMatrix (Int.castRingHom ℂ) (matZ g)).det = 1
    rw [← hd, hdet, map_one]
  have hx : (binaryIntegralComplex g.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec y = x := by
    funext i
    exact hxy i
  have hinv : ((binaryIntegralComplex g.val)⁻¹ : Binary.GL2).val.mulVec x = y := by
    rw [← hx, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hfun : (fun i => ∑ j, ((binaryIntegralComplex g.val)⁻¹ : Binary.GL2).val i j * x j) =
      y := funext fun i => congrFun hinv i
  change eval x (Binary.homogeneousAction m e (binaryIntegralComplex g.val) v).val = _
  rw [Binary.homogeneousAction_coe, SymFixed.eval_action_of_det e _ hdetC]
  exact congrArg (fun w : Fin 2 → ℂ => eval w v.val) hfun

/-- `β_0(z(L^n)) = n β_0(z)`. -/
theorem ev01_cocycle_pow (z : crossedCocycles (levelRep m e)) (n : ℕ) :
    eval ![0, 1] (z.val (lower 1 ^ n)).val = (n : ℂ) * eval ![0, 1] (z.val (lower 1)).val := by
  induction n with
  | zero =>
    rw [pow_zero, TwoGenerator.cocycle_one z]
    simp
  | succ n ih =>
    rw [pow_succ', TwoGenerator.cocycle_mul z, Submodule.coe_add, map_add, ev01_L e, ih]
    push_cast
    ring

/-- **The value of a cocycle on a parabolic element is determined by the class at the cusp `0`**:
if `δ γ = γ L^k` (all of determinant one), `δ x = x`, `γ y = x` and `y = c (0, 1)`, then
`z(δ)(x) = c^m k β_0(z)`. -/
theorem eval_cusp_value (z : crossedCocycles (levelRep m e)) (δ γ : binaryArithmeticLevel)
    (k : ℕ) (hcomm : δ * γ = γ * lower 1 ^ k) (hδ : (matZ δ).det = 1)
    (hγ : (matZ γ).det = 1) (x : Fin 2 → ℂ) (c : ℂ)
    (hδx : ∀ i, ∑ j, (((matZ δ i j : ℤ)) : ℂ) * x j = x i)
    (hγy : ∀ i, ∑ j, (((matZ γ i j : ℤ)) : ℂ) * (c • (![0, 1] : Fin 2 → ℂ)) j = x i) :
    eval x (z.val δ).val = c ^ m * (k : ℂ) * eval ![0, 1] (z.val (lower 1)).val := by
  have h1 := TwoGenerator.cocycle_mul z δ γ
  have h2 := TwoGenerator.cocycle_mul z γ (lower 1 ^ k)
  rw [hcomm, h2] at h1
  have e1 := congrArg (fun w : Binary.HomogeneousPoly m => eval x w.val) h1
  simp only [Submodule.coe_add, map_add] at e1
  rw [eval_levelRep_of_det_one m e δ hδ _ x x hδx,
    eval_levelRep_of_det_one m e γ hγ _ x (c • (![0, 1] : Fin 2 → ℂ)) hγy,
    SymFixed.eval_smul_of_homogeneous (SymFixed.isHomogeneous _), ev01_cocycle_pow] at e1
  linear_combination (-1 : ℂ) * e1

end Values

section Inverse

variable (m : ℕ) (e : ℤ) (p : Nat.Primes)

/-- Value at `(0, 1)` of `ρ(α_∞)⁻¹ v`: `p^{-e} v(0, ε_p)`. -/
theorem ev01_inv_none (v : Binary.HomogeneousPoly m) :
    eval ![0, 1] (rationalRho m e (heckeRep p none)⁻¹ v : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * eval ![0, (((signP p : ℤˣ) : ℤ) : ℂ)] v.val := by
  have hy : ∀ i, ∑ j, ((heckeRep p none : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℂ)) i j *
      (![0, 1] : Fin 2 → ℂ) j = (![0, (((signP p : ℤˣ) : ℤ) : ℂ)] : Fin 2 → ℂ) i := by
    intro i
    rw [heckeMatC_none]
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [eval_rationalRho_inv m e (heckeRep p none) (p.val : ℂ) (det_none p) v ![0, 1]
    (![0, (((signP p : ℤˣ) : ℤ) : ℂ)] : Fin 2 → ℂ) hy]

/-- Value at `(0, 1)` of `ρ(α_i)⁻¹ v`: `p^{-e} v(i, p)`. -/
theorem ev01_inv_some (i : Fin p.val) (v : Binary.HomogeneousPoly m) :
    eval ![0, 1] (rationalRho m e (heckeRep p (some i))⁻¹ v : Binary.HomogeneousPoly m).val =
      (p.val : ℂ) ^ (-e) * eval ![(i.val : ℂ), (p.val : ℂ)] v.val := by
  have hy : ∀ j, ∑ k, ((heckeRep p (some i) : Matrix (Fin 2) (Fin 2) ℚ).map
      (algebraMap ℚ ℂ)) j k * (![0, 1] : Fin 2 → ℂ) k =
      (![(i.val : ℂ), (p.val : ℂ)] : Fin 2 → ℂ) j := by
    intro j
    rw [heckeMatC_some]
    fin_cases j <;> simp [Fin.sum_univ_two]
  rw [eval_rationalRho_inv m e (heckeRep p (some i)) (p.val : ℂ) (det_some p i) v ![0, 1]
    (![(i.val : ℂ), (p.val : ℂ)] : Fin 2 → ℂ) hy]

end Inverse

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryCusp
