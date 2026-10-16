module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.CoeffGen
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.Parabolic
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa

@[expose] public section


/-!
# The action of the rational stabilizer on the fibre `𝓡_{n,H₀}` and the coefficient morphisms of the `P_H`-level Hecke correspondences

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
  TernaryPoly.OrdinaryResidueParabolic TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPoly.OrdinaryResidueSupport (axis)


/-- The action of an element `blockMatrix lam u C` of the rational stabilizer on the fibre `𝓡_{n,H₀}`, read in the binary
coordinate `fiberLin`: `q ↦ det(C)⁻¹ • q(C⁻¹ ·)`.  (It does not depend on `λ` or `u`.) -/
def fibreMap (n : ℕ) (C : GL2) : (FibRep n).V →ₗ[ℚ] (FibRep n).V :=
  (fiberLin n).symm.toLinearMap ∘ₗ
    ((C.val.det⁻¹ • homogeneousBinarySubstitute (n + 1) (C⁻¹).val) ∘ₗ (fiberLin n).toLinearMap)

theorem fiberLin_fibreMap (n : ℕ) (C : GL2) (a : (FibRep n).V) :
    fiberLin n (fibreMap n C a) = C.val.det⁻¹ • homogeneousBinarySubstitute (n + 1) (C⁻¹).val (fiberLin n a) := by
  simp [fibreMap]

theorem lof_fibreMap (n : ℕ) (ξ : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hξ : ξ.val = blockMatrix lam u C) (a : (FibRep n).V) :
    DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (fibreMap n C a) =
      residueAction n (-1) ξ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a) := by
  obtain ⟨q, rfl⟩ := (numeratorRelations n (axis 0)).mkQ_surjective a
  rw [residueAction_lof n (-1) ξ (axis 0) (axis 0) ((lam : ℚ)⁻¹) (substitute_inverse_denominator ξ lam u C hξ) q]
  congr 1
  apply (fiberLin n).injective
  rw [fiberLin_fibreMap]
  have h1 : fiberLin n ((numeratorRelations n (axis 0)).mkQ q) = scaledRestriction n 0 q := rfl
  have h2 : fiberLin n ((numeratorRelations n (axis 0)).mkQ
      (transformedNumerator n (-1) ξ ((lam : ℚ)⁻¹) q)) =
      scaledRestriction n 0 (transformedNumerator n (-1) ξ ((lam : ℚ)⁻¹) q) := rfl
  rw [h1, h2, scaledRestriction_transformed n ξ lam u C hξ q]


section Matrices

variable (p : ℕ) [Fact p.Prime]

theorem p_ne_zero_rat : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The unit `p⁻¹ ∈ ℚˣ`. -/
def lamP : ℚˣ := Units.mk0 ((p : ℚ)⁻¹) (inv_ne_zero (p_ne_zero_rat p))

/-- `diag(1/p, 1) ∈ GL₂(ℚ)`. -/
def C1 : GL2 :=
  ⟨!![(p : ℚ)⁻¹, 0; 0, 1], !![(p : ℚ), 0; 0, 1],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]⟩

theorem integral_val (k : ModThreeGoodAction.IntegralGL) (i j : Fin 3) :
    (OrdinaryFullAction.integral k).val i j = ((k.val i j : ℤ) : ℚ) := rfl

theorem gInv_val_eq : (gInv p).val = !![(p : ℚ)⁻¹, 0, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem gInv_val : (gInv p).val = blockMatrix (lamP p) (0 : Fin 2 → ℚ) 1 := by
  rw [gInv_val_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix, lamP]

theorem integral_sigma_inv :
    (OrdinaryFullAction.integral sigma)⁻¹ = OrdinaryFullAction.integral sigma := by
  rw [← map_inv, sigma_inv]

theorem xi1_val : (xi1 p).val = blockMatrix 1 (0 : Fin 2 → ℚ) (C1 p) := by
  ext i j
  unfold xi1
  rw [integral_sigma_inv]
  rw [Units.val_mul, Units.val_mul, gInv_val_eq]
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, C1, sigma, integral_val, Matrix.mul_apply, Fin.sum_univ_three]

end Matrices


section Coeff

variable (n : ℕ)

theorem lofHom_injective : Function.Injective (lofHom n).hom := fun _ _ h =>
  DirectSum.of_injective (β := ResidueFiber n) (axis 0) h

/-- The coefficient morphism `Res_j 𝓡_{n,H₀} ⟶ Res_f 𝓡_{n,H₀}` of a `P_H`-level correspondence `(j, f)` whose conjugating
element is `ξ`: `c` is the induced linear map on the fibre, determined by `lof (c a) = ξ · lof a`. -/
def coeffMor {H : Type} [Group H] (j f : H →* PH) (ξ : OrdinaryFullAction.GL3)
    (c : (FibRep n).V →ₗ[ℚ] (FibRep n).V)
    (hc : ∀ a, DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (c a) =
      residueAction n (-1) ξ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a))
    (hf : ∀ h, OrdinaryFullAction.integral ((f h : PH) : ModThreeGoodAction.IntegralGL) =
      ξ * OrdinaryFullAction.integral ((j h : PH) : ModThreeGoodAction.IntegralGL) * ξ⁻¹) :
    Rep.res j (FibRep n) ⟶ Rep.res f (FibRep n) :=
  coeffG OrdinaryFullAction.integral (Rep.of (residueAction n (-1))) (FibRep n) (lofHom n)
    (lofHom_injective n) j f ξ c hc hf

/-- The coefficient morphism `𝓡_{n,H₀} ⟶ Res_f 𝓡_{n,H₀}` for `j = id`. -/
def coeffMor0 (f : PH →* PH) (ξ : OrdinaryFullAction.GL3)
    (c : (FibRep n).V →ₗ[ℚ] (FibRep n).V)
    (hc : ∀ a, DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (c a) =
      residueAction n (-1) ξ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a))
    (hf : ∀ h : PH, OrdinaryFullAction.integral ((f h : PH) : ModThreeGoodAction.IntegralGL) =
      ξ * OrdinaryFullAction.integral (h : ModThreeGoodAction.IntegralGL) * ξ⁻¹) :
    FibRep n ⟶ Rep.res f (FibRep n) :=
  coeffG0 OrdinaryFullAction.integral (Rep.of (residueAction n (-1))) (FibRep n) (lofHom n)
    (lofHom_injective n) f ξ c hc hf

end Coeff


section Pair

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The `P_H`-level coefficient morphism of the correspondence `x = 1`, `ξ = g`. -/
def c0 : Rep.res (Sx PH (primeDatum p).S 1).subtype (FibRep n) ⟶ Rep.res (f0 p) (FibRep n) :=
  coeffMor n (Sx PH (primeDatum p).S 1).subtype (f0 p) (gInv p) (fibreMap n 1)
    (fun a => lof_fibreMap n (gInv p) (lamP p) 0 1 (gInv_val p) a) (fun h => f0_hf h)

/-- The `P_H`-level coefficient morphism of the correspondence `x = σ`, `ξ = σ⁻¹ g σ`. -/
def c1 : Rep.res (Sx PH (primeDatum p).S sigma).subtype (FibRep n) ⟶ Rep.res (f1 (p := p)) (FibRep n) :=
  coeffMor n (Sx PH (primeDatum p).S sigma).subtype (f1 (p := p)) (xi1 p) (fibreMap n (C1 p))
    (fun a => lof_fibreMap n (xi1 p) 1 0 (C1 p) (xi1_val p) a) (fun h => f1_hf h)

theorem one_ne_sigma : (1 : ModThreeGoodAction.IntegralGL) ≠ sigma := by
  intro h
  have := congrArg (fun g : ModThreeGoodAction.IntegralGL => g.val 0 0) h
  simp [sigma] at this

end Pair


section Decomp

variable (p : ℕ) [Fact p.Prime] (n k : ℕ)

/-- **The prime Hecke operator in group homology, restricted to `P_H`.**  Under the Shapiro isomorphism
(`groupHomology.map PH.subtype (lofHom n) k = (shapiroHomologyIso n k).inv`) the homology Hecke operator of
`g = diag(p,1,1)⁻¹` on `H_k(GL₃(ℤ), 𝓡_n)` is the sum of the two `P_H`-level correspondences, for the double cosets `S_p · 1 · P_H`
and `S_p · σ · P_H`. -/
theorem prime_hecke_pair :
    groupHomology.map PH.subtype (lofHom n) k ≫ heckeOp (primeDatum p) (Rep.of (residueAction n (-1))) k =
      (trR (Sx PH (primeDatum p).S 1) (FibRep n) k ≫ groupHomology.map (f0 p) (c0 p n) k ≫
        groupHomology.map PH.subtype (lofHom n) k) +
      (trR (Sx PH (primeDatum p).S sigma) (FibRep n) k ≫ groupHomology.map (f1 (p := p)) (c1 p n) k ≫
        groupHomology.map PH.subtype (lofHom n) k) := by
  exact hecke_mackey_pair PH OrdinaryFullAction.integral (primeDatum p) (Rep.of (residueAction n (-1))) (FibRep n)
    (lofHom n) integral_injective' one_ne_sigma (doubleCosetReps p) 1 sigma (gInv p) (xi1 p) gInv_mul_one
    gInv_mul_sigma (f0 p) (f1 (p := p)) (fun h => f0_hf h) (fun h => f1_hf h) (c0 p n) (c1 p n)
    (fun a => by exact (lof_fibreMap n (gInv p) (lamP p) 0 1 (gInv_val p) a))
    (fun a => by exact (lof_fibreMap n (xi1 p) 1 0 (C1 p) (xi1_val p) a)) k

end Decomp

end TernaryPeriodPolynomials.Argument.HeckeHomology
