module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeHecke
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.NatScalar
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa

@[expose] public section


/-!
# The identity term of the prime Hecke correspondence under the Hochschild-Serre isomorphism

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open CategoryTheory
open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPoly.OrdinaryResidueParabolic (GL2 binarySubstitute)
open TernaryPoly.SinglePoleCoordinate (Binary)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPeriodPolynomials.Argument.FareyTree

variable (p : ℕ) [Fact p.Prime]

theorem f3_val_00 (h : PH) : ((f3 p h : PH) : IntegralGL).val 0 0 = h.1.val 0 0 :=
  f_val_00 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_10 (h : PH) : ((f3 p h : PH) : IntegralGL).val 1 0 = p * h.1.val 1 0 :=
  f_val_10 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_20 (h : PH) : ((f3 p h : PH) : IntegralGL).val 2 0 = p * h.1.val 2 0 :=
  f_val_20 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_11 (h : PH) : ((f3 p h : PH) : IntegralGL).val 1 1 = h.1.val 1 1 :=
  f_val_11 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_12 (h : PH) : ((f3 p h : PH) : IntegralGL).val 1 2 = h.1.val 1 2 :=
  f_val_12 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_21 (h : PH) : ((f3 p h : PH) : IntegralGL).val 2 1 = h.1.val 2 1 :=
  f_val_21 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem f3_val_22 (h : PH) : ((f3 p h : PH) : IntegralGL).val 2 2 = h.1.val 2 2 :=
  f_val_22 (p := p) ⟨h.1, PH_le_Sp p h.2⟩

theorem lamHom_f3 (h : PH) : lamHom (f3 p h) = lamHom h := by
  apply Units.ext
  exact f3_val_00 p h

theorem pi_f3 (h : PH) : pi (f3 p h) = pi h := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact f3_val_11 p h
  · exact f3_val_12 p h
  · exact f3_val_21 p h
  · exact f3_val_22 p h

theorem uvec_f3 (h : PH) : uvec (f3 p h) = fun i => (p : ℤ) * uvec h i := by
  funext i
  fin_cases i
  · exact f3_val_10 p h
  · exact f3_val_20 p h


theorem f3_mem_U (u : PH) (hu : u ∈ U) : f3 p u ∈ U := by
  rw [mem_U] at hu ⊢
  rw [pi_f3, lamHom_f3]
  exact hu

theorem f3_mul_inv_mem_U (g : PH) : f3 p g * g⁻¹ ∈ U := by
  rw [mem_U]
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_inv, pi_f3, mul_inv_cancel]
  · rw [map_mul, map_inv, lamHom_f3, mul_inv_cancel]

theorem hφU_f3 : ∀ u : U, f3 p (u : PH) ∈ U := fun u => f3_mem_U p u u.2

open TernaryPeriodPolynomials.Argument.HochschildSerre in
theorem muPhi_toAdd (v : Multiplicative (Fin 2 → ℤ)) :
    Multiplicative.toAdd (muPhi (f3 p) (hφU_f3 p) eU v) = fun i => (p : ℤ) * Multiplicative.toAdd v i := by
  have h1 := eU_muPhi (f3 p) (hφU_f3 p) eU v
  have h2 : ((eU (muPhi (f3 p) (hφU_f3 p) eU v) : U) : PH) = f3 p ((eU v : U) : PH) :=
    congrArg Subtype.val h1
  have h3 := congrArg uvec h2
  rw [eU_coe, uvec_radPH, eU_coe, uvec_f3, uvec_radPH] at h3
  exact h3

open TernaryPeriodPolynomials.Argument.HochschildSerre in
theorem omega_f3 :
    (omegaZ (muPhi (f3 p) (hφU_f3 p) eU HochschildSerre.e1) (muPhi (f3 p) (hφU_f3 p) eU HochschildSerre.e2) : ℤ) = (p : ℤ) ^ 2 := by
  unfold omegaZ
  simp only [muPhi_toAdd]
  simp [TernaryPeriodPolynomials.Argument.HochschildSerre.e1, TernaryPeriodPolynomials.Argument.HochschildSerre.e2]
  ring


theorem binarySubstitute_one_apply (q : Binary) :
    binarySubstitute (1 : Matrix (Fin 2) (Fin 2) ℚ) q = q := by
  unfold binarySubstitute
  have : (fun i : Fin 2 => ∑ j : Fin 2, MvPolynomial.C ((1 : Matrix (Fin 2) (Fin 2) ℚ) i j) *
      (MvPolynomial.X j : Binary)) = MvPolynomial.X := by
    funext i
    fin_cases i <;> simp [Matrix.one_apply]
  rw [this]
  exact congrArg (fun f => f q) MvPolynomial.bind₁_X_left

theorem fibreMap_one (n : ℕ) (a : (FibRep n).V) : fibreMap n 1 a = a := by
  apply (fiberLin n).injective
  rw [fiberLin_fibreMap]
  have h1 : ((1 : GL2) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by simp
  have h2 : (((1 : GL2)⁻¹ : GL2) : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by simp
  rw [h1, h2, inv_one, one_smul]
  apply Subtype.ext
  exact binarySubstitute_one_apply _


/-- The coefficient morphism of `f₃`: `ξ₃ = g` acts on the fibre by `fibreMap n 1` (the identity). -/
def c3 (n : ℕ) : FibRep n ⟶ Rep.res (f3 p) (FibRep n) :=
  coeffMor0 n (f3 p) (gInv p) (fibreMap n 1)
    (fun a => lof_fibreMap n (gInv p) (lamP p) 0 1 (gInv_val p) a) (fun h => f3_hf h)

open TernaryPeriodPolynomials.Argument.HochschildSerre in
/-- **The identity term.**  Under the Hochschild-Serre isomorphism `κ`, the `P_H`-level correspondence
`(f₃, c₃)` (`(η,u,D) ↦ (η, pu, D)`, identity on the fibre) acts as the scalar `p²` (the determinant of `u ↦ pu` on the radical). -/
theorem kappaLit_f3 (n : ℕ) (x : groupHomology (FibRep n) 3) :
    kappaLit n (groupHomology.map (f3 p) (c3 p n) 3 x) = ((p : ℚ) ^ 2) • kappaLit n x := by
  have hker : (pibar.ker : Set (PH ⧸ U)).Finite := by
    have := finite_ker_pibar; exact Set.toFinite _
  have : Projective (Rep.res pibar FareyTree.P1) := projective_res_P1 pibar hker
  have : Projective (Rep.res pibar FareyTree.P0) := projective_res_P0 pibar hker
  have h := hsFarey_scalarCoeff (FibRep n) eU pibar pibar_surjective hker
    (isZero_res_three eU (fun u => FibRep_U n u)) (Dplain (n + 1))
    (homologyIsoRes eU (fun u => FibRep_U n u) (Dplain (n + 1)) pibar (fiberLin n)
      (fun g a => fiber_compat n g a))
    (fun u => FibRep_U n u) (f3 p) (c3 p n) (hφU_f3 p) (f3_mul_inv_mem_U p) 1
    (fun x => by rw [one_smul]; exact congrArg (gammaEquiv eU (fun u => FibRep_U n u)) (fibreMap_one n x)) x
  have h2 : (omegaZ (muPhi (f3 p) (hφU_f3 p) eU HochschildSerre.e1)
      (muPhi (f3 p) (hφU_f3 p) eU HochschildSerre.e2) : ℚ) = (p : ℚ) ^ 2 := by
    have := omega_f3 p
    exact_mod_cast this
  rw [h2, mul_one] at h
  exact h

theorem T3_simplify (n k : ℕ) :
    trR (Sx PH (primeDatum p).S 1) (FibRep n) k ≫ groupHomology.map (f0 p) (c0 p n) k =
      groupHomology.map (f3 p) (c3 p n) k :=
  trR_top_map OrdinaryFullAction.integral (Rep.of (residueAction n (-1))) (FibRep n) (lofHom n)
    (lofHom_injective n) (Sx PH (primeDatum p).S 1) (fun h => one_mem_Sx h) (f3 p) (gInv p) (fibreMap n 1)
    (fun a => lof_fibreMap n (gInv p) (lamP p) 0 1 (gInv_val p) a) (fun h => f3_hf h) k


/-- The `x = 1` double coset contributes `p²` under `κ`. -/
theorem kappaLit_T3raw (n : ℕ) (x : groupHomology (FibRep n) 3) :
    kappaLit n ((groupHomology.map (f0 p) (c0 p n) 3).hom ((trR (Sx PH (primeDatum p).S 1) (FibRep n) 3).hom x)) =
      ((p : ℚ) ^ 2) • kappaLit n x := by
  have h := congrArg (fun m => m.hom x) (T3_simplify p n 3)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  exact kappaLit_f3 p n x

end TernaryPeriodPolynomials.Argument.HeckeHomology
