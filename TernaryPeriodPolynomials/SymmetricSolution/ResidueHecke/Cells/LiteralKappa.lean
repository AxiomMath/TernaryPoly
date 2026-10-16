module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.PHLevi
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.HSIso
public import TernaryPeriodPolynomials.BoundaryComparison.BinaryDuality
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.DualityG

@[expose] public section


/-!
# Lemma B.1: the literal `κ`, the algebraic composite `edge₂ ∘ κ ∘ Sh`, and the comparison with `res_H`

Formalized by Claude Sonnet 5.5.  Uses `PHLevi`
(matrix structure of `P_H`) and the `HochschildSerre` development.

**Proved (group homology only, no geometry).**

* `kappaLit n : H₃(P_H, 𝓡_{n,H} ⊗ det⁻¹) ≃ₗ[ℚ] H₁(GL₂(ℤ), D_{n+1})` (Mathlib's `groupHomology`), the Hochschild-Serre isomorphism
  of the split extension `1 → ℤ² → P_H → GL₂(ℤ) ⋉ {±1}`: the determinant factor `det C` of the twisted residue action and the
  inverse-conjugation factor on `H₂(ℤ²)` cancel (`deltaG_eq`: the conjugation `g` acts on `U ≅ ℤ²` by `λ⁻¹C`, of determinant `det C`
  since `λ = ±1`; `fiber_compat`);
* `shLit n`: Shapiro; `residuePeriodAlg n = edge₂ ∘ κ ∘ Sh : H₃(G, 𝓡_n ⊗ det⁻¹) ≃ₗ[ℚ] ℬ_{n+1}` (period space).

**The residue comparison.** `PHCompat n`: `edge₂ ∘ κ ∘ Sh = c · res_H` for a fixed `c ≠ 0`, where
`res_H = resH ∘ H3_G_equiv` reads the residue of the value on the identity apartment of the Borel-Serre dual. It identifies the library's cap-product duality with the Hochschild-Serre/cellular
coordinates of `P_H`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.SinglePoleCoordinate TernaryPoly.SinglePole
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GroupHomology

instance binaryV_finite (d : ℕ) : Module.Finite ℚ (BinaryV d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg (σ := Fin 2) (R := ℚ) d)

/-- `literalFiberMap n 0` as a linear equivalence. -/
def fiberLin (n : ℕ) : (FibRep n).V ≃ₗ[ℚ] (Dplain (n + 1)).V :=
  LinearEquiv.ofBijective (literalFiberMap n 0)
    ⟨literalFiberMap_injective n 0, literalFiberMap_surjective n 0⟩

instance fibRep_finite (n : ℕ) : Module.Finite ℚ (FibRep n).V :=
  Module.Finite.equiv (fiberLin n).symm

open TernaryPeriodPolynomials.Argument.HochschildSerre (muG eU_muG deltaG omegaZ)

theorem muG_eU (g : PH) (v : Multiplicative (Fin 2 → ℤ)) :
    muG AppendixBResidue.U AppendixBResidue.eU g v =
      Multiplicative.ofAdd (conjVec g (Multiplicative.toAdd v)) := by
  apply AppendixBResidue.eU.injective
  have h1 := eU_muG AppendixBResidue.U AppendixBResidue.eU g v
  rw [h1]
  apply Subtype.ext
  rw [conjN_coe, conj_eU]

theorem deltaG_eq (g : PH) :
    deltaG AppendixBResidue.eU g = (((pi g).val.det : ℤ) : ℚ) := by
  unfold deltaG omegaZ
  rw [muG_eU, muG_eU]
  have hl : ((lamHom g : ℤˣ) : ℤ) * ((lamHom g : ℤˣ) : ℤ) = 1 := by
    rcases lam_cases g with h | h <;> rw [h] <;> norm_num
  simp [conjVec, HochschildSerre.e1, HochschildSerre.e2, Matrix.det_fin_two]
  have hlQ : (((lamHom g : ℤˣ) : ℤ) : ℚ) * (((lamHom g : ℤˣ) : ℤ) : ℚ) = 1 := by exact_mod_cast hl
  linear_combination (((((pi g).val 0 0 : ℤ) : ℚ)) * (((pi g).val 1 1 : ℤ) : ℚ) -
    (((pi g).val 1 0 : ℤ) : ℚ) * (((pi g).val 0 1 : ℤ) : ℚ)) * hlQ

theorem homogeneousAction_neg_one (d : ℕ) (h : BinaryModularSymbol.GL2) (q : BinaryV d) :
    BinaryModularSymbolCoefficients.homogeneousAction d (-1) h q =
      (((Matrix.GeneralLinearGroup.det h : ℚˣ) : ℚ))⁻¹ •
        BinaryModularSymbolCoefficients.homogeneousAction d 0 h q := by
  apply Subtype.ext
  simp [BinaryModularSymbolCoefficients.homogeneousAction_coe,
    BinaryModularSymbolCoefficients.action_apply, BinaryModularSymbolCoefficients.determinantCharacter]

theorem fiber_compat (n : ℕ) (g : PH) (a : (FibRep n).V) :
    fiberLin n (deltaG AppendixBResidue.eU g • (FibRep n).ρ g a) =
      (Dplain (n + 1)).ρ (pibar (QuotientGroup.mk g)) (fiberLin n a) := by
  have h := fiberRep_literal n g a
  have hdet : (((Matrix.GeneralLinearGroup.det (BinaryModularSymbol.integral (pi g)) : ℚˣ) : ℚ)) =
      (((pi g).val.det : ℤ) : ℚ) := by
    simp only [BinaryModularSymbol.integral, Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (Int.castRingHom ℚ) (pi g).val).symm
  have hne : (((pi g).val.det : ℤ) : ℚ) ≠ 0 := by
    have : IsUnit (pi g).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (pi g).isUnit
    exact_mod_cast this.ne_zero
  rw [map_smul, deltaG_eq]
  change (((pi g).val.det : ℤ) : ℚ) • literalFiberMap n 0 (fiberRep n g a) =
    BinaryModularSymbolCoefficients.homogeneousAction (n + 1) 0 (BinaryModularSymbol.integral (pi g))
      (literalFiberMap n 0 a)
  rw [h, homogeneousAction_neg_one, hdet, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- **The literal `κ`**: the Hochschild-Serre isomorphism
`H₃(P_H, 𝓡_{n,H} ⊗ det⁻¹) ≃ H₁(GL₂(ℤ), D_{n+1})`, `U ≅ ℤ²` the unipotent radical. -/
def kappaLit (n : ℕ) : groupHomology (FibRep n) 3 ≃ₗ[ℚ] groupHomology (Dplain (n + 1)) 1 :=
  HochschildSerre.hsFarey AppendixBResidue.U (FibRep n) pibar pibar_surjective
    (by have := finite_ker_pibar; exact Set.toFinite _)
    (HochschildSerre.isZero_res_three AppendixBResidue.eU (fun u => FibRep_U n u)) (Dplain (n + 1))
    (HochschildSerre.homologyIsoRes AppendixBResidue.eU (fun u => FibRep_U n u) (Dplain (n + 1)) pibar
      (fiberLin n) (fun g a => fiber_compat n g a))

/-- **`Sh`**: the Shapiro isomorphism `H₃(G, 𝓡_n ⊗ det⁻¹) ≃ H₃(P_H, 𝓡_{n,H} ⊗ det⁻¹)` (`shapiroHomologyIso`). -/
def shLit (n : ℕ) : groupHomology (ResRep n) 3 ≃ₗ[ℚ] groupHomology (FibRep n) 3 :=
  (shapiroHomologyIso n 3).toLinearEquiv

/-- **`edge₂ ∘ κ ∘ Sh`**, purely algebraic (group homology): an isomorphism of `H₃(G, 𝓡_n ⊗ det⁻¹)` onto the period space
`ℬ_{n+1}`. -/
def residuePeriodAlg (n : ℕ) :
    groupHomology (ResRep n) 3 ≃ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  (shLit n).trans ((kappaLit n).trans (Statements.BinaryDuality.periodEquivHomology' (n + 1)))

/-- **`res_H`**: the literal residue coordinate at `a = 0` of the value, on the identity apartment, of the Borel-Serre dual of
a class (`H3_G_equiv`, built from the cap-product duality of the library). -/
def resHLit (n : ℕ) : groupHomology (ResRep n) 3 →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  (resH n).comp (H3_G_equiv n).toLinearMap

/-- **The residue comparison square of Lemma B.1** (`eq:residue-comparison-diagram`): `edge₂ ∘ κ ∘ Sh = c · res_H` for a fixed
nonzero scalar `c` (independent of the class).  It is proved for every `n` by `FaceMain.phCompat_of_tree` with `TreeMapsMain.treeData` (S4). -/
def PHCompat (n : ℕ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ x : groupHomology (ResRep n) 3, residuePeriodAlg n x = c • resHLit n x

/-- The uniform version: one scalar for all `n`. -/
def PHCompatUniform : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ (n : ℕ) (x : groupHomology (ResRep n) 3), residuePeriodAlg n x = c • resHLit n x

end TernaryPeriodPolynomials.Argument.AppendixBResidue
