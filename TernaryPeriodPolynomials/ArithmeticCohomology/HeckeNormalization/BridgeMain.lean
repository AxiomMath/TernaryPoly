module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeCosets

@[expose] public section


/-!
# B1 from the interface statements: `HomologyHomBridge p d (p^(d+1))`

Formalized by Claude Sonnet 5.5.

`bridge_of_interfaces`: granting `L1 d` (Frobenius duality), `L2 p` (transposition), `L3 p` (dual lift), `L4 p` (the transposed lift
covers the identity) and `L5 p d` (the Frobenius-form Hecke formula), the homology `T₂(p)` transported to the period space is
`p^(d+1) • periodHecke d (diag(p,1))`.  The proof is the bookkeeping: descent of `Φ` to `F` (`descend`), the
coset identification and the pointwise summand identity (`homT_eq`), the central scaling of the Hom operator (`hecke_C1_neg`)
and the cancellation of the normalisation `κ` and of the factor `2 = piL E0 / reference`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology

theorem bridge_of_interfaces (p d : ℕ) [Fact p.Prime] (h1 : L1 d) (h2 : L2 p) (h3 : L3 p) (h4 : L4 p)
    (h5 : L5 p d) : HomologyHomBridge p d ((p : ℚ) ^ (d + 1)) := by
  obtain ⟨F0⟩ := h1
  obtain ⟨s⟩ := h3
  obtain ⟨l, hl⟩ := h2 s
  have hov := h4 s l hl
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply LinearMap.ext
  intro q
  let y := (periodEquivHomology d).symm q
  have hq : edge2 (Dplain d) y = q.val := by
    have := congrArg Subtype.val ((periodEquivHomology d).apply_symm_apply q)
    exact this
  obtain ⟨F, hF⟩ := descend d ((F0.frob y : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) (F0.frob y).2
  have e5 := h5 F0 s l hl hov y
  rw [F0.eval ((heckeOp (binDatum p) (binMod d) 1).hom y), homT_eq p s d F _ hF] at e5
  have hE0 : ((F0.frob y : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) E0 = F0.κ • q.val := by
    rw [F0.eval, hq]
  have hFref : F.val reference = (F0.κ / 2) • q.val := by
    have h2 : ((F0.frob y : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) E0 = (2 : ℚ) • F.val reference := by
      rw [hF, piL_E0, map_smul]
    rw [hE0] at h2
    rw [div_eq_inv_mul, mul_smul, h2, smul_smul]
    norm_num
  have hqF : periodEquiv d F = (F0.κ / 2) • q := Subtype.ext hFref
  have hH := BinaryRationalHecke.periodHecke_evaluation d (BinaryRationalHeckePrime.primeDiagonal p) F
  rw [hqF, map_smul] at hH
  have hHv : (BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
      (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) F).val reference =
      (F0.κ / 2) • ((BinaryRationalHecke.periodHecke d (BinaryRationalHeckePrime.primeDiagonal p) q).val) := by
    have := congrArg Subtype.val hH
    exact this.symm
  rw [BridgeHom.hecke_C1_neg p d F, LinearMap.smul_apply, hHv] at e5
  have hk := F0.κ_ne
  have key : F0.κ • edge2 (Dplain d) ((heckeOp (binDatum p) (binMod d) 1).hom y) =
      F0.κ • ((p : ℚ) ^ (d + 1) •
        (BinaryRationalHecke.periodHecke d (BinaryRationalHeckePrime.primeDiagonal p) q).val) := by
    rw [e5]
    simp only [smul_smul]
    congr 1
    field_simp
    ring
  apply Subtype.ext
  exact smul_right_injective _ hk key

/-- **The printed sentence for the paper's homology `T₂(p)`**, granting the five interface statements. -/
theorem printed_sentence_of_interfaces (p d : ℕ) [Fact p.Prime] (hd : Even d) (h1 : L1 d) (h2 : L2 p) (h3 : L3 p)
    (h4 : L4 p) (h5 : L5 p d) : HomologyPrintedSentence p d hd :=
  homologyPrintedSentence_of_bridge hd (bridge_of_interfaces p d h1 h2 h3 h4 h5)

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
