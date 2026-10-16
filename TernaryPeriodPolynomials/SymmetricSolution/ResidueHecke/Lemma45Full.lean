module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Lemma45Literal
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Eigenperiod
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.PoleRemoval
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.OrdinaryExtensionSeeds

@[expose] public section


/-!
# Lemma 4.5 (`lem:residue-period`) and its proof, on literal group homology

Formalized by Claude Sonnet 5.5.  The paper, Lemma 4.5, its proof, the eigenperiod
argument and the removal of the pole.

`lemma_4_5_full n` bundles, for the module `ℛ_n ⊗ det` (`ResRep n`), `ℳ_n ⊗ det` (`MRep n`) and `G = GL₃(ℤ)`:

1. sentences 1-6 of the lemma (`Statements.Lemma45Literal.lemma_4_5_literal`): the residue cycle `F_q`, the inverse reading `q(b,c)`,
   `[a c^n] q = 0` on `𝓛_n`, stability under `T₃(p,1)` and under the homology operator `T₂(p)`;
2. the complex transport: `𝓛_n ⊗_ℚ ℂ ⊆ ℬ_{n+1} ⊗ ℂ` is stable under the usual analytic prime operator `complexHecke (n+1) diag(p,1)`
   (through the literal homology `T₂(p)` and the unconditional bridge `T₂(p) = p^{d+1} periodHecke`), and killed by `[X Y^{d-1}]`;
3. the eigenperiod formula `eq:period-extreme-L`: `[X Y^{d-1}] oddPeriod h = -d i^d ∫_0^∞ h(it) t^{d-1} dt`-moment
   `= -d i^d Γ(d)(2π)^{-d} L(h,d)`, and the nonvanishing of this coefficient for every nonzero common eigenperiod
   (Lemma 2.5 inside `actual_eigenperiod_extreme_ne_zero`);
4. `𝓛_n ⊗ ℂ = 0` for odd `n` (the eigenperiod argument) and `𝓛_n = 0` on literal homology for every `n`;
5. the pole removal: every class of `H₃(G, ℳ_n ⊗ det)` has literal residue `0`, in particular the trace cycle `S = ∑ F(r)` has
   `res_{a=0} S = 2 q_0 = 0`; the liftable residues of the Hom model vanish; and the downstream conclusion that the odd symmetric period
   data have polynomial seeds (`TernaryPoly.symmetric_odd_polynomial_seeds`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma45Full

open MvPolynomial TernaryPoly TernaryPoly.BinaryComplexPeriod TernaryPoly.OrdinaryResiduePeriod
open TernaryPoly.SymmetricOddRationalTower TernaryPoly.BinaryLiftableResiduePolynomial
open TernaryPeriodPolynomials.Argument.Lemma45Full TernaryPeriodPolynomials.Argument.Lemma45Literal
  TernaryPeriodPolynomials.Argument.AppendixBResidue

/-- **Lemma 4.5 on literal homology, complete** (see the module documentation). -/
theorem lemma_4_5_full (n : ℕ) :
    -- (1) sentences 1-6 of the lemma on literal homology
    ((∀ q : periodSpace (n + 1), ∃! x : groupHomology (ResRep n) 3, resHLit n x = q ∧
        (H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) = Lemma45Literal.Fq n q) ∧
      (∀ x : groupHomology (ResRep n) 3, ((resHLit n x).val : SinglePoleCoordinate.BinaryV (n + 1)) =
        SinglePoleCoordinate.literalFiberMap n 0
          ((H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) (OrdinaryResidueSupport.axis 0))) ∧
      (Lemma45Literal.LnHom n = (OrdinaryFullCoefficient.liftableResidueHoms n (-1)).map (periodEquiv n).toLinearMap) ∧
      (∀ q ∈ Lemma45Literal.LnHom n, (q.val : SinglePoleCoordinate.BinaryV (n + 1)).val.coeff (Finsupp.single 0 1 + Finsupp.single 1 n) = 0) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ Lemma45Literal.LnHom n, Lemma45Literal.T3B p n q ∈ Lemma45Literal.LnHom n) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ Lemma45Literal.LnHom n, Lemma45Literal.T2B p n q ∈ Lemma45Literal.LnHom n)) ∧
    -- (2) complex transport of `𝓛_n` and stability under the analytic prime operators
    (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ LnC n,
      complexHecke (n + 1) (BinaryRationalHeckePrime.primeDiagonal p) q ∈ LnC n) ∧
    (∀ q ∈ LnC n, extreme ℂ (n + 1) q = 0) ∧
    -- (4) the eigenperiod argument and `𝓛_n = 0`
    (Odd n → LnC n = ⊥) ∧ LnHom n = ⊥ ∧
    -- (5) the residue removal on literal homology
    (∀ x : groupHomology (MRep n) 3, resHLit n (resImage n x) = 0) ∧
    (∀ S : OrdinaryFullCoefficient.SinglePoleHom n (-1),
      SinglePoleCoordinate.literalFiberMap n 0
        (((OrdinaryFullCoefficient.residueHom n (-1) S).val (OrdinaryApartmentPresentation.frameCycle 1))
          (OrdinaryResidueSupport.axis 0)) = 0) ∧
    OrdinaryFullCoefficient.liftableResidueHoms n (-1) = ⊥ :=
  ⟨Statements.Lemma45Literal.lemma_4_5_literal n, fun p _ q hq => LnC_stable p n q hq, LnC_extreme n, LnC_eq_bot n, LnHom_eq_bot n,
    residue_of_top_class_zero n, top_cycle_literal_residue_zero n, liftableResidueHoms_eq_bot_of_homology n⟩

/-- **The eigenperiod formula and its nonvanishing** (`eq:period-extreme-L`, Lemma 2.5), independent of `n`. -/
theorem eigenperiod_extreme :
    (∀ (d : ℕ), 0 < d → ∀ (h : BinaryCuspPeriod.Forms d),
      (BinaryCuspPeriod.oddPeriod h).coeff (BinaryCuspPeriod.exponent d 1) =
        -(d : ℂ) * Complex.I ^ d * BinaryCuspPeriod.moment h (d : ℂ) ∧
      BinaryCuspPeriod.moment h (d : ℂ) = Complex.Gamma (d : ℂ) / (2 * (Real.pi : ℂ)) ^ d *
        ModularForm.L (BinaryCuspPeriod.weight_pos d) h (d : ℂ)) ∧
    (∀ (d : ℕ), Even d → ∀ (q : space ℂ d), q ≠ 0 → ∀ a : Nat.Primes → ℂ,
      (∀ p, BinaryCuspPeriodDetection.primePeriodHecke d p q = a p • q) → extreme ℂ d q ≠ 0) :=
  ⟨fun _ hd h => ⟨BinaryCuspPeriod.coeff_oddPeriod_extreme hd h, BinaryCuspPeriod.moment_nat_eq hd h⟩,
    fun d hd q hq a ha => BinaryCuspPeriodDetection.actual_eigenperiod_extreme_ne_zero d hd
      (BinaryLiftableResidueDetection.actualIntertwining d hd) q hq a ha⟩

/-- **The pole removal downstream**: odd homogeneous symmetric period data in the Todd kernel have polynomial seeds. -/
theorem pole_removal_seeds {f : TernaryPolynomial} {n : ℕ} (hf : MvPolynomial.IsHomogeneous f n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    ∃ P Q, SymmetricSeedData f P Q :=
  symmetric_odd_polynomial_seeds hf hn hrel hs hJ

/-- **The pole removal, literal**: the odd seed system extends to a polynomial, with the vanishing of the lowest period
derived from `LnHom n = 0` on literal group homology (`liftableResidueHoms_eq_bot_of_homology`) instead of the Hom-model gate. -/
theorem pole_removal_seeds_literal {f : TernaryPolynomial} {n : ℕ} (hf : MvPolynomial.IsHomogeneous f n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    ∃ P Q, SymmetricSeedData f P Q :=
  symmetric_odd_polynomial_seeds_h hf hn hrel hs hJ

/-- The finite tower of such an `f` has vanishing lowest period (literal form). -/
theorem pole_removal_lowest_zero_literal {f : TernaryPolynomial} {n : ℕ} (hf : MvPolynomial.IsHomogeneous f n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    ∃ k : ℕ, ∃ q : Fin k → MvPolynomial (Fin 2) ℚ, ∃ l : Fin k → TernaryPolynomial,
      (∀ i, SymmetricBinaryPeriodRelations (q i) ∧ (q i).IsHomogeneous (n + 1 - 2 * (i : ℕ)) ∧
        binaryPeriodLift (q i) = (X 0 + X 1 + X 2) * l i) ∧
      f = ∑ i : Fin k, (X 0 + X 1 + X 2) ^ (2 * (i : ℕ)) * l i ∧ lowest q = 0 :=
  symmetric_odd_period_tower_lowest_zero_h hf hn hrel hs hJ

/-- **Lemma 4.5, sentences 1-6 and the proof** in one statement. -/
theorem lemma_4_5_all (n : ℕ) :
    (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ Lemma45Literal.LnHom n, Lemma45Literal.T2B p n q ∈ Lemma45Literal.LnHom n) ∧
    LnHom n = ⊥ :=
  ⟨fun p _ q hq => LnHom_binary_stable_literal p n q hq, LnHom_eq_bot n⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma45Full
