module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Eigenperiod
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.OrdinaryExtensionSeeds

@[expose] public section

/-!
# Lemma 4.5: the pole removal, literal

Formalized by Claude Sonnet 5.5.  Paper: Lemma 4.5 proof.

The Hom-model proof that the odd seed system extends to a polynomial (`TernaryPoly.symmetric_odd_polynomial_seeds`) uses the analytic gate
`ActualIntertwining` only to know that every full-level single-pole Hom has zero residue Hom (`BinaryLiftableResiduePolynomial.residueHom_eq_zero`).
Here that vanishing is `residueHom_eq_zero_h`, obtained from `liftableResidueHoms_eq_bot_of_homology` (`LnHom n = 0` on literal group homology):
the trace cycle `S = ∑ F(r)` is a class of `H₃(G, ℳ_n ⊗ det)`, its residue `2 q_0` vanishes, so `q_0 = 0` and the three seeds are polynomial
(`lowest_eq_zero_h`, `symmetric_odd_period_tower_lowest_zero_h`, `symmetric_odd_polynomial_seeds_h`).  The eigenperiod argument behind
`LnHom_eq_bot` still uses the analytic Hecke compatibility `periodMap_hecke` of the cited Pasol-Popa result, fed by the homology operator.
-/

open MvPolynomial
noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Full

open TernaryPoly TernaryPoly.BinaryLiftableResidueDetection TernaryPoly.OrdinaryFullCoefficient
open TernaryPoly.SymmetricRationalTrace TernaryPoly.SymmetricOddRationalSeed TernaryPoly.SymmetricOddRationalTower
open TernaryPoly.SinglePoleSupport TernaryPoly.BinaryLiftableResiduePolynomial

section Homology

variable {n k : ℕ}

/-- Every single-pole Hom has zero residue Hom, from the homology-literal vanishing of `𝓛_n` (no analytic gate). -/
theorem residueHom_eq_zero_h (n : ℕ) (F : SinglePoleHom n (-1)) : residueHom n (-1) F = 0 :=
  (Submodule.mem_bot ℚ).mp (liftableResidueHoms_eq_bot_of_homology n ▸ (⟨F, rfl⟩ : residueHom n (-1) F ∈ liftableResidueHoms n (-1)))

theorem residue_value_eq_zero_h (n : ℕ) (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    SinglePole.residue n (F.val c) = 0 := by
  have he := congrArg (fun G : ResidueHom n (-1) => G.val c) (residueHom_eq_zero_h n F)
  exact he

theorem value_polynomial_h (n : ℕ) (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    ∃ p : SinglePole.V n, F.val c = SinglePole.polynomialInclusion n p := by
  have : F.val c ∈ (SinglePole.polynomialInclusion n).range := by
    rw [← SinglePole.residue_exact]; exact residue_value_eq_zero_h n F c
  obtain ⟨p, hp⟩ := this
  exact ⟨p, hp.symm⟩

theorem relations_polynomial_h (n : ℕ) (x : SinglePole.singlePole n)
    (hx : Relations (SinglePole.singlePoleAction n (-1)) x) :
    ∃ p : SinglePole.V n, x = SinglePole.polynomialInclusion n p := by
  obtain ⟨F, hF⟩ := (exists_hom_iff (SinglePole.singlePoleAction n (-1)) x).mpr hx
  obtain ⟨p, hp⟩ := value_polynomial_h n F (OrdinaryApartmentPresentation.frameCycle 1)
  exact ⟨p, hF.symm.trans hp⟩

theorem homogeneousTrace_polynomial_h
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i, (q i).IsHomogeneous (n + 1 - 2 * (i : ℕ)))
    (l : Fin k → TP) (hl : ∀ i, binaryPeriodLift (q i) = (X 0 + X 1 + X 2) * l i)
    (he : f = ∑ i : Fin k, (X 0 + X 1 + X 2) ^ (2 * (i : ℕ)) * l i)
    (hr : PeriodRelations f) (hs : S f = f) :
    ∃ p : SinglePole.V n, homogeneousTrace f hf q hq hd = SinglePole.polynomialInclusion n p :=
  relations_polynomial_h n _ (homogeneousTrace_relations f hf q hq hd l hl he hr hs)

/-- **The lowest period vanishes**, with the premise supplied by literal homology (`LnHom_eq_bot`) instead of `ActualIntertwining`. -/
theorem lowest_eq_zero_h
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i, (q i).IsHomogeneous (n + 1 - 2 * (i : ℕ)))
    (l : Fin k → TP) (hl : ∀ i, binaryPeriodLift (q i) = (X 0 + X 1 + X 2) * l i)
    (he : f = ∑ i : Fin k, (X 0 + X 1 + X 2) ^ (2 * (i : ℕ)) * l i)
    (hr : PeriodRelations f) (hs : S f = f) : lowest q = 0 := by
  obtain ⟨p, hp⟩ := homogeneousTrace_polynomial_h f hf q hq hd l hl he hr hs
  have hz := coordinateResidue_homogeneousTrace f hf q hq hd 0
  rw [hp, SinglePoleCoordinate.coordinateResidue_polynomial] at hz
  have hb : lowestHomogeneous q hd = 0 :=
    (smul_eq_zero.mp hz.symm).resolve_left (by norm_num)
  exact congrArg Subtype.val hb

end Homology

/-- **The pole removal for the odd symmetric seed system, literal**: the finite tower of an odd homogeneous symmetric
period polynomial in the Todd kernel has vanishing lowest period.  The only analytic input of the Hom-model proof
(`ActualIntertwining`) is replaced by the homology-literal `LnHom n = 0`. -/
theorem symmetric_odd_period_tower_lowest_zero_h {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    ∃ k : ℕ, ∃ q : Fin k → MvPolynomial (Fin 2) ℚ, ∃ l : Fin k → TernaryPolynomial,
      (∀ i, SymmetricBinaryPeriodRelations (q i) ∧
        (q i).IsHomogeneous (n + 1 - 2 * (i : ℕ)) ∧
        binaryPeriodLift (q i) = (X 0 + X 1 + X 2) * l i) ∧
      f = ∑ i : Fin k, (X 0 + X 1 + X 2) ^ (2 * (i : ℕ)) * l i ∧ lowest q = 0 := by
  obtain ⟨k, q, l, hq, he⟩ := symmetric_odd_period_tower hf hn hrel.1 hs hJ
  refine ⟨k, q, l, hq, he, ?_⟩
  exact lowest_eq_zero_h f hf q (fun i => (hq i).1) (fun i => (hq i).2.1) l (fun i => (hq i).2.2) he hrel hs

/-- **The odd seed system extends to a polynomial** (the possible pole in `P` disappears, all three seeds are polynomial), derived from
literal homology. -/
theorem symmetric_odd_polynomial_seeds_h {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    ∃ P Q : TernaryPolynomial, SymmetricSeedData f P Q := by
  obtain ⟨k, q, l, hq, he, hzero⟩ := symmetric_odd_period_tower_lowest_zero_h hf hn hrel hs hJ
  refine ⟨regular q (X 0) (X 1) (X 2), qPolynomial q (fun i => (hq i).1), ?_⟩
  rw [he]
  exact polynomial_data_of_lowest_zero q (fun i => (hq i).1) l (fun i => (hq i).2.2) hzero

end TernaryPeriodPolynomials.Argument.Lemma45Full
