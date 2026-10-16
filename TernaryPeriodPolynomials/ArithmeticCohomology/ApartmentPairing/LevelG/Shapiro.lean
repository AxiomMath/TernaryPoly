module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Descent
public import TernaryPeriodPolynomials.BoundaryComparison.FiberModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.SectorInduction

@[expose] public section


/-!
# Lemma 3.3 at level `G`: coset unfolding (Frobenius reciprocity) and Shapiro's lemma through duality

Formalized by Claude Sonnet 5.5.

Paper: "unfolding a chain over `K\G`
labels the translated basis by its covector `ℓg`.  The functional `φ_λ` selects the identity coset, not the sum of all
covectors".

The library's 26-covector coefficient system `actualCoefficients n e` is `Ind_K^G` of the `K`-representation `E` (the library
`inducedIso`, `coinducedIso`), `evaluation n` is the value at the distinguished covector `ℓ` (the identity coset), and a
`G`-equivariant functional is determined by its evaluation at `ℓ` (`coeff_eq_evaluation`, the other 25 coordinates are translates).
Hence Frobenius reciprocity `Hom_G(St, M) ≃ Hom_K(St, E)` (`frobenius`) and, with Borel--Serre duality for `G` and `K`,
`shapiroG : H₃(G, M) ≃ H₃(K, E_{n,t})` (`t ∈ {0,1}`, determinant exponent `e = -t`) with
`F^K_{Sh z}(ℓ) = evaluation(F^G_z(ℓ))` (`shapiroG_evaluation`): the functional `φ_λ(F) = λ(F(ℓ))` is `λ ∘ evaluation`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryCovectors TernaryPoly.PolynomialGLAction
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

/-- The determinant exponent `e = -t` of the coefficient system `E_{n,t}`. -/
abbrev expT (t : Fin 2) : ℤ := -((t : ℕ) : ℤ)

/-- `(toCoinduced F)(g) = ρ(g)·F(row g)` evaluated through the identity coset: the value of `ρ(g) F` at the
distinguished covector. -/
theorem toCoinduced_eq_evaluation (n : ℕ) (e : ℤ) (F : Coefficients n) (g : IntegralGL) :
    (toCoinduced n e F).val g = evaluation n (coefficientAction n e g F) := by
  have h := congrArg (fun f => f.val 1) (toCoinduced_equivariant n e g F)
  rw [toCoinduced_one] at h
  rw [h]
  change _ = ((toCoinduced n e F).val (1 * g))
  rw [one_mul]

/-- A coefficient is recovered from the evaluations of its translates. -/
theorem coeff_eq_evaluation (n : ℕ) (e : ℤ) (F : Coefficients n) (r : NonzeroCovector) :
    F r = integralAction n e (representative r)⁻¹
      (evaluation n (coefficientAction n e (representative r) F)) := by
  rw [← toCoinduced_eq_evaluation]
  have := congrArg (fun f => f r) (fromCoinduced_toCoinduced n e F)
  exact this.symm

/-- The coefficient system `M = Ind_K^G E_{n,t}` as the library's 26-covector system with determinant exponent `-t`. -/
abbrev MG (n : ℕ) (t : Fin 2) : Rep.{0} ℚ IntegralGL := actualCoefficients n (expT t)

/-- Forward map of Frobenius reciprocity: compose a `G`-equivariant functional into `M` with the evaluation at the
distinguished covector (the identity coset). -/
def frobFwd (n : ℕ) (t : Fin 2) : homKGen stG (MG n t) →ₗ[ℚ] homK (coeff n t) where
  toFun ψ := ⟨(evaluation n) ∘ₗ ψ.1, by
    intro k z
    have h1 := ψ.2 k.val z
    have h2 : stG k.val z = OrdinaryIncidenceChains.complex.cyclesAction k z :=
      OrdinaryFullAction.cycleAction_K k z
    rw [h2] at h1
    change evaluation n (ψ.1 (OrdinaryIncidenceChains.complex.cyclesAction k z)) =
      coeff n t k.val (evaluation n (ψ.1 z))
    rw [h1]
    exact evaluation_action n (expT t) k.val k.2 (ψ.1 z)⟩
  map_add' _ _ := by
    apply Subtype.ext
    ext z
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    ext z
    simp

theorem frobFwd_apply (n : ℕ) (t : Fin 2) (ψ : homKGen stG (MG n t)) (z : OrdinaryIncidenceChains.Cycles) :
    (frobFwd n t ψ).1 z = evaluation n (ψ.1 z) := rfl

theorem frobFwd_injective (n : ℕ) (t : Fin 2) : Function.Injective (frobFwd n t) := by
  intro ψ ψ' h
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  funext r
  have key : ∀ (χ : homKGen stG (MG n t)), (χ.1 z) r =
      integralAction n (expT t) (representative r)⁻¹ ((frobFwd n t χ).1 (stG (representative r) z)) := by
    intro χ
    rw [frobFwd_apply, χ.2 (representative r) z]
    exact coeff_eq_evaluation n (expT t) (χ.1 z) r
  rw [key ψ, key ψ', h]

theorem frobFwd_surjective (n : ℕ) (t : Fin 2) : Function.Surjective (frobFwd n t) := by
  rintro ⟨Φ, hΦ⟩
  have hΦ' : ∀ k z, Φ (OrdinaryIncidenceChains.complex.cyclesAction k z) =
      GoodChainComplex.coefficientAction n (expT t) k (Φ z) := fun k z => hΦ k z
  refine ⟨⟨(inducedPrincipalOrdinaryFunctional n (expT t) Φ hΦ').hom.toLinearMap, ?_⟩, ?_⟩
  · intro g z
    exact Rep.hom_comm_apply (inducedOrdinaryFunctional n (expT t) Φ hΦ') g z
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    exact inducedOrdinaryFunctional_evaluation n (expT t) Φ hΦ' z

/-- **Frobenius reciprocity** `Hom_G(St, Ind_K^G E_{n,t}) ≃ Hom_K(St, E_{n,t})`: the value at the identity coset. -/
def frobenius (n : ℕ) (t : Fin 2) : homKGen stG (MG n t) ≃ₗ[ℚ] homK (coeff n t) :=
  LinearEquiv.ofBijective (frobFwd n t) ⟨frobFwd_injective n t, frobFwd_surjective n t⟩

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **Shapiro's lemma through Borel--Serre duality**: `H₃(X̄_G; 𝓜) = H₃(G, Ind_K^G E_{n,t}) ≃ H₃(K, E_{n,t})`, the composite of
`Θ^G`, Frobenius reciprocity and the inverse of `Θ^K` (`H3_K_equiv`).  Its identification with Mathlib's group-homology Shapiro
isomorphism is not part of the library (recorded as a comparison obligation). -/
def shapiroG (n : ℕ) (t : Fin 2) : groupHomology (MG n t) 3 ≃ₗ[ℚ] groupHomology (EK n t) 3 :=
  (thetaG (MG n t)).trans ((frobenius n t).trans (H3_K_equiv n t).symm)

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
theorem shapiroG_functional (n : ℕ) (t : Fin 2) (z : groupHomology (MG n t) 3) :
    ((H3_K_equiv n t (shapiroG n t z) : homK (coeff n t)) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) =
      evaluation n ∘ₗ (thetaG (MG n t) z : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] MG n t) := by
  unfold shapiroG
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- The value `F_z(ℓ)` of the `K`-level class `Sh(z)` is the identity-coset component of the `G`-level value. -/
theorem shapiroG_evaluation (n : ℕ) (t : Fin 2) (z : groupHomology (MG n t) 3) :
    (H3_K_equiv n t (shapiroG n t z)).1 OrdinaryTopBoundaryComparison.identityApartment =
      evaluation n (topEvaluationG (MG n t) z) := by
  rw [show ((H3_K_equiv n t (shapiroG n t z)).1 : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) =
    evaluation n ∘ₗ (thetaG (MG n t) z : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] MG n t) from shapiroG_functional n t z]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
