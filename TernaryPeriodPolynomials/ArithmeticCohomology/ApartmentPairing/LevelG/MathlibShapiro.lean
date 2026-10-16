module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

@[expose] public section


/-!
# Mathlib's Shapiro isomorphism for `M = Ind_K^G E_{n,t}` and the comparison with `shapiroG`

Formalized by Claude Sonnet 5.5.

Paper: "Shapiro's lemma gives `H₃(X̄_G; 𝓜) ≅ H₃(K, E_{n,t})`".  `mathlibShapiro` is Mathlib's group-homology
Shapiro isomorphism `groupHomology.indIso` transported along `TernaryPoly.inducedIso` to the library's 26-covector system
`MG n t = actualCoefficients n (-t)`.  The Lemma 3.3 export uses `shapiroG` (defined through Borel--Serre duality of `G` and
`K`, `Shapiro.lean`); their equality is the precisely stated Prop `ShapiroComparison`, which is shown EQUIVALENT to `H₃ = 0` in `Naturality/ShapiroCor.lean`, together with the corrected scaled comparison.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryActualEvaluation
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

example (n : ℕ) (t : Fin 2) : subgroupCoefficients n (expT t) = EK n t := rfl

open scoped Classical in
/-- Mathlib's Shapiro isomorphism for `M = Ind_K^G E_{n,t}`. -/
def mathlibShapiro (n : ℕ) (t : Fin 2) : groupHomology (MG n t) 3 ≅ groupHomology (EK n t) 3 :=
  ((groupHomology.functor ℚ IntegralGL 3).mapIso (inducedIso n (expT t)).symm) ≪≫
    groupHomology.indIso K (subgroupCoefficients n (expT t)) 3

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The comparison between `shapiroG` and Mathlib's Shapiro isomorphism, with scalar `1`.**  As a statement about the two
isomorphisms this Prop is FALSE unless `H₃(G, M_{n,t}) = 0`: it is shown in `Naturality/ShapiroCor.lean` that
`mathlibShapiro z = [G:K] • shapiroG z` (`mathlibShapiro_eq_index_smul`), hence `ShapiroComparison n t ↔ ∀ z, z = 0`
(`shapiroComparison_iff_trivial`).  The correct comparison is `shapiroComparison_scaled`:
`H3_K_equiv n t ((mathlibShapiro n t).hom z) = [G:K] • frobenius n t (thetaG (MG n t) z)`.  The factor is the index of the stabilizer
`K` of the distinguished covector: Mathlib's isomorphism has inverse `Cor_K^G ∘ ι_*` (unnormalised), while `Θ^G` and `Θ^K` are
normalised by averaging over `G/Γ(6)` and `K/Γ(6)`.  The Prop is kept as the interface it was; nothing depends on it. -/
def ShapiroComparison (n : ℕ) (t : Fin 2) : Prop :=
  ∀ z : groupHomology (MG n t) 3,
    H3_K_equiv n t ((mathlibShapiro n t).hom z) = frobenius n t (thetaG (MG n t) z)

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- The comparison obligation is equivalent to `shapiroG = mathlibShapiro` pointwise. -/
theorem shapiroG_eq_mathlib_iff (n : ℕ) (t : Fin 2) :
    ShapiroComparison n t ↔ ∀ z, shapiroG n t z = (mathlibShapiro n t).hom z := by
  constructor
  · intro h z
    apply (H3_K_equiv n t).injective
    rw [h z]
    unfold shapiroG
    simp
  · intro h z
    rw [← h z]
    unfold shapiroG
    simp

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
