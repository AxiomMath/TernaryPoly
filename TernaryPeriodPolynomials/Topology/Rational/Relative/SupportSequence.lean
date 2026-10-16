module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSupportedExact
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportBiprod
public import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree

section Diagonal
variable {C : Type*} [Category C] [Abelian C]

/-- The actual split signed diagonal sequence of an object with itself. -/
def diagonalRow (M : C) : ShortComplex C :=
  ShortComplex.mk (biprod.lift (𝟙 M) (-(𝟙 M))) (biprod.desc (𝟙 M) (𝟙 M)) (by simp)

/-- The four components give the literal signed diagonal splitting identity. -/
theorem diagonal_split_identity (M : C) :
    (biprod.fst ≫ biprod.lift (𝟙 M) (-(𝟙 M)) : M ⊞ M ⟶ M ⊞ M) +
      biprod.desc (𝟙 M) (𝟙 M) ≫ biprod.inr = 𝟙 (M ⊞ M) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [Preadditive.add_comp, Preadditive.comp_add]

/-- A literal splitting of the signed diagonal sequence. -/
def diagonalSplitting (M : C) : (diagonalRow M).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := by simp [diagonalRow]
  s_g := by simp [diagonalRow]
  id := diagonal_split_identity M

end Diagonal
variable {X : Type} [TopologicalSpace X]

/-- The actual supported intersection and small sum form their canonical quotient short exact sequence. -/
abbrev smallRow (U V : Set X) := RelativeChainSequence.sequence (supportedDiagonal U V)

/-- The literal map from supported intersection/sum chains into the ambient diagonal sequence. -/
def smallToDiagonal (U V : Set X) : smallRow U V ⟶ diagonalRow (chains X) where
  τ₁ := supportedInclusion (U ∩ V)
  τ₂ := biprod.map (supportedInclusion U) (supportedInclusion V)
  τ₃ := supportedSmallSumInclusion U V
  comm₁₂ := by
    apply biprod.hom_ext <;>
      simp only [diagonalRow, smallRow, RelativeChainSequence.sequence, supportedDiagonal,
        Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, Category.comp_id,
        Preadditive.comp_neg, Preadditive.neg_comp]
    · ext n c
      rfl
    · congr 1
  comm₂₃ := by
    change biprod.map (supportedInclusion U) (supportedInclusion V) ≫
      biprod.desc (𝟙 _) (𝟙 _) = cokernel.π (supportedDiagonal U V) ≫ supportedSmallSumInclusion U V
    rw [supportedSmallSumInclusion, cokernel.π_desc]
    apply biprod.hom_ext' <;> simp [supportedSum]

/-- The actual componentwise quotient sequence underlying relative-support Mayer–Vietoris. -/
def quotientChainRow (U V : Set X) := quotientRow (smallToDiagonal U V)

/-- The relative-support quotient row is genuinely short exact at chain level. -/
theorem quotientChainRow_shortExact (U V : Set X) : (quotientChainRow U V).ShortExact := by
  have : Mono (smallToDiagonal U V).τ₃ := inferInstanceAs (Mono (supportedSmallSumInclusion U V))
  exact quotientRow_shortExact (smallToDiagonal U V)
    (RelativeChainSequence.shortExact (supportedDiagonal U V)) (diagonalSplitting (chains X)).shortExact

/-- Every degree of the actual rational quotient sequence has a genuine linear splitting. -/
def quotientDegreeSplitting (U V : Set X) (n : ℕ) :
    ((quotientChainRow U V).map (eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)).Splitting :=
  ((quotientChainRow_shortExact U V).map_of_exact (eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)).splittingOfProjective

end TernaryPoly.RationalRelativeSupport
