module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Cone
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]
  {A B : ChainComplex C ℕ} (f : A ⟶ B)
  (r : ∀ n, B.X n ⟶ A.X n) (fr : ∀ n, f.f n ≫ r n=𝟙 _)

include fr in
theorem splitDegree_mono : Mono f :=
  HomologicalComplex.mono_of_mono_f f (fun n => mono_of_mono_fac (fr n))

include fr in
theorem quotientShortExact : (ShortComplex.cokernelSequence f).ShortExact := by
  exact { exact := ShortComplex.cokernelSequence_exact f
          mono_f := splitDegree_mono f r fr
          epi_g := by change Epi (cokernel.π f); infer_instance }

/-- The quotient sequence inherits the specified graded retraction, not an assumed chain splitting. -/
def quotientDegreeSplitting (n : ℕ) :
    ((ShortComplex.cokernelSequence f).map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting := by
  have h := (quotientShortExact f r fr).map_of_exact (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  exact ShortComplex.Splitting.ofExactOfRetraction _ h.exact (r n) (fr n) h.epi_g

def quotientSection (n : ℕ) : (cokernel f).X n ⟶ B.X n := (quotientDegreeSplitting f r fr n).s

theorem quotientSection_g (n : ℕ) : quotientSection f r fr n ≫ (cokernel.π f).f n=𝟙 _ :=
  (quotientDegreeSplitting f r fr n).s_g

theorem quotient_split (n : ℕ) : r n ≫ f.f n + (cokernel.π f).f n ≫ quotientSection f r fr n=𝟙 _ :=
  (quotientDegreeSplitting f r fr n).id

/-- A specified graded split injection has its actual cokernel as its chain homotopy cofiber. -/
def quotientConeEquiv : _root_.HomotopyEquiv (homotopyCofiber f) (cokernel f) :=
  Cone.equivalence (ShortComplex.cokernelSequence f) r fr
    (quotientSection f r fr) (quotientSection_g f r fr) (quotient_split f r fr)

variable (S : ShortComplex (ChainComplex C ℕ)) (u : A ⟶ S.X₁) (v : B ⟶ S.X₂)
  (square : u ≫ S.f=f ≫ v)

/-- The literal quotient map into a target short complex extends its given middle arrow. -/
def quotientMap : cokernel f ⟶ S.X₃ := cokernel.desc f (v ≫ S.g) (by
  rw [←Category.assoc,←square,Category.assoc,S.zero,comp_zero])

/-- The full short-complex comparison retains both prescribed geometric maps. -/
def quotientComparison : ShortComplex.cokernelSequence f ⟶ S where
  τ₁ := u
  τ₂ := v
  τ₃ := quotientMap f S u v square
  comm₁₂ := square
  comm₂₃ := (cokernel.π_desc _ _ _).symm

include fr in
theorem quotientMap_quasiIso (hS : S.ShortExact) (hu : QuasiIso u) (hv : QuasiIso v) :
    QuasiIso (quotientMap f S u v square) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (quotientComparison f S u v square)
    (quotientShortExact f r fr) hS hu hv

/-- The actual cone map to a target quotient is built from its explicit chain comparison. -/
def coneMap : homotopyCofiber f ⟶ S.X₃ :=
  (quotientConeEquiv f r fr).hom ≫ quotientMap f S u v square

include fr in
theorem coneMap_quasiIso (hS : S.ShortExact) (hu : QuasiIso u) (hv : QuasiIso v) :
    QuasiIso (coneMap f r fr S u v square) := by
  have : QuasiIso (quotientMap f S u v square) := quotientMap_quasiIso f r fr S u v square hS hu hv
  unfold coneMap
  infer_instance

theorem coneMap_inr : homotopyCofiber.inr f ≫ coneMap f r fr S u v square=v ≫ S.g := by
  change _ ≫ (Cone.projection (ShortComplex.cokernelSequence f) ≫ quotientMap f S u v square)=_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ quotientMap f S u v square)
      (Cone.inr_projection (ShortComplex.cokernelSequence f))).trans (cokernel.π_desc _ _ _))

end TernaryPoly.BoundaryFaceResolutionComparison
