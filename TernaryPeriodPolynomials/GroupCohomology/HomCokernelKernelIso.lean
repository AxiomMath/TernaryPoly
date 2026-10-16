module

public import TernaryPeriodPolynomials.GroupCohomology.HomCokernelKernelDegree

@[expose] public section

noncomputable section
namespace TernaryPoly.HomCokernelKernel
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {K L : ChainComplex (Rep.{0} ℚ G) ℕ}
  (i : K ⟶ L) (V : Rep.{0} ℚ G)

/-- The actual degreewise cokernel-descent isomorphism. -/
def componentIso (n : ℕ) :
    (homCochains (cokernel i) V).X n ≅ (kernel (homPullback i V)).X n where
  hom := (toKernel i V).f n
  inv := inverseDegree i V n
  hom_inv_id := toKernel_inverseDegree i V n
  inv_hom_id := inverseDegree_toKernel i V n

/-- Actual quotient precomposition and explicit degreewise descent give the literal
Hom-cokernel/restriction-kernel cochain isomorphism, with arbitrary rational coefficients. -/
def cochainIso : homCochains (cokernel i) V ≅ kernel (homPullback i V) :=
  HomologicalComplex.Hom.isoOfComponents (componentIso i V)
    (fun a b _ => (toKernel i V).comm a b)

/-- The forward comparison is actual quotient precomposition into the kernel. -/
theorem cochainIso_hom : (cochainIso i V).hom = toKernel i V := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- The inverse components are the explicitly defined cokernel descents. -/
theorem cochainIso_inv_f (n : ℕ) : (cochainIso i V).inv.f n = inverseDegree i V n := rfl

/-- The forward comparison includes as literal quotient precomposition. -/
theorem cochainIso_hom_inclusion :
    (cochainIso i V).hom ≫ kernel.ι (homPullback i V) = homPullback (cokernel.π i) V := by
  rw [cochainIso_hom,toKernel_inclusion]

/-- The inverse comparison recovers the actual ambient cochain. -/
theorem cochainIso_inv_projection :
    (cochainIso i V).inv ≫ homPullback (cokernel.π i) V = kernel.ι (homPullback i V) := by
  rw [← cochainIso_hom_inclusion,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

/-- Literal evaluation of the forward comparison. -/
theorem cochainIso_hom_apply (n : ℕ) (c : (cokernel i).X n ⟶ V) :
    kernelValue i V n ((cochainIso i V).hom.f n c) = (cokernel.π i).f n ≫ c :=
  toKernel_apply i V n c

/-- Literal evaluation of the inverse comparison. -/
theorem cochainIso_inv_apply (n : ℕ) (x : (kernel (homPullback i V)).X n) :
    (cochainIso i V).inv.f n x =
      RelativeChainHomotopy.degreeDesc i n (kernelValue i V n x) (kernelValue_condition i V n x) := rfl

/-- The literal comparison induces an isomorphism in every cohomological degree. -/
def cohomologyIso (n : ℕ) :
    (homCochains (cokernel i) V).homology n ≅ (kernel (homPullback i V)).homology n :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso (cochainIso i V)

end TernaryPoly.HomCokernelKernel
