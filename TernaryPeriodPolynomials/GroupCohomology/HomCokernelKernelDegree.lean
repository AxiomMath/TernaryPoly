module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyHom
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainHomotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.HomCokernelKernel
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {K L : ChainComplex (Rep.{0} ℚ G) ℕ}
  (i : K ⟶ L) (V : Rep.{0} ℚ G)

/-- Actual ambient cochain represented by an element of the actual restriction-kernel degree. -/
def kernelValue (n : ℕ) (x : (kernel (homPullback i V)).X n) : L.X n ⟶ V :=
  (kernel.ι (homPullback i V)).f n x

/-- The actual ambient cochain represented by a restriction-kernel element kills the subcomplex. -/
theorem kernelValue_condition (n : ℕ) (x : (kernel (homPullback i V)).X n) :
    i.f n ≫ kernelValue i V n x = 0 :=
  congrArg (fun f => f x) (HomologicalComplex.congr_hom (kernel.condition (homPullback i V)) n)

/-- Actual precomposition with the quotient projection lands in the literal restriction kernel. -/
def toKernel : homCochains (cokernel i) V ⟶ kernel (homPullback i V) :=
  kernel.lift (homPullback i V) (homPullback (cokernel.π i) V) (by
    rw [← homPullback_comp,cokernel.condition,EquivariantSingularPairHomotopy.homPullback_zero])

/-- Inclusion of the actual kernel comparison is exactly quotient precomposition. -/
theorem toKernel_inclusion : toKernel i V ≫ kernel.ι (homPullback i V) = homPullback (cokernel.π i) V :=
  kernel.lift_ι _ _ _

/-- The exact evaluation formula for the actual comparison into the restriction kernel. -/
theorem toKernel_apply (n : ℕ) (c : (cokernel i).X n ⟶ V) :
    kernelValue i V n ((toKernel i V).f n c) = (cokernel.π i).f n ≫ c :=
  congrArg (fun f => f c) (HomologicalComplex.congr_hom (toKernel_inclusion i V) n)

/-- The explicit inverse degree map: descend the kernel's actual ambient cochain through the
actual cokernel projection. -/
def inverseDegree (n : ℕ) : (kernel (homPullback i V)).X n ⟶ (homCochains (cokernel i) V).X n :=
  ModuleCat.ofHom {
    toFun := fun x => RelativeChainHomotopy.degreeDesc i n (kernelValue i V n x) (kernelValue_condition i V n x)
    map_add' := fun x y => by
      apply (cancel_epi ((cokernel.π i).f n)).mp
      rw [Preadditive.comp_add,RelativeChainHomotopy.projection_degreeDesc,
        RelativeChainHomotopy.projection_degreeDesc,RelativeChainHomotopy.projection_degreeDesc]
      exact map_add ((kernel.ι (homPullback i V)).f n).hom x y
    map_smul' := fun r x => by
      apply (cancel_epi ((cokernel.π i).f n)).mp
      rw [Linear.comp_smul,RelativeChainHomotopy.projection_degreeDesc,RelativeChainHomotopy.projection_degreeDesc]
      exact map_smul ((kernel.ι (homPullback i V)).f n).hom r x }

/-- The explicit inverse retains exactly the original ambient cochain under the actual projection. -/
theorem inverseDegree_projection (n : ℕ) (x : (kernel (homPullback i V)).X n) :
    (cokernel.π i).f n ≫ inverseDegree i V n x = kernelValue i V n x :=
  RelativeChainHomotopy.projection_degreeDesc _ _ _ _

/-- The explicit degreewise descent is left inverse to the actual kernel comparison. -/
theorem toKernel_inverseDegree (n : ℕ) : (toKernel i V).f n ≫ inverseDegree i V n = 𝟙 _ := by
  ext c
  apply (cancel_epi ((cokernel.π i).f n)).mp
  exact (inverseDegree_projection i V n _).trans (toKernel_apply i V n c)

/-- The explicit degreewise descent is right inverse to the actual kernel comparison. -/
theorem inverseDegree_toKernel (n : ℕ) : inverseDegree i V n ≫ (toKernel i V).f n = 𝟙 _ := by
  apply (cancel_mono ((kernel.ι (homPullback i V)).f n)).mp
  ext x
  exact (toKernel_apply i V n _).trans (inverseDegree_projection i V n x)

end TernaryPoly.HomCokernelKernel
