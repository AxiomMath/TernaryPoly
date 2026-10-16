module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyResolution
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantTwist

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.RadicalFirstCohomologyLattice
open LatticeTopCohomology RelativeStabilizerMatrices RelativeStabilizerParameters
open RadicalCoinvariantAlgebra ModThreeGoodAction

/-- The actual integral plane radical, parametrized by its two upper-right entries. -/
def planeHom : Lattice →* IntegralGL where
  toFun g := planeElement 1 ![g.toAdd.1,g.toAdd.2]
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeElement_val,planeMatrix]
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [planeElement_val,planeMatrix,Fin.sum_univ_three,add_comm]

/-- The actual integral line radical, parametrized by the last two entries of its first row. -/
def lineHom : Lattice →* IntegralGL where
  toFun g := lineElement 1 ![g.toAdd.1,g.toAdd.2] 1
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineElement_val,lineMatrix]
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [lineElement_val,lineMatrix,Fin.sum_univ_three,add_comm]

theorem planeHom_injective : Function.Injective planeHom := by
  intro g h he
  change g.toAdd=h.toAdd
  apply Prod.ext
  · have ht := congrArg (fun u : IntegralGL => u.val 0 2) he
    simpa [planeHom,planeElement_val,planeMatrix] using ht
  · have ht := congrArg (fun u : IntegralGL => u.val 1 2) he
    simpa [planeHom,planeElement_val,planeMatrix] using ht

theorem lineHom_injective : Function.Injective lineHom := by
  intro g h he
  change g.toAdd=h.toAdd
  apply Prod.ext
  · have ht := congrArg (fun u : IntegralGL => u.val 0 1) he
    simpa [lineHom,lineElement_val,lineMatrix] using ht
  · have ht := congrArg (fun u : IntegralGL => u.val 0 2) he
    simpa [lineHom,lineElement_val,lineMatrix] using ht

/-- These are actual subgroups of the original integral matrix group. -/
def planeRadical : Subgroup IntegralGL := planeHom.range
def lineRadical : Subgroup IntegralGL := lineHom.range

def planeParamEquiv : Lattice ≃* planeRadical := MonoidHom.ofInjective planeHom_injective
def lineParamEquiv : Lattice ≃* lineRadical := MonoidHom.ofInjective lineHom_injective

theorem planeHom_mem_HP (g : Lattice) : HP (planeHom g) := planeElement_mem _ _

theorem lineHom_mem_HL (g : Lattice) : HL (lineHom g) := by
  apply (lineElement_mem_iff _ _ _).mpr
  simp [GammaEntries]

theorem planeHom_first : planeHom first=rootElement 1 1 := by
  exact rootElement_plane_first.symm

theorem planeHom_second : planeHom second=rootElement 2 1 := by
  exact rootElement_plane_second.symm

theorem lineHom_first : lineHom first=rootElement 0 1 := by
  exact rootElement_line_first.symm

theorem lineHom_second : lineHom second=rootElement 1 1 := by
  exact rootElement_line_second.symm

/-- The genuine homogeneous inverse-substitution representation of the plane lattice. -/
abbrev planeRep (n : ℕ) : Rep ℚ Lattice :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp planeHom)

/-- The genuine homogeneous inverse-substitution representation of the line lattice. -/
abbrev lineRep (n : ℕ) : Rep ℚ Lattice :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp lineHom)

/-- The same coefficient representation on the actual plane matrix subgroup. -/
def planeSubgroupRep (n : ℕ) : Rep ℚ planeRadical :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp planeRadical.subtype)

/-- The same coefficient representation on the actual line matrix subgroup. -/
def lineSubgroupRep (n : ℕ) : Rep ℚ lineRadical :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp lineRadical.subtype)

theorem planeRep_first (n : ℕ) : (planeRep n).ρ first=homogeneousShear n 0 2 := by
  change PolynomialGLAction.integralAction n 0 (planeHom first)=_
  rw [planeHom_first,integralAction_root]
  rfl

theorem planeRep_second (n : ℕ) : (planeRep n).ρ second=homogeneousShear n 1 2 := by
  change PolynomialGLAction.integralAction n 0 (planeHom second)=_
  rw [planeHom_second,integralAction_root]
  rfl

theorem lineRep_first (n : ℕ) : (lineRep n).ρ first=homogeneousShear n 0 1 := by
  change PolynomialGLAction.integralAction n 0 (lineHom first)=_
  rw [lineHom_first,integralAction_root]
  rfl

theorem lineRep_second (n : ℕ) : (lineRep n).ρ second=homogeneousShear n 0 2 := by
  change PolynomialGLAction.integralAction n 0 (lineHom second)=_
  rw [lineHom_second,integralAction_root]
  rfl

@[simp] theorem planeSubgroupRep_parameter (n : ℕ) (g : Lattice) :
    (planeSubgroupRep n).ρ (planeParamEquiv g)=(planeRep n).ρ g := rfl

@[simp] theorem lineSubgroupRep_parameter (n : ℕ) (g : Lattice) :
    (lineSubgroupRep n).ρ (lineParamEquiv g)=(lineRep n).ρ g := rfl

end TernaryPoly.RadicalFirstCohomologyLattice
