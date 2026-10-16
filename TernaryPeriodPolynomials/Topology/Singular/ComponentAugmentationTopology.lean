module

public import TernaryPeriodPolynomials.Topology.ContractibleSingularHomology
public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearizationSingular

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularComponentAugmentation
open Topology CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped unitInterval Simplicial

variable {ι : Type} (E : ι → Type) [∀ i,TopologicalSpace (E i)]

abbrev Total := Σ i,E i

/-- Every singular simplex has a single component label because its domain is connected. -/
theorem simplex_label_constant [TopologicalSpace ι] [DiscreteTopology ι]
    (n : ℕ) (simplex : FreeActionLinearization.SingularSimplex (TopCat.of (Total E)) n)
    (u v : Convexity.StdSimplex ℝ (Fin (n+1))) :
    ((TopCat.toSSetObjEquiv _ _ simplex) u).1=((TopCat.toSSetObjEquiv _ _ simplex) v).1 :=
  TotallyDisconnectedSpace.eq_of_continuous
    (fun z => ((TopCat.toSSetObjEquiv _ _ simplex) z).1)
    ((continuous_sigma (fun _ => continuous_const)).comp (TopCat.toSSetObjEquiv _ _ simplex).continuous) u v

variable [∀ i,ContractibleSpace (E i)]

def componentPoint (i : ι) : E i := (id_nullhomotopic (E i)).choose

def componentContraction (i : ι) : ContinuousMap.Homotopy (ContinuousMap.id (E i))
    (ContinuousMap.const (E i) (componentPoint E i)) :=
  (id_nullhomotopic (E i)).choose_spec.some

variable [TopologicalSpace ι] [DiscreteTopology ι]

def labelMap : C(Total E,ι) := ⟨Sigma.fst,continuous_sigma (fun _ => continuous_const)⟩

def componentSection : C(ι,Total E) := ⟨fun i => ⟨i,componentPoint E i⟩,continuous_of_discreteTopology⟩

/-- The componentwise contraction is continuous on the whole topological sum; it is not claimed
or required to be equivariant for a group action. -/
def totalContraction : ContinuousMap.Homotopy (ContinuousMap.id (Total E))
    ((componentSection E).comp (labelMap E)) where
  toFun z := ⟨z.2.1,componentContraction E z.2.1 (z.1,z.2.2)⟩
  continuous_toFun := by
    have hc : Continuous (fun z : Σ i, E i × I =>
        (⟨z.1,componentContraction E z.1 (z.2.2,z.2.1)⟩ : Total E)) :=
      continuous_sigma (fun i => continuous_sigmaMk.comp
        ((componentContraction E i).continuous.comp (continuous_snd.prodMk continuous_fst)))
    exact hc.comp ((Homeomorph.sigmaProdDistrib (X := E) (Y := I)).continuous.comp continuous_swap)
  map_zero_left x := by
    change (⟨x.1,componentContraction E x.1 (0,x.2)⟩ : Total E)=x
    exact congrArg (Sigma.mk x.1) ((componentContraction E x.1).map_zero_left x.2)
  map_one_left x := by
    change (⟨x.1,componentContraction E x.1 (1,x.2)⟩ : Total E)=_
    exact congrArg (Sigma.mk x.1) ((componentContraction E x.1).map_one_left x.2)

def labelHomotopyEquiv : ContinuousMap.HomotopyEquiv (Total E) ι where
  toFun := labelMap E
  invFun := componentSection E
  left_inv := ⟨(totalContraction E).symm⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id ι)⟩

/-- Actual positive singular homology of a sum of contractible components is zero. -/
theorem positive_homology_isZero (n : ℕ) (hn : n≠0) :
    IsZero ((ContractibleSingularHomology.chains (Total E)).homology n) := by
  let e := ContractibleSingularHomology.chainHomotopyEquiv (labelHomotopyEquiv E)
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℚ) n
    (ModuleCat.of ℚ ℚ) (TopCat.of ι) hn).of_iso (e.toHomologyIso n)

/-- The actual path-component quotient is literally the label set. -/
def pathComponentEquiv : ZerothHomotopy (Total E) ≃ ι where
  toFun := ZerothHomotopy.lift Sigma.fst (by
    intro x y p
    have h := TotallyDisconnectedSpace.eq_of_continuous (fun t => (p t).1)
      ((labelMap E).continuous.comp p.continuous) (0:I) (1:I)
    simpa using h)
  invFun i := ZerothHomotopy.mk ⟨i,componentPoint E i⟩
  left_inv q := by
    induction q with | mk x =>
    exact ZerothHomotopy.sound
      (((componentContraction E x.1).evalAt x.2).symm.map continuous_sigmaMk)
  right_inv _ := rfl

/-- Singular simplicial components have the same literal labels. -/
def singularComponentEquiv : SSet.π₀ (TopCat.toSSet.obj (TopCat.of (Total E))) ≃ ι :=
  TopCat.zerothHomotopyEquiv.symm.trans (pathComponentEquiv E)

@[simp] theorem singularComponentEquiv_mk
    (simplex : FreeActionLinearization.SingularSimplex (TopCat.of (Total E)) 0) :
    singularComponentEquiv E (SSet.π₀.mk simplex)=(TopCat.toSSetObj₀Equiv simplex).1 := rfl

end TernaryPoly.SingularComponentAugmentation
