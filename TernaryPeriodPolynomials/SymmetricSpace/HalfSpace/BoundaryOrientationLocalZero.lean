module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsModel
public import TernaryPeriodPolynomials.Topology.Rational.Local.ChartHomology
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

noncomputable section
namespace TernaryPoly.HalfSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalLocalChartHomology SymmetricSpaceBoundaryCharts

/-- The actual nonnegative height line is contractible. -/
instance halfLine_contractible : ContractibleSpace HalfLine :=
  (convex_Ici (0 : ℝ)).contractibleSpace ⟨0,by simp⟩

/-- The actual product half-space is contractible. -/
instance productModel_contractible : ContractibleSpace ProductModel := inferInstance

/-- The fixed inward anchor has height one, so it avoids every height-zero boundary point. -/
theorem inwardAnchor_ne (p : ProductModel) (hp : p.2.val = 0) :
    (p.1,(⟨1,zero_le_one⟩ : HalfLine)) ≠ p := by
  intro h
  have hh := congrArg (fun z : ProductModel => z.2.val) h
  change 1 = p.2.val at hh
  rw [hp] at hh
  norm_num at hh

/-- A genuine straight-line contraction of the punctured half-space toward the
fixed height-one inward anchor; the puncture is on the height-zero face. -/
def puncturedProductContraction (p : ProductModel) (hp : p.2.val = 0) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥({p}ᶜ : Set ProductModel))
      (ContinuousMap.const _ ⟨(p.1,⟨1,zero_le_one⟩),inwardAnchor_ne p hp⟩) where
  toFun z := ⟨((1-z.1.val) • z.2.val.1 + z.1.val • p.1,
    ⟨(1-z.1.val)*z.2.val.2.val+z.1.val,
      add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) z.2.val.2.property) z.1.property.1⟩),by
      intro he
      change ((1-z.1.val) • z.2.val.1 + z.1.val • p.1,
        (⟨(1-z.1.val)*z.2.val.2.val+z.1.val,_⟩ : HalfLine)) = p at he
      by_cases ht : z.1.val = 0
      · apply z.2.property
        change z.2.val = p
        simpa only [ht,sub_zero,zero_smul,one_smul,add_zero,one_mul] using he
      · have hh := congrArg (fun q : ProductModel => q.2.val) he
        change (1-z.1.val)*z.2.val.2.val+z.1.val = p.2.val at hh
        have htpos : 0 < z.1.val := lt_of_le_of_ne z.1.property.1 (Ne.symm ht)
        have hnonneg := mul_nonneg (sub_nonneg.mpr z.1.property.2) z.2.val.2.property
        rw [hp] at hh
        linarith⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

/-- Removing a height-zero point leaves the actual product half-space contractible. -/
theorem puncturedProduct_contractible (p : ProductModel) (hp : p.2.val = 0) :
    ContractibleSpace ↥({p}ᶜ : Set ProductModel) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨(p.1,⟨1,zero_le_one⟩),inwardAnchor_ne p hp⟩,⟨puncturedProductContraction p hp⟩⟩

/-- Every positive-lower-degree local homology group at a boundary point of the
actual product half-space vanishes. -/
theorem productBoundary_local_isZero (p : ProductModel) (hp : p.2.val = 0)
    (n : ℕ) (hn : n ≠ 0) : IsZero ((localChains p).homology (n+1)) := by
  let := puncturedProduct_contractible p hp
  exact (homology_isZero (X := ↥({p}ᶜ : Set ProductModel)) n hn).of_iso
    (relativeSuccIso ({p}ᶜ : Set ProductModel) n hn)

end TernaryPoly.HalfSpaceBoundaryOrientation
