module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneDetection
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlane

@[expose] public section


open CategoryTheory MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RelativeEdgeCohomologyPolynomials
open RadicalFirstCohomologyLattice RadicalFirstCohomology LatticeTopCohomology
open LatticeFirstCohomology groupCohomology

/-- At step one the parameterized shear is the existing genuine radical-generator action. -/
theorem shearStep_one (i j : Fin 3) : shearStep i j 1=shear i j := by
  apply MvPolynomial.algHom_ext
  intro k
  simp [shearStep,shear]

/-- The literal degree-raised binary contraction of the two genuine plane-cocycle values. -/
def planeCocycleContract (n : ℕ) : cocycles₁ (planeRep n) →ₗ[ℚ] BinaryH (n+1) where
  toFun c := ⟨X 0*planeEvalAlg (c first : Poly)+X 1*planeEvalAlg (c second : Poly),by
    change (X 0*planeEvalAlg (c first : Poly)+X 1*planeEvalAlg (c second : Poly)).IsHomogeneous (n+1)
    simpa only [Nat.add_comm,planeEval_coe] using
      ((isHomogeneous_X ℚ 0).mul (planeEval n (c first)).property).add
        ((isHomogeneous_X ℚ 1).mul (planeEval n (c second)).property)⟩
  map_add' c d := by
    apply Subtype.ext
    change X 0*planeEvalAlg ((c first : Poly)+(d first : Poly))+
      X 1*planeEvalAlg ((c second : Poly)+(d second : Poly))=
      (X 0*planeEvalAlg (c first : Poly)+X 1*planeEvalAlg (c second : Poly))+
        (X 0*planeEvalAlg (d first : Poly)+X 1*planeEvalAlg (d second : Poly))
    simp only [map_add]
    ring
  map_smul' r c := by
    apply Subtype.ext
    change X 0*planeEvalAlg (r • (c first : Poly))+
      X 1*planeEvalAlg (r • (c second : Poly))=r • _
    simp [planeEvalAlg,Algebra.smul_def]
    ring

/-- The binary contraction vanishes exactly on actual group coboundaries. -/
theorem planeCocycleContract_eq_zero_iff (n : ℕ) (c : cocycles₁ (planeRep n)) :
    planeCocycleContract n c=0 ↔ H1π (planeRep n) c=0 := by
  constructor
  · intro hc
    have hq := congrArg (fun p : BinaryH (n+1) => rename (![0,1] : Fin 2 → Fin 3) (p : MvPolynomial (Fin 2) ℚ)) hc
    change rename (![0,1] : Fin 2 → Fin 3)
      (X 0*planeEvalAlg (c first : Poly)+X 1*planeEvalAlg (c second : Poly))=0 at hq
    simp only [map_add,map_mul,rename_X,plane_rename_eval] at hq
    obtain ⟨v,hv,hv0,hv1⟩ := plane_pair_exact_of_contract_zero 1 (by norm_num)
      (c first) (c second) (c first).property (c second).property
      (by simpa only [shearStep_one] using plane_cocycle_closed n c) hq
    have he : c=coboundary (planeRep n) ⟨v,hv⟩ := by
      apply cocycle_is_coboundary_of_generators
      · change c first=(planeRep n).ρ first ⟨v,hv⟩-⟨v,hv⟩
        rw [planeRep_first]
        apply Subtype.ext
        change (c first : Poly)=shear 0 2 v-v
        simpa only [shearStep_one] using hv0.symm
      · change c second=(planeRep n).ρ second ⟨v,hv⟩-⟨v,hv⟩
        rw [planeRep_second]
        apply Subtype.ext
        change (c second : Poly)=shear 1 2 v-v
        simpa only [shearStep_one] using hv1.symm
    rw [he,H1π_eq_zero_iff]
    exact ⟨⟨v,hv⟩,rfl⟩
  · intro hc
    rw [H1π_eq_zero_iff] at hc
    obtain ⟨v,hv⟩ := hc
    have he : c=coboundary (planeRep n) v := by
      apply cocycles₁_ext
      intro g
      exact (congrFun hv g).symm
    rw [he]
    apply Subtype.ext
    change X 0*planeEvalAlg ((planeRep n).ρ first v-v : Poly)+
      X 1*planeEvalAlg ((planeRep n).ρ second v-v : Poly)=0
    rw [planeRep_first,planeRep_second]
    change X 0*planeEvalAlg (shear 0 2 v-v)+X 1*planeEvalAlg (shear 1 2 v-v)=0
    simp only [map_sub,planeEval_shear,sub_self,mul_zero,add_zero]

end TernaryPoly.OrdinaryFaceRadical
