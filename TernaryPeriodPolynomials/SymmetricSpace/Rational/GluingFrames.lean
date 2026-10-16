module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingCocycle
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.Charts

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates
open SymmetricSpaceRationalAction SymmetricSpaceRationalCharts
open TopologicalSpace

/-- The literal rational-frame change from g coordinates to h coordinates. -/
def changeMatrix (g h : RationalGL) : RealGL := realRational (h⁻¹*g)

@[simp] theorem changeMatrix_self (g : RationalGL) : changeMatrix g g=1 := by simp [changeMatrix]

theorem changeMatrix_reverse (g h : RationalGL) : changeMatrix h g=(changeMatrix g h)⁻¹ := by
  simp [changeMatrix,map_inv,mul_inv_rev]

theorem changeMatrix_mul (g h k : RationalGL) :
    changeMatrix h k*changeMatrix g h=changeMatrix g k := by
  simp [changeMatrix,←map_mul,mul_assoc]

theorem changeMatrix_left (a g h : RationalGL) : changeMatrix (a*g) (a*h)=changeMatrix g h := by
  simp [changeMatrix,mul_assoc]

def overlap (g h : RationalGL) : Opens Corner := domain (changeMatrix g h)

theorem overlap_reverse (g h : RationalGL) : overlap g h=overlap h g := by
  change domain (changeMatrix g h)=domain (changeMatrix h g)
  rw [changeMatrix_reverse g h,domain_inv]

theorem overlap_self (g : RationalGL) : overlap g g=⊤ := by
  rw [overlap,changeMatrix_self,domain_one]

/-- The actual homeomorphism from one rational-chart overlap to its reverse overlap. -/
def pairTransition (g h : RationalGL) : overlap g h ≃ₜ overlap h g :=
  (transition (changeMatrix g h)).trans
    (Homeomorph.setCongr (congrArg (fun U : Opens Corner => (U : Set Corner)) (overlap_reverse g h)))

@[simp] theorem pairTransition_val (g h : RationalGL) (p : overlap g h) :
    (pairTransition g h p).val=(transition (changeMatrix g h) p).val := rfl

def chartPoint (g h : RationalGL) (S : Space) : overlap g h :=
  ⟨chartEmbedding g S,interior_subset_domain _ (chartHomeomorph g S).property⟩

/-- Every actual rational-frame transition agrees with the original form space. -/
theorem pairTransition_chart (g h : RationalGL) (S : Space) :
    (pairTransition g h (chartPoint g h S)).val=chartEmbedding h S := by
  rw [pairTransition_val]
  change (transition (changeMatrix g h)
    (interiorPoint (changeMatrix g h) (act (realRational g⁻¹) S))).val=chartEmbedding h S
  rw [transition_interiorPoint,←act_mul,chartEmbedding_apply]
  congr 2
  simp [changeMatrix,map_mul,mul_assoc]

theorem transition_one_of_eq {r : RealGL} (hr : r=1) (p : domain r) :
    (transition r p).val=p.val := by
  subst r
  exact transition_one p

theorem pairTransition_self (g : RationalGL) (p : overlap g g) : pairTransition g g p=p := by
  apply Subtype.ext
  rw [pairTransition_val]
  exact transition_one_of_eq (changeMatrix_self g) p

/-- The rational-frame overlaps satisfy the actual intersection axiom. -/
theorem pairTransition_inter (g h k : RationalGL) (p : overlap g h) (hp : p.val∈overlap g k) :
    (pairTransition g h p).val∈overlap h k := by
  have hp' : p.val∈domain (changeMatrix h k*changeMatrix g h) := by
    rw [changeMatrix_mul]
    exact hp
  exact transition_inter (changeMatrix g h) (changeMatrix h k) p hp'

theorem transition_cocycle_of_mul (r s t : RealGL) (ht : s*r=t)
    (p : domain r) (hp : p.val∈domain t) :
    (transition s ⟨(transition r p).val,transition_inter r s p (ht.symm ▸ hp)⟩).val=
      (transition t ⟨p.val,hp⟩).val := by
  subst t
  exact transition_cocycle_apply r s p hp

/-- The rational-frame cocycle identity holds on the full actual triple overlap. -/
theorem pairTransition_cocycle (g h k : RationalGL) (p : overlap g h) (hp : p.val∈overlap g k) :
    (pairTransition h k ⟨(pairTransition g h p).val,pairTransition_inter g h k p hp⟩).val=
      (pairTransition g k ⟨p.val,hp⟩).val := by
  exact transition_cocycle_of_mul (changeMatrix g h) (changeMatrix h k) (changeMatrix g k)
    (changeMatrix_mul g h k) p hp

end TernaryPoly.SymmetricSpaceRationalGluing
