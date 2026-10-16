module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesRational
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open Module Matrix OrdinaryIncidence OrdinaryFullAction RelativeStabilizerCoordinates
open SymmetricSpaceRationalAction

/-- A literal rational matrix whose vector action is the inverse coordinate map of a basis. -/
def basisFrame (b : Basis (Fin 3) ℚ (Fin 3 → ℚ)) : RationalGL :=
  GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ (Fin 3 → ℚ)).symm b.equivFun.symm)

theorem vectorAction_basisFrame (b : Basis (Fin 3) ℚ (Fin 3 → ℚ)) :
    vectorAction (basisFrame b)=b.equivFun.symm := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ (Fin 3 → ℚ))
    (GeneralLinearGroup.toLin (basisFrame b))=_
  rw [basisFrame,MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply]

/-- An incident actual rational line and plane admit a basis adapted to both subspaces. -/
theorem incident_basis (L : Line) (P : Plane) (hLP : incidence L P) :
    ∃ b : Basis (Fin 3) ℚ (Fin 3 → ℚ),b 0∈L.val ∧ b 1∈P.val := by
  classical
  have hn : L.val≠⊥ := by
    intro h
    have hd := L.property.1
    rw [h,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨w,hwP,hwL⟩ := IsConcreteLE.exists_of_lt hLP
  have hPtop : P.val≠⊤ := by
    intro h
    have hd := P.property.1
    rw [h] at hd
    norm_num at hd
  obtain ⟨u,hu⟩ := SetLike.exists_not_mem_of_ne_top P.val hPtop
  have h1 : LinearIndependent ℚ (![v] : Fin 1 → (Fin 3 → ℚ)) :=
    linearIndependent_unique_iff.mpr hv0
  have hw : w∉Submodule.span ℚ (Set.range (![v] : Fin 1 → (Fin 3 → ℚ))) := by
    intro hw
    apply hwL
    apply (Submodule.span_le.mpr ?_) hw
    rintro z ⟨i,rfl⟩
    fin_cases i
    exact hv
  have h2 : LinearIndependent ℚ (![v,w] : Fin 2 → (Fin 3 → ℚ)) := by
    have hh := (linearIndependent_finSnoc (x:=w) (v:=(![v] : Fin 1 → (Fin 3 → ℚ)))).mpr ⟨h1,hw⟩
    have he : Fin.snoc (![v] : Fin 1 → (Fin 3 → ℚ)) w=![v,w] := by
      funext i
      fin_cases i <;> rfl
    rw [he] at hh
    exact hh
  have hu' : u∉Submodule.span ℚ (Set.range (![v,w] : Fin 2 → (Fin 3 → ℚ))) := by
    intro hh
    apply hu
    apply (Submodule.span_le.mpr ?_) hh
    rintro z ⟨i,rfl⟩
    fin_cases i
    · exact hLP.le hv
    · exact hwP
  have h3 : LinearIndependent ℚ (![v,w,u] : Fin 3 → (Fin 3 → ℚ)) := by
    have hh := (linearIndependent_finSnoc (x:=u) (v:=(![v,w] : Fin 2 → (Fin 3 → ℚ)))).mpr ⟨h2,hu'⟩
    have he : Fin.snoc (![v,w] : Fin 2 → (Fin 3 → ℚ)) u=![v,w,u] := by
      funext i
      fin_cases i <;> rfl
    rw [he] at hh
    exact hh
  let b := basisOfPiSpaceOfLinearIndependent h3
  have hb : (b : Fin 3 → (Fin 3 → ℚ))=![v,w,u] := coe_basisOfPiSpaceOfLinearIndependent h3
  exact ⟨b,by rw [hb]; exact hv,by rw [hb]; exact hwP⟩

/-- Every rational incident pair is exactly the pair of labels of an actual rational frame. -/
theorem exists_frame_for_incident (L : Line) (P : Plane) (hLP : incidence L P) :
    ∃ g : RationalGL,lineLabel g=L ∧ planeLabel g=P := by
  obtain ⟨b,hb0,hb1⟩ := incident_basis L P hLP
  refine ⟨basisFrame b,?_,?_⟩
  · apply Subtype.ext
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro z ⟨v,hv,rfl⟩
      change vectorAction (basisFrame b) v∈L.val
      rw [vectorAction_basisFrame,Basis.equivFun_symm_apply]
      obtain ⟨h1,h2⟩ := (mem_L0 v).mp hv
      simp only [Fin.sum_univ_three,h1,h2,zero_smul,add_zero]
      exact L.val.smul_mem _ hb0
    · exact (subspaceAction_finrank (basisFrame b) L0).trans (finrank_L0.trans L.property.1.symm)
  · apply Subtype.ext
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro z ⟨v,hv,rfl⟩
      change vectorAction (basisFrame b) v∈P.val
      rw [vectorAction_basisFrame,Basis.equivFun_symm_apply]
      have h2 := (mem_P0 v).mp hv
      simp only [Fin.sum_univ_three,h2,zero_smul,add_zero]
      exact P.val.add_mem (P.val.smul_mem _ (hLP.le hb0)) (P.val.smul_mem _ hb1)
    · exact (subspaceAction_finrank (basisFrame b) P0).trans (finrank_P0.trans P.property.1.symm)

end TernaryPoly.SymmetricSpaceBoundaryFaces
