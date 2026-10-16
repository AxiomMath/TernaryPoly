module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberSequence
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Five

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.CofiberSequence
open CategoryTheory Category Limits HomologicalComplex Preadditive ZeroObject

variable {C : Type*} [Category* C] [Abelian C]
  {A B A' B' : ChainComplex C ℕ} (f : A ⟶ B) (g : A' ⟶ B')
  (u : A ⟶ A') (v : B ⟶ B') (h : Homotopy (f ≫ v) (u ≫ g))

def nullHomotopy : Homotopy (f ≫ (v ≫ homotopyCofiber.inr g)) 0 :=
  (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    ((h.compRight (homotopyCofiber.inr g)).trans
      ((Homotopy.ofEq (Category.assoc _ _ _)).trans
        (((homotopyCofiber.inrCompHomotopy g (fun n => ⟨n+1,Cone.downRel n⟩)).compLeft u).trans
          (Homotopy.ofEq comp_zero))))

/-- The actual cone map induced by a specified homotopy-commutative square. -/
def comparisonMap : homotopyCofiber f ⟶ homotopyCofiber g :=
  homotopyCofiber.desc f (v ≫ homotopyCofiber.inr g) (nullHomotopy f g u v h)

theorem inr_comparisonMap : homotopyCofiber.inr f ≫ comparisonMap f g u v h=v ≫ homotopyCofiber.inr g :=
  homotopyCofiber.inr_desc _ _ _

theorem left_comparisonMap (n : ℕ) : left f n ≫ (comparisonMap f g u v h).f (n+1)=
    h.hom n (n+1) ≫ right g (n+1) + u.f n ≫ left g n := by
  rw [show left f n=homotopyCofiber.inlX f n (n+1) (Cone.downRel n) from rfl,
    comparisonMap,homotopyCofiber.inlX_desc_f]
  simp only [nullHomotopy,Homotopy.trans,Homotopy.ofEq,Homotopy.compRight,
    Homotopy.compLeft,Pi.add_apply,zero_add,add_zero]
  rw [homotopyCofiber.inrCompHomotopy_hom _ _ n (n+1) (Cone.downRel n)]
  rfl

/-- The map on the shifted corner quotient is precisely the suspension of the prescribed corner map. -/
theorem comparisonMap_projection : comparisonMap f g u v h ≫ projection g=projection f ≫ Suspension.map u := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero => exact (isZero_zero C).eq_of_tgt _ _
  | succ n =>
    apply homotopyCofiber.ext_from_X f n (n+1) (Cone.downRel n)
    · change left f n ≫ ((comparisonMap f g u v h).f (n+1) ≫ first g n)=left f n ≫ (first f n ≫ u.f n)
      rw [←Category.assoc,left_comparisonMap,add_comp,Category.assoc,Category.assoc,
        right_first,left_first,comp_zero,comp_id,zero_add,←Category.assoc,left_first,id_comp]
    · change right f (n+1) ≫ ((comparisonMap f g u v h).f (n+1) ≫ first g n)=right f (n+1) ≫ (first f n ≫ u.f n)
      have hm : right f (n+1) ≫ (comparisonMap f g u v h).f (n+1)=v.f (n+1) ≫ right g (n+1) :=
        homotopyCofiber.inrX_desc_f _ _ _ (n+1)
      rw [←Category.assoc,hm,Category.assoc,right_first,comp_zero,←Category.assoc,right_first,zero_comp]

def comparisonShortComplex : shortComplex f ⟶ shortComplex g where
  τ₁ := v
  τ₂ := comparisonMap f g u v h
  τ₃ := Suspension.map u
  comm₁₂ := (inr_comparisonMap f g u v h).symm
  comm₂₃ := comparisonMap_projection f g u v h

/-- A homotopy-commutative square of chain homotopy equivalences induces a genuine cone quasi-isomorphism. -/
theorem comparisonMap_quasiIso (eu : _root_.HomotopyEquiv A A') (hu : eu.hom=u)
    (ev : _root_.HomotopyEquiv B B') (hv : ev.hom=v) : QuasiIso (comparisonMap f g u v h) := by
  have hv' : QuasiIso v := by rw [←hv]; infer_instance
  have hu' : QuasiIso (Suspension.map u) := by
    rw [←hu]
    exact inferInstanceAs (QuasiIso (Suspension.equivalence eu).hom)
  have : QuasiIso (comparisonShortComplex f g u v h).τ₁ := hv'
  have : QuasiIso (comparisonShortComplex f g u v h).τ₃ := hu'
  exact middle_quasiIso (comparisonShortComplex f g u v h)
    (shortExact f) (shortExact g)

end TernaryPoly.BoundaryFaceResolutionComparison.CofiberSequence
