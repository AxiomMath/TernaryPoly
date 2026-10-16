module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVBiprodPairing

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex

/-- The literal degree formula for a map out of an actual complex biproduct. -/
theorem complexBiprod_desc_apply {s : ComplexShape ℕ}
    {C D K : HomologicalComplex (ModuleCat.{0} ℚ) s} (f : C ⟶ K) (g : D ⟶ K)
    (n : ℕ) (x : (C ⊞ D).X n) :
    (biprod.desc f g).f n x =
      f.f n ((biprod.fst : C ⊞ D ⟶ C).f n x) + g.f n ((biprod.snd : C ⊞ D ⟶ D).f n x) :=
  congrArg (fun h => h x) (HomologicalComplex.congr_hom (biprod.desc_eq (f := f) (g := g)) n)

/-- The literal first projection of a map into an actual complex biproduct. -/
theorem complexBiprod_lift_fst {s : ComplexShape ℕ}
    {C D K : HomologicalComplex (ModuleCat.{0} ℚ) s} (f : K ⟶ C) (g : K ⟶ D)
    (n : ℕ) (x : K.X n) : (biprod.fst : C ⊞ D ⟶ C).f n ((biprod.lift f g).f n x) = f.f n x :=
  congrArg (fun h => h x) (HomologicalComplex.congr_hom (biprod.lift_fst f g) n)

/-- The literal second projection of a map into an actual complex biproduct. -/
theorem complexBiprod_lift_snd {s : ComplexShape ℕ}
    {C D K : HomologicalComplex (ModuleCat.{0} ℚ) s} (f : K ⟶ C) (g : K ⟶ D)
    (n : ℕ) (x : K.X n) : (biprod.snd : C ⊞ D ⟶ D).f n ((biprod.lift f g).f n x) = g.f n x :=
  congrArg (fun h => h x) (HomologicalComplex.congr_hom (biprod.lift_snd f g) n)

/-- Two literal chains or cochains in a complex biproduct agree when both actual components agree. -/
theorem complexBiprod_ext {s : ComplexShape ℕ} (C D : HomologicalComplex (ModuleCat.{0} ℚ) s)
    (n : ℕ) {x y : (C ⊞ D).X n}
    (h₁ : (biprod.fst : C ⊞ D ⟶ C).f n x = (biprod.fst : C ⊞ D ⟶ C).f n y)
    (h₂ : (biprod.snd : C ⊞ D ⟶ D).f n x = (biprod.snd : C ⊞ D ⟶ D).f n y) : x = y := by
  have h (z : (C ⊞ D).X n) :
      (biprod.inl : C ⟶ C ⊞ D).f n ((biprod.fst : C ⊞ D ⟶ C).f n z) +
        (biprod.inr : D ⟶ C ⊞ D).f n ((biprod.snd : C ⊞ D ⟶ D).f n z) = z :=
    congrArg (fun h => h z) (HomologicalComplex.congr_hom (biprod.total (X := C) (Y := D)) n)
  exact (h x).symm.trans ((congrArg₂ (· + ·)
    (congrArg ((biprod.inl : C ⟶ C ⊞ D).f n) h₁)
    (congrArg ((biprod.inr : D ⟶ C ⊞ D).f n) h₂)).trans (h y))

end TernaryPoly.SingularLocalCompactCapMV
