module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyNaturality

@[expose] public section

noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularCoverRestriction

variable {G H : Type} [Group G] [Group H] (φ : H →* G)

/-- The literal group-cochain restriction written in bar Hom coordinates. -/
def barHomMap (V : Rep ℚ G) :
    (Rep.barComplex ℚ G).linearYonedaObj ℚ V ⟶
      (Rep.barComplex ℚ H).linearYonedaObj ℚ (Rep.res φ V) :=
  (groupCohomology.inhomogeneousCochainsIso V).inv ≫
    groupCohomology.cochainsMap φ (𝟙 (Rep.res φ V)) ≫
      (groupCohomology.inhomogeneousCochainsIso (Rep.res φ V)).hom

/-- The actual bar-resolution restriction sends a tuple generator to its image tuple. -/
def barDegreeMap (n : ℕ) :
    (Rep.barComplex ℚ H).X n ⟶ Rep.res φ ((Rep.barComplex ℚ G).X n) :=
  Rep.freeLift ℚ H _ (fun x : Fin n → H =>
    Finsupp.single (φ ∘ x) (MonoidAlgebra.single 1 1))

/-- On actual free bar generators, the degree map is precisely the group homomorphism on tuples. -/
theorem barDegreeMap_generator (n : ℕ) (x : Fin n → H) :
    (barDegreeMap φ n).hom (Finsupp.single x (MonoidAlgebra.single 1 1))=
      Finsupp.single (φ ∘ x) (MonoidAlgebra.single 1 1) := by
  change (Representation.freeLift (Rep.res φ (Rep.free ℚ G (Fin n → G))).ρ
    (fun y : Fin n → H => Finsupp.single (φ ∘ y) (MonoidAlgebra.single 1 1)))
      (Finsupp.single x (MonoidAlgebra.single 1 1))=_
  simp only [Representation.freeLift_single_single,map_one,Module.End.one_apply,one_smul]

/-- The literal cochain restriction is precomposition by the explicit bar map. -/
theorem barHomMap_apply (V : Rep ℚ G) (n : ℕ) (c : (Rep.barComplex ℚ G).X n ⟶ V) :
    (barHomMap φ V).f n c=barDegreeMap φ n ≫ Rep.resMap φ c := by
  apply Rep.free_ext
  intro x
  change (Representation.freeLift (Rep.res φ V).ρ
      (fun y => c.hom (Finsupp.single (φ ∘ y) (MonoidAlgebra.single 1 1))))
        (Finsupp.single x (MonoidAlgebra.single 1 1))=
    c.hom ((Representation.freeLift (Rep.res φ ((Rep.barComplex ℚ G).X n)).ρ
      (fun y => Finsupp.single (φ ∘ y) (MonoidAlgebra.single 1 1)))
        (Finsupp.single x (MonoidAlgebra.single 1 1)))
  simp only [Representation.freeLift_single_single,map_one,Module.End.one_apply,one_smul]

/-- The explicit degree maps commute with the actual bar differential. -/
theorem barDegreeMap_comm (i j : ℕ) :
    barDegreeMap φ i ≫ Rep.resMap φ ((Rep.barComplex ℚ G).d i j)=
      (Rep.barComplex ℚ H).d i j ≫ barDegreeMap φ j := by
  have h := congrArg (fun m => m (𝟙 ((Rep.barComplex ℚ G).X j)))
    ((barHomMap φ ((Rep.barComplex ℚ G).X j)).comm j i)
  change (Rep.barComplex ℚ H).d i j ≫
      (barHomMap φ ((Rep.barComplex ℚ G).X j)).f j (𝟙 _) =
    (barHomMap φ ((Rep.barComplex ℚ G).X j)).f i ((Rep.barComplex ℚ G).d i j ≫ 𝟙 _) at h
  rw [barHomMap_apply,barHomMap_apply] at h
  have hid : Rep.resMap φ (𝟙 ((Rep.barComplex ℚ G).X j))=𝟙 _ := rfl
  rw [hid] at h
  simpa only [Category.comp_id] using h.symm

/-- The actual bar-chain map into the restricted target complex. -/
def barMap : Rep.barComplex ℚ H ⟶
    ((Rep.resFunctor φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ G) where
  f n := barDegreeMap φ n
  comm' i j _ := barDegreeMap_comm φ i j

end TernaryPoly.SingularCoverRestriction
