module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex Representation SymmetricSpaceBoundaryFull

variable {G : Type} [Group G] (S : Subgroup G)

/-- The literal scalar degree-zero stabilizer bar generator. -/
def scalarBarZero : (Rep.barResolution ℚ S).complex.X 0 :=
  Finsupp.single default (MonoidAlgebra.single 1 1)

/-- The literal scalar degree-one stabilizer bar generator indexed by its group element. -/
def scalarBarOne (h : S) : (Rep.barResolution ℚ S).complex.X 1 :=
  Finsupp.single (fun _ => h) (MonoidAlgebra.single 1 1)

/-- A scalar zero-bar with the complete ambient induction coordinate. -/
def inducedZero (g : G) : (inducedBarComplex S).X 0 :=
  IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ g (scalarBarZero S)

/-- A scalar one-bar with the complete ambient induction and subgroup coordinates. -/
def inducedOne (g : G) (h : S) : (inducedBarComplex S).X 1 :=
  IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 1).ρ g (scalarBarOne S h)

/-- The induction relation moves a subgroup action into its inverse left induction coordinate. -/
theorem inducedBar_mk_action (n : ℕ) (g : G) (h : S)
    (b : (Rep.barResolution ℚ S).complex.X n) :
    IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ g
        (((Rep.barResolution ℚ S).complex.X n).ρ h b) =
      IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ ((h.val)⁻¹ * g) b := by
  have hu := Rep.hom_comm_apply (barInductionUnit S n) h b
  change IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ 1
    (((Rep.barResolution ℚ S).complex.X n).ρ h b) =
    Representation.ind S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ h.val
      (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ 1 b) at hu
  have hv := congrArg (fun x => Representation.ind S.subtype
    ((Rep.barResolution ℚ S).complex.X n).ρ g⁻¹ x) hu
  simpa only [ind_mk, inv_inv, one_mul] using hv

/-- The actual stabilizer action on the scalar zero-bar retains the translating group element. -/
theorem scalarBarZero_action (h : S) :
    ((Rep.barResolution ℚ S).complex.X 0).ρ h (scalarBarZero S) =
      Finsupp.single default (MonoidAlgebra.single h 1) := by
  change Representation.free ℚ S (Fin 0 → S) h
    (Finsupp.single default (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]

/-- The actual one-bar differential is its translated zero-bar minus its base zero-bar. -/
theorem scalarBarOne_boundary (h : S) :
    ((Rep.barResolution ℚ S).complex.d 1 0).hom (scalarBarOne S h) =
      ((Rep.barResolution ℚ S).complex.X 0).ρ h (scalarBarZero S) - scalarBarZero S := by
  change (Rep.barComplex.d ℚ S 0).hom
    (Finsupp.single (fun _ : Fin 1 => h) (MonoidAlgebra.single 1 1)) =
    Representation.free ℚ S (Fin 0 → S) h
      (Finsupp.single default (MonoidAlgebra.single 1 1)) -
        Finsupp.single default (MonoidAlgebra.single 1 1)
  rw [Rep.barComplex.d_single, Representation.free_single_single, mul_one]
  have h₀ : (fun i : Fin 0 => (fun _ : Fin 1 => h) i.succ) = default := Subsingleton.elim _ _
  have h₁ : Fin.contractNth 0 (· * ·) (fun _ : Fin 1 => h) = default := Subsingleton.elim _ _
  simp [h₀, h₁]
  change (Finsupp.single (default : Fin 0 → S) (MonoidAlgebra.single h (1 : ℚ)) +
    -Finsupp.single default (MonoidAlgebra.single 1 (1 : ℚ)) : (Fin 0 → S) →₀ MonoidAlgebra ℚ S) =
    Finsupp.single default (MonoidAlgebra.single h (1 : ℚ)) -
      Finsupp.single default (MonoidAlgebra.single 1 (1 : ℚ))
  erw [sub_eq_add_neg]

/-- The induced differential retains both actual group coordinates and the inverse convention. -/
theorem inducedOne_boundary (g : G) (h : S) :
    ((inducedBarComplex S).d 1 0).hom (inducedOne S g h) =
      inducedZero S ((h.val)⁻¹ * g) - inducedZero S g := by
  rw [inducedOne, inducedBar_d_mk, scalarBarOne_boundary, map_sub, inducedBar_mk_action]
  rfl

/-- Canonical parabolic inclusion preserves the entire scalar zero-bar and ambient coordinate. -/
theorem inducedZero_map (T : Subgroup G) (hST : S ≤ T) (g : G) :
    (inducedBarMap S T hST).f 0 (inducedZero S g) = inducedZero T g := by
  change (inducedBarDegree S T hST 0).hom (IndV.mk _ _ g (scalarBarZero S)) = _
  rw [inducedBarDegree_mk]
  congr 1
  change (SingularCoverRestriction.barMap (Subgroup.inclusion hST)).f 0 (scalarBarZero S) = scalarBarZero T
  change (SingularCoverRestriction.barDegreeMap (Subgroup.inclusion hST) 0).hom
    (Finsupp.single default (MonoidAlgebra.single 1 1)) = _
  rw [SingularCoverRestriction.barDegreeMap_generator]
  exact congrArg (fun x => Finsupp.single x (MonoidAlgebra.single (1 : T) (1 : ℚ)))
    (Subsingleton.elim _ _)

end TernaryPoly.OrdinaryBoundaryActualEvaluation
