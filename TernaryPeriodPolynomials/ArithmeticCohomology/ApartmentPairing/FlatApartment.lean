module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatCone
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCycle
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyCycles

@[expose] public section


/-!
# The boundary of the compactified flat is the coordinate apartment

The hexagon cone cycle of `FlatCone` represents the identity apartment class of the boundary
(`hexagon_class_eq`): the literal Mayer--Vietoris edge map is injective, and both classes have the
alternating sum of the six chamber flags as edge (the flag of the `k`-th chamber is
`(e_{σ_k 0}, ⟨e_{σ_k 0}, e_{σ_k 1}⟩)`, with sign `(-1)^k`, and the oriented coordinate apartment
`L₀ → L₁ → L₂ → L₀` is the same six-term chain). Consequently the relative class `flatClass` of the
compactified flat has connecting homomorphism the identity apartment class (`delta_flatClass`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory AlgebraicTopology
open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceRationalAction TernaryPoly.SymmetricSpaceRationalCharts
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization
open TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.BoundaryFaceResolutionComparison
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.IntegralGL3Congruence
  CategoryTheory Limits HomologicalComplex
open TernaryPoly.EquivariantSingularMayerVietoris TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularBoundaryRestriction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

/-! ### The coordinate apartment is the alternating sum of the six chamber flags -/

theorem permGL_mulVec_single (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (permGL σ).val.mulVec (Pi.single i 1) = Pi.single (σ i) (1 : ℚ) := by
  rw [permGL_val, Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply]
  congr 1
  rw [eq_comm, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem L0_eq_span : RelativeStabilizerCoordinates.L0 =
    Submodule.span ℚ {(Pi.single 0 1 : Fin 3 → ℚ)} := by
  ext v
  rw [RelativeStabilizerCoordinates.mem_L0, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, ?_⟩
    funext j
    fin_cases j <;> simp [h1, h2]
  · rintro ⟨c, rfl⟩
    simp

theorem lineLabel_permGL_val (σ : Equiv.Perm (Fin 3)) :
    (lineLabel (permGL σ)).val = Submodule.span ℚ {(Pi.single (σ 0) 1 : Fin 3 → ℚ)} := by
  change (OrdinaryFullAction.subspaceAction (permGL σ) RelativeStabilizerCoordinates.L0) = _
  rw [OrdinaryFullAction.subspaceAction_apply, L0_eq_span, Submodule.map_span,
    Set.image_singleton]
  congr 2
  change OrdinaryFullAction.vectorAction (permGL σ) (Pi.single 0 1) = _
  rw [rational_vector_apply, permGL_mulVec_single]


/-! ### The identity apartment as the alternating sum of the six chamber flags -/

open TernaryPoly.OrdinaryApartmentPresentation TernaryPoly.OrdinaryApartmentSpanComparison
  TernaryPoly.AugmentedFrameComplex TernaryPoly.GoodApartmentCycles
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology

theorem planeLabel_hexW_succ (k : ℕ) (hk : Even k) :
    planeLabel (hexW (k + 1)) = planeLabel (hexW k) := by
  have hpt : fk (k + 1) pa = fk k pa := by
    rw [fk, fk, hexW_succ_even k hk]
    exact chamber_wall_one _ 0
  apply planeFace_unique (x := fk (k + 1) pa)
  · exact chamber_plane_mem (hexW (k + 1)) 1
  · rw [hpt]
    exact chamber_plane_mem (hexW k) 1

theorem lineLabel_hexW_succ (k : ℕ) (hk : ¬ Even k) :
    lineLabel (hexW (k + 1)) = lineLabel (hexW k) := by
  have hpt : fk (k + 1) pb = fk k pb := by
    rw [fk, fk, hexW_succ_odd k hk]
    exact chamber_wall_two _ 0
  apply lineFace_unique (x := fk (k + 1) pb)
  · exact chamber_line_mem (hexW (k + 1)) 1
  · rw [hpt]
    exact chamber_line_mem (hexW k) 1

theorem lineLabel_hexW_six : lineLabel (hexW 6) = lineLabel (hexW 0) := by rw [hexW_six]

theorem line_hex0 : line (augmentedLine 1 0) = lineLabel (hexW 0) := by
  apply Subtype.ext
  rw [hexW, lineLabel_permGL_val]
  simp [line, augmentedLine, vectorLine, template, hexPerm]

theorem line_hex1 : line (augmentedLine 1 1) = lineLabel (hexW 1) := by
  apply Subtype.ext
  rw [hexW, lineLabel_permGL_val]
  have h : hexPerm 1 0 = 1 := by decide
  simp [line, augmentedLine, vectorLine, template, h]

theorem line_hex3 : line (augmentedLine 1 2) = lineLabel (hexW 3) := by
  apply Subtype.ext
  rw [hexW, lineLabel_permGL_val]
  have h : hexPerm 3 0 = 2 := by decide
  simp [line, augmentedLine, vectorLine, template, h]

theorem single_flag_congr (g : RationalGL) (L : OrdinaryIncidence.Line) (P : OrdinaryIncidence.Plane)
    (hL : L = lineLabel g) (hP : P = planeLabel g) (h : L.val < P.val) :
    (Finsupp.single (⟨(L, P), h⟩ : OrdinaryIncidenceChains.Edge) (1 : ℚ)) =
      Finsupp.single (flagLabel g : OrdinaryIncidenceChains.Edge) 1 := by
  subst hL hP
  rfl

theorem le_plane (g : RationalGL) (L : OrdinaryIncidence.Line) (hL : L = lineLabel g)
    (P : OrdinaryIncidence.Plane) (hP : P = planeLabel g) : L.val ≤ P.val := by
  subst hL hP
  exact (labels_incident g).le


local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-! ### The hexagon class is the identity apartment class -/

theorem identityApartment_val :
    (identityApartment : OrdinaryIncidenceChains.Cycles).val =
      apartmentChain (fun _ => True) (lineLabel (hexW 0)) (lineLabel (hexW 1)) (lineLabel (hexW 3)) := by
  change (frameCycle 1).val = _
  rw [frameCycle_apartment, apartmentCycle_coe, line_hex0, line_hex1, line_hex3]

theorem apartmentChain_hex :
    apartmentChain (fun _ => True) (lineLabel (hexW 0)) (lineLabel (hexW 1)) (lineLabel (hexW 3)) =
      Finsupp.single (flagLabel (hexW 0) : OrdinaryIncidenceChains.Edge) (1 : ℚ) -
        Finsupp.single (flagLabel (hexW 1) : OrdinaryIncidenceChains.Edge) 1 +
        Finsupp.single (flagLabel (hexW 2) : OrdinaryIncidenceChains.Edge) 1 -
        Finsupp.single (flagLabel (hexW 3) : OrdinaryIncidenceChains.Edge) 1 +
        Finsupp.single (flagLabel (hexW 4) : OrdinaryIncidenceChains.Edge) 1 -
        Finsupp.single (flagLabel (hexW 5) : OrdinaryIncidenceChains.Edge) 1 := by
  have hP01 : planeLabel (hexW 1) = planeLabel (hexW 0) := planeLabel_hexW_succ 0 (by decide)
  have hL12 : lineLabel (hexW 2) = lineLabel (hexW 1) := lineLabel_hexW_succ 1 (by decide)
  have hP23 : planeLabel (hexW 3) = planeLabel (hexW 2) := planeLabel_hexW_succ 2 (by decide)
  have hL34 : lineLabel (hexW 4) = lineLabel (hexW 3) := lineLabel_hexW_succ 3 (by decide)
  have hP45 : planeLabel (hexW 5) = planeLabel (hexW 4) := planeLabel_hexW_succ 4 (by decide)
  have hL56 : lineLabel (hexW 6) = lineLabel (hexW 5) := lineLabel_hexW_succ 5 (by decide)
  rw [hexW_six] at hL56
  have a1 : (lineLabel (hexW 0)).val ≤ (planeLabel (hexW 0)).val := le_plane (hexW 0) _ rfl _ rfl
  have a2 : (lineLabel (hexW 1)).val ≤ (planeLabel (hexW 0)).val :=
    le_plane (hexW 1) _ rfl _ hP01.symm
  have b1 : (lineLabel (hexW 1)).val ≤ (planeLabel (hexW 2)).val :=
    le_plane (hexW 2) _ hL12.symm _ rfl
  have b2 : (lineLabel (hexW 3)).val ≤ (planeLabel (hexW 2)).val :=
    le_plane (hexW 3) _ rfl _ hP23.symm
  have c1 : (lineLabel (hexW 3)).val ≤ (planeLabel (hexW 4)).val :=
    le_plane (hexW 4) _ hL34.symm _ rfl
  have c2 : (lineLabel (hexW 0)).val ≤ (planeLabel (hexW 4)).val :=
    le_plane (hexW 5) _ hL56 _ hP45.symm
  unfold apartmentChain
  rw [lineChain_of_common_plane _ _ _ _ a1 a2, lineChain_of_common_plane _ _ _ _ b1 b2,
    lineChain_of_common_plane _ _ _ _ c1 c2]
  simp only [flagChain]
  rw [single_flag_congr (hexW 0) _ _ rfl rfl _, single_flag_congr (hexW 1) _ _ rfl hP01.symm _,
    single_flag_congr (hexW 2) _ _ hL12.symm rfl _, single_flag_congr (hexW 3) _ _ rfl hP23.symm _,
    single_flag_congr (hexW 4) _ _ hL34.symm rfl _, single_flag_congr (hexW 5) _ _ hL56 hP45.symm _]
  abel

theorem edge_identityApartment :
    ordinaryCycleInclusion.hom identityApartment =
      MonoidAlgebra.single (flagLabel (hexW 0)) (1 : ℚ) - MonoidAlgebra.single (flagLabel (hexW 1)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 2)) 1 - MonoidAlgebra.single (flagLabel (hexW 3)) 1 +
        MonoidAlgebra.single (flagLabel (hexW 4)) 1 - MonoidAlgebra.single (flagLabel (hexW 5)) 1 := by
  change edgeCoefficients.symm (identityApartment : OrdinaryIncidenceChains.Cycles).val = _
  rw [identityApartment_val, apartmentChain_hex]
  rfl

/-- **The hexagon cone cycle represents the identity apartment class** of the boundary. -/
theorem hexagon_class_eq :
    homologyMap faceConeToBoundary 1 (faceCone.homologyπ 1 coneCycle) =
      identityApartmentBoundaryClass := by
  have hm : Mono boundaryEdgeMap := by
    rw [← boundaryH1OrdinaryCyclesIso_edge]
    infer_instance
  apply (Rep.mono_iff_injective boundaryEdgeMap).mp hm
  rw [coneCycle_edge_flags, identityApartmentBoundaryClass_edge, edge_identityApartment]



/-! ### The relative class of the flat and its boundary -/

/-- The compactified flat, as a degree-two chain of the bordification. -/
def flatRep : (equivariantChains principalSix (TopCat.of Glued)).X 2 := flatChain

theorem d_flatRep :
    ((equivariantChains principalSix (TopCat.of Glued)).d 2 1).hom flatRep =
      (upstairsBoundaryChainMap.f 1).hom hexBoundaryChain := by
  rw [hexBoundaryChain_upstairs]
  exact d_flatChain

/-- The flat as a chain of the relative complex of the bordification modulo its boundary. -/
def flatRelChain : upstairsRelativeChains.X 2 := (upstairsRelativeSequence.g.f 2).hom flatRep

theorem flatRelChain_d : (upstairsRelativeChains.d 2 1).hom flatRelChain = 0 := by
  have hcomm := congrArg (fun m => m.hom flatRep) (upstairsRelativeSequence.g.comm 2 1)
  have hz := congrArg (fun m => (m.f 1).hom hexBoundaryChain) upstairsRelativeSequence.zero
  change (upstairsRelativeChains.d 2 1).hom ((upstairsRelativeSequence.g.f 2).hom flatRep) =
    (upstairsRelativeSequence.g.f 1).hom
      (((equivariantChains principalSix (TopCat.of Glued)).d 2 1).hom flatRep) at hcomm
  rw [d_flatRep] at hcomm
  exact hcomm.trans hz

/-- The relative cycle of the flat. -/
def flatRelCycle : upstairsRelativeChains.cycles 2 :=
  upstairsRelativeChains.cyclesMk flatRelChain 1
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)) flatRelChain_d

/-- **The relative homology class of the compactified diagonal flat.** -/
def flatClass : upstairsRelativeChains.homology 2 := upstairsRelativeChains.homologyπ 2 flatRelCycle

theorem cyclesMk_hex
    (hk : (ComplexShape.down ℕ).next 1 = 0)
    (hx : (forget₂ (Rep.{0} ℚ principalSix) Ab).map (boundaryChains.d 1 0) hexBoundaryChain = 0) :
    boundaryChains.cyclesMk hexBoundaryChain 0 hk hx = cyclesMap faceConeToBoundary 1 coneCycle := by
  have hi : Function.Injective (boundaryChains.iCycles 1).hom :=
    (Rep.mono_iff_injective _).mp inferInstance
  apply hi
  have e1 := boundaryChains.i_cyclesMk hexBoundaryChain 0 hk hx
  have e2 := congrArg (fun m => m.hom coneCycle) (HomologicalComplex.cyclesMap_i faceConeToBoundary 1)
  have e3 : (faceCone.iCycles 1).hom coneCycle = coneChain := coneCycle_value
  change (boundaryChains.iCycles 1).hom (boundaryChains.cyclesMk hexBoundaryChain 0 hk hx) = hexBoundaryChain at e1
  change (boundaryChains.iCycles 1).hom ((cyclesMap faceConeToBoundary 1).hom coneCycle) =
    (faceConeToBoundary.f 1).hom ((faceCone.iCycles 1).hom coneCycle) at e2
  rw [e1, e2, e3]
  rfl

/-- **The boundary of the flat is the identity apartment**: the connecting homomorphism of the
pair `(M̄, ∂M̄)` carries the class of the compactified flat to the coordinate apartment class. -/
theorem delta_flatClass :
    upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass = identityApartmentBoundaryClass := by
  have h := upstairsRelativeSequence_shortExact.δ_apply 2 1 rfl flatRelChain flatRelChain_d
    flatRep rfl hexBoundaryChain d_flatRep.symm 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
  erw [cyclesMk_hex] at h
  have hnat := congrArg (fun m => m.hom coneCycle)
    (HomologicalComplex.homologyπ_naturality faceConeToBoundary 1)
  refine h.trans ?_
  exact (hnat.symm.trans hexagon_class_eq : _)


/-- Because the bordification is contractible, the connecting homomorphism is an isomorphism, so the
geometric class of the compactified flat is the algebraic relative apartment class. -/
theorem flatClass_eq_identityApartmentRelativeClass :
    flatClass = identityApartmentRelativeClass := by
  have hm : Mono upstairsRelativeH2BoundaryIso.hom := inferInstance
  apply (Rep.mono_iff_injective _).mp hm
  rw [upstairsRelativeH2BoundaryIso_hom]
  exact delta_flatClass.trans identityApartmentRelativeClass_connecting.symm

end TernaryPeriodPolynomials.Argument.Lemma33
