module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardBadLineMixedCuspidal
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.LevelThreeParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.CohomologyRestrictionTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel

@[expose] public section


/-!
# The bad-line mixed cuspidal group is the parabolic `H¹(Γ₁'(3), Sym^{n+1})`

For `n > 0`, the Hochschild-Serre mixed cuspidal group of the standard bad line
(`FaceCuspidal`, the classes of `H¹(ℤˣ × Γ₁'(3), H¹(N, Sym^n))` vanishing on the cusp subgroup of every
complete flag over the line) is isomorphic, through the Kostant isomorphism
`H¹(N, Sym^n) ≅ Sym^{n+1}` and the elimination of the `ℤˣ` factor, to the parabolic classes of
`H¹(Γ₁'(3), Sym^{n+1})` (`badLineCuspidalEquivParabolic`). Combined with `Face/CuspIso` the locally
inner classes at the standard bad line are `parabolicCrossedH1 (levelRep (n+1) 0)`, of exact dimension
`(n+3)/3 - 1`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face


/-- The Levi cusp subgroup is the face cusp of the binary edge. -/
theorem faceCusp_binaryEdge (frame : GeneralLinearGroup (Fin 2) ℚ) :
    faceCusp integralBadLineSplitting.conjAct standardBadLine standardBadLineSemidirectEquiv
      (binaryEdge frame) = leviCusp frame := by
  ext x
  change standardBadLineAmbientHom (SemidirectProduct.inr x) ∈
    fixedPointLevel rationalLevel (binaryEdge frame) ↔ x ∈ leviCusp frame
  rw [ambient_inr_mem_edge_iff frame x.1 x.2]
  simp [leviCusp, Subgroup.mem_prod]

/-- `H¹(N, E)` of the standard bad line, as the radical module of the Levi `ℤˣ × Γ₁'(3)`. -/
abbrev BLModule (n : ℕ) :=
  CrossedH1 ((faceRep integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
    standardBadLineSemidirectEquiv).comp SemidirectProduct.inl)

/-- The Levi action on the bad-line radical cohomology. -/
abbrev blAction (n : ℕ) : Representation ℂ (ℤˣ × binaryArithmeticLevel) (BLModule n) :=
  leviCrossedH1Representation integralBadLineSplitting.conjAct
    (faceRep integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
      standardBadLineSemidirectEquiv)

/-- Quantifying over the complete flags above the standard bad line is quantifying over the cusp
frames of the binary Levi, for any predicate of the cusp subgroup. -/
theorem forall_edge_iff_forall_frame (P : Subgroup (ℤˣ × binaryArithmeticLevel) → Prop) :
    (∀ e : {e : Edges // endpoint .line e = standardBadLine},
        P (faceCusp integralBadLineSplitting.conjAct standardBadLine
          standardBadLineSemidirectEquiv e.val)) ↔
      ∀ frame : GeneralLinearGroup (Fin 2) ℚ, P (leviCusp frame) :=
  ⟨fun h frame => (congrArg P (faceCusp_binaryEdge frame)).mp
      (h ⟨binaryEdge frame, binaryEdge_endpoint frame⟩),
    fun h e => by
      have edgeExists := exists_binaryEdge e.val e.property
      obtain ⟨frame, hframe⟩ := edgeExists
      rw [hframe]
      exact (congrArg P (faceCusp_binaryEdge frame)).mpr (h frame)⟩

/-- The mixed cuspidal group of the bad line, in terms of the cusp frames of the binary Levi. -/
theorem mem_faceCuspidal_badLine_iff (n : ℕ) (m : CrossedH1 (blAction n)) :
    m ∈ (FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
        standardBadLineSemidirectEquiv : Submodule ℂ (CrossedH1 (blAction n))) ↔
      ∀ frame : GeneralLinearGroup (Fin 2) ℚ,
        crossedPullbackH1 (leviCusp frame).subtype (blAction n) m = 0 :=
  (mem_faceCuspidal_iff integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
    standardBadLineSemidirectEquiv m).trans
    (forall_edge_iff_forall_frame
      (fun H => crossedPullbackH1 H.subtype (blAction n) m = 0))

/-- Sol's presentation of the Levi action on the bad-line radical cohomology. -/
abbrev blAction' (n : ℕ) :=
  leviCrossedH1Representation integralBadLineSplitting.conjAct (standardBadLineRepresentation n)

/-- The two presentations agree definitionally. -/
def blSwitch (n : ℕ) : CrossedH1 (blAction n) ≃ₗ[ℂ] CrossedH1 (blAction' n) :=
  LinearEquiv.refl ℂ _

theorem equiv_map_sub {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℂ M] [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) (x y : M) : e (x - y) = e x - e y :=
  map_sub e x y

variable (n : ℕ) (positive : 0 < n)

/-- The Kostant isomorphism `H¹(N, Sym^n) ≅ Sym^{n+1}` on the face presentation. -/
def blTheta : BLModule n ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  explicitRadicalBinaryEquiv n positive

/-- Kostant isomorphism, then elimination of the unit factor of the Levi. -/
def badLinePsi : CrossedH1 (blAction n) ≃ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation n) :=
  (blSwitch n).trans ((explicitBinaryMixedH1Equiv n positive).trans (binaryLeviH1Equiv n))

theorem badLinePsi_mk (x : crossedCocycles (blAction n)) :
    ∃ y : crossedCocycles (binaryArithmeticRepresentation n),
      (∀ γ, y.val γ = blTheta n positive (x.val (1, γ))) ∧
        badLinePsi n positive ((crossedBoundaries (blAction n)).mkQ x) =
          (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ y :=
  ⟨binaryLeviCrossedEquiv n (crossedRepresentationEqEquiv _ _
    (explicitRadicalBinary_transport_eq n positive)
    (crossedCoefficientEquiv _ (explicitRadicalBinaryEquiv n positive) x)),
    fun _ => rfl, rfl⟩

theorem blEquivariant (v : BLModule n) (l : ℤˣ × binaryArithmeticLevel) :
    blTheta n positive (blAction n l v) =
      binaryArithmeticRepresentation n l.2 (blTheta n positive v) :=
  explicitRadicalBinaryEquiv_equivariant n positive l v

/-- Primitive criterion on the Levi cusp, transferred through the Kostant isomorphism. -/
theorem blPrimitive_iff (x : crossedCocycles (blAction n))
    (y : crossedCocycles (binaryArithmeticRepresentation n))
    (hy : ∀ γ, y.val γ = blTheta n positive (x.val (1, γ)))
    (frame : GeneralLinearGroup (Fin 2) ℚ) :
    (∃ wM : BLModule n, ∀ s : leviCusp frame, x.val s.1 = blAction n s.1 wM - wM) ↔
      ∃ w : Binary.HomogeneousPoly (n + 1), ∀ t : binaryCuspLevel frame,
        y.val t.1 = binaryArithmeticRepresentation n t.1 w - w := by
  set θ := blTheta n positive with hθ
  constructor
  · rintro ⟨wM, hwM⟩
    refine ⟨θ wM, fun t => ?_⟩
    have hmem : ((1 : ℤˣ), t.1) ∈ leviCusp frame := Subgroup.mem_prod.mpr ⟨trivial, t.2⟩
    have h1 := hwM ⟨((1 : ℤˣ), t.1), hmem⟩
    have h2 : x.val (1, t.1) = blAction n (1, t.1) wM - wM := h1
    rw [hy, h2, equiv_map_sub θ, blEquivariant n positive]
  · rintro ⟨w, hw⟩
    refine ⟨θ.symm w, fun s => ?_⟩
    obtain ⟨⟨u, γ⟩, hs⟩ := s
    have hγ : γ ∈ binaryCuspLevel frame := (Subgroup.mem_prod.mp hs).2
    let Y : crossedCocycles (binaryLeviRepresentation n) :=
      ⟨fun l => θ (x.val l), fun a b => by
        have h := x.property a b
        change θ (x.val (a * b)) = θ (x.val a) + binaryArithmeticRepresentation n a.2 (θ (x.val b))
        rw [h, LinearEquiv.map_add, blEquivariant n positive]⟩
    have hfac := binaryLeviCrossed_factor n Y (u, γ)
    have hY1 : Y.val (1, γ) = y.val γ := (hy γ).symm
    have hw' := hw ⟨γ, hγ⟩
    apply θ.injective
    have hR : θ (blAction n (u, γ) (θ.symm w) - θ.symm w) =
        binaryArithmeticRepresentation n γ w - w := by
      rw [equiv_map_sub θ, blEquivariant n positive, LinearEquiv.apply_symm_apply]
    rw [hR]
    have hL : θ (x.val (u, γ)) = Y.val (u, γ) := rfl
    rw [hL, hfac, hY1]
    exact hw'

theorem mk_mem_binaryParabolicH1_iff (y : crossedCocycles (binaryArithmeticRepresentation n)) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ y ∈ binaryParabolicH1 n ↔
      ∀ frame : GeneralLinearGroup (Fin 2) ℚ, ∃ w : Binary.HomogeneousPoly (n + 1),
        ∀ t : binaryCuspLevel frame, y.val t.1 = binaryArithmeticRepresentation n t.1 w - w := by
  unfold binaryParabolicH1
  rw [Submodule.mem_iInf]
  refine forall_congr' fun frame => ?_
  rw [LinearMap.mem_ker]
  exact pullback_mk_eq_zero_iff (binaryArithmeticRepresentation n) (binaryCuspLevel frame).subtype y

theorem mk_mem_faceCuspidal_iff (x : crossedCocycles (blAction n)) :
    (crossedBoundaries (blAction n)).mkQ x ∈
        (FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv : Submodule ℂ (CrossedH1 (blAction n))) ↔
      ∀ frame : GeneralLinearGroup (Fin 2) ℚ, ∃ wM : BLModule n,
        ∀ s : leviCusp frame, x.val s.1 = blAction n s.1 wM - wM := by
  rw [mem_faceCuspidal_badLine_iff]
  exact forall_congr' fun frame =>
    pullback_mk_eq_zero_iff (blAction n) (leviCusp frame).subtype x

theorem badLine_mem_cuspidal_iff (m : CrossedH1 (blAction n)) :
    m ∈ (FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
        standardBadLineSemidirectEquiv : Submodule ℂ (CrossedH1 (blAction n))) ↔
      badLinePsi n positive m ∈ binaryParabolicH1 n := by
  have mExists := (crossedBoundaries (blAction n)).mkQ_surjective m
  obtain ⟨x, rfl⟩ := mExists
  have psiExists := badLinePsi_mk n positive x
  obtain ⟨y, hy, hΨ⟩ := psiExists
  exact (mk_mem_faceCuspidal_iff n x).trans
    ((forall_congr' fun frame => blPrimitive_iff n positive x y hy frame).trans
      ((mk_mem_binaryParabolicH1_iff n y).symm.trans
        (Iff.of_eq (congrArg (fun z => z ∈ binaryParabolicH1 n) hΨ.symm))))

theorem badLine_map_psi_eq :
    Submodule.map (badLinePsi n positive).toLinearMap
        (FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv : Submodule ℂ (CrossedH1 (blAction n))) =
      parabolicCrossedH1 (binaryArithmeticRepresentation n) := by
  ext c
  rw [← binaryParabolicH1_eq_parabolicCrossedH1 n]
  rw [Submodule.mem_map_equiv]
  have h := badLine_mem_cuspidal_iff n positive ((badLinePsi n positive).symm c)
  have hc : badLinePsi n positive ((badLinePsi n positive).symm c) = c :=
    LinearEquiv.apply_symm_apply _ c
  exact h.trans (Iff.of_eq (congrArg (fun z => z ∈ binaryParabolicH1 n) hc))

/-- **The bad-line mixed cuspidal group is the parabolic `H¹(Γ₁'(3), Sym^{n+1})`.** -/
def badLineCuspidalEquivParabolic :
    (FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
        standardBadLineSemidirectEquiv : Submodule ℂ (CrossedH1 (blAction n))) ≃ₗ[ℂ]
      parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
  ((badLinePsi n positive).submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (badLine_map_psi_eq n positive))

/-- **Locally inner classes at the standard bad line `≅` parabolic `H¹(Γ₁'(3), Sym^{n+1})`.** -/
def badLineLocallyInnerEquivParabolic :
    locallyInnerClasses n trivialCharacter .line standardBadLine ≃ₗ[ℂ]
      parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
  (badLineLocallyInnerEquiv n trivialCharacter).trans (badLineCuspidalEquivParabolic n positive)

include positive in
/-- **Exact dimension of the locally inner classes at the standard bad line:**
`dim + 1 = ⌊(n + 3)/3⌋`. -/
theorem finrank_badLine_locallyInner :
    Module.finrank ℂ (locallyInnerClasses n trivialCharacter .line standardBadLine) + 1 =
      (n + 3) / 3 := by
  rw [(badLineLocallyInnerEquivParabolic n positive).finrank_eq]
  have h := TernaryPeriodPolynomials.LevelThree.ExactLevel.finrank_level_parabolicH1_eq
    (m := n + 1) (e := 0) (by omega)
  rw [← TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree.parabolicCrossedH1_eq] at h
  have e : (n + 1 + 2) / 3 = (n + 3) / 3 := by omega
  rw [e] at h
  exact h

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
