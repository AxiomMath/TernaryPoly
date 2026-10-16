module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.FlagGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesFrames

@[expose] public section


/-!
# L3a: the flag building of the model is the rational incidence geometry of the geometric side

`Flags .line`, `Flags .plane`, `Edges` of the cochain model (cosets of the line, plane and Borel
parabolics of `GL₃(ℚ)`) are identified, `GL₃(ℚ)`-equivariantly, with the rational lines, rational planes
and incident (line, plane) pairs of `TernaryPoly.OrdinaryIncidence`, which label the boundary faces of the
bordification (`TernaryPoly.SymmetricSpaceBoundaryFaces.lineLabel`, `planeLabel`):
`flagLineEquiv`, `flagPlaneEquiv`, `edgeEquiv`, with `flagLine_mk : flagLine (g B) = lineLabel g`,
equivariance `flagLine_smul`, `flagPlane_smul`, `edgePair_smul`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.OrdinaryIncidence (Line Plane incidence)
open TernaryPoly.SymmetricSpaceBoundaryFaces (lineLabel planeLabel)

/-- The rational line of a line flag. -/
def flagLine (F : Flags .line) : Line :=
  ⟨flagSubspace .line F, by simpa using flagSubspace_finrank .line F, trivial⟩

/-- The rational plane of a plane flag. -/
def flagPlane (F : Flags .plane) : Plane :=
  ⟨flagSubspace .plane F, by simpa using flagSubspace_finrank .plane F, by
    induction F using Quotient.inductionOn with
    | h frame =>
      refine ⟨⟨flagSubspace .line (endpoint .line (QuotientGroup.mk frame)), by
        simpa using flagSubspace_finrank .line _, trivial⟩, ?_⟩
      exact edge_subspace_incidence (QuotientGroup.mk frame)⟩

theorem flagLine_val (F : Flags .line) : (flagLine F).val = flagSubspace .line F := rfl
theorem flagPlane_val (F : Flags .plane) : (flagPlane F).val = flagSubspace .plane F := rfl

theorem flagLine_injective : Function.Injective flagLine := fun _ _ h =>
  flagSubspace_injective .line (congrArg Subtype.val h)

theorem flagPlane_injective : Function.Injective flagPlane := fun _ _ h =>
  flagSubspace_injective .plane (congrArg Subtype.val h)

open TernaryPoly.RelativeStabilizerCoordinates in
theorem flagLine_mk (g : RationalGL3) : flagLine (QuotientGroup.mk g) = lineLabel g := by
  apply Subtype.ext
  ext v
  change v ∈ frameSubspace .line g ↔ v ∈ (TernaryPoly.OrdinaryFullAction.subspaceAction g
    L0)
  rw [mem_frameSubspace, TernaryPoly.OrdinaryFullAction.subspaceAction_apply, Submodule.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_L0 c).mpr hc, TernaryPoly.SymmetricSpaceBoundaryFaces.rational_vector_apply g c⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_L0 c).mp hc, (TernaryPoly.SymmetricSpaceBoundaryFaces.rational_vector_apply g c).symm⟩

open TernaryPoly.RelativeStabilizerCoordinates in
theorem flagPlane_mk (g : RationalGL3) : flagPlane (QuotientGroup.mk g) = planeLabel g := by
  apply Subtype.ext
  ext v
  change v ∈ frameSubspace .plane g ↔ v ∈ (TernaryPoly.OrdinaryFullAction.subspaceAction g
    P0)
  rw [mem_frameSubspace, TernaryPoly.OrdinaryFullAction.subspaceAction_apply, Submodule.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_P0 c).mpr hc, TernaryPoly.SymmetricSpaceBoundaryFaces.rational_vector_apply g c⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (mem_P0 c).mp hc, (TernaryPoly.SymmetricSpaceBoundaryFaces.rational_vector_apply g c).symm⟩

theorem flagLine_smul (g : RationalGL3) (F : Flags .line) :
    flagLine (g • F) = TernaryPoly.OrdinaryFullAction.lineAction g (flagLine F) := by
  induction F using Quotient.inductionOn with
  | h h =>
    change flagLine (QuotientGroup.mk (g * h)) = _
    rw [flagLine_mk, flagLine_mk]
    apply Subtype.ext
    exact TernaryPoly.OrdinaryFullAction.subspaceAction_mul g h _

theorem flagPlane_smul (g : RationalGL3) (F : Flags .plane) :
    flagPlane (g • F) = TernaryPoly.OrdinaryFullAction.planeAction g (flagPlane F) := by
  induction F using Quotient.inductionOn with
  | h h =>
    change flagPlane (QuotientGroup.mk (g * h)) = _
    rw [flagPlane_mk, flagPlane_mk]
    apply Subtype.ext
    exact TernaryPoly.OrdinaryFullAction.subspaceAction_mul g h _

/-- There are at least two distinct rational lines other than any given one. -/
theorem exists_line_ne (L : Line) : ∃ M : Line, M ≠ L := by
  have h0 : (Pi.single 0 1 : Fin 3 → ℚ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have h1 : (Pi.single 1 1 : Fin 3 → ℚ) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  let M0 : Line := ⟨Submodule.span ℚ {(Pi.single 0 1 : Fin 3 → ℚ)},
    finrank_span_singleton h0, trivial⟩
  let M1 : Line := ⟨Submodule.span ℚ {(Pi.single 1 1 : Fin 3 → ℚ)},
    finrank_span_singleton h1, trivial⟩
  by_cases hL : M0 = L
  · refine ⟨M1, fun h => ?_⟩
    have e : M0 = M1 := hL.trans h.symm
    have hm : (Pi.single 0 1 : Fin 3 → ℚ) ∈ Submodule.span ℚ {(Pi.single 1 1 : Fin 3 → ℚ)} := by
      have : (Pi.single 0 1 : Fin 3 → ℚ) ∈ M0.val := Submodule.mem_span_singleton_self _
      rw [e] at this
      exact this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrFun hc 0
    simp at this
  · exact ⟨M0, hL⟩

theorem exists_plane_above (L : Line) : ∃ P : Plane, incidence L P := by
  obtain ⟨M, hM⟩ := exists_line_ne L
  exact ⟨TernaryPoly.GoodIncidenceConnected.spanPlane (fun _ => True) L M (Ne.symm hM),
    TernaryPoly.GoodIncidenceConnected.line_lt_plane (fun _ => True) le_sup_left⟩

theorem flagLine_surjective : Function.Surjective flagLine := by
  intro L
  obtain ⟨P, hP⟩ := exists_plane_above L
  obtain ⟨g, hg, _⟩ := TernaryPoly.SymmetricSpaceBoundaryFaces.exists_frame_for_incident L P hP
  exact ⟨QuotientGroup.mk g, (flagLine_mk g).trans hg⟩

theorem flagPlane_surjective : Function.Surjective flagPlane := by
  intro P
  obtain ⟨L, hL⟩ := P.property.2
  have hLP : incidence L P := TernaryPoly.GoodIncidenceConnected.line_lt_plane (fun _ => True) hL
  obtain ⟨g, _, hg⟩ := TernaryPoly.SymmetricSpaceBoundaryFaces.exists_frame_for_incident L P hLP
  exact ⟨QuotientGroup.mk g, (flagPlane_mk g).trans hg⟩

/-- The rational line and plane of a complete flag are incident. -/
theorem edge_incidence (e : Edges) :
    incidence (flagLine (endpoint .line e)) (flagPlane (endpoint .plane e)) := by
  have hle := edge_subspace_incidence e
  exact TernaryPoly.GoodIncidenceConnected.line_lt_plane (fun _ => True) hle

/-- The pair of a complete flag. -/
def edgePair (e : Edges) : {p : Line × Plane // incidence p.1 p.2} :=
  ⟨(flagLine (endpoint .line e), flagPlane (endpoint .plane e)), edge_incidence e⟩

theorem edgePair_injective : Function.Injective edgePair := by
  intro e e' h
  have h1 := congrArg (fun p => p.1.1) h
  have h2 := congrArg (fun p => p.1.2) h
  exact edge_eq_of_endpoints_eq e e' (flagPlane_injective h2) (flagLine_injective h1)

theorem edgePair_surjective : Function.Surjective edgePair := by
  rintro ⟨⟨L, P⟩, hLP⟩
  obtain ⟨g, hL, hP⟩ := TernaryPoly.SymmetricSpaceBoundaryFaces.exists_frame_for_incident L P hLP
  refine ⟨QuotientGroup.mk g, Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact (flagLine_mk g).trans hL
  · exact (flagPlane_mk g).trans hP

/-- **Complete flags are the incident pairs of a rational line and a rational plane.** -/
def edgeEquiv : Edges ≃ {p : Line × Plane // incidence p.1 p.2} :=
  Equiv.ofBijective edgePair ⟨edgePair_injective, edgePair_surjective⟩

/-- Line flags are the rational lines. -/
def flagLineEquiv : Flags .line ≃ Line := Equiv.ofBijective flagLine ⟨flagLine_injective, flagLine_surjective⟩

/-- Plane flags are the rational planes. -/
def flagPlaneEquiv : Flags .plane ≃ Plane :=
  Equiv.ofBijective flagPlane ⟨flagPlane_injective, flagPlane_surjective⟩

/-- The identification of complete flags with incident pairs is equivariant for `GL₃(ℚ)`. -/
theorem edgePair_smul (g : RationalGL3) (e : Edges) :
    (edgePair (g • e)).1 = (TernaryPoly.OrdinaryFullAction.lineAction g (edgePair e).1.1,
      TernaryPoly.OrdinaryFullAction.planeAction g (edgePair e).1.2) := by
  change (flagLine (endpoint .line (g • e)), flagPlane (endpoint .plane (g • e))) = _
  rw [endpoint_smul, endpoint_smul, flagLine_smul, flagPlane_smul]
  rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
