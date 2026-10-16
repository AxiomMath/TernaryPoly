module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspFullness
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TracePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointLinear
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AwayGood
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AllCorrespondences

@[expose] public section


/-!
# Local nondegeneracy from Hecke adjointness of the cusp pairing

Fix a representative line `v̄` and the plane cusp `g` of its dual plane. Suppose the local value at
`v̄` is detected by a bilinear pairing `⟨b, η⟩` between the line summand classes `b` and the local
cohomology classes `η` at the plane cusp, in the following sense:

* **detection**: a nonzero pairing of a line class with the plane coordinate of a class forces a
  nonzero local value for every admissible choice of representatives;
* **left nondegeneracy**: a line summand class with nonzero coordinate at `v̄` pairs nontrivially
  with the plane coordinate of some class of the plane stratum;
* **adjointness**: for each away-from-three correspondence `t`, the functional `⟨b, ·⟩` is an
  eigenfunctional of the local Hecke operator `T_t` at the plane cusp with the eigenvalue
  `e_t` of the pair character (for `T_p`, the adjointness `⟨T_p x, y⟩ = κ ⟨x, T_p y⟩` of the Levi
  pairing combined with the affine edge formulas yields exactly such an eigenvalue, see
  `HeckeAdjointLevi.pairing_eigen_of_edge`).

The plane stratum is finite dimensional and the away-from-three Hecke operators on it commute, so it
is the sum of the joint generalized eigenspaces of the family; the nonzero functional
`a ↦ ⟨b, cuspRes a⟩` is nonzero on the one for the character `e`. Its image under the Shapiro
coordinate lies in the local joint generalized eigenspace of the pair character, and any plane
summand class with this coordinate has nonzero local value against `b`. This is local nondegeneracy
at the cusp.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLocal

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  {n : ℕ}

/-- The plane stratum `H²(Γ, Fun(plane flags, V))` is finite dimensional (it is a factor of the
finite-dimensional space of boundary coordinates). -/
theorem finiteDimensional_plane (n : ℕ) (χ : RankOneCharacter) :
    FiniteDimensional ℂ (StratumH2 n χ .plane) := by
  have := TernaryPeriodPolynomials.BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional
    n χ
  exact Module.Finite.of_injective
    (LinearMap.inl ℂ (StratumH2 n χ .plane) (StratumH2 n χ .line)) (fun x y h => by simpa using h)

/-- **Local pairing data at a line cusp.** A bilinear pairing of the line summand with the local
cohomology at the plane cusp `g`, with the three properties used to produce a nonzero partner:
detection of the local value, left nondegeneracy on the plane coordinates, and eigenfunctional
adjointness for the character `e`. -/
structure LocalPairingData (Θ : TraceData ι L P) (D : InducingData n)
    (T : DualityData n D.chi) (v : L) (g : Bool) (e : HeckeCorrespondence → ℂ) where
  /-- The pairing of a line summand class with a local plane class. -/
  pairing : boundarySummand D .line →ₗ[ℂ] CuspH2 n D.chi .plane g →ₗ[ℂ] ℂ
  /-- Left nondegeneracy: a line class with nonzero coordinate at `v̄` pairs nontrivially with the
  Shapiro coordinate of some plane class. -/
  nondegenerate : ∀ b : boundarySummand D .line,
    fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b.1 ≠ 0 →
    ∃ a : StratumH2 n D.chi .plane, pairing b (cuspRes n D.chi .plane g a) ≠ 0
  /-- Adjointness: `⟨b, ·⟩` is an eigenfunctional of every away-from-three local Hecke operator at
  the plane cusp, with eigenvalue `e t`. -/
  eigen : ∀ (t : {t : HeckeCorrespondence // AwayThree t}) (b : boundarySummand D .line)
    (η : CuspH2 n D.chi .plane g),
    pairing b (localOp n D.chi t.1 t.2 .plane g η) = e t.1 * pairing b η
  /-- Detection: a nonzero pairing of the classes of the representatives forces a nonzero local
  value. -/
  value : ∀ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
    (y : MaximalCycles n D.chi .plane)
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
      z ∈ boundarySummand D .line),
    EdgePrimitive z w → PlaneEdgeExact y →
    pairing ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi)
        .line) z, hz⟩
      (cuspRes n D.chi .plane g (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y)) ≠ 0 →
    lineValue Θ T v z w y ≠ 0

/-- **Local nondegeneracy from Hecke adjointness.** Local pairing data for the pair character at
the plane cusp `g` gives local nondegeneracy at the representative line `v̄`: the joint generalized
eigenclass `η` is the Shapiro coordinate of a vector of the joint generalized eigenspace, on which
the eigenfunctional `⟨b, cuspRes ·⟩` is nonzero. -/
theorem localNondegenerate_of_localPairing (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g : Bool)
    (data : LocalPairingData Θ D T v g (pairCharacter D hecke hhecke)) :
    LocalNondegenerate Θ D T hecke hhecke v g := by
  intro b hb hne
  have := finiteDimensional_plane n D.chi
  obtain ⟨a₁, ha₁⟩ := data.nondegenerate ⟨b, hb⟩ hne
  obtain ⟨φ, hφ⟩ : ∃ φ : StratumH2 n D.chi .plane →ₗ[ℂ] ℂ,
      ∀ a, φ a = data.pairing ⟨b, hb⟩ (cuspRes n D.chi .plane g a) :=
    ⟨(data.pairing ⟨b, hb⟩).comp (cuspRes n D.chi .plane g), fun a => rfl⟩
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 : φ a₁ = 0 := by simp [h0]
    rw [hφ] at h1
    exact ha₁ h1
  have hcomm : ∀ s t : {t : HeckeCorrespondence // AwayThree t},
      Commute (hecke .plane s.1) (hecke .plane t.1) := by
    intro s t
    exact TernaryPeriodPolynomials.HeckeCommutativity.realizesHecke_comm_all
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) (hecke .plane)
      (hhecke .plane)
      (TernaryPeriodPolynomials.HeckeCommutativity.good_of_awayThree s.2) t.1
  have hφT : ∀ (t : {t : HeckeCorrespondence // AwayThree t}) (a : StratumH2 n D.chi .plane),
      φ (hecke .plane t.1 a) = pairCharacter D hecke hhecke t.1 * φ a := by
    intro t a
    have h := cuspRes_hecke hecke hhecke t.1 t.2 .plane g a
    exact (hφ _).trans ((congrArg (data.pairing ⟨b, hb⟩) h).trans
      ((data.eigen t ⟨b, hb⟩ (cuspRes n D.chi .plane g a)).trans
        (congrArg (fun x => pairCharacter D hecke hhecke t.1 * x) (hφ a).symm)))
  obtain ⟨a₀, ha₀, hφa₀⟩ := exists_mem_jointSpace_of_functional
    (fun t : {t : HeckeCorrespondence // AwayThree t} => hecke .plane t.1) hcomm φ hφ0
    (fun t => pairCharacter D hecke hhecke t.1) hφT
  have hη : cuspRes n D.chi .plane g a₀ ∈
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane g := by
    simp only [localJoint, Submodule.mem_iInf, Subtype.forall]
    intro t ht
    exact intertwine_mem_maxGenEigenspace (cuspRes n D.chi .plane g) (hecke .plane t)
      (localOp n D.chi t ht .plane g) (cuspRes_hecke hecke hhecke t ht .plane g)
      (pairCharacter D hecke hhecke t) (mem_jointSpace_iff.mp ha₀ ⟨t, ht⟩)
  have hne0 : data.pairing ⟨b, hb⟩ (cuspRes n D.chi .plane g a₀) ≠ 0 := by
    rw [← hφ a₀]
    exact hφa₀
  refine ⟨cuspRes n D.chi .plane g a₀, hη, ?_⟩
  intro ξ hξ hξη
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective _ b
  have hz' : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z = b := hz
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ ξ
  have hy' : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y = ξ := hy
  have hzmem : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z ∈
        boundarySummand D .line := by
    rw [hz']
    exact hb
  obtain ⟨w, hw⟩ := TernaryPeriodPolynomials.BoundaryDuality.TracePairing.exists_edgePrimitive_of_mem
    z hzmem
  have hflat : PlaneEdgeExact y :=
    TernaryPeriodPolynomials.BoundaryDuality.TracePairing.flat_of_mem hξ y hy'
  have hbz : (⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z, hzmem⟩ :
        boundarySummand D .line) = ⟨b, hb⟩ := Subtype.ext hz'
  refine ⟨z, w, y, hz', hy', hw, data.value z w y hzmem hw hflat ?_⟩
  have e := congrArg₂ (fun x y => data.pairing x y) hbz
    ((congrArg (cuspRes n D.chi .plane g) hy').trans hξη)
  exact fun h => hne0 (e.symm.trans h)

/-- **Local nondegeneracy from an edge pairing.** Let `π : X × Y → ℂ` be a pairing of Levi
cohomology groups, `xb` the edge image of the line coordinate of a line summand class, and `g'` the
edge map of the local cohomology at the plane cusp. If the functional `π (xb b) (g' ·)` is an
eigenfunctional of every away-from-three local operator with the pair character (this is what
`HeckeAdjointLevi.pairing_eigen_of_edge` and `HeckeAdjointLevi.pairing_eigen_of_adjoint` produce
from the edge formulas and the adjointness of the Levi Hecke operators), the pairing is nondegenerate
on the plane coordinates, and a nonzero pairing of the classes forces a nonzero local value, then
the local value is nondegenerate at the cusp. -/
theorem localNondegenerate_of_edges (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g : Bool) {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (xb : boundarySummand D .line →ₗ[ℂ] X) (g' : CuspH2 n D.chi .plane g →ₗ[ℂ] Y)
    (heigen : ∀ (t : {t : HeckeCorrespondence // AwayThree t}) (b : boundarySummand D .line)
      (η : CuspH2 n D.chi .plane g),
      π (xb b) (g' (localOp n D.chi t.1 t.2 .plane g η)) =
        pairCharacter D hecke hhecke t.1 * π (xb b) (g' η))
    (nondegenerate : ∀ b : boundarySummand D .line,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b.1 ≠ 0 →
      ∃ a : StratumH2 n D.chi .plane, π (xb b) (g' (cuspRes n D.chi .plane g a)) ≠ 0)
    (value : ∀ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane)
      (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
        z ∈ boundarySummand D .line),
      EdgePrimitive z w → PlaneEdgeExact y →
      π (xb ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi)
          .line) z, hz⟩)
        (g' (cuspRes n D.chi .plane g (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y))) ≠ 0 →
      lineValue Θ T v z w y ≠ 0) :
    LocalNondegenerate Θ D T hecke hhecke v g :=
  localNondegenerate_of_localPairing Θ T hecke hhecke v g
    { pairing := LinearMap.compl₁₂ π xb g'
      nondegenerate := fun b hb => by simpa using nondegenerate b hb
      eigen := fun t b η => by simpa using heigen t b η
      value := fun z w y hz hw hflat hne => value z w y hz hw hflat (by simpa using hne) }

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLocal
