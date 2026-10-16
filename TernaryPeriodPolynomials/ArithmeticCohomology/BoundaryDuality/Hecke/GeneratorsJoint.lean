module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Coordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.TpExistence

@[expose] public section


/-!
# The joint generalized eigenspace of the prime operators `T_p` at a cusp

At a cusp, write `J` for the joint generalized eigenspace of the local operators of the prime
correspondences `T_p = Γ diag(p,1,1) Γ` (`p ≠ 3`) for a character `c`, and `L ⊆ J` for the joint
generalized eigenspace of all away-from-three local operators. Dimension bounds for the local
eigenspace proved through the edge formulas of `T_p` bound `J` as well, since they only test
membership against the operators `T_p`.

Once `J ⊆ L`, local nondegeneracy needs no eigen relation for the operators outside `{T_p}`: a
nonzero pairing of the line class with a class of `J` already produces an element of `L`. The edge
map to the Levi cohomology then only has to be defined on `J`, whose classes are parabolic, and the
eigenfunctional relation for the `T_p` enters only to show that the pairing is nonzero on `J`: a
functional on a finite-dimensional space which is an eigenfunctional of a commuting family is
nonzero on the joint generalized eigenspace of its eigenvalues, and an injective edge map with image
of the same dimension is onto that eigenspace.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators

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
open TernaryPeriodPolynomials.Separation

/-- The joint generalized eigenspace, at the cusp `(side, good)`, of the local operators of the
prime correspondences `T_p` (`p ≠ 3`) for the character `c`. -/
def localJointGen (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) : Submodule ℂ (CuspH2 n χ side good) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3},
    (localOp n χ (TpExistence.tp p.1) (TpExistence.tp_awayThree p.1 p.2) side good).maxGenEigenspace
      (c (TpExistence.tp p.1))

/-- The local joint generalized eigenspace for all away-from-three correspondences lies in the one
for the prime correspondences. -/
theorem localJoint_le_localJointGen (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ)
    (side : Side) (good : Bool) : localJoint n χ c side good ≤ localJointGen n χ c side good := by
  intro x hx
  simp only [localJointGen, localJoint, Submodule.mem_iInf] at hx ⊢
  intro p
  exact hx ⟨TpExistence.tp p.1, TpExistence.tp_awayThree p.1 p.2⟩

/-- **Local upper bound for the prime correspondences only.** The joint generalized eigenspace of
the operators `T_p` at the cusp is finite dimensional of dimension at most `m`. -/
def LocalUpperBoundGen (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) (m : ℕ) : Prop :=
  FiniteDimensional ℂ (localJointGen n χ c side good) ∧
    Module.finrank ℂ (localJointGen n χ c side good) ≤ m

/-- A bound for the prime correspondences gives the bound for all away-from-three
correspondences. -/
theorem LocalUpperBoundGen.toLocalUpperBound {n : ℕ} {χ : RankOneCharacter}
    {c : HeckeCorrespondence → ℂ} {side : Side} {good : Bool} {m : ℕ}
    (h : LocalUpperBoundGen n χ c side good m) : LocalUpperBound n χ c side good m := by
  obtain ⟨hfin, hle⟩ := h
  exact ⟨Submodule.finiteDimensional_of_le (localJoint_le_localJointGen n χ c side good),
    (Submodule.finrank_mono (localJoint_le_localJointGen n χ c side good)).trans hle⟩

variable {n : ℕ}

/-- **A nonzero pairing on the prime eigenspace.** Let `ψ` be a nonzero functional on a finite
dimensional space `Y`, an eigenfunctional (`ψ ∘ B_p = e_p ψ`) of a commuting family `B_p`. If the
edge `g'` out of the cusp-local subspace `J` maps onto the joint generalized eigenspace of the `B_p`
for `e`, then `ψ ∘ g'` is nonzero on `J`. -/
theorem exists_pairing_ne_zero_of_eigen {M Y : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] {κ : Type*} (B : κ → Module.End ℂ Y)
    (hcomm : ∀ i j, Commute (B i) (B j)) (e : κ → ℂ) (ψ : Y →ₗ[ℂ] ℂ) (hψ0 : ψ ≠ 0)
    (hψ : ∀ i y, ψ (B i y) = e i * ψ y) (J : Submodule ℂ M) (g' : J →ₗ[ℂ] Y)
    (hsurj : ∀ y ∈ jointSpace B e, ∃ η : J, g' η = y) : ∃ η : J, ψ (g' η) ≠ 0 := by
  obtain ⟨y, hy, hψy⟩ := exists_mem_jointSpace_of_functional B hcomm ψ hψ0 e hψ
  obtain ⟨η, rfl⟩ := hsurj y hy
  exact ⟨η, hψy⟩

/-- An injective map into a finite-dimensional space `K` from a space of dimension at least that of
`K` has range `K`, provided its range lies in `K`. -/
theorem range_eq_of_finrank_le {J Y : Type*} [AddCommGroup J] [Module ℂ J] [AddCommGroup Y]
    [Module ℂ Y] (g' : J →ₗ[ℂ] Y) (hinj : Function.Injective g') (K : Submodule ℂ Y)
    [FiniteDimensional ℂ K] (hle : ∀ η, g' η ∈ K)
    (hdim : Module.finrank ℂ K ≤ Module.finrank ℂ J) : ∀ y ∈ K, ∃ η : J, g' η = y := by
  have hrange : LinearMap.range g' ≤ K := by
    rintro _ ⟨η, rfl⟩
    exact hle η
  have hfr : Module.finrank ℂ (LinearMap.range g') = Module.finrank ℂ J :=
    LinearMap.finrank_range_of_inj hinj
  have heq : LinearMap.range g' = K :=
    Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  intro y hy
  rw [← heq] at hy
  exact hy

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]

/-- **Local nondegeneracy with the edge map defined on the prime eigenspace only.** Let
`J = localJointGen` be the joint generalized eigenspace of the operators `T_p` at the plane cusp `g`,
assumed to lie in the joint generalized eigenspace `L` of all away-from-three operators. Let `π` be a pairing of
Levi cohomology groups, `xb` the edge image of the line coordinate of a line summand class, and `g'`
the edge map of the plane cusp, defined on `J` only (its classes are the parabolic ones). If every
line class with nonzero coordinate at `v̄` pairs nontrivially with the edge of some class of `J`, and
a nonzero pairing of the classes forces a nonzero local value, then the local value is nondegenerate
at the cusp. -/
theorem localNondegenerate_of_edges_gen (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g : Bool)
    (hJ : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g ≤
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane g)
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (xb : boundarySummand D .line →ₗ[ℂ] X)
    (g' : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g →ₗ[ℂ] Y)
    (nondegenerate : ∀ b : boundarySummand D .line,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b.1 ≠ 0 →
      ∃ η : localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g, π (xb b) (g' η) ≠ 0)
    (value : ∀ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane)
      (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
        z ∈ boundarySummand D .line)
      (hy : cuspRes n D.chi .plane g (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y) ∈
          localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g),
      EdgePrimitive z w → PlaneEdgeExact y →
      π (xb ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi)
          .line) z, hz⟩)
        (g' ⟨cuspRes n D.chi .plane g (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y), hy⟩) ≠ 0 →
      lineValue Θ T v z w y ≠ 0) :
    LocalNondegenerate Θ D T hecke hhecke v g := by
  intro b hb hne
  obtain ⟨η, hη⟩ := nondegenerate ⟨b, hb⟩ hne
  refine ⟨(η : CuspH2 n D.chi .plane g), hJ η.2, ?_⟩
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
  obtain ⟨w, hw⟩ :=
    TernaryPeriodPolynomials.BoundaryDuality.TracePairing.exists_edgePrimitive_of_mem
      z hzmem
  have hflat : PlaneEdgeExact y :=
    TernaryPeriodPolynomials.BoundaryDuality.TracePairing.flat_of_mem hξ y hy'
  have hbz : (⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z, hzmem⟩ :
        boundarySummand D .line) = ⟨b, hb⟩ := Subtype.ext hz'
  have hcl : cuspRes n D.chi .plane g (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y) =
        (η : CuspH2 n D.chi .plane g) := by
    rw [hy']
    exact hξη
  have hmemJ : cuspRes n D.chi .plane g (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y) ∈
        localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g := by
    rw [hcl]
    exact η.2
  refine ⟨z, w, y, hz', hy', hw, value z w y hzmem hmemJ hw hflat ?_⟩
  have hsub : (⟨cuspRes n D.chi .plane g (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y), hmemJ⟩ :
        localJointGen n D.chi (pairCharacter D hecke hhecke) .plane g) = η := Subtype.ext hcl
  have e := congrArg₂ (fun x y => π (xb x) (g' y)) hbz hsub
  exact fun h => hη (e.symm.trans h)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
