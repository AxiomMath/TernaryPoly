module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient

@[expose] public section


/-!
# The local `T_p` at the good line is `1 + p^{-(n+1)} T_p` on the binary edge

For the explicit local correspondence `goodLineCosets p` of the good-line stabilizer
`Λ₁ = {Q(3b, m, 1)}` and classes whose restriction to the radical vanishes, the Sol binary edge
`H²(Λ₁, Sym^n ⊗ det⁻¹) ⊇ ker(res) → H¹(GL₂(ℤ), Sym^{n+1})` (twist `0`) intertwines the local Hecke
operator with `1 + p^{-(n+1)} T_p`, `T_p` the cohomological Hecke operator of
`GL₂(ℤ) diag(p, 1) GL₂(ℤ)` (`edgeK_hecke`). The local operator preserves the kernel of the
restriction (`heckeK_mem`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineHecke

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates GoodLineCosets GoodLineEdge
open GoodLineCoordinate IdentityPlaneCoordinate LevelOneHeckeH1 HeckeH1 AmbientHecke LocalHecke

variable (n : ℕ) (p : Nat.Primes)

/-- `ρ(α_j)⁻¹ = p^{n+1} ρ(B_j)` on `Sym^{n+1}` with twist `0`. -/
theorem rho_rep_inv0 (j : Option (Fin p.val)) (v : arithmeticBinaryRep (n + 1) 0) :
    rationalRho (n + 1) 0 (binaryHeckeRepresentative p j)⁻¹ v =
      ((p.val : ℂ) ^ (n + 1)) • rationalRho (n + 1) 0 (BGL p j) v := by
  set u : ℚˣ := Units.mk0 (p.val : ℚ) (p_ne_zero p)
  have h := BGL_inv_eq p j
  have hrep : (binaryHeckeRepresentative p j)⁻¹ =
      BGL p j * GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
    rw [show binaryHeckeRepresentative p j =
      (GeneralLinearGroup.scalar (Fin 2) u⁻¹)⁻¹ * (BGL p j)⁻¹ by rw [h, inv_mul_cancel_left]]
    rw [_root_.mul_inv_rev, inv_inv, inv_inv]
  rw [hrep, map_mul, Module.End.mul_apply, ← map_smul]
  congr 1
  change Binary.homogeneousAction (n + 1) 0
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.scalar (Fin 2) u⁻¹))
      (v : Binary.HomogeneousPoly (n + 1)) = _
  rw [GeneralLinearGroup.map_scalar]
  refine (EisensteinGraph.StandardConstruction.BinaryCentralCoefficient.homogeneousAction_scalar
    (n + 1) 0 _ (v : Binary.HomogeneousPoly (n + 1))).trans ?_
  congr 1
  simp [u]

/-- The Hecke cocycle of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` on `Sym^{n+1}` with twist `0`. -/
abbrev heckeZ0 : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ]
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  heckeCocycle (arithmeticCosets p) (arithmeticBinaryRep (n + 1) 0) (rationalRho (n + 1) 0)
    (arithmetic_compat (n + 1) 0) integralEmbed_injective

theorem cast_p1 : ((p.val : ℂ) ^ (n + 1))⁻¹ * (p.val : ℂ) ^ (n + 1) = 1 := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact inv_mul_cancel₀ (pow_ne_zero _ hp)

variable (hn : 0 < n)

/-- **Cocycle-level identity**: `E(Tc) = E(c) + p^{-(n+1)} T_p E(c)`. -/
theorem edgeCycleL_hecke (c : RelL n) :
    goodLineBinaryEdgeCycle n hn (heckeRelL n p c) =
      goodLineBinaryEdgeCycle n hn c +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeZ0 n p (goodLineBinaryEdgeCycle n hn c) := by
  apply groupCohomology.cocycles₁_ext
  intro m
  have h := binaryEdgeL_hecke n p hn c m
  have hz : heckeZ0 n p (goodLineBinaryEdgeCycle n hn c) m =
      ∑ j, rationalRho (n + 1) 0 (binaryHeckeRepresentative p j)⁻¹
        (goodLineBinaryEdgeCycle n hn c (arithmeticDelta p m j)) :=
    heckeCocycle_apply _ _ _ _ _ _ _
  have hsum : ∑ j : Option (Fin p.val), Binary.homogeneousAction (n + 1) 0 (cx2 (BGL p j))
        (bE n hn c (arithmeticDelta p m j)) =
      ((p.val : ℂ) ^ (n + 1))⁻¹ • heckeZ0 n p (goodLineBinaryEdgeCycle n hn c) m := by
    rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [rho_rep_inv0, smul_smul, cast_p1, one_smul]
    rfl
  exact h.trans (by rw [hsum]; rfl)

/-- **Class-level identity for relative cocycles.** -/
theorem edgeRelL_hecke (c : RelL n) :
    goodLineBinaryEdge n hn
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) (heckeRelL n p c)) =
      goodLineBinaryEdge n hn
          (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) c) +
        ((p.val : ℂ) ^ (n + 1))⁻¹ • arithmeticHecke (n + 1) 0 p (goodLineBinaryEdge n hn
          (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) c)) := by
  rw [← goodLineBinaryEdgeCycle_H1, ← goodLineBinaryEdgeCycle_H1, edgeCycleL_hecke, map_add, map_smul,
    arithmeticHecke, heckeH1_H1π]

/-! ### On the ambient `H²(Λ₁, V)` -/

/-- The comparison of ambient cohomology with group cohomology of `Λ₁`. -/
def toH2L : H2 Λ₁ (ρn n) →ₗ[ℂ] groupCohomology.H2 (goodLineCoefficientRep n) :=
  (LinearMap.range (boundaryMap Λ₁ (ρn n))).liftQ
    ((groupCohomology.H2π (goodLineCoefficientRep n)).hom ∘ₗ ambientCocycleToGroup Λ₁ (ρn n)) (by
      rintro _ ⟨P, rfl⟩
      exact LinearMap.mem_ker.mpr ((ambientCocycle_H2_zero_iff Λ₁ (ρn n) _).mpr ⟨P, rfl⟩))

theorem toH2L_classOf (C : cocycles Λ₁ (ρn n)) :
    toH2L n (classOf Λ₁ (ρn n) C) =
      groupCohomology.H2π (goodLineCoefficientRep n) (ambientCocycleToGroup Λ₁ (ρn n) C) := rfl

theorem toH2L_injective : Function.Injective (toH2L n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change toH2L n (classOf Λ₁ (ρn n) C) = 0 at hx
  rw [toH2L_classOf] at hx
  exact (classOf_eq_zero_iff Λ₁ (ρn n) C).mpr ((ambientCocycle_H2_zero_iff Λ₁ (ρn n) C).mp hx)

/-- The classes whose restriction to the radical vanishes. -/
def KL : Submodule ℂ (H2 Λ₁ (ρn n)) :=
  (LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))).comap
    (toH2L n)

/-- The binary edge on `KL`. -/
def edgeK : KL n →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (goodLineBinaryEdge n hn).comp (LinearMap.codRestrict _ ((toH2L n).comp (KL n).subtype) (fun x => x.2))

theorem edgeK_injective : Function.Injective (edgeK n hn) := by
  intro x y h
  have h1 := goodLineBinaryEdge_injective_of_invariant_H2_zero n hn
    (ModularH2.binaryH2_zero _) h
  apply Subtype.ext
  exact toH2L_injective n (congrArg Subtype.val h1)

/-- A class of `KL` is represented by a relative cocycle. -/
theorem exists_rel (x : H2 Λ₁ (ρn n)) (hx : x ∈ KL n) :
    ∃ c : RelL n, toH2L n x = groupCohomology.H2π (goodLineCoefficientRep n) c.val := by
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective goodLineRadicalInclusion
    goodLineRadicalInclusion_injective (goodLineCoefficientRep n) ⟨toH2L n x, hx⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- The Hecke image of a class of `KL`, computed from a relative representative. -/
theorem toH2L_hecke (x : H2 Λ₁ (ρn n)) (c : RelL n)
    (hc : toH2L n x = groupCohomology.H2π (goodLineCoefficientRep n) c.val) :
    toH2L n (cohomologyAction (ρn n) (goodLineCosets p) x) =
      groupCohomology.H2π (goodLineCoefficientRep n) (heckeRelL n p c).val := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change toH2L n (cohomologyAction (ρn n) (goodLineCosets p) (classOf Λ₁ (ρn n) C)) = _
  rw [cohomologyAction_classOf, toH2L_classOf]
  change toH2L n (classOf Λ₁ (ρn n) C) = _ at hc
  rw [toH2L_classOf] at hc
  exact ambientHecke_congr (goodLineCosets p) (ρn n) C (liftCocycle (goodLineCosets p) (ρn n) c.val)
    (hc.trans (congrArg (groupCohomology.H2π (goodLineCoefficientRep n))
      (ambientCocycleToGroup_lift (goodLineCosets p) (ρn n) c.val).symm))

/-- **The local Hecke operator preserves `KL`.** -/
theorem heckeK_mem (x : H2 Λ₁ (ρn n)) (hx : x ∈ KL n) :
    cohomologyAction (ρn n) (goodLineCosets p) x ∈ KL n := by
  obtain ⟨c, hc⟩ := exists_rel n x hx
  show toH2L n (cohomologyAction (ρn n) (goodLineCosets p) x) ∈
    LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))
  rw [toH2L_hecke n p x c hc]
  exact (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) (heckeRelL n p c)).2

/-- **The local Hecke operator of the good line, identified on `KL`.** -/
theorem edgeK_hecke (x : H2 Λ₁ (ρn n)) (hx : x ∈ KL n) :
    edgeK n hn ⟨cohomologyAction (ρn n) (goodLineCosets p) x, heckeK_mem n p x hx⟩ =
      edgeK n hn ⟨x, hx⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        arithmeticHecke (n + 1) 0 p (edgeK n hn ⟨x, hx⟩) := by
  obtain ⟨c, hc⟩ := exists_rel n x hx
  have e1 : (⟨toH2L n (cohomologyAction (ρn n) (goodLineCosets p) x), heckeK_mem n p x hx⟩ :
      LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))) =
      relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) (heckeRelL n p c) :=
    Subtype.ext (toH2L_hecke n p x c hc)
  have e2 : (⟨toH2L n x, hx⟩ :
      LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))) =
      relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) c := Subtype.ext hc
  show goodLineBinaryEdge n hn ⟨toH2L n (cohomologyAction (ρn n) (goodLineCosets p) x),
      heckeK_mem n p x hx⟩ = goodLineBinaryEdge n hn ⟨toH2L n x, hx⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        arithmeticHecke (n + 1) 0 p (goodLineBinaryEdge n hn ⟨toH2L n x, hx⟩)
  rw [e1, e2, edgeRelL_hecke]

end TernaryPeriodPolynomials.Spectral.GoodLineHecke
