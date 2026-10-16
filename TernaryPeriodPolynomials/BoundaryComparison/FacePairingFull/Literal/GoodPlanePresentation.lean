module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceGeneric
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.FaceIdentification
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3

@[expose] public section


/-!
# The good-plane cusp: a native presentation and the conjugation to block coordinates

The library's good-plane edge map (`GoodPlaneEdge3.goodPlaneEdge`) is defined on the local cohomology at the cusp flag
`cuspFlag .plane true` through the conjugation transport `psiG` (`conjH2`, `f ↦ ρ(gF)⁻¹ f(gF ·)`) to the
block-coordinate stabilizer `ΛG = gF⁻¹ Γ_F gF`, where `Γ_F`-cohomology becomes `ℤ² ⋊ (Γ₁'(3) × ℤˣ)`-cohomology and
Sol's edge `splitCohomologyEdge` applies. To compare it with the Hochschild-Serre isomorphism of `Face/Iso`, this file
puts the *same* stabilizer in the form required by the generic face machinery (`Face.faceRep`, `faceH2Equiv`,
`locallyInnerEquivCuspidal`):

* `gpIota : ℤ² ⋊ (Γ₁'(3) × ℤˣ) ≃* Γ_F`, the library splitting of `ΛG` followed by `h ↦ gF h gF⁻¹`;
  `gp_radical_fixes`: its radical fixes every complete flag over the cusp (so the generic Hochschild-Serre machinery applies);
* `gpPush`: an inhomogeneous two-cocycle of the face presentation, pushed to a two-cocycle of `ΛG`, twisting the
  coefficients by `ρ(gF)⁻¹` (`gpA`);
* `conj_prism`, `H2π_conj_eq_push`: the conjugation transport of a homogeneous cocycle and the pushed inhomogeneous face
  cocycle define the same class in `H²(ΛG, V)`: they differ by the coboundary of the explicit one-cochain
  `a ↦ ρ(gF)⁻¹ K(1, gF a gF⁻¹)`, `K(x, y) = C(x, x gF, y gF) - C(x, y, y gF)` (prism operator for right translation by `gF`,
  `prism`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodPlaneId

/-- The conjugation `h ↦ gF h gF⁻¹` identifies the block-coordinate stabilizer `ΛG` with the stabilizer of the
good-plane cusp. -/
def lamEquiv : ΛG ≃* ↥(cuspLevel .plane true) where
  toFun h := ⟨gF * h.val * gF⁻¹, hH_conj h.val h.property⟩
  invFun y := ⟨gF⁻¹ * y.val * gF, by simpa using hH'_conj y.val y.property⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change gF * (a.val * b.val) * gF⁻¹ = gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹)
    group)

/-- The presentation `ℤ² ⋊ (Γ₁'(3) × ℤˣ) ≃ Γ_F` of the stabilizer of the good-plane cusp flag, native to the
library's edge map. -/
def gpIota : RadicalLattice ⋊[goodPlaneSplitting.conjAct] Levi ≃* ↥(cuspLevel .plane true) :=
  goodPlaneSplitting.semidirectProductMulEquiv.trans lamEquiv

theorem sigma_inl (r : RadicalLattice) :
    goodPlaneSplitting.semidirectProductMulEquiv (SemidirectProduct.inl r) = radInc r := by
  change radInc r * goodPlaneSplitting 1 = _
  rw [map_one, mul_one]

theorem sigma_inr (l : Levi) :
    goodPlaneSplitting.semidirectProductMulEquiv (SemidirectProduct.inr l) = secL l := by
  change radInc 1 * goodPlaneSplitting l = _
  rw [map_one, one_mul]
  rfl

theorem gpIota_inl_val (r : RadicalLattice) :
    (gpIota (SemidirectProduct.inl r)).val = gF * planeUnipotent (r.toAdd.1 : ℚ) (r.toAdd.2 : ℚ) * gF⁻¹ := by
  change gF * ((goodPlaneSplitting.semidirectProductMulEquiv (SemidirectProduct.inl r)).val) * gF⁻¹ = _
  rw [sigma_inl]
  rfl

/-- **The radical of the good plane fixes every complete flag over it** (library presentation). -/
theorem gp_radical_fixes (r : RadicalLattice) (e : Edges)
    (he : endpoint .plane e = cuspFlag .plane true) :
    (gpIota (SemidirectProduct.inl r)).val • e = e := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
  have h1 : (QuotientGroup.mk g : Flags .plane) = QuotientGroup.mk gF := he.trans cuspFlag_eq
  have h2 := QuotientGroup.eq.mp h1
  have hg' : gF⁻¹ * g ∈ parabolic .plane := by
    have h3 : g⁻¹ * gF ∈ parabolic .plane := by simpa using h2
    have h4 := (parabolic .plane).inv_mem h3
    simpa [mul_assoc] using h4
  rw [gpIota_inl_val]
  change (QuotientGroup.mk (gF * planeUnipotent (r.toAdd.1 : ℚ) (r.toAdd.2 : ℚ) * gF⁻¹ * g) : Edges) =
    QuotientGroup.mk g
  apply QuotientGroup.eq.mpr
  have key := planeUnipotent_conj_mem_borel (gF⁻¹ * g) hg' (-(r.toAdd.1 : ℚ)) (-(r.toAdd.2 : ℚ))
  have hinv : (gF * planeUnipotent (r.toAdd.1 : ℚ) (r.toAdd.2 : ℚ) * gF⁻¹ * g)⁻¹ * g =
      (gF⁻¹ * g)⁻¹ * planeUnipotent (-(r.toAdd.1 : ℚ)) (-(r.toAdd.2 : ℚ)) * (gF⁻¹ * g) := by
    rw [← planeUnipotent_inv]
    group
  rw [hinv]
  exact key


/-! ### The twisted push to the block coordinates -/

variable (n : ℕ)

theorem rep_comm' {W : Type} [AddCommGroup W] [Module ℂ W] (R : Representation ℂ RationalGL3 W)
    (a b c d : RationalGL3) (h : a * b = c * d) (v : W) : R a (R b v) = R c (R d v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h]

/-- The face representation of the good-plane cusp in the library presentation. -/
abbrev gpRep :=
  faceRep goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota

/-- The coordinate change `ρ(gF)⁻¹` between the cusp coordinates and the block coordinates. -/
def gpA : Module.End ℂ (HomogeneousPoly n) :=
  rationalCoefficientComponent n trivialCharacter gF⁻¹

theorem gpA_intertwine (s : RadicalLattice ⋊[goodPlaneSplitting.conjAct] Levi) (v : HomogeneousPoly n) :
    gpA n (gpRep n s v) =
      rationalCoefficientComponent n trivialCharacter
        (goodPlaneSplitting.semidirectProductMulEquiv s).val (gpA n v) := by
  change rationalCoefficientComponent n trivialCharacter gF⁻¹
      (rationalCoefficientComponent n trivialCharacter
        (gF * (goodPlaneSplitting.semidirectProductMulEquiv s).val * gF⁻¹) v) = _
  apply rep_comm'
  group

theorem gpA_intertwine_symm (g : ΛG) (v : HomogeneousPoly n) :
    gpA n (gpRep n (goodPlaneSplitting.semidirectProductMulEquiv.symm g) v) =
      rationalCoefficientComponent n trivialCharacter g.val (gpA n v) := by
  rw [gpA_intertwine, MulEquiv.apply_symm_apply]

/-- Push an inhomogeneous two-cocycle of the face presentation of the good-plane cusp to a two-cocycle of the
block-coordinate stabilizer `ΛG`, twisting the coefficients by `ρ(gF)⁻¹`. -/
def gpPush (c : inhomogeneousTwoCycles (gpRep n)) : groupCohomology.cocycles₂ (coefRep n) := by
  refine ⟨fun p => (gpA n (c.val (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1)
    (goodPlaneSplitting.semidirectProductMulEquiv.symm p.2)) : coefRep n), ?_⟩
  refine (groupCohomology.mem_cocycles₂_iff (A := coefRep n) _).mpr ?_
  intro g h j
  have h1 := c.property (goodPlaneSplitting.semidirectProductMulEquiv.symm g)
    (goodPlaneSplitting.semidirectProductMulEquiv.symm h)
    (goodPlaneSplitting.semidirectProductMulEquiv.symm j)
  have h2 := congrArg (gpA n) h1
  simp only [map_zero, map_add, map_sub] at h2
  rw [gpA_intertwine_symm] at h2
  simp only [map_mul]
  have h4 : gpA n (c.val (goodPlaneSplitting.semidirectProductMulEquiv.symm g *
        goodPlaneSplitting.semidirectProductMulEquiv.symm h)
      (goodPlaneSplitting.semidirectProductMulEquiv.symm j)) +
      gpA n (c.val (goodPlaneSplitting.semidirectProductMulEquiv.symm g)
        (goodPlaneSplitting.semidirectProductMulEquiv.symm h)) =
      rationalCoefficientComponent n trivialCharacter g.val (gpA n (c.val
        (goodPlaneSplitting.semidirectProductMulEquiv.symm h)
        (goodPlaneSplitting.semidirectProductMulEquiv.symm j))) +
      gpA n (c.val (goodPlaneSplitting.semidirectProductMulEquiv.symm g)
        (goodPlaneSplitting.semidirectProductMulEquiv.symm h *
          goodPlaneSplitting.semidirectProductMulEquiv.symm j)) := by
    linear_combination (norm := abel) -h2
  exact h4

theorem gpPush_apply (c : inhomogeneousTwoCycles (gpRep n)) (g h : ΛG) :
    gpPush n c (g, h) = gpA n (c.val (goodPlaneSplitting.semidirectProductMulEquiv.symm g)
      (goodPlaneSplitting.semidirectProductMulEquiv.symm h)) := rfl

theorem sigma_symm_inl (r : RadicalLattice) :
    goodPlaneSplitting.semidirectProductMulEquiv.symm (radInc r) = SemidirectProduct.inl r := by
  rw [MulEquiv.symm_apply_eq]
  exact (sigma_inl r).symm

theorem gpPush_relative (c : radicalZeroTwoCycles goodPlaneSplitting.conjAct (gpRep n)) :
    gpPush n c.val ∈ relativeTwoCocycles goodPlaneExtension.inl (coefRep n) := by
  intro r r'
  change gpA n (c.val.val (goodPlaneSplitting.semidirectProductMulEquiv.symm (radInc r))
    (goodPlaneSplitting.semidirectProductMulEquiv.symm (radInc r'))) = 0
  rw [sigma_symm_inl, sigma_symm_inl, c.property r r', map_zero]

theorem gpPush_sub (a b : inhomogeneousTwoCycles (gpRep n)) :
    gpPush n (a - b) = gpPush n a - gpPush n b := by
  apply Subtype.ext
  funext p
  change gpA n ((a - b).val _ _) = gpA n (a.val _ _) - gpA n (b.val _ _)
  rw [← map_sub]
  rfl

theorem gpPush_add (a b : inhomogeneousTwoCycles (gpRep n)) :
    gpPush n (a + b) = gpPush n a + gpPush n b := by
  apply Subtype.ext
  funext p
  change gpA n ((a + b).val _ _) = gpA n (a.val _ _) + gpA n (b.val _ _)
  rw [← map_add]
  rfl

theorem gpPush_boundary (u : (RadicalLattice ⋊[goodPlaneSplitting.conjAct] Levi) → HomogeneousPoly n) :
    groupCohomology.H2π (coefRep n) (gpPush n (inhomogeneousBoundaryMap (gpRep n) u)) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun g => (gpA n (u (goodPlaneSplitting.semidirectProductMulEquiv.symm g)) : coefRep n), ?_⟩
  funext p
  have hd := groupCohomology.d₁₂_hom_apply (coefRep n)
    (fun g => gpA n (u (goodPlaneSplitting.semidirectProductMulEquiv.symm g))) p
  rw [hd]
  change _ = gpA n (gpRep n (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1)
      (u (goodPlaneSplitting.semidirectProductMulEquiv.symm p.2)) -
    u (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1 *
      goodPlaneSplitting.semidirectProductMulEquiv.symm p.2) +
    u (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1))
  rw [map_add, map_sub, gpA_intertwine_symm, map_mul]
  rfl

/-! ### Conjugation by the frame is the inhomogeneous conjugation up to a coboundary -/

section Prism

variable {n} (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))

theorem cocycle4 (v0 v1 v2 v3 : RationalGL3) :
    C.val.val ![v1, v2, v3] - C.val.val ![v0, v2, v3] + C.val.val ![v0, v1, v3] -
      C.val.val ![v0, v1, v2] = 0 :=
  congrFun C.property ![v0, v1, v2, v3]

theorem equivar3 (a : ↥(cuspLevel .plane true)) (v0 v1 v2 : RationalGL3) :
    C.val.val ![a.val * v0, a.val * v1, a.val * v2] =
      rationalCoefficientComponent n trivialCharacter a.val (C.val.val ![v0, v1, v2]) := by
  have h := C.val.property a ![v0, v1, v2]
  have e : (fun i => a.val * (![v0, v1, v2] : Fin 3 → RationalGL3) i) =
      ![a.val * v0, a.val * v1, a.val * v2] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  exact h

/-- The prism `K`. -/
def Kf (g x y : RationalGL3) : HomogeneousPoly n :=
  C.val.val ![x, x * g, y * g] - C.val.val ![x, y, y * g]

theorem prism (g x0 x1 x2 : RationalGL3) :
    C.val.val ![x0 * g, x1 * g, x2 * g] - C.val.val ![x0, x1, x2] =
      Kf C g x1 x2 - Kf C g x0 x2 + Kf C g x0 x1 := by
  have T1 := cocycle4 C x0 (x0 * g) (x1 * g) (x2 * g)
  have T2 := cocycle4 C x0 x1 (x1 * g) (x2 * g)
  have T3 := cocycle4 C x0 x1 x2 (x2 * g)
  unfold Kf
  linear_combination (norm := abel) T1 - T2 + T3

theorem Kf_equivar (g : RationalGL3) (a : ↥(cuspLevel .plane true)) (x y : RationalGL3) :
    Kf C g (a.val * x) (a.val * y) =
      rationalCoefficientComponent n trivialCharacter a.val (Kf C g x y) := by
  unfold Kf
  have e1 : (![a.val * x, a.val * x * g, a.val * y * g] : Fin 3 → RationalGL3) =
      ![a.val * x, a.val * (x * g), a.val * (y * g)] := by
    simp only [mul_assoc]
  have e2 : (![a.val * x, a.val * y, a.val * y * g] : Fin 3 → RationalGL3) =
      ![a.val * x, a.val * y, a.val * (y * g)] := by
    simp only [mul_assoc]
  rw [e1, e2, equivar3 C a, equivar3 C a, map_sub]

/-- **Conjugation by the frame, in inhomogeneous form.** The inhomogeneous two-cocycle of the conjugated
(block-coordinate) cocycle differs from `ρ(gF)⁻¹` times that of the original cocycle, transported along
`h ↦ gF h gF⁻¹`, by the coboundary of an explicit one-cochain. -/
theorem conj_prism (a b : ΛG) :
    (GoodPlaneConj.conjCycle (rationalCoefficientComponent n trivialCharacter) gF
      (cuspLevel .plane true) ΛG hH_conj C).val.val ![1, a.val, a.val * b.val] =
    gpA n (C.val.val ![1, gF * a.val * gF⁻¹, gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹)]) +
      (rationalCoefficientComponent n trivialCharacter a.val
          (gpA n (Kf C gF 1 (gF * b.val * gF⁻¹))) -
        gpA n (Kf C gF 1 (gF * (a.val * b.val) * gF⁻¹)) +
        gpA n (Kf C gF 1 (gF * a.val * gF⁻¹))) := by
  have hv : (![1 * gF, gF * a.val * gF⁻¹ * gF, gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹) * gF] :
      Fin 3 → RationalGL3) =
      (fun i => gF * (![1, a.val, a.val * b.val] : Fin 3 → RationalGL3) i) := by
    funext i
    fin_cases i
    · change 1 * gF = gF * 1
      group
    · change gF * a.val * gF⁻¹ * gF = gF * a.val
      group
    · change gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹) * gF = gF * (a.val * b.val)
      group
  have hp := prism C gF 1 (gF * a.val * gF⁻¹) (gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹))
  rw [hv] at hp
  have hK1 := Kf_equivar C gF (lamEquiv a) 1 (gF * b.val * gF⁻¹)
  rw [mul_one] at hK1
  have hgp : rationalCoefficientComponent n trivialCharacter a.val
      (gpA n (Kf C gF 1 (gF * b.val * gF⁻¹))) =
      gpA n (rationalCoefficientComponent n trivialCharacter (gF * a.val * gF⁻¹)
        (Kf C gF 1 (gF * b.val * gF⁻¹))) := by
    apply rep_comm'
    group
  have hab : gF * (a.val * b.val) * gF⁻¹ = gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹) := by group
  rw [hab, hgp]
  change gpA n (C.val.val (fun i => gF * (![1, a.val, a.val * b.val] : Fin 3 → RationalGL3) i)) = _
  have hp' := eq_add_of_sub_eq hp
  have hK1' : Kf C gF (gF * a.val * gF⁻¹) (gF * a.val * gF⁻¹ * (gF * b.val * gF⁻¹)) =
      rationalCoefficientComponent n trivialCharacter (gF * a.val * gF⁻¹)
        (Kf C gF 1 (gF * b.val * gF⁻¹)) := hK1
  rw [hp', hK1']
  simp only [map_add, map_sub]
  abel

end Prism


/-- The conjugated ambient cocycle and the pushed face cocycle define the same class of `H²(ΛG, V)`. -/
theorem H2π_conj_eq_push
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter)) :
    groupCohomology.H2π (coefRep n)
        (ambientCocycleToGroup ΛG (ρn n)
          (GoodPlaneConj.conjCycle (rationalCoefficientComponent n trivialCharacter) gF
            (cuspLevel .plane true) ΛG hH_conj C)) =
      groupCohomology.H2π (coefRep n)
        (gpPush n (faceCycle goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota C)) := by
  rw [← sub_eq_zero, ← map_sub, groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun a => (gpA n (Kf C gF 1 (gF * a.val * gF⁻¹)) : coefRep n), ?_⟩
  funext p
  have hd := groupCohomology.d₁₂_hom_apply (coefRep n)
    (fun a => (gpA n (Kf C gF 1 (gF * a.val * gF⁻¹)) : coefRep n)) p
  rw [hd]
  have hc := conj_prism C p.1 p.2
  change _ = (GoodPlaneConj.conjCycle (rationalCoefficientComponent n trivialCharacter) gF
      (cuspLevel .plane true) ΛG hH_conj C).val.val ![1, p.1.val, p.1.val * p.2.val] -
    gpA n ((faceCycle goodPlaneSplitting.conjAct n trivialCharacter (cuspFlag .plane true) gpIota C).val
      (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1)
      (goodPlaneSplitting.semidirectProductMulEquiv.symm p.2))
  rw [faceCycle_apply]
  have e1 : (gpIota (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1)).val =
      gF * p.1.val * gF⁻¹ := by
    change gF * (goodPlaneSplitting.semidirectProductMulEquiv
      (goodPlaneSplitting.semidirectProductMulEquiv.symm p.1)).val * gF⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
  have e2 : (gpIota (goodPlaneSplitting.semidirectProductMulEquiv.symm p.2)).val =
      gF * p.2.val * gF⁻¹ := by
    change gF * (goodPlaneSplitting.semidirectProductMulEquiv
      (goodPlaneSplitting.semidirectProductMulEquiv.symm p.2)).val * gF⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
  rw [e1, e2, hc]
  exact (add_sub_cancel_left _ _).symm

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.GoodPlaneId
