module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularCapSystem
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section


/-!
# The Alexander-Whitney diagonal system of equivariant singular chains

`singDelta p q : C_{p+q}(E) ⟶ C_p(E) ⊗ C_q(E)` sends a simplex to (front face) ⊗ (back face); with the Leibniz
rule (from the library's `aw_signed_identity`) and the augmentation of `singEps` it is a `DiagSystem`.  The diagonal
is natural for equivariant maps of spaces.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.TopHomology
open SphereOddDegree.AlexanderWhitney
open scoped Simplicial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The Alexander-Whitney diagonal in bidegree `(p, q)`. -/
def singDelta0 (p q : ℕ) : chainRep G E (p+q) ⟶ chainRep G E p ⊗ chainRep G E q :=
  capE E (chainRep G E p) p q (𝟙 _)

theorem singDelta0_chainElement (p q : ℕ) (σ : SingularSimplex E (p+q)) :
    (singDelta0 (G := G) E p q).hom (chainElement G E (p+q) σ) =
      (chainElement G E p (frontSimplex E p q σ)) ⊗ₜ[ℚ] (chainElement G E q (backSimplex E p q σ)) :=
  capE_chainElement E (chainRep G E p) p q (𝟙 _) σ

/-- The diagonal with an arbitrary total degree. -/
def singDelta (p q n : ℕ) (h : p + q = n) : chainRep G E n ⟶ chainRep G E p ⊗ chainRep G E q :=
  eqToHom (congrArg (chainRep G E) h.symm) ≫ singDelta0 E p q

theorem eqToHom_chainElement {m m' : ℕ} (h : m = m') (σ : SingularSimplex E m) :
    (eqToHom (congrArg (chainRep G E) h) : chainRep G E m ⟶ chainRep G E m').hom (chainElement G E m σ) =
      chainElement G E m' ((TopCat.toSSet.obj E).map (eqToHom (by rw [h])).op σ) := by
  subst h
  simp

theorem singDelta_succ_chainElement (p q : ℕ) (h : p + 1 + q = p + q + 1) (σ : SingularSimplex E (p+q+1)) :
    (singDelta (G := G) E (p+1) q (p+q+1) h).hom (chainElement G E (p+q+1) σ) =
      (chainElement G E (p+1) (frontSimplex E (p+1) q (SphereOddDegree.awCastSimplex E p q σ))) ⊗ₜ[ℚ]
        (chainElement G E q (backSimplex E (p+1) q (SphereOddDegree.awCastSimplex E p q σ))) := by
  have h1 : (singDelta (G := G) E (p+1) q (p+q+1) h).hom (chainElement G E (p+q+1) σ) =
      (singDelta0 (G := G) E (p+1) q).hom
        ((eqToHom (congrArg (chainRep G E) h.symm) : chainRep G E (p+q+1) ⟶ chainRep G E (p+1+q)).hom
          (chainElement G E (p+q+1) σ)) := rfl
  rw [h1, eqToHom_chainElement E h.symm σ, singDelta0_chainElement]
  rfl

theorem singDiag_leibniz (p q n : ℕ) (h : p + q = n) :
    equivariantD G E (n+1) n ≫ singDelta E p q n h =
      singDelta E (p+1) q (n+1) (by omega) ≫ (equivariantD G E (p+1) p ▷ chainRep G E q) +
        ((-1 : ℤ)^p) • (singDelta E p (q+1) (n+1) (by omega) ≫ (chainRep G E p ◁ equivariantD G E (q+1) q)) := by
  subst h
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  have hL : (Rep.Hom.hom (equivariantD G E (p + q + 1) (p + q) ≫ singDelta E p q (p+q) rfl)).toLinearMap
      (chainElement G E (p + q + 1) σ) =
      ∑ k : Fin (p+q+2), (-1 : ℤ)^k.val •
        ((chainElement G E p (frontSimplex E p q ((TopCat.toSSet.obj E).δ k σ))) ⊗ₜ[ℚ]
          (chainElement G E q (backSimplex E p q ((TopCat.toSSet.obj E).δ k σ)))) := by
    change (singDelta E p q (p+q) rfl).hom ((equivariantD G E (p + q + 1) (p + q)).hom (chainElement G E (p + q + 1) σ)) = _
    rw [chainElement_d]
    simp only [map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (singDelta (G := G) E p q (p+q) rfl).hom (chainElement G E (p+q) ((TopCat.toSSet.obj E).δ k σ)) =
        (singDelta0 (G := G) E p q).hom (chainElement G E (p+q) ((TopCat.toSSet.obj E).δ k σ)) := rfl
    rw [this, singDelta0_chainElement]
  have hR1 : (Rep.Hom.hom (singDelta E (p + 1) q (p + q + 1) (by omega) ≫
        (equivariantD G E (p+1) p ▷ chainRep G E q))).toLinearMap (chainElement G E (p + q + 1) σ) =
      ∑ i : Fin (p+2), (-1 : ℤ)^i.val •
        ((chainElement G E p (faceSimplex E p i (frontSimplex E (p+1) q (SphereOddDegree.awCastSimplex E p q σ)))) ⊗ₜ[ℚ]
          (chainElement G E q (backSimplex E (p+1) q (SphereOddDegree.awCastSimplex E p q σ)))) := by
    change (equivariantD G E (p+1) p ▷ chainRep G E q).hom
      ((singDelta E (p + 1) q (p + q + 1) (by omega)).hom (chainElement G E (p + q + 1) σ)) = _
    rw [singDelta_succ_chainElement, Rep.hom_whiskerRight, Representation.IntertwiningMap.rTensor_apply]
    change (equivariantD G E (p+1) p).hom (chainElement G E (p+1) _) ⊗ₜ[ℚ] _ = _
    rw [chainElement_d, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul']
    rfl
  have hR2 : (Rep.Hom.hom (singDelta E p (q + 1) (p + q + 1) (by omega) ≫
        (chainRep G E p ◁ equivariantD G E (q+1) q))).toLinearMap (chainElement G E (p + q + 1) σ) =
      ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
        ((chainElement G E p (frontSimplex E p (q+1) σ)) ⊗ₜ[ℚ]
          (chainElement G E q (faceSimplex E q j (backSimplex E p (q+1) σ)))) := by
    change (chainRep G E p ◁ equivariantD G E (q+1) q).hom
      ((singDelta0 (G := G) E p (q + 1)).hom (chainElement G E (p + (q + 1)) σ)) = _
    rw [singDelta0_chainElement, Rep.hom_whiskerLeft, Representation.IntertwiningMap.lTensor_apply]
    change _ ⊗ₜ[ℚ] (equivariantD G E (q+1) q).hom (chainElement G E (q+1) _) = _
    rw [chainElement_d, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    rfl
  let F : SingularSimplex E p → (chainRep G E p : Rep ℚ G) := fun τ => chainElement G E p τ
  let T : SingularSimplex E q → (chainRep G E p : Rep ℚ G) →ₗ[ℚ] (chainRep G E p ⊗ chainRep G E q : Rep ℚ G) :=
    fun τ => (TensorProduct.mk ℚ (chainRep G E p) (chainRep G E q)).flip (chainElement G E q τ)
  have key := TernaryPoly.SingularLocalCap.aw_signed_identity (X := E) (W := (chainRep G E p : Rep ℚ G))
    (M := (chainRep G E p ⊗ chainRep G E q : Rep ℚ G)) p q F T σ
  simp only [map_sum, map_zsmul] at key
  have hsum : (Rep.Hom.hom (singDelta E (p + 1) q (p + q + 1) (by omega) ≫
        (equivariantD G E (p+1) p ▷ chainRep G E q) +
        ((-1 : ℤ)^p) • (singDelta E p (q + 1) (p + q + 1) (by omega) ≫
          (chainRep G E p ◁ equivariantD G E (q+1) q)))).toLinearMap (chainElement G E (p + q + 1) σ) =
      (Rep.Hom.hom (singDelta E (p + 1) q (p + q + 1) (by omega) ≫
        (equivariantD G E (p+1) p ▷ chainRep G E q))).toLinearMap (chainElement G E (p + q + 1) σ) +
      ((-1 : ℤ)^p) • (Rep.Hom.hom (singDelta E p (q + 1) (p + q + 1) (by omega) ≫
          (chainRep G E p ◁ equivariantD G E (q+1) q))).toLinearMap (chainElement G E (p + q + 1) σ) := rfl
  rw [hL, hsum, hR1, hR2]
  exact key

/-- The Alexander-Whitney diagonal system of the equivariant singular chains. -/
def singDiagSystem : DiagSystem (equivariantChains G E) where
  Δ p q n h := singDelta E p q n h
  leibniz p q n h := singDiag_leibniz E p q n h
  eps := singEps E
  eps_d := singEps_d E
  counit p := by
    have h := singEps_counit E (chainRep G E p) p (𝟙 _)
    have e : singDelta (G := G) E p 0 p (add_zero p) = capE E (chainRep G E p) p 0 (𝟙 _) := by
      simp [singDelta, singDelta0]
    rw [e]
    exact h

theorem singDiagSystem_cap {W : Rep.{0} ℚ G} {a : ℕ} (b : chainRep G E a ⟶ W)
    (hb : (equivariantChains G E).d (a+1) a ≫ b = 0) (q : ℕ) :
    (singDiagSystem E).toCapSystem.cap b hb q = capE E W a q b := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  change (b ▷ chainRep G E q).hom ((singDelta0 (G := G) E a q).hom (chainElement G E (a+q) σ)) = _
  rw [singDelta0_chainElement, Rep.hom_whiskerRight, Representation.IntertwiningMap.rTensor_apply]
  exact (capE_chainElement E W a q b σ).symm

section Natural

variable {E' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E'] (F : E ⟶ E')
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)

/-- The map of equivariant singular chains induced by an equivariant map of spaces. -/
abbrev spaceChainMap : equivariantChains G E ⟶ equivariantChains G E' :=
  TernaryPoly.SingularCoverNaturality.chainMap F hF

theorem spaceChainMap_chainElement (n : ℕ) (σ : SingularSimplex E n) :
    ((spaceChainMap E F hF).f n).hom (chainElement G E n σ) =
      chainElement G E' n ((TopCat.toSSet.map F).app (Opposite.op ⦋n⦌) σ) :=
  congrArg (fun m => m.hom (1 : ℚ)) (TernaryPoly.SingularCoverNaturality.generator_map F n σ)

theorem singDiag_natural (p q n : ℕ) (h : p + q = n) :
    (spaceChainMap E F hF).f n ≫ singDelta E' p q n h =
      singDelta E p q n h ≫ ((spaceChainMap E F hF).f p ⊗ₘ (spaceChainMap E F hF).f q) := by
  subst h
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  change (singDelta0 (G := G) E' p q).hom (((spaceChainMap E F hF).f (p+q)).hom (chainElement G E (p+q) σ)) =
    ((spaceChainMap E F hF).f p ⊗ₘ (spaceChainMap E F hF).f q).hom ((singDelta0 (G := G) E p q).hom
        (chainElement G E (p+q) σ))
  rw [spaceChainMap_chainElement, singDelta0_chainElement, singDelta0_chainElement, Rep.hom_tensorHom]
  change _ = ((spaceChainMap E F hF).f p).hom (chainElement G E p (frontSimplex E p q σ)) ⊗ₜ[ℚ]
    ((spaceChainMap E F hF).f q).hom (chainElement G E q (backSimplex E p q σ))
  rw [spaceChainMap_chainElement, spaceChainMap_chainElement, frontSimplex_naturality,
    backSimplex_naturality]
  rfl

theorem spaceChainMap_eps : (spaceChainMap E F hF).f 0 ≫ singEps E' = singEps E := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  change (singEps (G := G) E').hom (((spaceChainMap E F hF).f 0).hom (chainElement G E 0 σ)) =
    (singEps (G := G) E).hom (chainElement G E 0 σ)
  rw [spaceChainMap_chainElement]
  erw [singEps_chainElement (G := G) E', singEps_chainElement (G := G) E]

end Natural

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
