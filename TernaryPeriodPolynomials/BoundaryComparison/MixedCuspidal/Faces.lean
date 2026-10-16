module

public import TernaryPeriodPolynomials.BoundaryComparison.MixedCuspidal.C3
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaces

@[expose] public section


/-!
# Lemma C.3: the faces of `Γ(N)`, the locally inner characterization, and independence of the frame

Paper: Lemma C.3 (`ar:lem:seed`).

For the plane cusp `h⁻¹Ph` of `Γ(N)` (`h ∈ SL₃(ℤ)`) with plane group `Γ_{h⁻¹Ph}`:

* `face_cuspidal_eq_locally_inner`: the image in `H²(Γ_{h⁻¹Ph}, E_n)` of the mixed cuspidal group
  (computed with the frame `h` through the Levi `Γ₂(N)`) is the group of *locally inner* classes:
  zero restriction to the radical and to the stabilizer of every complete flag over the plane.  This
  statement involves only the plane group and its flag stabilizers;
* `face_cuspidal_frame_independent`, `face_cuspidal_conj_independent`, `face_cuspidal_orbit`: the
  choice of the integral conjugator inside a face (`h ↦ q h γ`, `q ∈ P(ℚ) ∩ SL₃(ℤ)`, `γ ∈ SL₃(ℤ)`)
  does not matter: the canonical isomorphisms of the plane groups carry the cuspidal group onto the
  cuspidal group;
* `plane_faces_finite`, `plane_face_exhaustive`: the `Γ(N)`-orbits of rational planes form a finite
  set `PlaneFaces N`, and each rational plane is covered;
* `seed_span_eq_mixedCuspidal_planeFaces`: the product over `PlaneFaces N` (at the chosen
  representatives) of the mixed cuspidal groups is the product of the edge images of the seeds.

All statements are unconditional.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalFaces

open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- **Locally inner characterization of `𝒞_{P'}(E)`**.  For every `N ≠ 0` and every
cusp `h⁻¹Ph`, the image of the mixed cuspidal group in `H²(Γ_{h⁻¹Ph}, E_n)` consists exactly of
the classes vanishing on the radical and on the stabilizer (inside the plane group) of every complete
flag over the plane. -/
theorem face_cuspidal_eq_locally_inner (N n : ℕ) [NeZero N] (h : SL(3, ℤ)) :
    SeedC3S4c.faceCuspidalInH2 N h n = SeedC3S4c.faceLocallyInner N h n :=
  SeedC3S4c.faceCuspidalInH2_eq_locallyInner N h n

/-- **Independence of the frame inside `P(ℚ) ∩ SL₃(ℤ)`.** -/
theorem face_cuspidal_frame_independent (N n : ℕ) [NeZero N] (h q : SL(3, ℤ))
    (hq : q ∈ SeedC3S4c.planeBorel) :
    Submodule.map (SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.frameHom N h q hq)
        (SeedC3S4c.faceRep N h n) (SeedC3S4c.faceRep N (q * h) n) (SeedC3S4c.frameT n)
        (SeedC3S4c.frameT_intertwines N h n q hq)) (SeedC3S4c.faceCuspidalInH2 N h n) =
      SeedC3S4c.faceCuspidalInH2 N (q * h) n :=
  SeedC3S4c.map_faceCuspidalInH2_frame N h n q hq

/-- **Independence under `Γ(N)`-translation (indeed `SL₃(ℤ)`): conjugation `h ↦ h γ`.** -/
theorem face_cuspidal_conj_independent (N n : ℕ) [NeZero N] (h γ : SL(3, ℤ)) :
    Submodule.map (SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.conjGammaHom N h γ)
        (SeedC3S4c.faceRep N h n) (SeedC3S4c.faceRep N (h * γ) n) (SeedC3S4c.faceConjT γ n)
        (SeedC3S4c.faceConjT_intertwines N h γ n)) (SeedC3S4c.faceCuspidalInH2 N h n) =
      SeedC3S4c.faceCuspidalInH2 N (h * γ) n :=
  SeedC3S4c.map_faceCuspidalInH2_conj N h γ n

/-- **Independence of the representative of a face** (`h ↦ q h γ`). -/
theorem face_cuspidal_orbit (N n : ℕ) [NeZero N] (h q γ : SL(3, ℤ))
    (hq : q ∈ SeedC3S4c.planeBorel) :
    Submodule.map (SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.conjGammaHom N (q * h) γ)
        (SeedC3S4c.faceRep N (q * h) n) (SeedC3S4c.faceRep N (q * h * γ) n)
        (SeedC3S4c.faceConjT γ n) (SeedC3S4c.faceConjT_intertwines N (q * h) γ n))
      (Submodule.map (SeedC3S4c.EdgeNat.h2Map (SeedC3S4c.frameHom N h q hq)
        (SeedC3S4c.faceRep N h n) (SeedC3S4c.faceRep N (q * h) n) (SeedC3S4c.frameT n)
        (SeedC3S4c.frameT_intertwines N h n q hq)) (SeedC3S4c.faceCuspidalInH2 N h n)) =
      SeedC3S4c.faceCuspidalInH2 N (q * h * γ) n :=
  SeedC3S4c.faceCuspidalInH2_orbit N n h q γ hq

/-- The set of faces (`Γ(N)`-orbits of rational planes) is finite. -/
theorem plane_faces_finite (N : ℕ) [NeZero N] : Finite (SeedC3S4c.PlaneFaces N) :=
  inferInstance

/-- **Exhaustiveness.** Every rational plane `g P g⁻¹` of `Γ(N)`, `N ≥ 3`, belongs to a face `i`:
its stabilizer in `Γ(N)` is the plane group of an integral conjugator `h`, and the chosen
representative of `i` differs from `h` by `q h γ` with `q ∈ P(ℚ) ∩ SL₃(ℤ)`, `γ ∈ Γ(N)`. -/
theorem plane_face_exhaustive (N : ℕ) [NeZero N] (hN : 3 ≤ N) (g : GL (Fin 3) ℚ) :
    ∃ (i : SeedC3S4c.PlaneFaces N) (h : SL(3, ℤ)),
      (∀ p ∈ gammaN N,
        InPQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ SeedC3S4c.gammaNPAt N h) ∧
      ∃ q ∈ SeedC3S4c.planeBorel, ∃ γ ∈ gammaN N, (Quotient.out i : SL(3, ℤ)) = q * h * γ :=
  SeedC3S4c.exists_face_rep N hN g

/-- **`⊕_{faces} 𝒞_F(E)` is the span of the seeds**, over the finite set of faces at the chosen
representatives (unconditional). -/
theorem seed_span_eq_mixedCuspidal_planeFaces (N n : ℕ) [NeZero N] :
    Submodule.pi Set.univ (fun i : SeedC3S4c.PlaneFaces N =>
        Submodule.map (SeedC3S4c.faceEdge N (Quotient.out i) n)
          (SeedC3S4c.faceSeedKerSpan N (Quotient.out i) n)) =
      Submodule.pi Set.univ (fun i : SeedC3S4c.PlaneFaces N =>
        SeedC3S4c.faceCuspidal N (Quotient.out i) n) :=
  MixedCuspidalC3.seed_span_eq_mixedCuspidal_family N n (fun i : SeedC3S4c.PlaneFaces N => Quotient.out i)

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalFaces
