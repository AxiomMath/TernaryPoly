module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceCharacters
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.Descent

@[expose] public section


/-!
# Descent of the line-face pairing along the Levi `GL₂(ℤ)`

Formalized by Claude Sonnet 5.5.

`levi_face_pairing_descends`: a finite group `G` with a homomorphism `Lv : G → GL₂(ℤ)` (the Levi component of the face stabilizer; determinant and reflection elements included) acts on `V`, `W`; if the face pairing `e` is scaled
by `g` exactly by the product of the two internal scalars, the Koszul scalar `radDet (rowAct (Lv g)) = det (Lv g)` (`radDet_rowAct`, the library's law `PhiC_pullback`) and the Poincaré-Lefschetz scalar `det (Lv g)` (`cuspConjNat`),
then `e` is `G`-invariant (`koszul_times_base_scale`) and its restriction to the invariants is still perfect.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

omit [Fintype G] in
theorem levi_face_pairing_invariant (Lv : G →* GL (Fin 2) ℤ) (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) =
      (radDet (rowAct (Lv g).val) : ℂ) * (((Lv g).val.det : ℤ) : ℂ) * e x y) (g : G) (x : V) (y : W) :
    e (ρ g x) (σ g y) = e x y := by
  have h := koszul_times_base_scale (A := (Lv g).val) (by simp)
  have h' : (radDet (rowAct (Lv g).val) : ℂ) * (((Lv g).val.det : ℤ) : ℂ) = 1 := by exact_mod_cast h
  rw [hscale, h', one_mul]

/-- **The descended pairing is perfect** (left kernel). -/
theorem levi_face_pairing_descends_left (Lv : G →* GL (Fin 2) ℤ) (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) =
      (radDet (rowAct (Lv g).val) : ℂ) * (((Lv g).val.det : ℤ) : ℂ) * e x y)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (v : isoSub ρ 1) (h : ∀ w, isoPairing (ρ := ρ) (σ := σ) e 1 1 v w = 0) : v = 0 :=
  isoPairing_left e 1 1 1 (fun g => by simp) (fun g x y => by simpa using levi_face_pairing_invariant Lv e hscale g x y) hL v h

/-- Right kernel. -/
theorem levi_face_pairing_descends_right (Lv : G →* GL (Fin 2) ℤ) (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) =
      (radDet (rowAct (Lv g).val) : ℂ) * (((Lv g).val.det : ℤ) : ℂ) * e x y)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0) (w : isoSub σ 1) (h : ∀ v, isoPairing (ρ := ρ) (σ := σ) e 1 1 v w = 0) : w = 0 :=
  isoPairing_right e 1 1 1 (fun g => by simp) (fun g x y => by simpa using levi_face_pairing_invariant Lv e hscale g x y) hR w h

/-- The invariants have the same dimension. -/
theorem levi_face_pairing_descends_finrank [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (Lv : G →* GL (Fin 2) ℤ)
    (e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hscale : ∀ g x y, e (ρ g x) (σ g y) =
      (radDet (rowAct (Lv g).val) : ℂ) * (((Lv g).val.det : ℤ) : ℂ) * e x y)
    (hL : ∀ v, (∀ w, e v w = 0) → v = 0) (hR : ∀ w, (∀ v, e v w = 0) → w = 0) :
    Module.finrank ℂ (isoSub ρ 1) = Module.finrank ℂ (isoSub σ 1) :=
  isoPairing_finrank_eq e 1 1 1 (fun g => by simp) (fun g x y => by simpa using levi_face_pairing_invariant Lv e hscale g x y) hL hR

end TernaryPeriodPolynomials.Argument.FaceDescent
