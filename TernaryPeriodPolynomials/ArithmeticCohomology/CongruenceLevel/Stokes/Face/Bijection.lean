module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms

@[expose] public section


/-!
# Step 1a: the bijection between the pairs (face of `Γ(6)`, orbit of its face group on `Γ(6)/Γ(M)`) and the faces of `Γ(M)`

Formalized by Claude Sonnet 5.5.

For `6 ∣ M`, `lineFaceOverEquiv M h6 : (Σ i : LineFaces 6, S_i-orbits on Γ(6)/Γ(M)) ≃ LineFaces M` sends `(i, O)` to the face of the conjugator `h_i u_O`, `u_O ∈ Γ(6)` a representative of the orbit
(`uOLine`); `mk6_lineFaceOver`: the face of `Γ(6)` under it is `i`.  Same for planes.  (This is the combinatorial half of Step 1; the frame invariance of the pairing is `FrameInvarianceLine`.)
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open MulAction
open TernaryPeriodPolynomials.Argument.SeedC3

section LineBij

variable (M : ℕ) [NeZero M]

theorem mem_lineSub_iff (i : LineFaces 6) (s : ↥(gammaN 6)) :
    s ∈ lineSub i ↔ i.rep * (s : SL(3, ℤ)) * i.rep⁻¹ ∈ gammaNQ 6 := Iff.rfl

theorem conj_mem_lineBorel_of_mem_lineSub (i : LineFaces 6) {s : ↥(gammaN 6)} (hs : s ∈ lineSub i) :
    i.rep * (s : SL(3, ℤ)) * i.rep⁻¹ ∈ lineBorel :=
  mem_lineBorel_of_mem_lineStab ((mem_lineSub_iff i s).1 hs).2

theorem mem_lineSub_of_conj_mem_lineBorel (i : LineFaces 6) {s : ↥(gammaN 6)}
    (hs : i.rep * (s : SL(3, ℤ)) * i.rep⁻¹ ∈ lineBorel) : s ∈ lineSub i := by
  have hg : i.rep * (s : SL(3, ℤ)) * i.rep⁻¹ ∈ gammaN 6 := by
    have := (gammaN_normal 6).conj_mem _ s.2 i.rep
    simpa [mul_assoc] using this
  exact (mem_lineSub_iff i s).2 ⟨hg, mem_lineStab_of_gammaN (by norm_num) hg hs.1 hs.2⟩

/-- The face of `Γ(M)` over the pair `(i, O)`: the face of the conjugator `h_i u_O`. -/
def lineFaceOver (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) : LineFaces M :=
  LineFaces.mk (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)))

omit [NeZero M] in
theorem uOLine_coset (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    ((uOLine M i o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o :=
  Quotient.out_eq (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M)

omit [NeZero M] in
theorem lineFaceOver_surjective :
    Function.Surjective (fun x : (Σ i : LineFaces 6, orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
      lineFaceOver M x.1 x.2) := by
  intro i'
  set h : SL(3, ℤ) := i'.rep with hh
  obtain ⟨q, hq, γ, hγ, hrep⟩ := LineFaces.rel_rep (N := 6) h
  set j : LineFaces 6 := LineFaces.mk h with hj
  let g : ↥(gammaN 6) := ⟨γ⁻¹, (gammaN 6).inv_mem hγ⟩
  let x : ↥(gammaN 6) ⧸ Δ6 M := (g : ↥(gammaN 6) ⧸ Δ6 M)
  let o : orbitRel.Quotient ↥(lineSub j) (↥(gammaN 6) ⧸ Δ6 M) :=
    Quotient.mk (orbitRel ↥(lineSub j) (↥(gammaN 6) ⧸ Δ6 M)) x
  refine ⟨⟨j, o⟩, ?_⟩
  have hmo : orbitRel ↥(lineSub j) (↥(gammaN 6) ⧸ Δ6 M) (Quotient.out o) x :=
    Quotient.mk_out (s := orbitRel ↥(lineSub j) (↥(gammaN 6) ⧸ Δ6 M)) x
  rw [orbitRel_apply, mem_orbit_iff] at hmo
  obtain ⟨s, hs⟩ := hmo
  have hu : ((uOLine M j o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = (((s : ↥(gammaN 6)) * g : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) := by
    rw [uOLine_coset, ← hs]; rfl
  have hδ : ((s : ↥(gammaN 6)) * g)⁻¹ * uOLine M j o ∈ Δ6 M := QuotientGroup.eq.mp hu.symm
  set δ : ↥(gammaN 6) := ((s : ↥(gammaN 6)) * g)⁻¹ * uOLine M j o with hδdef
  have hu' : uOLine M j o = (s : ↥(gammaN 6)) * g * δ := by rw [hδdef]; group
  have hq' := conj_mem_lineBorel_of_mem_lineSub j s.2
  have hδM : (δ : SL(3, ℤ)) ∈ gammaN M := hδ
  have key : j.rep * ((uOLine M j o : ↥(gammaN 6)) : SL(3, ℤ)) =
      (j.rep * (s : SL(3, ℤ)) * j.rep⁻¹ * q) * h * (δ : SL(3, ℤ)) := by
    rw [hu']
    have hg : (g : SL(3, ℤ)) = γ⁻¹ := rfl
    simp only [Subgroup.coe_mul, hg]
    have : j.rep = q * h * γ := hrep
    rw [this]
    group
  have hrel : (lineFaceSetoid M).r h (j.rep * ((uOLine M j o : ↥(gammaN 6)) : SL(3, ℤ))) :=
    ⟨j.rep * (s : SL(3, ℤ)) * j.rep⁻¹ * q, lineBorel.mul_mem hq' hq, δ, hδM, key⟩
  show LineFaces.mk (j.rep * ((uOLine M j o : ↥(gammaN 6)) : SL(3, ℤ))) = i'
  have e1 : LineFaces.mk (N := M) (j.rep * ((uOLine M j o : ↥(gammaN 6)) : SL(3, ℤ))) = LineFaces.mk (N := M) h :=
    (Quotient.sound hrel).symm
  rw [e1]
  exact Quotient.out_eq i'

omit [NeZero M] in
theorem lineFaceOver_injective (h6 : 6 ∣ M) :
    Function.Injective (fun x : (Σ i : LineFaces 6, orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
      lineFaceOver M x.1 x.2) := by
  rintro ⟨i, o⟩ ⟨j, p⟩ heq
  obtain ⟨q, hq, γ, hγ, hrel⟩ := Quotient.exact heq
  have hγ6 : γ ∈ gammaN 6 := gammaN_mono h6 hγ
  have hij : i = j := by
    have hr : (lineFaceSetoid 6).r i.rep j.rep :=
      ⟨q, hq, (uOLine M i o : SL(3, ℤ)) * γ * ((uOLine M j p : ↥(gammaN 6)) : SL(3, ℤ))⁻¹,
        (gammaN 6).mul_mem ((gammaN 6).mul_mem (uOLine M i o).2 hγ6) ((gammaN 6).inv_mem (uOLine M j p).2), by
          have e : j.rep * ((uOLine M j p : ↥(gammaN 6)) : SL(3, ℤ)) =
              q * (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hrel
          calc j.rep = j.rep * ((uOLine M j p : ↥(gammaN 6)) : SL(3, ℤ)) * ((uOLine M j p : ↥(gammaN 6)) : SL(3, ℤ))⁻¹ := by group
            _ = _ := by rw [e]; group⟩
    have e1 : (Quotient.mk (lineFaceSetoid 6) i.rep : LineFaces 6) = Quotient.mk (lineFaceSetoid 6) j.rep := Quotient.sound hr
    rw [show (Quotient.mk (lineFaceSetoid 6) i.rep : LineFaces 6) = i from Quotient.out_eq i,
      show (Quotient.mk (lineFaceSetoid 6) j.rep : LineFaces 6) = j from Quotient.out_eq j] at e1
    exact e1
  subst hij
  set U : ↥(gammaN 6) := uOLine M i o with hU
  set U' : ↥(gammaN 6) := uOLine M i p with hU'
  let γ' : ↥(Δ6 M) := ⟨⟨γ, hγ6⟩, hγ⟩
  have hs : (U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ : ↥(gammaN 6)) ∈ lineSub i := by
    apply mem_lineSub_of_conj_mem_lineBorel
    have e : i.rep * (U' : SL(3, ℤ)) = q * (i.rep * (U : SL(3, ℤ))) * γ := hrel
    have e2 : i.rep * ((U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ : ↥(gammaN 6)) : SL(3, ℤ)) * i.rep⁻¹ = q := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hg : ((γ' : ↥(gammaN 6)) : SL(3, ℤ)) = γ := rfl
      rw [hg]
      calc i.rep * ((U' : SL(3, ℤ)) * γ⁻¹ * (U : SL(3, ℤ))⁻¹) * i.rep⁻¹
          = (i.rep * (U' : SL(3, ℤ))) * γ⁻¹ * (U : SL(3, ℤ))⁻¹ * i.rep⁻¹ := by group
        _ = q := by rw [e]; group
    rw [e2]; exact hq
  let sS : ↥(lineSub i) := ⟨_, hs⟩
  have hsm : sS • (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out p := by
    rw [← uOLine_coset M i o, ← uOLine_coset M i p]
    change ((U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ * U : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = (U' : ↥(gammaN 6) ⧸ Δ6 M)
    rw [QuotientGroup.eq]
    have : (U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ * U)⁻¹ * U' = (γ' : ↥(gammaN 6)) := by group
    rw [this]; exact γ'.2
  have hor : orbitRel ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M) (Quotient.out p) (Quotient.out o) := by
    rw [orbitRel_apply, mem_orbit_iff]; exact ⟨sS, hsm⟩
  have h1 := Quotient.sound hor
  rw [Quotient.out_eq, Quotient.out_eq] at h1
  rw [h1]

omit [NeZero M] in
theorem mk6_lineFaceOver (h6 : 6 ∣ M) (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    LineFaces.mk (N := 6) (lineFaceOver M i o).rep = i := by
  obtain ⟨q, hq, γ, hγ, hrep⟩ := LineFaces.rel_rep (N := M) (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)))
  have hr : (lineFaceSetoid 6).r i.rep (lineFaceOver M i o).rep :=
    ⟨q, hq, ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)) * γ,
      (gammaN 6).mul_mem (uOLine M i o).2 (gammaN_mono h6 hγ), by
        have : (lineFaceOver M i o).rep = q * (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hrep
        rw [this]; group⟩
  have e1 : (Quotient.mk (lineFaceSetoid 6) i.rep : LineFaces 6) =
      Quotient.mk (lineFaceSetoid 6) (lineFaceOver M i o).rep := Quotient.sound hr
  rw [show (Quotient.mk (lineFaceSetoid 6) i.rep : LineFaces 6) = i from Quotient.out_eq i] at e1
  exact e1.symm

/-- **The bijection between the pairs `(i, O)` (a face `i` of `Γ(6)` and an orbit `O` of its line group on `Γ(6)/Γ(M)`) and the line faces of `Γ(M)`**, `6 ∣ M`. -/
def lineFaceOverEquiv (h6 : 6 ∣ M) : (Σ i : LineFaces 6, orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) ≃ LineFaces M :=
  Equiv.ofBijective (fun x => lineFaceOver M x.1 x.2) ⟨lineFaceOver_injective M h6, lineFaceOver_surjective M⟩

end LineBij


theorem PlaneFaces_rel_rep (N : ℕ) (h : SL(3, ℤ)) :
    (planeFaceSetoid N).r h (planeFaceRepr (Quotient.mk (planeFaceSetoid N) h : PlaneFaces N)) :=
  (planeFaceSetoid N).iseqv.symm (Quotient.mk_out (s := planeFaceSetoid N) h)

section PlaneBij

variable (M : ℕ) [NeZero M]

theorem mem_planeSub_iff (i : PlaneFaces 6) (s : ↥(gammaN 6)) :
    s ∈ planeSub i ↔ (planeFaceRepr i) * (s : SL(3, ℤ)) * (planeFaceRepr i)⁻¹ ∈ gammaNP 6 := Iff.rfl

theorem conj_mem_planeBorel_of_mem_planeSub (i : PlaneFaces 6) {s : ↥(gammaN 6)} (hs : s ∈ planeSub i) :
    (planeFaceRepr i) * (s : SL(3, ℤ)) * (planeFaceRepr i)⁻¹ ∈ planeBorel :=
  ⟨(((mem_planeSub_iff i s).1 hs).2).1, (((mem_planeSub_iff i s).1 hs).2).2.1⟩

theorem mem_planeSub_of_conj_mem_planeBorel (i : PlaneFaces 6) {s : ↥(gammaN 6)}
    (hs : (planeFaceRepr i) * (s : SL(3, ℤ)) * (planeFaceRepr i)⁻¹ ∈ planeBorel) : s ∈ planeSub i := by
  have hg : (planeFaceRepr i) * (s : SL(3, ℤ)) * (planeFaceRepr i)⁻¹ ∈ gammaN 6 := by
    have := (gammaN_normal 6).conj_mem _ s.2 (planeFaceRepr i)
    simpa [mul_assoc] using this
  exact (mem_planeSub_iff i s).2 ⟨hg, mem_planeStab_of_gammaN (by norm_num) hg hs.1 hs.2⟩

/-- The plane face of `Γ(M)` over the pair `(i, O)`: the face of the conjugator `h_i u_O`. -/
def planeFaceOver (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) : PlaneFaces M :=
  (Quotient.mk (planeFaceSetoid M) ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) : PlaneFaces M)

omit [NeZero M] in
theorem uOPlane_coset (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    ((uOPlane M i o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o :=
  Quotient.out_eq (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M)

omit [NeZero M] in
theorem planeFaceOver_surjective :
    Function.Surjective (fun x : (Σ i : PlaneFaces 6, orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
      planeFaceOver M x.1 x.2) := by
  intro i'
  set h : SL(3, ℤ) := (planeFaceRepr i') with hh
  obtain ⟨q, hq, γ, hγ, hrep⟩ := PlaneFaces_rel_rep 6 h
  set j : PlaneFaces 6 := (Quotient.mk (planeFaceSetoid 6) h : PlaneFaces 6) with hj
  let g : ↥(gammaN 6) := ⟨γ⁻¹, (gammaN 6).inv_mem hγ⟩
  let x : ↥(gammaN 6) ⧸ Δ6 M := (g : ↥(gammaN 6) ⧸ Δ6 M)
  let o : orbitRel.Quotient ↥(planeSub j) (↥(gammaN 6) ⧸ Δ6 M) :=
    Quotient.mk (orbitRel ↥(planeSub j) (↥(gammaN 6) ⧸ Δ6 M)) x
  refine ⟨⟨j, o⟩, ?_⟩
  have hmo : orbitRel ↥(planeSub j) (↥(gammaN 6) ⧸ Δ6 M) (Quotient.out o) x :=
    Quotient.mk_out (s := orbitRel ↥(planeSub j) (↥(gammaN 6) ⧸ Δ6 M)) x
  rw [orbitRel_apply, mem_orbit_iff] at hmo
  obtain ⟨s, hs⟩ := hmo
  have hu : ((uOPlane M j o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = (((s : ↥(gammaN 6)) * g : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) := by
    rw [uOPlane_coset, ← hs]; rfl
  have hδ : ((s : ↥(gammaN 6)) * g)⁻¹ * uOPlane M j o ∈ Δ6 M := QuotientGroup.eq.mp hu.symm
  set δ : ↥(gammaN 6) := ((s : ↥(gammaN 6)) * g)⁻¹ * uOPlane M j o with hδdef
  have hu' : uOPlane M j o = (s : ↥(gammaN 6)) * g * δ := by rw [hδdef]; group
  have hq' := conj_mem_planeBorel_of_mem_planeSub j s.2
  have hδM : (δ : SL(3, ℤ)) ∈ gammaN M := hδ
  have key : (planeFaceRepr j) * ((uOPlane M j o : ↥(gammaN 6)) : SL(3, ℤ)) =
      ((planeFaceRepr j) * (s : SL(3, ℤ)) * (planeFaceRepr j)⁻¹ * q) * h * (δ : SL(3, ℤ)) := by
    rw [hu']
    have hg : (g : SL(3, ℤ)) = γ⁻¹ := rfl
    simp only [Subgroup.coe_mul, hg]
    have : (planeFaceRepr j) = q * h * γ := hrep
    rw [this]
    group
  have hrel : (planeFaceSetoid M).r h ((planeFaceRepr j) * ((uOPlane M j o : ↥(gammaN 6)) : SL(3, ℤ))) :=
    ⟨(planeFaceRepr j) * (s : SL(3, ℤ)) * (planeFaceRepr j)⁻¹ * q, planeBorel.mul_mem hq' hq, δ, hδM, key⟩
  show (Quotient.mk (planeFaceSetoid M) ((planeFaceRepr j) * ((uOPlane M j o : ↥(gammaN 6)) : SL(3, ℤ))) : PlaneFaces M) = i'
  have e1 : (Quotient.mk (planeFaceSetoid M) ((planeFaceRepr j) * ((uOPlane M j o : ↥(gammaN 6)) : SL(3, ℤ))) : PlaneFaces M) = (Quotient.mk (planeFaceSetoid M) h : PlaneFaces M) :=
    (Quotient.sound hrel).symm
  rw [e1]
  exact Quotient.out_eq i'

omit [NeZero M] in
theorem planeFaceOver_injective (h6 : 6 ∣ M) :
    Function.Injective (fun x : (Σ i : PlaneFaces 6, orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) =>
      planeFaceOver M x.1 x.2) := by
  rintro ⟨i, o⟩ ⟨j, p⟩ heq
  obtain ⟨q, hq, γ, hγ, hrel⟩ := Quotient.exact heq
  have hγ6 : γ ∈ gammaN 6 := gammaN_mono h6 hγ
  have hij : i = j := by
    have hr : (planeFaceSetoid 6).r (planeFaceRepr i) (planeFaceRepr j) :=
      ⟨q, hq, (uOPlane M i o : SL(3, ℤ)) * γ * ((uOPlane M j p : ↥(gammaN 6)) : SL(3, ℤ))⁻¹,
        (gammaN 6).mul_mem ((gammaN 6).mul_mem (uOPlane M i o).2 hγ6) ((gammaN 6).inv_mem (uOPlane M j p).2), by
          have e : (planeFaceRepr j) * ((uOPlane M j p : ↥(gammaN 6)) : SL(3, ℤ)) =
              q * ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hrel
          calc (planeFaceRepr j) = (planeFaceRepr j) * ((uOPlane M j p : ↥(gammaN 6)) : SL(3, ℤ)) * ((uOPlane M j p : ↥(gammaN 6)) : SL(3, ℤ))⁻¹ := by group
            _ = _ := by rw [e]; group⟩
    have e1 : (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr i) : PlaneFaces 6) = Quotient.mk (planeFaceSetoid 6) (planeFaceRepr j) := Quotient.sound hr
    rw [show (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr i) : PlaneFaces 6) = i from Quotient.out_eq i,
      show (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr j) : PlaneFaces 6) = j from Quotient.out_eq j] at e1
    exact e1
  subst hij
  set U : ↥(gammaN 6) := uOPlane M i o with hU
  set U' : ↥(gammaN 6) := uOPlane M i p with hU'
  let γ' : ↥(Δ6 M) := ⟨⟨γ, hγ6⟩, hγ⟩
  have hs : (U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ : ↥(gammaN 6)) ∈ planeSub i := by
    apply mem_planeSub_of_conj_mem_planeBorel
    have e : (planeFaceRepr i) * (U' : SL(3, ℤ)) = q * ((planeFaceRepr i) * (U : SL(3, ℤ))) * γ := hrel
    have e2 : (planeFaceRepr i) * ((U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ : ↥(gammaN 6)) : SL(3, ℤ)) * (planeFaceRepr i)⁻¹ = q := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hg : ((γ' : ↥(gammaN 6)) : SL(3, ℤ)) = γ := rfl
      rw [hg]
      calc (planeFaceRepr i) * ((U' : SL(3, ℤ)) * γ⁻¹ * (U : SL(3, ℤ))⁻¹) * (planeFaceRepr i)⁻¹
          = ((planeFaceRepr i) * (U' : SL(3, ℤ))) * γ⁻¹ * (U : SL(3, ℤ))⁻¹ * (planeFaceRepr i)⁻¹ := by group
        _ = q := by rw [e]; group
    rw [e2]; exact hq
  let sS : ↥(planeSub i) := ⟨_, hs⟩
  have hsm : sS • (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out p := by
    rw [← uOPlane_coset M i o, ← uOPlane_coset M i p]
    change ((U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ * U : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = (U' : ↥(gammaN 6) ⧸ Δ6 M)
    rw [QuotientGroup.eq]
    have : (U' * (γ' : ↥(gammaN 6))⁻¹ * U⁻¹ * U)⁻¹ * U' = (γ' : ↥(gammaN 6)) := by group
    rw [this]; exact γ'.2
  have hor : orbitRel ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M) (Quotient.out p) (Quotient.out o) := by
    rw [orbitRel_apply, mem_orbit_iff]; exact ⟨sS, hsm⟩
  have h1 := Quotient.sound hor
  rw [Quotient.out_eq, Quotient.out_eq] at h1
  rw [h1]

omit [NeZero M] in
theorem mk6_planeFaceOver (h6 : 6 ∣ M) (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr (planeFaceOver M i o)) : PlaneFaces 6) = i := by
  obtain ⟨q, hq, γ, hγ, hrep⟩ := PlaneFaces_rel_rep M ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)))
  have hr : (planeFaceSetoid 6).r (planeFaceRepr i) (planeFaceRepr (planeFaceOver M i o)) :=
    ⟨q, hq, ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)) * γ,
      (gammaN 6).mul_mem (uOPlane M i o).2 (gammaN_mono h6 hγ), by
        have : planeFaceRepr (planeFaceOver M i o) = q * ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hrep
        rw [this]; group⟩
  have e1 : (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr i) : PlaneFaces 6) =
      Quotient.mk (planeFaceSetoid 6) (planeFaceRepr (planeFaceOver M i o)) := Quotient.sound hr
  rw [show (Quotient.mk (planeFaceSetoid 6) (planeFaceRepr i) : PlaneFaces 6) = i from Quotient.out_eq i] at e1
  exact e1.symm

/-- **The bijection between the pairs `(i, O)` (a face `i` of `Γ(6)` and an orbit `O` of its plane group on `Γ(6)/Γ(M)`) and the plane faces of `Γ(M)`**, `6 ∣ M`. -/
def planeFaceOverEquiv (h6 : 6 ∣ M) : (Σ i : PlaneFaces 6, orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) ≃ PlaneFaces M :=
  Equiv.ofBijective (fun x => planeFaceOver M x.1 x.2) ⟨planeFaceOver_injective M h6, planeFaceOver_surjective M⟩

end PlaneBij

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
