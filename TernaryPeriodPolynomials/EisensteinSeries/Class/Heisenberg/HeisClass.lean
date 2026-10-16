module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisForm1
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisLatticeInv

@[expose] public section


open scoped ContDiff
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {ρt : Pt → E →L[ℝ] E} {G : Type} [Group G]

theorem invH_mulH_anti (n x : Pt) : invH (mulH n x) = mulH (invH x) (invH n) := by
  simp only [invH, mulH]
  ext <;> simp
  ring

/-- **The frame cochain of a `2`-form** (the invariant-frame coefficients `ρ(q)⁻¹ ω(X_{m+1}, X_{m+2})`, packed into the Chevalley-Eilenberg
cochain space `CE E`). -/
def frameCochain (ρt : Pt → E →L[ℝ] E) (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) : Pt → CE E :=
  fun q => pack2 (fun m => gauge2 ρt om m q)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem frameCochain_apply (om : Pt → Pt [⋀^Fin 2]→L[ℝ] E) (q : Pt) (m : Fin 3) :
    frameCochain ρt om q (i2 m) = gauge2 ρt om m q := by
  fin_cases m <;> rfl

omit [CompleteSpace E] in
theorem gauge2_equivariant (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) (m : Fin 3) (g : G)
    (x : Pt) : gauge2 ρt om.1.1 m (mulH (Λ.nOf g) x) = gauge2 ρt om.1.1 m x := by
  unfold gauge2
  rw [A2_equivariant R Λ om (m + 1) (m + 2) g x, invH_mulH_anti, R.mul]
  show ρt (invH x) (ρt (invH (Λ.nOf g)) (ρt (Λ.nOf g) _)) = _
  rw [R.cancel']

omit [CompleteSpace E] in
theorem frameCochain_equivariant (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) (g : G) (x : Pt) :
    frameCochain ρt om.1.1 (mulH (Λ.nOf g) x) = frameCochain ρt om.1.1 x := by
  unfold frameCochain
  congr 1
  funext m
  exact gauge2_equivariant R Λ om m g x

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem form_contDiff {n : ℕ} (w : Form (F := E) (Set.univ : Set Pt) n) : ContDiff ℝ ∞ (w.1 : RawForm Pt E n) :=
  contDiffOn_univ.mp w.2.1

omit [CompleteSpace E] in
theorem extDeriv_eq_zero_of_closed (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) (x : Pt) :
    extDeriv om.1.1 x = 0 := by
  have h := congrArg (fun f : Form (F := E) Set.univ 3 => (f.1 : RawForm Pt E 3) x) om.2.1
  simp only [d_apply _ _ (Set.mem_univ x)] at h
  exact h

end Main

section Assembly

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {ρt : Pt → E →L[ℝ] E} {G : Type} [Group G]

omit [CompleteSpace E] in
theorem frameCochain_mem_C1 (R : HeisRep ρt) (Λ : LatticeAction G) (N : ℕ)
    (hgens : ∃ ga gb gc : G, Λ.nOf ga = ((N : ℝ), 0, 0) ∧ Λ.nOf gb = (0, (N : ℝ), 0) ∧
      Λ.nOf gc = (0, 0, (N : ℝ)))
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) :
    frameCochain ρt om.1.1 ∈ C1 (N : ℝ) (N : ℝ) (N : ℝ) := by
  obtain ⟨ga, gb, gc, ha, hb, hc⟩ := hgens
  have hom := form_contDiff om.1
  refine ⟨pack2_contDiff (b := fun q m => gauge2 ρt om.1.1 m q) (fun m => gauge2_contDiff R hom m),
    fun p => ?_, fun p => ?_, fun p => ?_⟩
  · have := frameCochain_equivariant R Λ om gc p
    rw [hc, mulH_e3] at this
    exact this
  · have := frameCochain_equivariant R Λ om gb p
    rw [hb, mulH_e2] at this
    exact this
  · have := frameCochain_equivariant R Λ om ga p
    rw [ha, ← latX_eq_mulH] at this
    exact this

omit [CompleteSpace E] in
theorem frameCochain_closed (R : HeisRep ρt) (Λ : LatticeAction G)
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) :
    Dop (ceData (heisGen ρt) R.heisMod) (frameCochain ρt om.1.1) = 0 := by
  have hom := form_contDiff om.1
  funext p i
  have h := Dop_pack2 (heisGen ρt) R.heisMod (b := fun q m => gauge2 ρt om.1.1 m q)
    (fun m => gauge2_contDiff R hom m) p i
  show Dop (ceData (heisGen ρt) R.heisMod) (fun q => pack2 (fun m => gauge2 ρt om.1.1 m q)) p i = 0
  rw [h]
  split_ifs
  · have h2 := frame_div R hom p
    rw [extDeriv_eq_zero_of_closed R Λ om p] at h2
    simpa using h2.symm
  · rfl

/-- **The Nomizu-Kasuya averaging on the flag group, with the zig-zag class**.

Let `ρt` be a smooth unipotent representation of the Heisenberg group `H` (`HeisRep`), `G` a group acting on the chart `H ≅ ℝ³` by left translations through `nOf : G → H`, whose image is
contained in the lattice `(N ℤ)³` and contains its three generators, and let `ω` be a closed `E`-valued `2`-form on `H`, equivariant for `G` and the coefficients `g ↦ ρt (nOf g)`.
Then there is a closed equivariant form `ωc` whose gauge-trivialized frame coefficients are the constant Haar average `Av ω = heisAv (frameCochain ω)` (a `𝔇`-cocycle of the Chevalley-Eilenberg
complex with unipotent coefficients) and which has the same class as `ω` in `H²(G, E)`:
*the averaged pullback represents the restriction class, with coefficient transport included*. -/
theorem heis_class_av (R : HeisRep ρt) (Λ : LatticeAction G) (N : ℕ) (hN0 : N ≠ 0)
    (hrange : ∀ g, ∃ i j k : ℤ, Λ.nOf g = ((N : ℝ) * i, (N : ℝ) * j, (N : ℝ) * k))
    (hgens : ∃ ga gb gc : G, Λ.nOf ga = ((N : ℝ), 0, 0) ∧ Λ.nOf gb = (0, (N : ℝ), 0) ∧
      Λ.nOf gc = (0, 0, (N : ℝ)))
    (om : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ)) :
    ∃ ωc : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ),
      (∀ x m, gauge2 ρt ωc.1.1 m x = heisAv (N : ℝ) N N (frameCochain ρt om.1.1) (i2 m)) ∧
      ceD0 (heisGen ρt) (heisAv (N : ℝ) N N (frameCochain ρt om.1.1)) = 0 ∧
      deRhamClass isOpen_univ convex_univ Set.univ_nonempty (latAct Λ) (latRho R Λ) om =
        deRhamClass isOpen_univ convex_univ Set.univ_nonempty (latAct Λ) (latRho R Λ) ωc := by
  have hom := form_contDiff om.1
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hu := frameCochain_mem_C1 R Λ N hgens om
  have hcl := frameCochain_closed R Λ om
  obtain ⟨η, hη, hD0, hEq⟩ := heis_nomizu_ce (heisGen ρt) R.heisMod hN hN hN hu hcl
  have hηsm : ContDiff ℝ ∞ η := hη.1
  let a : Pt → Fin 3 → E := fun q k => η q (i1 k)
  have ha : ∀ k, ContDiff ℝ ∞ (fun q => a q k) := fun k => (contDiff_pi.mp hηsm) (i1 k)
  have hper : ∀ g x, a (mulH (Λ.nOf g) x) = a x := by
    intro g x
    obtain ⟨i, j, k, hijk⟩ := hrange g
    rw [hijk]
    funext c
    exact lattice_invariant (u := fun p => η p (i1 c)) (N := N) (fun p => congrFun (hη.2.1 p) (i1 c))
      (fun p => congrFun (hη.2.2.1 p) (i1 c)) (fun p => congrFun (hη.2.2.2 p) (i1 c)) i j k x
  let ψ := psiForm R ha
  have hψ := psiForm_equivariant R Λ ha hper
  let dψ : invClosed (isOpen_univ : IsOpen (Set.univ : Set Pt)) (latAct Λ) (latRho R Λ) :=
    ⟨d isOpen_univ 1 ψ, d_squared _ 1 ψ, fun g => by
      rw [← d_pullForm, hψ g, d_twForm]⟩
  have hψsm : ContDiff ℝ ∞ (psi1 ρt a) := psi1_contDiff R.smooth ha
  refine ⟨om - dψ, ?_, hD0, ?_⟩
  · intro x m
    have e1 : gauge2 ρt (om - dψ).1.1 m x = gauge2 ρt om.1.1 m x - gauge2 ρt dψ.1.1 m x := by
      unfold gauge2
      rw [← map_sub]
      congr 1
    have e2 : gauge2 ρt dψ.1.1 m x = Dop (ceData (heisGen ρt) R.heisMod) η x (i2 m) := by
      unfold gauge2
      have h1 : A2 dψ.1.1 (m + 1) (m + 2) x = extDeriv (psi1 ρt a) x ![Xf (m + 1) x, Xf (m + 2) x] := by
        unfold A2
        have := d_apply (isOpen_univ : IsOpen (Set.univ : Set Pt)) ψ (Set.mem_univ x)
        rw [show dψ.1.1 = (d isOpen_univ 1 ψ).1 from rfl, this]
        rfl
      rw [h1, frame_curl R hψsm m x, Dop_i2 (heisGen ρt) R.heisMod hηsm m x]
      congr 1
      funext k q
      exact gauge1_psi1 R a k q
    have e3 := congrFun (congrFun hEq x) (i2 m)
    simp only [Pi.sub_apply] at e3
    rw [e1, e2, ← e3, frameCochain_apply]
    abel
  · have h0 := deRhamClass_exact isOpen_univ convex_univ Set.univ_nonempty (latAct Λ) (latRho R Λ) dψ ψ hψ rfl
    have h1 := map_sub (deRhamClass isOpen_univ convex_univ Set.univ_nonempty (latAct Λ) (latRho R Λ)) om dψ
    rw [h1, h0, sub_zero]

end Assembly

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
