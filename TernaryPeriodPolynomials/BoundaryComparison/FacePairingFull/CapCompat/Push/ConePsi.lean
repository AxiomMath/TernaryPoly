module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCompat
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeStrata
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConeQuasi

@[expose] public section


/-!
# Carried maps between labelled pushout cones respect the strata

A chain map `u : K ⟶ K'` carried by the label carriers of `pushCarrierData` sends the `L`- and `P`-coordinates into
the `L'`- and `P'`-coordinates, hence (`PushCone.exists_strata`) induces carried chain maps of the three strata, and
is a quasi-isomorphism as soon as these are (`pushCone_map_quasiIso`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly.BoundaryFaceResolutionComparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

namespace PushCone

variable {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b)
  (KA : ∀ m, Submodule ℚ (A.X m)) (KL : ∀ m, Submodule ℚ (L.X m)) (KP : ∀ m, Submodule ℚ (P.X m))

theorem qL_mem (n : ℕ) {z : K.X n} (hz : z ∈ 𝒞.coneK KA KL KP n) : (𝒞.qL n).hom z ∈ KL n := by
  cases n with
  | zero =>
    obtain ⟨l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_zero KA KL KP z).1 hz
    change (𝒞.pL0).hom _ ∈ _
    rw [map_add, 𝒞.pL0_iL, 𝒞.pL0_iP, add_zero]
    exact hl
  | succ m =>
    obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ KA KL KP m z).1 hz
    change (𝒞.pL m).hom _ ∈ _
    rw [map_add, map_add, 𝒞.pL_iA, 𝒞.pL_iL, 𝒞.pL_iP, zero_add, add_zero]
    exact hl

theorem qP_mem (n : ℕ) {z : K.X n} (hz : z ∈ 𝒞.coneK KA KL KP n) : (𝒞.qP n).hom z ∈ KP n := by
  cases n with
  | zero =>
    obtain ⟨l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_zero KA KL KP z).1 hz
    change (𝒞.pP0).hom _ ∈ _
    rw [map_add, 𝒞.pP0_iL, 𝒞.pP0_iP, zero_add]
    exact hp
  | succ m =>
    obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ KA KL KP m z).1 hz
    change (𝒞.pP m).hom _ ∈ _
    rw [map_add, map_add, 𝒞.pP_iA, 𝒞.pP_iL, 𝒞.pP_iP, zero_add, zero_add]
    exact hp

theorem pA_mem (m : ℕ) {z : K.X (m+1)} (hz : z ∈ 𝒞.coneK KA KL KP (m+1)) : (𝒞.pA m).hom z ∈ KA m := by
  obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ KA KL KP m z).1 hz
  rw [map_add, map_add, 𝒞.pA_iA, 𝒞.pA_iL, 𝒞.pA_iP, add_zero, add_zero]
  exact hx

theorem exists_iL_of_mem (n : ℕ) {z : K.X n} (hz : z ∈ 𝒞.coneK (fun _ => ⊥) KL (fun _ => ⊥) n) :
    ∃ l ∈ KL n, z = (𝒞.iL n).hom l := by
  cases n with
  | zero =>
    obtain ⟨l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_zero _ KL _ z).1 hz
    rw [Submodule.mem_bot] at hp
    exact ⟨l, hl, by rw [hp, map_zero, add_zero]⟩
  | succ m =>
    obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ _ KL _ m z).1 hz
    rw [Submodule.mem_bot] at hx hp
    exact ⟨l, hl, by rw [hx, hp, map_zero, map_zero, zero_add, add_zero]⟩

theorem exists_iP_of_mem (n : ℕ) {z : K.X n} (hz : z ∈ 𝒞.coneK (fun _ => ⊥) (fun _ => ⊥) KP n) :
    ∃ p ∈ KP n, z = (𝒞.iP n).hom p := by
  cases n with
  | zero =>
    obtain ⟨l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_zero _ _ KP z).1 hz
    rw [Submodule.mem_bot] at hl
    exact ⟨p, hp, by rw [hl, map_zero, zero_add]⟩
  | succ m =>
    obtain ⟨x, hx, l, hl, p, hp, rfl⟩ := (𝒞.mem_coneK_succ _ _ KP m z).1 hz
    rw [Submodule.mem_bot] at hx hl
    exact ⟨p, hp, by rw [hx, hl, map_zero, map_zero, zero_add, zero_add]⟩

variable {A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
  {BA : CellBasis A} {BL : CellBasis L} {BP : CellBasis P}
  {ZF ZL ZP : Type} [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] {φL : ZF → ZL} {φP : ZF → ZP}
  (𝒟 : PushCone A' L' P' K' a' b')
  (ld : PushLabels a b BA BL BP ZF ZL ZP φL φP) (T : PushTargets 𝒟 ZF ZL ZP φL φP)

theorem carried_range_L (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n)) (n : ℕ)
    (l : L.X n) : ∃ l' : L'.X n, (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom l' := by
  have hmor : 𝒞.iL n ≫ u.f n ≫ (𝟙 (K'.X n) - 𝒟.qL n ≫ 𝒟.iL n) = 0 := by
    apply BL.hom_ext n
    intro t
    have hc : (u.f n).hom (coneCell BA BL BP 𝒞 n (inLcell n t)) ∈ pushK 𝒟 ld T n (inLcell n t) n :=
      hu n (inLcell n t)
    rw [pushK_inL, coneCell_inL] at hc
    obtain ⟨l1, -, hl1⟩ := 𝒟.exists_iL_of_mem _ n hc
    change (𝟙 (K'.X n) - 𝒟.qL n ≫ 𝒟.iL n).hom ((u.f n).hom ((𝒞.iL n).hom (BL.cell n t))) = 0
    rw [hl1]
    change (𝒟.iL n).hom l1 - (𝒟.iL n).hom ((𝒟.qL n).hom ((𝒟.iL n).hom l1)) = 0
    rw [𝒟.qL_iL, sub_self]
  have h := congrArg (fun φ => φ.hom l) hmor
  change (𝟙 (K'.X n) - 𝒟.qL n ≫ 𝒟.iL n).hom ((u.f n).hom ((𝒞.iL n).hom l)) = 0 at h
  refine ⟨(𝒟.qL n).hom ((u.f n).hom ((𝒞.iL n).hom l)), ?_⟩
  change _ - (𝒟.iL n).hom ((𝒟.qL n).hom _) = 0 at h
  exact sub_eq_zero.1 h

theorem carried_range_P (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n)) (n : ℕ)
    (p : P.X n) : ∃ p' : P'.X n, (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom p' := by
  have hmor : 𝒞.iP n ≫ u.f n ≫ (𝟙 (K'.X n) - 𝒟.qP n ≫ 𝒟.iP n) = 0 := by
    apply BP.hom_ext n
    intro t
    have hc : (u.f n).hom (coneCell BA BL BP 𝒞 n (inPcell n t)) ∈ pushK 𝒟 ld T n (inPcell n t) n :=
      hu n (inPcell n t)
    rw [pushK_inP, coneCell_inP] at hc
    obtain ⟨p1, -, hp1⟩ := 𝒟.exists_iP_of_mem _ n hc
    change (𝟙 (K'.X n) - 𝒟.qP n ≫ 𝒟.iP n).hom ((u.f n).hom ((𝒞.iP n).hom (BP.cell n t))) = 0
    rw [hp1]
    change (𝒟.iP n).hom p1 - (𝒟.iP n).hom ((𝒟.qP n).hom ((𝒟.iP n).hom p1)) = 0
    rw [𝒟.qP_iP, sub_self]
  have h := congrArg (fun φ => φ.hom p) hmor
  change (𝟙 (K'.X n) - 𝒟.qP n ≫ 𝒟.iP n).hom ((u.f n).hom ((𝒞.iP n).hom p)) = 0 at h
  refine ⟨(𝒟.qP n).hom ((u.f n).hom ((𝒞.iP n).hom p)), ?_⟩
  change _ - (𝒟.iP n).hom ((𝒟.qP n).hom _) = 0 at h
  exact sub_eq_zero.1 h

theorem strata_carried_L (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n))
    (uL : L ⟶ L') (huL : ∀ n, uL.f n = 𝒞.iL n ≫ u.f n ≫ 𝒟.qL n) (n : ℕ) (t : BL.S n) :
    (uL.f n).hom (BL.cell n t) ∈ T.FL (ld.labL n t) n := by
  have hc : (u.f n).hom (coneCell BA BL BP 𝒞 n (inLcell n t)) ∈ pushK 𝒟 ld T n (inLcell n t) n :=
    hu n (inLcell n t)
  rw [pushK_inL, coneCell_inL] at hc
  rw [huL n]
  exact 𝒟.qL_mem _ _ _ n hc

theorem strata_carried_P (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n))
    (uP : P ⟶ P') (huP : ∀ n, uP.f n = 𝒞.iP n ≫ u.f n ≫ 𝒟.qP n) (n : ℕ) (t : BP.S n) :
    (uP.f n).hom (BP.cell n t) ∈ T.FP (ld.labP n t) n := by
  have hc : (u.f n).hom (coneCell BA BL BP 𝒞 n (inPcell n t)) ∈ pushK 𝒟 ld T n (inPcell n t) n :=
    hu n (inPcell n t)
  rw [pushK_inP, coneCell_inP] at hc
  rw [huP n]
  exact 𝒟.qP_mem _ _ _ n hc

theorem strata_carried_A (u : K ⟶ K') (hu : ∀ n, (pushCarrierData 𝒞 𝒟 ld T).Carried (u.f n))
    (uA : A ⟶ A') (huA : ∀ n, uA.f n = 𝒞.iA n ≫ u.f (n+1) ≫ 𝒟.pA n) (n : ℕ) (s : BA.S n) :
    (uA.f n).hom (BA.cell n s) ∈ T.FA (ld.labA n s) n := by
  have hc : (u.f (n+1)).hom (coneCell BA BL BP 𝒞 (n+1) (Sum.inl s)) ∈
      pushK 𝒟 ld T (n+1) (Sum.inl s) (n+1) := hu (n+1) (Sum.inl s)
  rw [huA n]
  exact 𝒟.pA_mem _ _ _ n hc

variable (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)
  (SA' : DiagSystem A') (SL' : DiagSystem L') (SP' : DiagSystem P')

theorem strata_eps_L (u : K ⟶ K') (hueps : u.f 0 ≫ 𝒟.eps SL' SP' = 𝒞.eps SL SP) (uL : L ⟶ L')
    (hspec : 𝒞.iL 0 ≫ u.f 0 = uL.f 0 ≫ 𝒟.iL 0) (l : L.X 0) :
    SL'.eps.hom ((uL.f 0).hom l) = SL.eps.hom l := by
  have h := congrArg (fun φ => φ.hom ((𝒞.iL 0).hom l)) hueps
  have h2 : (u.f 0).hom ((𝒞.iL 0).hom l) = (𝒟.iL 0).hom ((uL.f 0).hom l) :=
    congrArg (fun φ => φ.hom l) hspec
  change (𝒟.eps SL' SP').hom ((u.f 0).hom ((𝒞.iL 0).hom l)) = (𝒞.eps SL SP).hom ((𝒞.iL 0).hom l) at h
  rw [h2, 𝒟.eps_iL, 𝒞.eps_iL] at h
  exact h

theorem strata_eps_P (u : K ⟶ K') (hueps : u.f 0 ≫ 𝒟.eps SL' SP' = 𝒞.eps SL SP) (uP : P ⟶ P')
    (hspec : 𝒞.iP 0 ≫ u.f 0 = uP.f 0 ≫ 𝒟.iP 0) (p : P.X 0) :
    SP'.eps.hom ((uP.f 0).hom p) = SP.eps.hom p := by
  have h := congrArg (fun φ => φ.hom ((𝒞.iP 0).hom p)) hueps
  have h2 : (u.f 0).hom ((𝒞.iP 0).hom p) = (𝒟.iP 0).hom ((uP.f 0).hom p) :=
    congrArg (fun φ => φ.hom p) hspec
  change (𝒟.eps SL' SP').hom ((u.f 0).hom ((𝒞.iP 0).hom p)) = (𝒞.eps SL SP).hom ((𝒞.iP 0).hom p) at h
  rw [h2, 𝒟.eps_iP, 𝒞.eps_iP] at h
  exact h

theorem strata_eps_A (hS : Strict (a := a) (b := b) SA SL SP) (hS' : Strict (a := a') (b := b') SA' SL' SP')
    (u : K ⟶ K') (uA : A ⟶ A') (uL : L ⟶ L') (uP : P ⟶ P')
    (huA : ∀ n, uA.f n = 𝒞.iA n ≫ u.f (n+1) ≫ 𝒟.pA n)
    (hspecL : 𝒞.iL 0 ≫ u.f 0 = uL.f 0 ≫ 𝒟.iL 0) (hspecP : 𝒞.iP 0 ≫ u.f 0 = uP.f 0 ≫ 𝒟.iP 0)
    (hepsL : ∀ l : L.X 0, SL'.eps.hom ((uL.f 0).hom l) = SL.eps.hom l) (x : A.X 0) :
    SA'.eps.hom ((uA.f 0).hom x) = SA.eps.hom x := by
  set y := (u.f 1).hom ((𝒞.iA 0).hom x) with hy
  have hx' : (uA.f 0).hom x = (𝒟.pA 0).hom y := by rw [huA 0]; rfl
  have hd : (K'.d 1 0).hom y = (𝒟.iL 0).hom ((uL.f 0).hom ((a.f 0).hom x)) -
      (𝒟.iP 0).hom ((uP.f 0).hom ((b.f 0).hom x)) := by
    have h1 : (K'.d 1 0).hom y = (u.f 0).hom ((K.d 1 0).hom ((𝒞.iA 0).hom x)) :=
      congrArg (fun φ => φ.hom ((𝒞.iA 0).hom x)) (u.comm 1 0)
    rw [h1, 𝒞.d_iA_zero, map_sub]
    have h2 : (u.f 0).hom ((𝒞.iL 0).hom ((a.f 0).hom x)) = (𝒟.iL 0).hom ((uL.f 0).hom ((a.f 0).hom x)) :=
      congrArg (fun φ => φ.hom ((a.f 0).hom x)) hspecL
    have h3 : (u.f 0).hom ((𝒞.iP 0).hom ((b.f 0).hom x)) = (𝒟.iP 0).hom ((uP.f 0).hom ((b.f 0).hom x)) :=
      congrArg (fun φ => φ.hom ((b.f 0).hom x)) hspecP
    rw [h2, h3]
  have hdec := 𝒟.decomp_succ 0 y
  have hd2 : (K'.d 1 0).hom y = (𝒟.iL 0).hom ((a'.f 0).hom ((𝒟.pA 0).hom y) + (L'.d 1 0).hom ((𝒟.pL 0).hom y)) +
      (𝒟.iP 0).hom (-(b'.f 0).hom ((𝒟.pA 0).hom y) + (P'.d 1 0).hom ((𝒟.pP 0).hom y)) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_add, 𝒟.d_iA_zero, 𝒟.d_iL, 𝒟.d_iP]
    simp only [map_add, map_neg]
    abel
  rw [hd2] at hd
  have hL := congrArg (𝒟.pL0).hom hd
  simp only [map_add, map_sub, 𝒟.pL0_iL, 𝒟.pL0_iP, add_zero, sub_zero] at hL
  have hL2 := congrArg SL'.eps.hom hL
  rw [map_add, hepsL] at hL2
  have e1 : SL'.eps.hom ((L'.d 1 0).hom ((𝒟.pL 0).hom y)) = 0 := by
    have := congrArg (fun φ => φ.hom ((𝒟.pL 0).hom y)) SL'.eps_d
    exact this
  have e2 : SL'.eps.hom ((a'.f 0).hom ((𝒟.pA 0).hom y)) = SA'.eps.hom ((𝒟.pA 0).hom y) :=
    congrArg (fun φ => φ.hom ((𝒟.pA 0).hom y)) hS'.a_eps
  have e3 : SL.eps.hom ((a.f 0).hom x) = SA.eps.hom x :=
    congrArg (fun φ => φ.hom x) hS.a_eps
  rw [e1, add_zero, e2, e3] at hL2
  rw [hx']
  exact hL2

end PushCone

open PushCone HomologicalComplex in
theorem pushConeOfCofiber_pA {A L P : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P) (n : ℕ) :
    (pushConeOfCofiber a b).pA n = CofiberSequence.first (pushArrow a b) n := by
  have hr := CofiberSequence.right_first (pushArrow a b) n
  have hA : coneIA a b n ≫ CofiberSequence.first (pushArrow a b) n = 𝟙 _ :=
    CofiberSequence.left_first (pushArrow a b) n
  have hL : coneIL a b (n+1) ≫ CofiberSequence.first (pushArrow a b) n = 0 := by
    unfold coneIL
    rw [Category.assoc]
    change _ ≫ (CofiberSequence.right (pushArrow a b) (n+1) ≫ CofiberSequence.first (pushArrow a b) n) = 0
    rw [hr, comp_zero]
  have hP : coneIP a b (n+1) ≫ CofiberSequence.first (pushArrow a b) n = 0 := by
    unfold coneIP
    rw [Category.assoc]
    change _ ≫ (CofiberSequence.right (pushArrow a b) (n+1) ≫ CofiberSequence.first (pushArrow a b) n) = 0
    rw [hr, comp_zero]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have hdec := (pushConeOfCofiber a b).decomp_succ n z
  generalize ((pushConeOfCofiber a b).pA n).hom z = x at hdec
  generalize ((pushConeOfCofiber a b).pL n).hom z = l at hdec
  generalize ((pushConeOfCofiber a b).pP n).hom z = p at hdec
  subst hdec
  have e1 : (CofiberSequence.first (pushArrow a b) n).hom ((coneIA a b n).hom x) = x := by
    simpa using congrArg (fun φ => φ.hom x) hA
  have e2 : (CofiberSequence.first (pushArrow a b) n).hom ((coneIL a b (n+1)).hom l) = 0 := by
    simpa using congrArg (fun φ => φ.hom l) hL
  have e3 : (CofiberSequence.first (pushArrow a b) n).hom ((coneIP a b (n+1)).hom p) = 0 := by
    simpa using congrArg (fun φ => φ.hom p) hP
  show x = (CofiberSequence.first (pushArrow a b) n).hom (_ + _ + _)
  rw [map_add, map_add]
  change x = (CofiberSequence.first (pushArrow a b) n).hom ((coneIA a b n).hom x) +
    (CofiberSequence.first (pushArrow a b) n).hom ((coneIL a b (n+1)).hom l) +
    (CofiberSequence.first (pushArrow a b) n).hom ((coneIP a b (n+1)).hom p)
  rw [e1, e2, e3]
  simp

open PushCone in
/-- **The comparison of labelled pushout cones.**  Given a labelled model cone and a target cone with acyclic label
carriers, and criteria for the three stratum maps to be quasi-isomorphisms, there is a chain map between the cones,
carried by the label carriers, compatible with the augmentations, and a quasi-isomorphism. -/
theorem exists_pushPsi {A L P A' L' P' : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P)
    (a' : A' ⟶ L') (b' : A' ⟶ P') {BA : CellBasis A} {BL : CellBasis L} {BP : CellBasis P}
    {ZF ZL ZP : Type} [MulAction Γ ZF] [MulAction Γ ZL] [MulAction Γ ZP] {φL : ZF → ZL} {φP : ZF → ZP}
    (ld : PushLabels a b BA BL BP ZF ZL ZP φL φP) (T : PushTargets (pushConeOfCofiber a' b') ZF ZL ZP φL φP)
    (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)
    (SA' : DiagSystem A') (SL' : DiagSystem L') (SP' : DiagSystem P')
    (hS : Strict (a := a) (b := b) SA SL SP) (hS' : Strict (a := a') (b := b') SA' SL' SP')
    (G : PushTargets.Good (pushConeOfCofiber a' b') SA' SL' SP' T)
    (hepsL : ∀ t : BL.S 0, SL.eps.hom (BL.cell 0 t) = (1 : ℚ))
    (hepsP : ∀ t : BP.S 0, SP.eps.hom (BP.cell 0 t) = (1 : ℚ))
    (qA : ∀ w : A ⟶ A', (∀ n s, (w.f n).hom (BA.cell n s) ∈ T.FA (ld.labA n s) n) →
      (∀ x, SA'.eps.hom ((w.f 0).hom x) = SA.eps.hom x) → QuasiIso w)
    (qL : ∀ w : L ⟶ L', (∀ n s, (w.f n).hom (BL.cell n s) ∈ T.FL (ld.labL n s) n) →
      (∀ x, SL'.eps.hom ((w.f 0).hom x) = SL.eps.hom x) → QuasiIso w)
    (qP : ∀ w : P ⟶ P', (∀ n s, (w.f n).hom (BP.cell n s) ∈ T.FP (ld.labP n s) n) →
      (∀ x, SP'.eps.hom ((w.f 0).hom x) = SP.eps.hom x) → QuasiIso w) :
    ∃ u : pushCone a b ⟶ pushCone a' b',
      (∀ n, (pushCarrierData (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T).Carried (u.f n)) ∧
      u.f 0 ≫ (pushConeOfCofiber a' b').eps SL' SP' = (pushConeOfCofiber a b).eps SL SP ∧ QuasiIso u := by
  obtain ⟨u, hu, hueps⟩ := exists_pushCarried_chainMap (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T
    SA SL SP SA' SL' SP' hS hS' G hepsL hepsP
  have hL := carried_range_L (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T u hu
  have hP := carried_range_P (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T u hu
  obtain ⟨uA, uL, uP, huL, huP, huA, hspecL, hspecP⟩ := exists_strata u hL hP
  have hepsL' := strata_eps_L (pushConeOfCofiber a b) (pushConeOfCofiber a' b') SL SP SL' SP' u hueps uL
    (hspecL 0)
  have hepsP' := strata_eps_P (pushConeOfCofiber a b) (pushConeOfCofiber a' b') SL SP SL' SP' u hueps uP
    (hspecP 0)
  have hepsA' := strata_eps_A (pushConeOfCofiber a b) (pushConeOfCofiber a' b') SA SL SP SA' SL' SP' hS hS'
    u uA uL uP huA (hspecL 0) (hspecP 0) hepsL'
  have hqA : QuasiIso uA := qA uA (strata_carried_A (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T u hu uA huA)
    hepsA'
  have hqL : QuasiIso uL := qL uL (strata_carried_L (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T u hu uL huL)
    hepsL'
  have hqP : QuasiIso uP := qP uP (strata_carried_P (pushConeOfCofiber a b) (pushConeOfCofiber a' b') ld T u hu uP huP)
    hepsP'
  refine ⟨u, hu, hueps, ?_⟩
  refine pushCone_map_quasiIso a b a' b' u uA uL uP hspecL hspecP (fun n => ?_)
  rw [← pushConeOfCofiber_pA]
  exact (huA n).symm

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
