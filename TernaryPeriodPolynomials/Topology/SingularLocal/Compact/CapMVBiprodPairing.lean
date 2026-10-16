module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairingNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open SingularLocalCap

/-- Push a genuine cap pairing through an actual chain map. -/
def pushPairing {C : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (h : L ⟶ M)
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b) (a b : ℕ) :
    C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b := (β a b).compr₂ (h.f b).hom

/-- An actual chain map preserves the exact cap Leibniz identity. -/
theorem pushPairing_leibniz {C : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (h : L ⟶ M)
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (hβ : Descent.Leibniz C K L β) : Descent.Leibniz C K M (pushPairing h β) := by
  intro a b x c
  change h.f b (β a b x (K.d (a+b+1) (a+b) c)) =
    h.f b (β (a+1) b (C.d a (a+1) x) ((Descent.castLeft K a b).hom c)) +
      (-1 : ℤ)^a • M.d (b+1) b (h.f (b+1) (β a (b+1) x c))
  rw [hβ,map_add,map_zsmul]
  exact congrArg (fun z => h.f b (β (a+1) b (C.d a (a+1) x) ((Descent.castLeft K a b).hom c)) +
    (-1 : ℤ)^a • z) (congrArg (fun f => f (β a (b+1) x c)) (h.comm (b+1) b)).symm

/-- The sum of two actual cap pairings has the same precise Leibniz convention. -/
theorem addPairing_leibniz {C : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (β γ : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (hβ : Descent.Leibniz C K L β) (hγ : Descent.Leibniz C K L γ) :
    Descent.Leibniz C K L (β + γ) := by
  intro a b x c
  change β a b x (K.d (a+b+1) (a+b) c) + γ a b x (K.d (a+b+1) (a+b) c) =
    (β (a+1) b (C.d a (a+1) x) ((Descent.castLeft K a b).hom c) +
      γ (a+1) b (C.d a (a+1) x) ((Descent.castLeft K a b).hom c)) +
    (-1 : ℤ)^a • L.d (b+1) b (β a (b+1) x c + γ a (b+1) x c)
  rw [hβ,hγ,map_add,smul_add]
  abel

/-- The actual pair of cap operations on two cochain complexes and two chain complexes. -/
def biprodPairing {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (γ : ∀ a b, D.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b) :=
  pushPairing biprod.inl (pullPairing biprod.fst (𝟙 K) β) +
    pushPairing biprod.inr (pullPairing biprod.snd (𝟙 K) γ)

/-- The actual pair of localized caps has the exact geometric Leibniz sign. -/
theorem biprodPairing_leibniz {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (γ : ∀ a b, D.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b)
    (hβ : Descent.Leibniz C K L β) (hγ : Descent.Leibniz D K M γ) :
    Descent.Leibniz (C ⊞ D) K (L ⊞ M) (biprodPairing β γ) :=
  addPairing_leibniz _ _
    (pushPairing_leibniz _ _ (pullPairing_leibniz _ _ _ hβ))
    (pushPairing_leibniz _ _ (pullPairing_leibniz _ _ _ hγ))

/-- The first component of the actual pair cap is the actual first cap. -/
theorem biprodPairing_fst {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (γ : ∀ a b, D.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b)
    (a b : ℕ) (x : (C ⊞ D).X a) (c : K.X (a+b)) :
    (biprod.fst : L ⊞ M ⟶ L).f b (biprodPairing β γ a b x c) =
      β a b ((biprod.fst : C ⊞ D ⟶ C).f a x) c := by
  change (biprod.fst : L ⊞ M ⟶ L).f b
    ((biprod.inl : L ⟶ L ⊞ M).f b (β a b ((biprod.fst : C ⊞ D ⟶ C).f a x) c) +
      (biprod.inr : M ⟶ L ⊞ M).f b (γ a b ((biprod.snd : C ⊞ D ⟶ D).f a x) c)) = _
  rw [map_add]
  have hl := congrArg (fun f => f (β a b ((biprod.fst : C ⊞ D ⟶ C).f a x) c))
    (HomologicalComplex.congr_hom (biprod.inl_fst (X := L) (Y := M)) b)
  have hr := congrArg (fun f => f (γ a b ((biprod.snd : C ⊞ D ⟶ D).f a x) c))
    (HomologicalComplex.congr_hom (biprod.inr_fst (X := L) (Y := M)) b)
  exact congrArg₂ (· + ·) hl hr |>.trans (add_zero _)

/-- The second component of the actual pair cap is the actual second cap. -/
theorem biprodPairing_snd {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b)
    (γ : ∀ a b, D.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] M.X b)
    (a b : ℕ) (x : (C ⊞ D).X a) (c : K.X (a+b)) :
    (biprod.snd : L ⊞ M ⟶ M).f b (biprodPairing β γ a b x c) =
      γ a b ((biprod.snd : C ⊞ D ⟶ D).f a x) c := by
  change (biprod.snd : L ⊞ M ⟶ M).f b
    ((biprod.inl : L ⟶ L ⊞ M).f b (β a b ((biprod.fst : C ⊞ D ⟶ C).f a x) c) +
      (biprod.inr : M ⟶ L ⊞ M).f b (γ a b ((biprod.snd : C ⊞ D ⟶ D).f a x) c)) = _
  rw [map_add]
  have hl := congrArg (fun f => f (β a b ((biprod.fst : C ⊞ D ⟶ C).f a x) c))
    (HomologicalComplex.congr_hom (biprod.inl_snd (X := L) (Y := M)) b)
  have hr := congrArg (fun f => f (γ a b ((biprod.snd : C ⊞ D ⟶ D).f a x) c))
    (HomologicalComplex.congr_hom (biprod.inr_snd (X := L) (Y := M)) b)
  exact congrArg₂ (· + ·) hl hr |>.trans (zero_add _)

end TernaryPoly.SingularLocalCompactCapMV
