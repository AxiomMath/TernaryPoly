module

public import TernaryPeriodPolynomials.Topology.Rational.Local.Orientation

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalLocalOrientation
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual relative-chain transport of a support by a homeomorphism. -/
def supportPullbackIso (e : X ≃ₜ Y) (K : Set Y) :
    relativeChains (e ⁻¹' K)ᶜ ≅ relativeChains Kᶜ :=
  relativeHomeomorphIso e _ _ (fun _ => Iff.rfl)

/-- Homeomorphism transport of support classes commutes with their literal point restrictions. -/
theorem supportPullbackIso_point (e : X ≃ₜ Y) (K : Set Y) (x : X) (hx : e x ∈ K) :
    (supportPullbackIso e K).hom ≫ supportPointMap K (e x) hx =
      supportPointMap (e ⁻¹' K) x hx ≫ (homeomorphLocalIso e x).hom := by
  unfold supportPullbackIso supportPointMap homeomorphLocalIso
  rw [relativeHomeomorphIso_hom,relativeHomeomorphIso_hom]
  erw [relativeMap_comp,relativeMap_comp]
  rfl

/-- The actual local homology isomorphism associated to a homeomorphism. -/
def pointHomologyIso (e : X ≃ₜ Y) (x : X) (k : ℕ) :
    (localChains x).homology k ≅ (localChains (e x)).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso (homeomorphLocalIso e x)

/-- Pullback of the actual point generators uses the inverse of the literal pair-map isomorphism. -/
def pullbackGenerator (e : X ≃ₜ Y) (k : ℕ) (o : ∀ y : Y, (localChains y).homology k)
    (x : X) : (localChains x).homology k :=
  (pointHomologyIso e x k).inv (o (e x))

/-- Actual local representability is preserved by homeomorphisms. -/
theorem locallyRepresented_pullback (e : X ≃ₜ Y) (k : ℕ)
    (o : ∀ y : Y, (localChains y).homology k) (ho : LocallyRepresented k o) :
    LocallyRepresented k (pullbackGenerator e k o) := by
  intro x
  obtain ⟨U,K,hx,hUK,c,hc⟩ := ho (e x)
  let iso := (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso
    (supportPullbackIso e K)
  refine ⟨⟨e ⁻¹' (U : Set Y),U.isOpen.preimage e.continuous⟩,e ⁻¹' K,hx,
    (fun _ hz => hUK hz),iso.inv c,?_⟩
  intro y hy hK
  apply (ModuleCat.mono_iff_injective (pointHomologyIso e y k).hom).mp inferInstance
  have hm := congrArg (fun f => homologyMap f k) (supportPullbackIso_point e K y hK)
  rw [homologyMap_comp,homologyMap_comp] at hm
  have hv := congrArg (fun f => f (iso.inv c)) hm
  have hv' : (pointHomologyIso e y k).hom
      (homologyMap (supportPointMap (e ⁻¹' K) y hK) k (iso.inv c)) = o (e y) := by
    have hh : homologyMap (supportPointMap K (e y) hK) k c = o (e y) := hc (e y) hy hK
    change homologyMap (supportPointMap K (e y) hK) k (iso.hom (iso.inv c)) =
      (pointHomologyIso e y k).hom
        (homologyMap (supportPointMap (e ⁻¹' K) y hK) k (iso.inv c)) at hv
    have hi : iso.hom (iso.inv c) = c := by
      change (iso.inv ≫ iso.hom) c = c
      rw [iso.inv_hom_id]
      rfl
    rw [hi,hh] at hv
    exact hv.symm
  simpa [pullbackGenerator] using hv'

/-- Pulling back a genuine homological orientation preserves its nonzero generators and
its actual local relative-class representatives. -/
def Orientation.pullback (e : X ≃ₜ Y) (k : ℕ) (o : Orientation k Y) : Orientation k X where
  generator := pullbackGenerator e k o.generator
  nonzero x := by
    intro h
    have hh := congrArg (fun c => (pointHomologyIso e x k).hom c) h
    exact o.nonzero (e x) (by simpa [pullbackGenerator] using hh)
  locallyRepresented := locallyRepresented_pullback e k o.generator o.locallyRepresented

end TernaryPoly.RationalLocalOrientation
