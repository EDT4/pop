import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

namespace CategoryTheory.Bicategory

variable {J : Type _} [Bicategory J]
variable {C : Type _} [Bicategory C]

section
variable (J)
@[simps]
def OplaxFunctor.const (c : C) : OplaxFunctor J C where
  obj     := fun _ => c
  map     := fun _ => 𝟙 c
  map₂    := fun _ => 𝟙 _
  mapId   := fun _ => 𝟙 _
  mapComp := fun _ _ => (leftUnitor (𝟙 c)).inv
end

-- TODO: Not sure. Did find any sources regarding this.
structure OplaxCone (F : OplaxFunctor J C) where
  pt : C
  π : OplaxNatTrans (OplaxFunctor.const J pt) F

structure IsOplaxLimit {F : OplaxFunctor J C} (t : OplaxCone F) where
  lift : ∀(s : OplaxCone F), s.pt ⟶ t.pt
  fac  : ∀(s : OplaxCone F) (j : J), lift s ≫ t.π.app j = s.π.app j
  uniq : ∀{s : OplaxCone F} (m : s.pt ⟶ t.pt), (∀j, m ≫ t.π.app j = s.π.app j) → (m = lift s)
  -- TODO: ?
  -- fac₂ : ∀(s : OplaxCone F) {j k : J} (f : j ⟶ k), s.π.naturality f = (whiskerRight (t.π.naturality f) (lift s)) ≫ (whiskerLeft (F.map f) (fac s j)) := by aesop
