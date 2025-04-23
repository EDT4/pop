import Mathlib.CategoryTheory.FullSubcategory

namespace CategoryTheory.FullSubcategory

open CategoryTheory

variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (P : C → Prop)
variable {F G : D ⥤ FullSubcategory P}

@[simps!]
def liftTrans
  (p : F ⋙ fullSubcategoryInclusion P ⟶ G ⋙ fullSubcategoryInclusion P)
  : F ⟶ G where
  app        := p.app
  naturality := p.naturality

@[simps!]
def liftIso
  (p : F ⋙ fullSubcategoryInclusion P ≅ G ⋙ fullSubcategoryInclusion P)
  : F ≅ G where
  hom := liftTrans _ p.hom
  inv := liftTrans _ p.inv
  hom_inv_id := by ext d ; exact congrArg (fun p => p.app d) p.hom_inv_id
  inv_hom_id := by ext d ; exact congrArg (fun p => p.app d) p.inv_hom_id
