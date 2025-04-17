import Mathlib.CategoryTheory.Comma.Basic

namespace CategoryTheory.Comma

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

@[simps!]
def lift
  (da : D ⥤ A)
  (db : D ⥤ B)
  (p : (da ⋙ L) ⟶ (db ⋙ R))
  : D ⥤ Comma L R
where
  obj d := {
    left   := da.obj d
    right  := db.obj d
    hom    := p.app d
  }
  map f := {
    left  := da.map f
    right := db.map f
    w  := p.naturality _
  }
