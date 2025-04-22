import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.CategoryTheory.Reassoc

namespace CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]

structure LaxPullback (L : A ⥤ C) (R : B ⥤ C) where
  left : A
  right : B
  middle : C
  homl : L.obj left ⟶ middle
  homr : R.obj right ⟶ middle

variable {L : A ⥤ C}
variable {R : B ⥤ C}

namespace LaxPullback

@[ext]
structure Hom (X Y : LaxPullback L R) where
  left   : X.left   ⟶ Y.left
  right  : X.right  ⟶ Y.right
  middle : X.middle ⟶ Y.middle
  wl : L.map left  ≫ Y.homl = X.homl ≫ middle := by aesop_cat
  wr : R.map right ≫ Y.homr = X.homr ≫ middle := by aesop_cat

instance Hom.inhabited
  [Inhabited (LaxPullback L R)]
  : Inhabited (LaxPullback.Hom (default : LaxPullback L R) default)
  := ⟨{ left := 𝟙 _, right := 𝟙 _, middle := 𝟙 _}⟩

attribute [reassoc (attr := simp)] LaxPullback.Hom.wl LaxPullback.Hom.wr

instance category : Category (LaxPullback L R) where
  Hom X Y := Hom X Y
  id X := {
    left   := 𝟙 X.left
    right  := 𝟙 X.right
    middle := 𝟙 X.middle
  }
  comp f g := {
    left   := f.left   ≫ g.left
    right  := f.right  ≫ g.right
    middle := f.middle ≫ g.middle
  }

section
  variable (L) (R)

  @[simps]
  def projLeft : LaxPullback L R ⥤ A where
    obj X := X.left
    map f := f.left

  @[simps]
  def projRight : LaxPullback L R ⥤ B where
    obj X := X.right
    map f := f.right

  @[simps]
  def projMid : LaxPullback L R ⥤ C where
    obj X := X.middle
    map f := f.middle

  def llm : NatTrans (projLeft L R ⋙ L) (projMid L R) where
    app := homl

  def rrm : NatTrans (projRight L R ⋙ R) (projMid L R) where
    app := homr
end

section
  variable {P₁ P₂ : LaxPullback L R}
  variable (f : P₁ ⟶ P₂)

  instance [IsIso f] : IsIso f.left   := (projLeft   L R).map_isIso f
  instance [IsIso f] : IsIso f.right  := (projRight  L R).map_isIso f
  instance [IsIso f] : IsIso f.middle := (projMid L R).map_isIso f
end
