import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

universe u v

variable {A : Type u} [Category.{v} A]
variable {B : Type u} [Category.{v} B]
variable {C : Type u} [Category.{v} C]

structure Stuff (L : A ⥤ C) (R : B ⥤ C) where
  left : A
  right : B
  middle : C
  homl : L.obj left ⟶ middle
  homr : R.obj right ⟶ middle

variable {L : A ⥤ C}
variable {R : B ⥤ C}

@[ext]
structure Stuff.Hom (X Y : Stuff L R) where
  left   : X.left   ⟶ Y.left
  right  : X.right  ⟶ Y.right
  middle : X.middle ⟶ Y.middle
  wl : L.map left  ≫ Y.homl = X.homl ≫ middle := by aesop_cat
  wr : R.map right ≫ Y.homr = X.homr ≫ middle := by aesop_cat

instance Stuff.category : Category (Stuff L R) where
  Hom X Y := Stuff.Hom X Y
  id X := {
    left   := 𝟙 X.left
    right  := 𝟙 X.right
    middle := 𝟙 X.middle
  }
  comp f g := {
    left   := f.left   ≫ g.left
    right  := f.right  ≫ g.right
    middle := f.middle ≫ g.middle
    wl := by simp ; rw [g.wl,←Category.assoc,f.wl,Category.assoc]
    wr := by simp ; rw [g.wr,←Category.assoc,f.wr,Category.assoc]
  }

variable (L) (R)

@[simps]
def leftFunctor : Stuff L R ⥤ A where
  obj X := X.left
  map f := f.left

@[simps]
def rightFunctor : Stuff L R ⥤ B where
  obj X := X.right
  map f := f.right

@[simps]
def middleFunctor : Stuff L R ⥤ C where
  obj X := X.middle
  map f := f.middle
