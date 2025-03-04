import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.CategoryTheory.Reassoc

namespace CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]

structure OplaxPullbackThing (L : A ⥤ C) (R : B ⥤ C) where
  left : A
  right : B
  middle : C
  homl : middle ⟶ L.obj left
  homr : middle ⟶ R.obj right

variable {L : A ⥤ C}
variable {R : B ⥤ C}

@[ext]
structure OplaxPullbackThing.Hom (X Y : OplaxPullbackThing L R) where
  left   : X.left   ⟶ Y.left
  right  : X.right  ⟶ Y.right
  middle : X.middle ⟶ Y.middle
  wl : X.homl ≫ L.map left = middle ≫ Y.homl := by aesop_cat
  wr : X.homr ≫ R.map right = middle ≫ Y.homr := by aesop_cat

attribute [reassoc (attr := simp)] OplaxPullbackThing.Hom.wl OplaxPullbackThing.Hom.wr

instance OplaxPullbackThing.category : Category (OplaxPullbackThing L R) where
  Hom X Y := OplaxPullbackThing.Hom X Y
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

variable (L) (R)

@[simps]
def leftFunctor : OplaxPullbackThing L R ⥤ A where
  obj X := X.left
  map f := f.left

@[simps]
def rightFunctor : OplaxPullbackThing L R ⥤ B where
  obj X := X.right
  map f := f.right

@[simps]
def middleFunctor : OplaxPullbackThing L R ⥤ C where
  obj X := X.middle
  map f := f.middle

def llm : NatTrans (middleFunctor L R) (leftFunctor L R ⋙ L) where
  app := OplaxPullbackThing.homl

def rrm : NatTrans (middleFunctor L R) (rightFunctor L R ⋙ R) where
  app := OplaxPullbackThing.homr
