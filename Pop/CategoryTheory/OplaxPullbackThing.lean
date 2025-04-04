import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.CategoryTheory.Reassoc

namespace CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]

-- TODO: One could try to rewrite this using a shape of `Option J` similar to WidePullback, lessening duplicated proofs, but the universes would result in a less general definition. ULift exists though.
structure OplaxPullbackThing (L : A ⥤ C) (R : B ⥤ C) where
  left   : A
  middle : C
  right  : B
  homl : middle ⟶ L.obj left
  homr : middle ⟶ R.obj right

variable {L : A ⥤ C}
variable {R : B ⥤ C}

namespace OplaxPullbackThing

@[ext]
structure Hom (x y : OplaxPullbackThing L R) where
  left   : x.left   ⟶ y.left
  middle : x.middle ⟶ y.middle
  right  : x.right  ⟶ y.right
  wl : x.homl ≫ L.map left = middle ≫ y.homl := by aesop_cat
  wr : x.homr ≫ R.map right = middle ≫ y.homr := by aesop_cat

instance Hom.inhabited
  [Inhabited (OplaxPullbackThing L R)]
  : Inhabited (OplaxPullbackThing.Hom (default : OplaxPullbackThing L R) default)
  := ⟨{ left := 𝟙 _, right := 𝟙 _, middle := 𝟙 _}⟩

attribute [reassoc (attr := simp)] OplaxPullbackThing.Hom.wl OplaxPullbackThing.Hom.wr

instance category : Category (OplaxPullbackThing L R) where
  Hom x y := Hom x y
  id x := {
    left   := 𝟙 x.left
    middle := 𝟙 x.middle
    right  := 𝟙 x.right
  }
  comp f g := {
    left   := f.left   ≫ g.left
    middle := f.middle ≫ g.middle
    right  := f.right  ≫ g.right
  }

@[simps]
def flip : OplaxPullbackThing L R ⥤ OplaxPullbackThing R L where
  obj o := {
    left   := o.right
    middle := o.middle
    right  := o.left
    homl   := o.homr
    homr   := o.homl
  }
  map f := {
    left   := f.right
    middle := f.middle
    right  := f.left
  }

section
  variable (L) (R)

  @[simps]
  def leftFunctor : OplaxPullbackThing L R ⥤ A where
    obj x := x.left
    map f := f.left

  @[simps]
  def middleFunctor : OplaxPullbackThing L R ⥤ C where
    obj x := x.middle
    map f := f.middle

  @[simps]
  def rightFunctor : OplaxPullbackThing L R ⥤ B where
    obj x := x.right
    map f := f.right

  @[simps]
  def llm : NatTrans (middleFunctor L R) (leftFunctor L R ⋙ L) where
    app := homl

  @[simps]
  def rrm : NatTrans (middleFunctor L R) (rightFunctor L R ⋙ R) where
    app := homr

  @[simps]
  def liftL
    (da : D ⥤ A)
    (db : D ⥤ B)
    (p : da ⋙ L ⟶ db ⋙ R)
    : D ⥤ OplaxPullbackThing L R
  where
    obj d := {
      left   := da.obj d
      middle := L.obj (da.obj d)
      right  := db.obj d
      homl   := 𝟙 _
      homr   := p.app d
    }
    map f := {
      left   := da.map f
      middle := L.map (da.map f)
      right  := db.map f
      wr := by
        simp only
        rewrite [← Functor.comp_map,← Functor.comp_map]
        exact (p.naturality f).symm
    }

  @[simps]
  def liftR
    (da : D ⥤ A)
    (db : D ⥤ B)
    (p : db ⋙ R ⟶ da ⋙ L)
    : D ⥤ OplaxPullbackThing L R
  where
    obj d := {
      left   := da.obj d
      middle := R.obj (db.obj d)
      right  := db.obj d
      homl   := p.app d
      homr   := 𝟙 _
    }
    map f := {
      left   := da.map f
      middle := R.map (db.map f)
      right  := db.map f
      wl := by
        simp only
        rewrite [← Functor.comp_map,← Functor.comp_map]
        exact (p.naturality f).symm
    }

  @[simps!]
  def byComma : Comma L R ⥤ OplaxPullbackThing L R
    := liftL L R (Comma.fst L R) (Comma.snd L R) (Comma.natTrans L R)

  @[simps!]
  def byFlippedComma : Comma R L ⥤ OplaxPullbackThing L R
    := liftR L R (Comma.snd R L) (Comma.fst R L) (Comma.natTrans R L)
end

section
  variable {P₁ P₂ : OplaxPullbackThing L R}
  variable (f : P₁ ⟶ P₂)

  instance [IsIso f] : IsIso f.left   := (leftFunctor   L R).map_isIso f
  instance [IsIso f] : IsIso f.middle := (middleFunctor L R).map_isIso f
  instance [IsIso f] : IsIso f.right  := (rightFunctor  L R).map_isIso f
end

variable {x y z: OplaxPullbackThing L R}
variable (h : x ⟶ y)
variable (i : x ≅ y)

-- The purpose of this is some search tactic, but why is this necessary when ext is on the structure already?
@[ext]
lemma hom_ext
  (f g : x ⟶ y)
  (el : f.left   = g.left)
  (em : f.middle = g.middle)
  (er : f.right  = g.right)
  : f = g
  := Hom.ext el em er

-- The fields preserve isomorphisms.
section
  @[simps!] def leftIso   : x.left   ≅ y.left   := (leftFunctor   L R).mapIso i
  @[simps!] def middleIso : x.middle ≅ y.middle := (middleFunctor L R).mapIso i
  @[simps!] def rightIso  : x.right  ≅ y.right  := (rightFunctor  L R).mapIso i
end

section
  variable {f : x ⟶ y} {g : y ⟶ z}
  @[simp] theorem comp_left   : (f ≫ g).left   = f.left   ≫ g.left   := rfl
  @[simp] theorem comp_middle : (f ≫ g).middle = f.middle ≫ g.middle := rfl
  @[simp] theorem comp_right  : (f ≫ g).right  = f.right  ≫ g.right  := rfl
  @[simp] theorem id_left   : Hom.left   (𝟙 x) = 𝟙 x.left   := rfl
  @[simp] theorem id_middle : Hom.middle (𝟙 x) = 𝟙 x.middle := rfl
  @[simp] theorem id_right  : Hom.right  (𝟙 x) = 𝟙 x.right  := rfl
end

@[simp]
lemma inv_left [IsIso h] : (inv h).left = inv h.left := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← OplaxPullbackThing.comp_left, IsIso.hom_inv_id, id_left]

@[simp]
lemma inv_middle [IsIso h] : (inv h).middle = inv h.middle := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← OplaxPullbackThing.comp_middle, IsIso.hom_inv_id, id_middle]

@[simp]
lemma inv_right [IsIso h] : (inv h).right = inv h.right := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← OplaxPullbackThing.comp_right, IsIso.hom_inv_id, id_right]

@[simps]
def isoMk
  {x y : OplaxPullbackThing L R}
  (l : x.left   ≅ y.left)
  (m : x.middle ≅ y.middle)
  (r : x.right  ≅ y.right)
  (hl : x.homl ≫ L.map l.hom = m.hom ≫ y.homl := by aesop_cat)
  (hr : x.homr ≫ R.map r.hom = m.hom ≫ y.homr := by aesop_cat)
  : x ≅ y
where
  hom := {
    left := l.hom
    right := r.hom
    wl := hl
    wr := hr
  }
  inv := {
    left   := l.inv
    middle := m.inv
    right  := r.inv
    wl := by
      rw [← L.mapIso_inv l , Iso.eq_inv_comp , ← Category.assoc , ← hl]
      simp only [Functor.mapIso_inv, Category.assoc, Iso.map_hom_inv_id, Category.comp_id]
    wr := by
      rw [← R.mapIso_inv r , Iso.eq_inv_comp , ← Category.assoc , ← hr]
      simp only [Functor.mapIso_inv, Category.assoc, Iso.map_hom_inv_id, Category.comp_id]
    }
