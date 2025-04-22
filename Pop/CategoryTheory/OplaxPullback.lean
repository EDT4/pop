import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.CategoryTheory.Reassoc

namespace CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

structure OplaxPullback where
  left   : A
  middle : C
  right  : B
  homl : middle ⟶ L.obj left
  homr : middle ⟶ R.obj right

variable {L} {R}

namespace OplaxPullback

@[ext]
structure Hom (x y : OplaxPullback L R) where
  left   : x.left   ⟶ y.left
  middle : x.middle ⟶ y.middle
  right  : x.right  ⟶ y.right
  wl : x.homl ≫ L.map left  = middle ≫ y.homl := by aesop_cat
  wr : x.homr ≫ R.map right = middle ≫ y.homr := by aesop_cat

instance Hom.inhabited
  [Inhabited (OplaxPullback L R)]
  : Inhabited (OplaxPullback.Hom (default : OplaxPullback L R) default)
  := ⟨{ left := 𝟙 _, right := 𝟙 _, middle := 𝟙 _}⟩

attribute [reassoc (attr := simp)] OplaxPullback.Hom.wl OplaxPullback.Hom.wr

@[simps]
abbrev Hom.id (x : OplaxPullback L R) : Hom x x := {
  left   := 𝟙 x.left
  middle := 𝟙 x.middle
  right  := 𝟙 x.right
}

@[simps]
abbrev Hom.comp {x y z : OplaxPullback L R} (f : Hom x y) (g : Hom y z) : Hom x z := {
  left   := f.left   ≫ g.left
  middle := f.middle ≫ g.middle
  right  := f.right  ≫ g.right
}

@[simps]
instance category : Category (OplaxPullback L R) where
  Hom  := Hom
  id   := Hom.id
  comp := Hom.comp

section
  variable (L) (R)

  @[simps]
  def projLeft : OplaxPullback L R ⥤ A where
    obj x := x.left
    map f := f.left

  @[simps]
  def projMid : OplaxPullback L R ⥤ C where
    obj x := x.middle
    map f := f.middle

  @[simps]
  def projRight : OplaxPullback L R ⥤ B where
    obj x := x.right
    map f := f.right

  @[simps]
  def llm : NatTrans (projMid L R) (projLeft L R ⋙ L) where
    app := homl

  @[simps]
  def rrm : NatTrans (projMid L R) (projRight L R ⋙ R) where
    app := homr
end

@[simps]
def lift
  (da : D ⥤ A)
  (db : D ⥤ B)
  (dc : D ⥤ C)
  (pl : NatTrans dc (da ⋙ L))
  (pr : NatTrans dc (db ⋙ R))
  : D ⥤ OplaxPullback L R
where
  obj d := {
    left   := da.obj d
    middle := dc.obj d
    right  := db.obj d
    homl   := pl.app d
    homr   := pr.app d
  }
  map f := {
    left   := da.map f
    middle := dc.map f
    right  := db.map f
  }

abbrev liftL (da : D ⥤ A) (db : D ⥤ B) (p : NatTrans (da ⋙ L) (db ⋙ R)) : D ⥤ OplaxPullback L R
  := lift da db (da ⋙ L) (NatTrans.id _) p

abbrev liftR (da : D ⥤ A) (db : D ⥤ B) (p : NatTrans (db ⋙ R) (da ⋙ L)) : D ⥤ OplaxPullback L R
  := lift da db (db ⋙ R) p (NatTrans.id _)

-- Alternative definition: lift (projRight _ _) (projLeft _ _) (projMid _ _) (rrm _ _) (llm _ _)
@[simps]
def flip : OplaxPullback L R ⥤ OplaxPullback R L where
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
  variable {P₁ P₂ : OplaxPullback L R}
  variable (f : P₁ ⟶ P₂)

  instance [IsIso f] : IsIso f.left   := (projLeft   L R).map_isIso f
  instance [IsIso f] : IsIso f.middle := (projMid L R).map_isIso f
  instance [IsIso f] : IsIso f.right  := (projRight  L R).map_isIso f
end

variable {x y z: OplaxPullback L R}
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
  @[simps!] def leftIso   : x.left   ≅ y.left   := (projLeft   L R).mapIso i
  @[simps!] def middleIso : x.middle ≅ y.middle := (projMid L R).mapIso i
  @[simps!] def rightIso  : x.right  ≅ y.right  := (projRight  L R).mapIso i
end

def flip_obj_invol {x : OplaxPullback L R} : flip.obj (flip.obj x) = x := rfl

def flip_invol : flip ⋙ flip ≅ 𝟭 (OplaxPullback L R) where
  hom := 𝟙 _
  inv := 𝟙 _

-- TODO: The strict variant also holds, but is it necessary?
-- def flip_iso : Cat.of (OplaxPullback L R) ≅ Cat.of (OplaxPullback R L) where
--   hom := flip
--   inv := flip

def flip_equiv : OplaxPullback L R ≌ OplaxPullback R L
  := .mk flip flip flip_invol.symm flip_invol

@[simp]
lemma inv_left [IsIso h] : (inv h).left = inv h.left := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← category_comp_left, IsIso.hom_inv_id, category_id_left]

@[simp]
lemma inv_middle [IsIso h] : (inv h).middle = inv h.middle := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← category_comp_middle, IsIso.hom_inv_id, category_id_middle]

@[simp]
lemma inv_right [IsIso h] : (inv h).right = inv h.right := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← category_comp_right, IsIso.hom_inv_id, category_id_right]

@[simps]
def isoMk
  {x y : OplaxPullback L R}
  (l : x.left   ≅ y.left)
  (m : x.middle ≅ y.middle)
  (r : x.right  ≅ y.right)
  (hl : x.homl ≫ L.map l.hom = m.hom ≫ y.homl := by aesop_cat)
  (hr : x.homr ≫ R.map r.hom = m.hom ≫ y.homr := by aesop_cat)
  : x ≅ y
where
  hom := {
    left := l.hom
    middle := m.hom
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
