import Mathlib.CategoryTheory.Category.Cat

namespace CategoryTheory

variable {D : Cat}
variable {J : Type _}
variable (I : Option J → Cat)
variable (F : ∀j, I (some j) ⟶ I none)

-- TODO: Whil this is a rewrite of OplaxPullback using a shape of `Option J` similar to WidePullback which can lessen duplicated proofs, the universes result in a less general definition. ULift exists though.
structure OplaxWidePullback where
  obj : ∀j, (I j).α
  hom : ∀j, obj none ⟶ (F j).obj (obj (some j))

variable {I}
variable {F}

namespace OplaxWidePullback

@[ext]
structure Hom (x y : OplaxWidePullback I F) where
  obj : ∀j, x.obj j ⟶ y.obj j
  w : ∀j, x.hom j ≫ (F j).map (obj (some j)) = obj none ≫ y.hom j := by aesop_cat

instance Hom.inhabited
  [Inhabited (OplaxWidePullback I F)]
  : Inhabited (OplaxWidePullback.Hom (default : OplaxWidePullback I F) default)
  := ⟨{ obj _ := 𝟙 _}⟩

attribute [reassoc (attr := simp)] OplaxWidePullback.Hom.w

@[simps]
abbrev Hom.id (x : OplaxWidePullback I F) : Hom x x where
  obj j := 𝟙 (x.obj j)

@[simps]
abbrev Hom.comp {x y z : OplaxWidePullback I F} (f : Hom x y) (g : Hom y z) : Hom x z where
  obj j := f.obj j ≫ g.obj j

@[simps]
instance category : Category (OplaxWidePullback I F) where
  Hom  := Hom
  id   := Hom.id
  comp := Hom.comp

section
  variable (F)

  @[simps]
  def functor j : Functor (OplaxWidePullback I F) (I j) where
    obj x := x.obj j
    map f := f.obj j

  @[simps]
  def natTrans j : NatTrans (functor F none) ((functor F (some j)).comp (F j)) where
    app o := o.hom j
end

@[simps]
def lift
  (d : ∀j, D ⟶ I j)
  (p : ∀j, d none ⟶ (d (some j) ⋙ F j))
  : D ⥤ OplaxWidePullback I F
where
  obj o := {
    obj j := (d j).obj o
    hom j := (p j).app o
  }
  map f := {
    obj j := (d j).map f
  }

section
  variable {P₁ P₂ : OplaxWidePullback I F}
  variable (f : P₁ ⟶ P₂)

  instance [IsIso f] {j} : IsIso (f.obj j) := (functor F j).map_isIso f
end

variable {x y z: OplaxWidePullback I F}
variable (h : x ⟶ y)
variable (i : x ≅ y)

-- TODO: The purpose of this is some search tactic, but why is this necessary when ext is on the structure already?
@[ext]
lemma hom_ext
  (f g : x ⟶ y)
  (e : f.obj = g.obj)
  : f = g
  := Hom.ext e

@[simps!] def objIso j : x.obj j ≅ y.obj j := (functor F j).mapIso i

@[simp]
lemma inv_obj j [IsIso h] : (inv h).obj j = inv (h.obj j) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← category_comp_obj, IsIso.hom_inv_id, category_id_obj]

@[simps]
def isoMk
  {x y : OplaxWidePullback I F}
  (o : ∀j, x.obj j ≅ y.obj j)
  (h : ∀j, x.hom j ≫ (F j).map (o (some j)).hom = (o none).hom ≫ y.hom j := by aesop_cat)
  : x ≅ y
where
  hom := {
    obj j := (o j).hom
    w := h
  }
  inv := {
    obj j := (o j).inv
    w j := by
      rw [← (F j).mapIso_inv (o j) , Iso.eq_inv_comp , ← Category.assoc , ← h]
      simp only [Functor.mapIso_inv, Category.assoc, Iso.map_hom_inv_id, Category.comp_id]
  }
