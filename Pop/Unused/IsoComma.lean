import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Iso

import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.FullSubcategory

namespace CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

structure IsoComma where
  left  : A
  right : B
  iso   : L.obj left ≅ R.obj right

variable {L} {R}

namespace IsoComma
  @[ext]
  structure Hom (x y : IsoComma L R) where
    left  : x.left  ⟶ y.left
    right : x.right ⟶ y.right
    whom : L.map left  ≫ y.iso.hom = x.iso.hom ≫ R.map right := by aesop_cat
    winv : R.map right ≫ y.iso.inv = x.iso.inv ≫ L.map left  := by aesop_cat

  instance Hom.inhabited
    [Inhabited (IsoComma L R)]
    : Inhabited (IsoComma.Hom (default : IsoComma L R) default)
    := ⟨{ left := 𝟙 _, right := 𝟙 _}⟩

  attribute [reassoc (attr := simp)] Hom.whom
  attribute [reassoc (attr := simp)] Hom.winv

  @[simps]
  instance category : Category (IsoComma L R) where
    Hom := Hom
    id X := {
      left  := 𝟙 X.left
      right := 𝟙 X.right
    }
    comp f g := {
      left  := f.left  ≫ g.left
      right := f.right ≫ g.right
    }

  section
    variable (L) (R)

    @[simps]
    def leftFunctor : IsoComma L R ⥤ A where
      obj x := x.left
      map f := f.left

    @[simps]
    def rightFunctor : IsoComma L R ⥤ B where
      obj x := x.right
      map f := f.right

    @[simps!]
    def natIso : (leftFunctor L R ⋙ L) ≅ (rightFunctor L R ⋙ R) where
      hom := {app o := o.iso.hom}
      inv := {app o := o.iso.inv}
  end

  @[simps]
  def lift
    (da : D ⥤ A)
    (db : D ⥤ B)
    (p : (da ⋙ L) ≅ (db ⋙ R))
    : D ⥤ IsoComma L R
  where
    obj d := {
      left   := da.obj d
      right  := db.obj d
      iso    := p.app d
    }
    map f := {
      left  := da.map f
      right := db.map f
      whom  := p.hom.naturality _
      winv  := p.inv.naturality _
    }

  @[simps]
  def flip : IsoComma L R ⥤ IsoComma R L where
    obj o := {
      left   := o.right
      right  := o.left
      iso    := o.iso.symm
    }
    map f := {
      left   := f.right
      right  := f.left
    }

  @[simps]
  def rightComma : IsoComma L R ⥤ Comma L R where
    obj o := {
      left  := o.left
      right := o.right
      hom   := o.iso.hom
    }
    map f := {
      left  := f.left
      right := f.right
      w     := f.whom
    }

  @[simps]
  def leftComma : IsoComma L R ⥤ Comma R L where
    obj o := {
      left  := o.right
      right := o.left
      hom   := o.iso.inv
    }
    map f := {
      left  := f.right
      right := f.left
      w     := f.winv
    }

  def flip_invol : flip ⋙ flip ≅ 𝟭 (IsoComma L R) where
    hom := 𝟙 _
    inv := 𝟙 _

  def flip_equiv : IsoComma L R ≌ IsoComma R L
    := .mk flip flip flip_invol.symm flip_invol

  section
    variable {x y z : IsoComma L R}
    variable (i : x ≅ y)
    variable (h : x ⟶ y)

    instance [IsIso h] : IsIso h.left  := (leftFunctor  L R).map_isIso h
    instance [IsIso h] : IsIso h.right := (rightFunctor L R).map_isIso h

    @[simps!] def leftIso  : x.left  ≅ y.left  := (leftFunctor  L R).mapIso i
    @[simps!] def rightIso : x.right ≅ y.right := (rightFunctor L R).mapIso i

    @[simp]
    lemma inv_left [IsIso h] : (inv h).left = inv h.left := by
      apply IsIso.eq_inv_of_hom_inv_id
      rw [← category_comp_left, IsIso.hom_inv_id, category_id_left]

    @[simp]
    lemma inv_right [IsIso h] : (inv h).right = inv h.right := by
      apply IsIso.eq_inv_of_hom_inv_id
      rw [← category_comp_right, IsIso.hom_inv_id, category_id_right]

    def flip_leftComma  : flip ⋙ leftComma  = rightComma (L := L) (R := R) := rfl
    def flip_rightComma : flip ⋙ rightComma = leftComma  (L := L) (R := R) := rfl
  end
end IsoComma

section
  open IsoComma

  variable (L R)

  def IsoCommaSet : Set (Comma L R) := fun p => IsIso p.hom

  noncomputable def IsoCommaSet.flip : FullSubcategory (IsoCommaSet L R) ⥤ FullSubcategory (IsoCommaSet R L) where
    obj o := {
      obj := {
        left  := o.obj.right
        right := o.obj.left
        hom := inv o.obj.hom (I := o.property)
      }
      property := let _ : IsIso o.obj.hom := o.property ; IsIso.inv_isIso
    }
    map f := {
      left := f.right
      right := f.left
      w := by rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp,f.w]
    }

  noncomputable def IsoCommaSet.natIso : (fullSubcategoryInclusion (IsoCommaSet L R) ⋙ Comma.fst L R) ⋙ L ≅ (fullSubcategoryInclusion (IsoCommaSet L R) ⋙ Comma.snd L R) ⋙ R where
    hom := whiskerLeft (fullSubcategoryInclusion (IsoCommaSet L R)) (Comma.natTrans L R)
    inv := {
      app o := inv o.obj.hom (I := o.property)
      naturality x y f := by
        let _ : IsIso y.obj.hom := y.property
        apply (IsIso.comp_inv_eq y.obj.hom).mpr
        aesop
    }

  def to_isoCommaSet : IsoComma L R ⥤ FullSubcategory (IsoCommaSet L R)
    := FullSubcategory.lift (IsoCommaSet L R) rightComma (fun o => Iso.isIso_hom o.iso)

  noncomputable def from_isoCommaSet : FullSubcategory (IsoCommaSet L R) ⥤ IsoComma L R
    := lift
      (fullSubcategoryInclusion _ ⋙ Comma.fst _ _)
      (fullSubcategoryInclusion _ ⋙ Comma.snd _ _)
      (IsoCommaSet.natIso _ _)

  noncomputable def isoComma_set : IsoComma L R ≌ FullSubcategory (IsoCommaSet L R) where
    functor := to_isoCommaSet L R
    inverse := from_isoCommaSet L R
    counitIso := by aesop
    unitIso := by
      dsimp only [from_isoCommaSet,to_isoCommaSet,IsoCommaSet.natIso]
      exact {
        hom := {
          app o := {left := 𝟙 _ , right := 𝟙 _}
          naturality _ _ _ := by
            apply Hom.ext
            . simp only [lift_obj_left ,Functor.comp_map,FullSubcategory.lift_map,category_comp_left ,lift_map_left ,fullSubcategoryInclusion.map,Comma.fst_map,rightComma_map_left ,Category.comp_id,Functor.id_map,Category.id_comp]
            . simp only [lift_obj_right,Functor.comp_map,FullSubcategory.lift_map,category_comp_right,lift_map_right,fullSubcategoryInclusion.map,Comma.snd_map,rightComma_map_right,Category.comp_id,Functor.id_map,Category.id_comp]
        }
        inv := {
          app o := {left := 𝟙 _ , right := 𝟙 _}
          naturality _ _ _ := by
            apply Hom.ext
            . simp only [lift_obj_left ,Functor.comp_map,FullSubcategory.lift_map,category_comp_left ,lift_map_left ,fullSubcategoryInclusion.map,Comma.fst_map,rightComma_map_left ,Category.comp_id,Functor.id_map,Category.id_comp]
            . simp only [lift_obj_right,Functor.comp_map,FullSubcategory.lift_map,category_comp_right,lift_map_right,fullSubcategoryInclusion.map,Comma.snd_map,rightComma_map_right,Category.comp_id,Functor.id_map,Category.id_comp]
        }
        hom_inv_id := by
          ext
          apply Hom.ext
          . simp only [NatTrans.comp_app,Category.comp_id,NatTrans.id_app,category_comp_left,category_id_left]
          . simp only [NatTrans.comp_app,Category.comp_id,NatTrans.id_app,category_comp_right,category_id_right]
        inv_hom_id := by
          ext
          apply Hom.ext
          . simp only [NatTrans.comp_app,Category.comp_id,NatTrans.id_app,category_comp_left,category_id_left]
          . simp only [NatTrans.comp_app,Category.comp_id,NatTrans.id_app,category_comp_right,category_id_right]
      }
end
