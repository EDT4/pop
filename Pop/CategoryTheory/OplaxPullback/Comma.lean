import Mathlib.CategoryTheory.Comma.Basic
import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

@[simps!]
def from_comma : Comma L R ⥤ OplaxPullback L R
  := liftL (Comma.fst L R) (Comma.snd L R) (Comma.natTrans L R)

@[simps!]
def from_flipped_comma : Comma R L ⥤ OplaxPullback L R
  := liftR (Comma.snd R L) (Comma.fst R L) (Comma.natTrans R L)

-- Partially-oplax pullback (on the left).
def CommaLeft : Set (OplaxPullback L R) := fun p => IsIso p.homl

namespace CommaLeft
  def from_comma : Comma L R ⥤ FullSubcategory (CommaLeft L R)
    := FullSubcategory.lift
      (CommaLeft L R)
      (OplaxPullback.from_comma L R)
      (by simp [OplaxPullback.from_comma,CommaLeft] ; infer_instance)

  noncomputable def to_comma : FullSubcategory (CommaLeft L R) ⥤ Comma L R where
    obj p := {
      left := p.obj.left
      right := p.obj.right
      hom := inv _ (I := p.property) ≫ p.obj.homr
    }
    map f := {
      left := f.left
      right := f.right
    }

  -- TODO: No timeout, but takes a lot of time? There should be a better way
  noncomputable def from_to_inverse : from_comma L R ⋙ to_comma L R ≅ 𝟭 (Comma L R) := NatIso.ofComponents
    (fun _ => {
      hom := {left := 𝟙 _ , right := 𝟙 _ , w := by simp only [from_comma,to_comma,OplaxPullback.from_comma] ; simp only [Functor.comp_obj,FullSubcategory.lift_obj_obj,lift_obj_left,lift_obj_middle,lift_obj_homl,NatTrans.id_app',lift_obj_homr,Comma.natTrans_app,Functor.id_obj,Functor.map_id,IsIso.inv_id,Category.comp_id]}
      inv := {left := 𝟙 _ , right := 𝟙 _ , w := by simp only [from_comma,to_comma,OplaxPullback.from_comma] ; simp only [Functor.id_obj,Functor.comp_obj,FullSubcategory.lift_obj_obj,lift_obj_left,lift_obj_middle,lift_obj_homl,NatTrans.id_app',lift_obj_homr,Comma.natTrans_app,Functor.map_id,IsIso.inv_id,Category.id_comp,Category.comp_id]}
    })
    (fun _ => by
      ext
      · simp only [Comma.comp_left ,Category.comp_id,Category.id_comp] ; rfl
      · simp only [Comma.comp_right,Category.comp_id,Category.id_comp] ; rfl
    )

  noncomputable def to_from_inverse : to_comma L R ⋙ from_comma L R ≅ 𝟭 _ := NatIso.ofComponents
    (fun x => {
      hom := {
        left   := 𝟙 _
        middle := inv x.obj.homl (I := x.property)
        right  := 𝟙 _
        wl := by
          simp only [from_comma,to_comma,OplaxPullback.from_comma]
          simp only [Functor.comp_obj,FullSubcategory.lift_obj_obj,lift_obj_middle,Functor.id_obj,lift_obj_homl,NatTrans.id_app',Functor.map_id,Category.comp_id,IsIso.inv_hom_id]
        wr := by
          simp only [from_comma,to_comma,OplaxPullback.from_comma]
          simp only [Functor.comp_obj,FullSubcategory.lift_obj_obj,lift_obj_middle,Functor.id_obj,lift_obj_homr,Comma.natTrans_app,Functor.map_id,Category.comp_id]
      }
      inv := {
        left   := 𝟙 _
        middle := x.obj.homl
        right  := 𝟙 _
        wl := by simp only [from_comma,to_comma,OplaxPullback.from_comma] ; aesop
        wr := by simp only [from_comma,to_comma,OplaxPullback.from_comma] ; aesop
      }
      hom_inv_id := Hom.ext
        (by apply (Eq.trans (OplaxPullback.category_comp_left   _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_left])
        (by apply (Eq.trans (OplaxPullback.category_comp_middle _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_middle,IsIso.inv_hom_id])
        (by apply (Eq.trans (OplaxPullback.category_comp_right  _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_right])
      inv_hom_id := Hom.ext
        (by apply (Eq.trans (OplaxPullback.category_comp_left   _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_left])
        (by apply (Eq.trans (OplaxPullback.category_comp_middle _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_middle,IsIso.hom_inv_id])
        (by apply (Eq.trans (OplaxPullback.category_comp_right  _ _) ·) ; simp only [Category.comp_id,FullSubcategory.id_def,category_id_right])
    })
    (fun f => Hom.ext
      (by
        simp only [from_comma,to_comma,OplaxPullback.from_comma,FullSubcategory.lift,Comma.fst,lift]
        simp only [Functor.comp_map,Functor.id_map,(·≫·)]
        simp only [Category.comp_id,Category.id_comp]
      )
      (by
        simp only [from_comma,to_comma,OplaxPullback.from_comma,FullSubcategory.lift,Comma.fst,lift]
        simp only [Functor.comp_map,Functor.id_map,(·≫·)]
        rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp,f.wl]
      )
      (by
        simp only [from_comma,to_comma,OplaxPullback.from_comma,FullSubcategory.lift,Comma.snd,lift]
        simp only [Functor.comp_map,Functor.id_map,(·≫·)]
        simp only [Category.comp_id,Category.id_comp]
      )
    )

  noncomputable def equiv_comma : FullSubcategory (CommaLeft L R) ≌ Comma L R
    := Equivalence.mk
      (to_comma L R)
      (from_comma L R)
      (to_from_inverse L R).symm
      (from_to_inverse L R)

end CommaLeft

-- Partially-oplax pullback (on the right).
def CommaRight : Set (OplaxPullback L R) := fun p => IsIso p.homr

namespace CommaRight
  def from_comma : Comma R L ⥤ FullSubcategory (CommaRight L R)
    := FullSubcategory.lift
      (CommaRight L R)
      (OplaxPullback.from_flipped_comma L R)
      (by simp [OplaxPullback.from_flipped_comma,CommaRight] ; infer_instance)

  noncomputable def to_comma : FullSubcategory (CommaRight L R) ⥤ Comma R L where
    obj p := {
      left := p.obj.right
      right := p.obj.left
      hom := inv _ (I := p.property) ≫ p.obj.homl
    }
    map f := {
      left := f.right
      right := f.left
    }

  noncomputable def from_to_inverse : from_comma L R ⋙ to_comma L R ≅ 𝟭 (Comma R L) := by
    simp only [from_comma,to_comma,OplaxPullback.from_flipped_comma]
    exact {
      hom := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
      inv := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
    }

  noncomputable def to_from_inverse : to_comma L R ⋙ from_comma L R ≅ 𝟭 _ := sorry

  noncomputable def equiv_comma : FullSubcategory (CommaRight L R) ≌ Comma R L
    := Equivalence.mk
      (to_comma L R)
      (from_comma L R)
      (to_from_inverse L R).symm
      (from_to_inverse L R)

end CommaRight
