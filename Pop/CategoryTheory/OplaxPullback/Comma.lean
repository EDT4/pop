import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

-- Partially-oplax pullback (on the left).
def CommaLeft : Set (OplaxPullback L R) := fun p => IsIso p.homl

-- Partially-oplax pullback (on the right).
def CommaRight : Set (OplaxPullback L R) := fun p => IsIso p.homr

def CommaLeft.from_comma : Comma L R ⥤ FullSubcategory (CommaLeft L R)
  := FullSubcategory.lift
    (CommaLeft L R)
    (OplaxPullback.byComma L R)
    (by simp [OplaxPullback.byComma,OplaxPullback.CommaLeft] ; infer_instance)

def CommaRight.from_comma : Comma R L ⥤ FullSubcategory (CommaRight L R)
  := FullSubcategory.lift
    (CommaRight L R)
    (OplaxPullback.byFlippedComma L R)
    (by simp [OplaxPullback.byFlippedComma,OplaxPullback.CommaRight] ; infer_instance)

noncomputable def CommaLeft.to_comma : FullSubcategory (CommaLeft L R) ⥤ Comma L R where
  obj p := {
    left := p.obj.left
    right := p.obj.right
    hom := inv _ (I := p.property) ≫ p.obj.homr
  }
  map f := {
    left := f.left
    right := f.right
  }

noncomputable def CommaRight.to_comma : FullSubcategory (CommaRight L R) ⥤ Comma R L where
  obj p := {
    left := p.obj.right
    right := p.obj.left
    hom := inv _ (I := p.property) ≫ p.obj.homl
  }
  map f := {
    left := f.right
    right := f.left
  }

  -- TODO: No timeout, but takes a lot of time? There should be a better way
  -- noncomputable def comma_pl_inverse : comma_pl F G ⋙ pl_comma F G ≅ 𝟭 (Comma F G) := by
  --   simp only [comma_pl,pl_comma,OplaxPullback.byComma]
  --   exact {
  --     hom := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --     inv := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --   }

  -- noncomputable def comma_pr_inverse : comma_pr F G ⋙ pr_comma F G ≅ 𝟭 (Comma G F) := by
  --   simp only [comma_pr,pr_comma,OplaxPullback.byFlippedComma]
  --   exact {
  --     hom := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --     inv := {app _ := {left := 𝟙 _ , right := 𝟙 _}}
  --   }

  -- TODO: Timeout?
  -- noncomputable def pl_comma_inverse : pl_comma F G ⋙ comma_pl F G ≅ 𝟭 _ where
  --   hom := {
  --     app x := {
  --       left := 𝟙 _
  --       middle := inv x.obj.homl (I := x.property)
  --       right := 𝟙 _
  --       wr := by simp only [pl_comma,comma_pl,OplaxPullback.byComma,OplaxPullback.liftL,Comma.natTrans_app,FullSubcategory.lift,Functor.comp_obj,Functor.id_obj,CategoryTheory.Functor.map_id,Category.comp_id]
  --     }
  --     naturality x y f := by
  --       apply OplaxPullback.Hom.ext
  --       . apply (Eq.trans OplaxPullback.comp_left ·)
  --         apply (Eq.trans · OplaxPullback.comp_left)
  --         simp only [OplaxPullback.category,pl_comma,comma_pl,OplaxPullback.byComma,OplaxPullback.liftL,Comma.fst_map,FullSubcategory.lift,Functor.id_obj,Functor.comp_map,Category.comp_id,Functor.id_map,Category.id_comp]
  --       . apply (Eq.trans OplaxPullback.comp_middle ·)
  --         apply (Eq.trans · OplaxPullback.comp_middle)
  --         simp only [pl_comma,comma_pl,Functor.comp_obj,Functor.comp_map,FullSubcategory.lift_map,OplaxPullback.byComma_map_middle,Functor.id_map,OplaxPullback.comp_middle,IsIso.eq_inv_comp,OplaxPullback.Hom.wl_assoc,IsIso.hom_inv_id,Category.comp_id]
  --       . apply (Eq.trans OplaxPullback.comp_right ·)
  --         apply (Eq.trans · OplaxPullback.comp_right)
  --         simp only [OplaxPullback.category,pl_comma,comma_pl,OplaxPullback.byComma,OplaxPullback.liftL,Comma.snd_map, FullSubcategory.lift,Functor.id_obj,Functor.comp_map,Category.comp_id,Functor.id_map,Category.id_comp]
  --   }
  --   inv := {
  --     app x := {
  --       left := 𝟙 _
  --       middle := x.obj.homl
  --       right := 𝟙 _
  --       wl := by simp only [Functor.id_obj,pl_comma,comma_pl,OplaxPullback.byComma,OplaxPullback.liftL,Comma.natTrans_app,Functor.comp_obj,FullSubcategory.lift_obj_obj,CategoryTheory.Functor.map_id,Category.comp_id]
  --       wr := by
  --         simp [pl_comma,comma_pl,OplaxPullback.byComma,OplaxPullback.liftL]
  --         sorry
  --     }
  --     naturality := sorry
  --   }
