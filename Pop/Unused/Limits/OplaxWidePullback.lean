import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Pop.Unused.OplaxWidePullback

namespace CategoryTheory.OplaxWidePullback

open CategoryTheory.Limits

universe s s'
variable {J : Type _}
variable {I : Option J → Cat}
variable {F : ∀j, I (some j) ⟶ I none}
variable {D : Type _} [Category D]
variable (G : D ⥤ OplaxWidePullback I F)

@[simps!]
def coconePrecompose
  {j : J}
  (c : Cocone (G ⋙ functor F (some j)))
  : Cocone (G ⋙ functor F none)
  := (Cocones.precompose (whiskerLeft G (OplaxWidePullback.natTrans F j))).obj ((F j).mapCocone c)

@[simps]
def cocone
  (cf : ∀j, Cocone (G ⋙ functor F j)) (tm : IsColimit (cf none))
  : Cocone G
  where
  pt := {
    obj j := (cf j).pt
    hom j := tm.desc (coconePrecompose _ (cf j))
  }
  ι := {
    app d := {obj j := (cf j).ι.app d}
    naturality _ _ t := by
      ext j
      simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id]
      exact (cf j).w t
  }

@[simps]
def isColimit
  {cf : ∀j, Cocone (G ⋙ functor F j)} (tf : ∀j, IsColimit (cf j))
  : IsColimit (cocone G cf (tf none))
  where
  desc s := {
    obj j := (tf j).desc ((functor F j).mapCocone s)
    w j := (tf none).hom_ext fun d => by
      rewrite [
        cocone_pt_hom,(tf none).fac_assoc,coconePrecompose_ι_app,Category.assoc,← (F j).map_comp,(tf j).fac,(functor F j).mapCocone_ι_app,functor_map,
        (tf none).fac_assoc,(functor F none).mapCocone_ι_app,functor_map
      ]
      exact (s.ι.app d).w j
  }
  uniq s m w := by
    ext j
    exact (tf j).uniq ((functor F j).mapCocone s) _ (fun d => by exact congr_arg (fun o => o.obj j) (w d))

instance hasColimit
  [h : ∀j, HasColimit (G ⋙ functor F j)]
  : HasColimit G
  := HasColimit.mk ⟨_,isColimit _ (fun _ => colimit.isColimit _)⟩

instance hasColimitsOfShape
  [h : ∀j, HasColimitsOfShape D (I j)]
  : HasColimitsOfShape D (OplaxWidePullback I F)
  where

instance hasColimitsOfSize
  [h : ∀j, HasColimitsOfSize.{s,s'} (I j).α]
  : HasColimitsOfSize.{s,s'} (OplaxWidePullback I F)
  := ⟨fun _ _ => inferInstance⟩
