import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory.Limits

universe s s'
variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {J : Type _} [Category J]
variable {L : A ⥤ C}
variable {R : B ⥤ C}
variable (F : J ⥤ OplaxPullback L R)

@[simps!]
def coconePrecompose_llm
  (c : Cocone (F ⋙ projLeft L R))
  : Cocone (F ⋙ projMid L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullback.llm L R))).obj (L.mapCocone c)

@[simps!]
def coconePrecompose_rrm
  (c : Cocone (F ⋙ projRight L R))
  : Cocone (F ⋙ projMid L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullback.rrm L R))).obj (R.mapCocone c)

@[simps]
def cocone
  (cl : Cocone (F ⋙ projLeft  L R))
  {cm : Cocone (F ⋙ projMid   L R)} (tm : IsColimit cm)
  (cr : Cocone (F ⋙ projRight L R))
  : Cocone F
  where
  pt := {
    left   := cl.pt
    middle := cm.pt
    right  := cr.pt
    homl := tm.desc (coconePrecompose_llm _ cl)
    homr := tm.desc (coconePrecompose_rrm _ cr)
  }
  ι := {
    app j := {
      left   := cl.ι.app j
      middle := cm.ι.app j
      right  := cr.ι.app j
    }
    naturality j₁ j₂ t := by
      ext
      . simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id] ; exact cl.w t
      . simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id] ; exact cm.w t
      . simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id] ; exact cr.w t
  }

@[simps]
def isColimit
  {cl : Cocone (F ⋙ projLeft  L R)} (tl : IsColimit cl)
  {cm : Cocone (F ⋙ projMid   L R)} (tm : IsColimit cm)
  {cr : Cocone (F ⋙ projRight L R)} (tr : IsColimit cr)
  : IsColimit (cocone F cl tm cr)
  where
  desc s := {
    left   := tl.desc ((projLeft  L R).mapCocone s)
    middle := tm.desc ((projMid   L R).mapCocone s)
    right  := tr.desc ((projRight L R).mapCocone s)
    wl := tm.hom_ext fun j => by
      rewrite [
        cocone_pt_homl,tm.fac_assoc,coconePrecompose_llm_ι_app,Category.assoc,← L.map_comp,tl.fac,(projLeft L R).mapCocone_ι_app,projLeft_map,
        tm.fac_assoc,(projMid L R).mapCocone_ι_app,projMid_map
      ]
      exact (s.ι.app j).wl
    wr := tm.hom_ext fun j => by
      rewrite [
        cocone_pt_homr,tm.fac_assoc,coconePrecompose_rrm_ι_app,Category.assoc,← R.map_comp,tr.fac,(projRight L R).mapCocone_ι_app,projRight_map,
        tm.fac_assoc,(projMid L R).mapCocone_ι_app,projMid_map
      ]
      exact (s.ι.app j).wr
  }
  uniq s m w := by
    ext
    . exact tl.uniq ((projLeft  L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullback.Hom.left   (w j))
    . exact tm.uniq ((projMid   L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullback.Hom.middle (w j))
    . exact tr.uniq ((projRight L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullback.Hom.right  (w j))

instance hasColimit
  [hl : HasColimit (F ⋙ projLeft  L R)]
  [hm : HasColimit (F ⋙ projMid   L R)]
  [hr : HasColimit (F ⋙ projRight L R)]
  : HasColimit F
  := HasColimit.mk ⟨_,isColimit _ (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)⟩

instance hasColimitsOfShape
  [ha : HasColimitsOfShape J A]
  [hb : HasColimitsOfShape J B]
  [hc : HasColimitsOfShape J C]
  : HasColimitsOfShape J (OplaxPullback L R)
  where

instance hasColimitsOfSize
  [ha : HasColimitsOfSize.{s,s'} A]
  [hb : HasColimitsOfSize.{s,s'} B]
  [hc : HasColimitsOfSize.{s,s'} C]
  : HasColimitsOfSize.{s,s'} (OplaxPullback L R)
  := ⟨fun _ _ => inferInstance⟩
