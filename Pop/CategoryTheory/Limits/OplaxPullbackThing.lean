import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Pop.CategoryTheory.OplaxPullbackThing

namespace CategoryTheory.OplaxPullbackThing

open CategoryTheory.Limits

universe s s'
variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {J : Type _} [Category J]
variable {L : A ⥤ C}
variable {R : B ⥤ C}
variable (F : J ⥤ OplaxPullbackThing L R)

-- instance hasLimit
--   (F : J ⥤ OplaxPullbackThing L R)
--   [HasLimit (F ⋙ leftFunctor   L R)]
--   [HasLimit (F ⋙ middleFunctor L R)]
--   [HasLimit (F ⋙ rightFunctor  L R)]
--   [PreservesLimit (F ⋙ rightFunctor L R) R]
--   : HasLimit F
--   := sorry
--
-- instance hasLimitsOfShape
--   [HasLimitsOfShape J A]
--   [HasLimitsOfShape J B]
--   [PreservesLimitsOfShape J L]
--   : HasLimitsOfShape J (OplaxPullbackThing L R)
--   where
--
-- instance hasLimitsOfSize
--   [HasLimitsOfSize.{s,s'} A]
--   [HasLimitsOfSize.{s,s'} B]
--   [PreservesLimitsOfSize.{s,s'} R]
--   : HasLimitsOfSize.{s,s'} (OplaxPullbackThing L R)
--   := fun _ _ => inferInstance

@[simps!]
def coconePrecompose_llm
  (c : Cocone (F ⋙ leftFunctor L R))
  : Cocone (F ⋙ middleFunctor L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullbackThing.llm L R))).obj (L.mapCocone c)

@[simps!]
def coconePrecompose_rrm
  (c : Cocone (F ⋙ rightFunctor L R))
  : Cocone (F ⋙ middleFunctor L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullbackThing.rrm L R))).obj (R.mapCocone c)

@[simps]
def cocone
  (cl : Cocone (F ⋙ leftFunctor   L R))
  {cm : Cocone (F ⋙ middleFunctor L R)} (tm : IsColimit cm)
  (cr : Cocone (F ⋙ rightFunctor  L R))
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
  {cl : Cocone (F ⋙ leftFunctor   L R)} (tl : IsColimit cl)
  {cm : Cocone (F ⋙ middleFunctor L R)} (tm : IsColimit cm)
  {cr : Cocone (F ⋙ rightFunctor  L R)} (tr : IsColimit cr)
  : IsColimit (cocone F cl tm cr)
  where
  desc s := {
    left   := tl.desc ((leftFunctor   L R).mapCocone s)
    middle := tm.desc ((middleFunctor L R).mapCocone s)
    right  := tr.desc ((rightFunctor  L R).mapCocone s)
    wl := tm.hom_ext fun j => by
      -- LHS
      rewrite [cocone_pt_homl,tm.fac_assoc,coconePrecompose_llm_ι_app,Category.assoc,← L.map_comp,tl.fac]
      simp only [llm]
      rewrite [(leftFunctor L R).mapCocone_ι_app,leftFunctor_map]

      -- RHS
      rewrite [tm.fac_assoc,(middleFunctor L R).mapCocone_ι_app,middleFunctor_map]

      exact (s.ι.app j).wl
    wr := tm.hom_ext fun j => by
      -- LHS
      rewrite [cocone_pt_homr,tm.fac_assoc,coconePrecompose_rrm_ι_app,Category.assoc,← R.map_comp,tr.fac]
      simp only [rrm]
      rewrite [(rightFunctor L R).mapCocone_ι_app,rightFunctor_map]

      -- RHS
      rewrite [tm.fac_assoc,(middleFunctor L R).mapCocone_ι_app,middleFunctor_map]

      exact (s.ι.app j).wr
  }
  uniq s m w := by
    ext
    . exact tl.uniq ((leftFunctor   L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullbackThing.Hom.left   (w j))
    . exact tm.uniq ((middleFunctor L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullbackThing.Hom.middle (w j))
    . exact tr.uniq ((rightFunctor  L R).mapCocone s) _ (fun j => by exact congr_arg OplaxPullbackThing.Hom.right  (w j))

instance hasColimit
  [hl : HasColimit (F ⋙ leftFunctor   L R)]
  [hm : HasColimit (F ⋙ middleFunctor L R)]
  [hr : HasColimit (F ⋙ rightFunctor  L R)]
  : HasColimit F
  := HasColimit.mk ⟨_,isColimit _ (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)⟩

instance hasColimitsOfShape
  [ha : HasColimitsOfShape J A]
  [hb : HasColimitsOfShape J B]
  [hc : HasColimitsOfShape J C]
  : HasColimitsOfShape J (OplaxPullbackThing L R)
  where

instance hasColimitsOfSize
  [ha : HasColimitsOfSize.{s,s'} A]
  [hb : HasColimitsOfSize.{s,s'} B]
  [hc : HasColimitsOfSize.{s,s'} C]
  : HasColimitsOfSize.{s,s'} (OplaxPullbackThing L R)
  := ⟨fun _ _ => inferInstance⟩
