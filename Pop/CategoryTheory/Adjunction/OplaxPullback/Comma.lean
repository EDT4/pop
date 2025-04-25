import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Pop.CategoryTheory.Adjunction.Comma
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.Comma

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type _} [Category A]
variable {B : Type _} [Category B] [pub : HasPushouts B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C) -- [pnl : PreservesColimitsOfShape ℕ L]
variable (R : B ⥤ C) -- [pnr : PreservesColimitsOfShape ℕ R]
variable (Lb : C ⥤ A)
variable (Rb : C ⥤ B)
variable (Ladj : Lb ⊣ L)
variable (Radj : Rb ⊣ R)

namespace CategoryTheory.OplaxPullback

abbrev to_comma.pushout_left : projMid L R ⋙ Rb ⟶ (projLeft L R ⋙ L) ⋙ Rb
  := whiskerRight (OplaxPullback.llm _ _) Rb

abbrev to_comma.pushout_right : ((whiskeringRight (OplaxPullback L R) C B).obj Rb).obj (projMid L R) ⟶ projRight L R
  := (Adjunction.homEquiv (Adjunction.whiskerRight _ Radj) _ _).invFun (OplaxPullback.rrm _ _)

noncomputable abbrev to_comma.pushout : OplaxPullback L R ⥤ B
  := Limits.pushout (to_comma.pushout_left L R Rb) (to_comma.pushout_right L R Rb Radj)

-- TODO: select cocone
@[simps!]
noncomputable def to_comma : OplaxPullback L R ⥤ Comma L R :=
  let pl := to_comma.pushout_left L R Rb
  let pr := to_comma.pushout_right L R Rb Radj
  Comma.lift
    (OplaxPullback.projLeft _ _)
    (to_comma.pushout L R Rb Radj)
    (
      whiskerLeft (OplaxPullback.projLeft L R ⋙ L) Radj.unit
      ≫ whiskerRight (pushout.inl pl pr) R
    )

@[simp] lemma to_comma_fst : to_comma L R Rb Radj ⋙ Comma.fst L R = OplaxPullback.projLeft L R   := Comma.lift_fst
@[simp] lemma to_comma_snd : to_comma L R Rb Radj ⋙ Comma.snd L R = to_comma.pushout L R Rb Radj := Comma.lift_snd
@[simp] lemma to_comma_natTrans
  : whiskerLeft (to_comma L R Rb Radj) (Comma.natTrans L R)
  = whiskerLeft (OplaxPullback.projLeft L R ⋙ L) Radj.unit
  ≫ whiskerRight (pushout.inl (to_comma.pushout_left L R Rb) (to_comma.pushout_right L R Rb Radj)) R
  := Comma.lift_natTrans

-- TODO: ?
noncomputable def Limits.pushoutIso
  {A : Type _} [Category A]
  {B : Type _} [Category B]
  {C : Type _} [Category C] [HasPushouts C]
  {F G₁ G₂ : B ⥤ C}
  (H : A ⥤ B)
  (f : F ⟶ G₁) (g : F ⟶ G₂)
  : H ⋙ pushout f g ≅ pushout (whiskerLeft H f) (whiskerLeft H g)
  := NatIso.ofComponents
    (fun a => Limits.pushoutObjIso f g (H.obj a) ≪≫ (Limits.pushoutObjIso (whiskerLeft H f) (whiskerLeft H g) a).symm)
    (by
      intro x y f
      simp
      sorry
    )

-- TODO: where?
def whiskerLeft_functor_comp
  {A : Type _} [Category A]
  {B : Type _} [Category B]
  {C : Type _} [Category C]
  {D : Type _} [Category D]
  (F : A ⥤ B)
  (G : B ⥤ C)
  (H₁ H₂ : C ⥤ D)
  (η : H₁ ⟶ H₂)
  : whiskerLeft (F ⋙ G) η = whiskerLeft F (whiskerLeft G η)
  := rfl
def whiskerLeft_functor_id
  {A : Type _} [Category A]
  {B : Type _} [Category B]
  (H₁ H₂ : A ⥤ B)
  (η : H₁ ⟶ H₂)
  : whiskerLeft (𝟭 _) η = η
  := rfl

noncomputable def to_from_comma_adj : OplaxPullback.to_comma L R Rb Radj ⊣ OplaxPullback.from_comma L R where
  unit := OplaxPullback.liftTrans
    (𝟙 _)
    (OplaxPullback.llm _ _)
    (pushout.inr _ _)
    (by
      simp only [whiskerRight_id',whiskerLeft_functor_id,whiskerLeft_functor_comp,from_comma_llm,whiskerLeft_id,whiskerLeft_id']
      rfl
    )
    (by
      rw [whiskerLeft_functor_comp,OplaxPullback.from_comma_rrm,to_comma_natTrans,whiskerLeft_functor_id]
      -- simp [pushout.condition]
      sorry
    )
    -- (by
    --   ext
    --   simp [Adjunction.homEquiv]
    --   -- apply Comma.lift_ext
    --   let cond := pushout.condition (f := to_comma.pushout_left L R Rb) (g := to_comma.pushout_right L R Rb Radj)
    --   -- simp [to_comma.pushout_left,to_comma.pushout_right,whiskerLeft,whiskerRight,Adjunction.whiskerRight,Adjunction.homEquiv]
    --   -- rfl
    --   -- rw [pushout.condition]
    --   sorry
    -- )
  counit := Comma.liftTrans
    (𝟙 _)
    ((Limits.pushoutIso _ _ _).hom ≫ pushout.desc
      (whiskerRight (Comma.natTrans L R) Rb ≫ whiskerLeft (Comma.snd L R) Radj.counit)
      (𝟙 _)
      (by simp [to_comma.pushout_left,to_comma.pushout_right,Adjunction.homEquiv] ; sorry)
    )
    -- ({
    --     app o := (Limits.pushoutObjIso _ _ _).hom ≫ pushout.desc
    --       (Rb.map o.hom ≫ Radj.counit.app o.right)
    --       (𝟙 _)
    --       (by simp only [Functor.comp_obj,projMid_obj,from_comma_obj_middle,whiskerRight_app,llm_app,from_comma_obj_homl,Functor.map_id,Category.id_comp,projRight_obj,from_comma_obj_right,to_comma.pushout_right,Adjunction.homEquiv,whiskeringRight_obj_map,NatTrans.comp_app, rrm_app, from_comma_obj_homr, Adjunction.whiskerRight_counit_app_app,Category.comp_id])
    --     naturality := sorry
    -- })

    -- (whiskerLeft (from_comma L R) $ pushout.desc
    --   (
    --     let t := whiskerRight (Comma.natTrans L R) Rb ≫ whiskerLeft (Comma.snd L R) Radj.counit
    --     sorry
    --   )
    --   (𝟙 _)
    --   sorry
    -- )
    (by simp ; sorry)
  left_triangle_components := sorry
  right_triangle_components := sorry
